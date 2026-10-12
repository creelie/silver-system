module

public import Std.Tactic.BVDecide
open Std.Sat

/-!
# CNF encoding of the Turán-stability models for Gethner–Sulanke Open Problem 1(b)

`Stab.encode n p sizes dmin flags` says: there is a graph `U` on the vertices `0, …, n-1` that is the
union of two plane triangulations `T₀, T₁` on the same vertices, has independence number at most `p`,
and whose complement `H` is split into the parts `P₀, P₁, …` (consecutive blocks of the given sizes)
by a partition that minimises the number of edges of `H` inside the parts. It is the formula written by
`scripts/stab2.py n p sizes out dmin - flags`, clause for clause and variable for variable (the
cardinality constraints are PySAT's sequential counter and totalizers), with the redundant
constraints named by `flags` (letters `a b d e p r`, and `n` to leave out the symmetry breaking).

Literals are written as signed DIMACS numbers (`Int`, variables counted from 1) and stored as
`cubeLit x = (|x| - 1, x > 0)`, so `Std.Sat.CNF.dimacs` prints them back unchanged. With `N = n(n-1)/2`
and `idx a b` the position of the pair `a < b` in the list of pairs:
* `E a b = 1 + idx a b`: `ab` is an edge of `U`;
* `L l a b = 1 + N + l N + idx a b`: `ab` is an edge of `T_l`;
* `O l i a b = 1 + 3N + (3l + i) N + idx a b`: `a` precedes `b` in Schnyder order `i` of `T_l`;
* auxiliary variables from `9N + 1` on, in order of creation.

Clauses (in this order):
1. each `O l i` is a strict linear order;
2. `U = T₀ ∪ T₁`;
3. Schnyder's condition for every edge of `T_l` (so `T_l` is planar); `T_l` has `3n - 6` edges;
4. Euler's bound in `T_l` on each part (`3s - 6`) and between two parts (bipartite: `2s - 4`);
5. every `p + 1` vertices span an edge of `U`; no 9 vertices of one part are pairwise adjacent
   (`K₉` is not biplanar);
6. Füredi's stability bound: `2 |M| + (non-edges of U between parts) ≤ t(n, p)` (Turán number), where
   `M` is the set of non-edges of `U` inside the parts;
7. local optimality: moving a vertex to another part does not lower the number of edges of `H`
   inside the parts; every vertex has degree at least `dmin` in `U`;
8. symmetry breaking: inside a part, the rows of the adjacency matrix of `U` (columns other than the
   two rows) increase lexicographically; if `01` is an edge of `U`, it lies in `T₀`;
9. redundant consequences of planarity (flags): `a` Euler on a part plus one vertex; `b` Euler on the
   union of two parts; `d` every vertex has degree at least 3 in `T_l`; `e` every edge of `T_l` lies in
   two triangles of `T_l`; `p` port bounds: if `T_l[Q]` has at least `K(|Q|)` edges it is connected
   (`K = 1, 2, 3s - 8` for `s = 2, 3, ≥ 4`), and contracting it gives `e(T_l[P]) + |N(Q) ∩ P| ≤ 3|P| - 3`;
   with two connected parts contracted separately, `≤ 3|P|`; `r` if they are also joined in `T_l`,
   contracting their union gives `≤ 3|P| - 3`, and separately `≤ 3|P| - 1`.
-/

@[expose] public section

namespace Stab

abbrev Lit := Literal Nat
@[inline] def Lit.neg (l : Lit) : Lit := (l.1, !l.2)

/-- A signed DIMACS literal (variables counted from 1) as a literal of `Std.Sat.CNF Nat`. -/
def cubeLit (x : Int) : Lit := ((x.natAbs - 1 : Nat), decide (0 < x))

structure St where
  /-- the largest variable number used so far -/
  top : Nat
  cls : Array (CNF.Clause Nat)

abbrev M := StateM St

/-- A new variable. -/
def newVar : M Int := modifyGet fun s => (((s.top + 1 : Nat) : Int), { s with top := s.top + 1 })
def emit (c : List Int) : M Unit := modify fun s => { s with cls := s.cls.push (c.map cubeLit) }

/-- The `k`-element sublists of a list (in lexicographic order). -/
def choose : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs => (choose k xs).map (x :: ·) ++ choose (k + 1) xs

/-- The pairs `(a, b)`, `a < b`, of a list of increasing numbers. -/
def pairsOf : List Nat → List (Nat × Nat)
  | [] => []
  | x :: xs => xs.map (x, ·) ++ pairsOf xs

/-- At most `k` of the literals `xs`, every clause extended by `extra`: PySAT's sequential counter.
Registers `s(i, j)` ("at least `j` of `x₁ … x_i`"), `1 ≤ i ≤ N - 1`, `1 ≤ j ≤ k`, on the diagonals
`d = i - j ≤ N - k - 1`, numbered when first mentioned. -/
def seqAtMost (xs : Array Int) (k : Nat) (extra : List Int) : M Unit := do
  let N := xs.size
  if N == 0 || k ≥ N then return
  if k == 0 then
    for x in xs do emit ((-x) :: extra)
    return
  if k + 1 == N then
    emit (xs.toList.map (- ·) ++ extra)
    return
  let mut reg : Std.HashMap (Nat × Nat) Int := {}
  for d in [0:N - k] do
    for i in [d + 1:min N (d + k + 1)] do
      let j := i - d
      if j == 1 then
        let v ← match reg[(i, 1)]? with
          | some v => pure v
          | none => do let v ← newVar; reg := reg.insert (i, 1) v; pure v
        emit ([-xs[i-1]!, v] ++ extra)
      let s := reg[(i, j)]!
      if i + 1 ≤ N - 1 && d + 1 ≤ N - k - 1 then
        let v ← match reg[(i + 1, j)]? with
          | some v => pure v
          | none => do let v ← newVar; reg := reg.insert (i + 1, j) v; pure v
        emit ([-s, v] ++ extra)
      if j < k then
        if i + 1 ≤ N - 1 then
          let v ← match reg[(i + 1, j + 1)]? with
            | some v => pure v
            | none => do let v ← newVar; reg := reg.insert (i + 1, j + 1) v; pure v
          emit ([-xs[i]!, -s, v] ++ extra)
      else
        emit ([-xs[i]!, -s] ++ extra)

/-- At least `k ≤ N` of the literals `xs`: at most `N - k` of their negations. -/
def seqAtLeast (xs : Array Int) (k : Nat) : M Unit := seqAtMost (xs.map (- ·)) (xs.size - k) []

/-- A node of PySAT's totalizer over the literals `xs` (`size ≥ 2`) with outputs `outs` ("at least
`j + 1`"): the left half has the first `⌈size/2⌉` literals. -/
partial def totNode (xs : Array Int) (outs : Array Int) : M Unit := do
  let n := xs.size
  let nl := n - n / 2
  let L := xs.extract 0 nl
  let R := xs.extract nl n
  let mut lo := L
  if nl > 1 then
    lo := #[]
    for _ in [0:nl] do lo := lo.push (← newVar)
  let mut ro := R
  if n / 2 > 1 then
    ro := #[]
    for _ in [0:n / 2] do ro := ro.push (← newVar)
  for j in [0:ro.size] do emit [-ro[j]!, outs[j]!]
  for i in [0:lo.size] do emit [-lo[i]!, outs[i]!]
  for i in [0:lo.size] do
    for j in [0:ro.size] do emit [-lo[i]!, -ro[j]!, outs[i + j + 1]!]
  if n / 2 > 1 then totNode R ro
  if nl > 1 then totNode L lo

/-- At most `k` of the literals `xs`: PySAT's totalizer. -/
def totAtMost (xs : Array Int) (k : Nat) : M Unit := do
  let N := xs.size
  if N == 0 || k ≥ N then return
  if k == 0 then
    for x in xs do emit [-x]
    return
  if k + 1 == N then
    emit (xs.toList.map (- ·))
    return
  let mut outs : Array Int := #[]
  for _ in [0:N] do outs := outs.push (← newVar)
  totNode xs outs
  emit [-outs[k]!]

/-- Exactly `k ≤ N` of the literals `xs` (PySAT's `CardEnc.equals` with the totalizer). -/
def totEquals (xs : Array Int) (k : Nat) : M Unit := do
  totAtMost (xs.map (- ·)) (xs.size - k)
  totAtMost xs k

/-- PySAT's `ITotalizer(xs, ubound)`: outputs `rhs[j]` forced true when at least `j + 1` of `xs` are
true (`j ≤ ubound`); nodes are merged in first-in first-out order. -/
def itot (xs : Array Int) (ubound : Nat) : M (Array Int) := do
  let cap := ubound + 1
  let mut q : Array (Array Int) := xs.map (#[·])
  let mut head := 0
  while head + 1 < q.size do
    let a := q[head]!
    let b := q[head + 1]!
    head := head + 2
    let m := min (a.size + b.size) cap
    let mut o : Array Int := #[]
    for _ in [0:m] do o := o.push (← newVar)
    for j in [0:b.size] do emit [-b[j]!, o[j]!]
    for i in [0:a.size] do emit [-a[i]!, o[i]!]
    for i in [0:a.size] do
      for j in [0:b.size] do
        if i + j + 2 ≤ m then emit [-a[i]!, -b[j]!, o[i + j + 1]!]
    q := q.push o
  return q[head]!

/-- Turán's number `t(n, p)`. -/
def turan (n p : Nat) : Nat :=
  let q := n / p
  let r := n % p
  (n * n - (r * (q + 1) * (q + 1) + (p - r) * q * q)) / 2

/-- The parts: consecutive blocks of the given sizes. -/
def parts (sizes : List Nat) : Array (Array Nat) := Id.run do
  let mut ps : Array (Array Nat) := #[]
  let mut v := 0
  for s in sizes do
    ps := ps.push ((Array.range s).map (v + ·))
    v := v + s
  return ps

/-- The state after writing the formula (`top` is the number of variables). -/
def encodeSt (n p : Nat) (sizes : List Nat) (dmin : Nat) (flags : String) : St := Id.run do
  let P := parts sizes
  let part : Array Nat := Id.run do
    let mut a : Array Nat := #[]
    for i in [0:P.size] do
      for _ in P[i]! do a := a.push i
    return a
  let V := List.range n
  let prs := pairsOf V
  let N := n * (n - 1) / 2
  let has (c : Char) : Bool := flags.contains c
  let idx (a b : Nat) : Nat := a * n - a * (a + 1) / 2 + (b - a - 1)
  let E (a b : Nat) : Int := if a < b then 1 + idx a b else 1 + idx b a
  let L (l a b : Nat) : Int := (1 + N + l * N : Nat) + (if a < b then idx a b else idx b a : Nat)
  let O (l i a b : Nat) : Int :=
    if a < b then ((1 + 3 * N + (3 * l + i) * N + idx a b : Nat) : Int)
    else -((1 + 3 * N + (3 * l + i) * N + idx b a : Nat) : Int)
  let inner (l : Nat) (Q : Array Nat) : List Int := (pairsOf Q.toList).map fun (a, b) => L l a b
  let act : M Unit := do
    -- 1. linear orders
    for l in [0:2] do
      for i in [0:3] do
        for a in [0:n] do
          for b in [0:n] do
            for c in [0:n] do
              if a != b && b != c && a != c then
                emit [-O l i a b, -O l i b c, O l i a c]
    -- 2. U = T₀ ∪ T₁
    for (a, b) in prs do
      emit [-E a b, L 0 a b, L 1 a b]
      for l in [0:2] do emit [-L l a b, E a b]
    -- 3. Schnyder's condition
    for l in [0:2] do
      for (a, b) in prs do
        for x in [0:n] do
          if x != a && x != b then
            let mut zs : List Int := []
            for i in [0:3] do
              let z ← newVar
              emit [-z, O l i a x]
              emit [-z, O l i b x]
              zs := zs ++ [z]
            emit ((-L l a b) :: zs)
    -- each layer is a triangulation: 3n - 6 edges
    for l in [0:2] do totEquals (prs.map fun (a, b) => L l a b).toArray (3 * n - 6)
    -- 4. Euler on a part and between two parts (bipartite)
    for l in [0:2] do
      for Q in P do
        if Q.size ≥ 3 then seqAtMost (inner l Q).toArray (3 * Q.size - 6) []
      for (qi, ri) in pairsOf (List.range P.size) do
        let Q := P[qi]!
        let R := P[ri]!
        if Q.size + R.size ≥ 3 then
          seqAtMost (Q.toList.flatMap fun a => R.toList.map fun b => L l a b).toArray
            (2 * (Q.size + R.size) - 4) []
    -- 5. independence number at most p; no K₉ inside a part
    for S in choose (p + 1) V do
      emit ((pairsOf S).map fun (a, b) => E a b)
    for Q in P do
      if Q.size ≥ 9 then
        for S in choose 9 Q.toList do
          emit ((pairsOf S).map fun (a, b) => -E a b)
    -- 6. Füredi's bound: a non-edge inside a part counts twice (each count is a copy variable)
    let mut dl : Array Int := #[]
    for (a, b) in prs do
      for _ in [0:(if part[a]! == part[b]! then 2 else 1)] do
        let c ← newVar
        emit [E a b, c]
        dl := dl.push c
    seqAtMost dl (turan n p) []
    -- 7. local optimality and minimum degree
    for v in [0:n] do
      let i := part[v]!
      for j in [0:P.size] do
        if j != i then
          seqAtMost ((P[i]!.toList.filter (· != v)).map (fun u => -E v u) ++
            P[j]!.toList.map (E v ·)).toArray P[j]!.size []
    if dmin > 0 then
      for v in [0:n] do seqAtLeast ((V.filter (· != v)).map (E v ·)).toArray dmin
    -- 8. symmetry breaking
    if !has 'n' then
      for Q in P do
        for (i, j) in pairsOf Q.toList do
          let mut prev : Option Int := none
          for k in [0:n] do
            if k != i && k != j then
              let pre : List Int := match prev with | some e => [-e] | none => []
              let a := E i k
              let b := E j k
              emit (pre ++ [-a, b])
              let eq ← newVar
              emit (pre ++ [a, b, eq])
              emit (pre ++ [-a, -b, eq])
              prev := some eq
    if n ≥ 2 && part[0]! == part[1]! then emit [-E 0 1, L 0 0 1]
    -- 9. redundant consequences of planarity
    if has 'a' then
      for l in [0:2] do
        for Q in P do
          if Q.size ≥ 2 then
            for v in [0:n] do
              if !Q.contains v then
                seqAtMost (inner l Q ++ Q.toList.map (L l v ·)).toArray (3 * Q.size - 3) []
    if has 'b' then
      for l in [0:2] do
        for (qi, ri) in pairsOf (List.range P.size) do
          let S := P[qi]! ++ P[ri]!
          if S.size ≥ 3 then seqAtMost (inner l S).toArray (3 * S.size - 6) []
    if has 'd' then
      for l in [0:2] do
        for v in [0:n] do seqAtLeast ((V.filter (· != v)).map (L l v ·)).toArray 3
    if has 'e' then
      for l in [0:2] do
        for (a, b) in prs do
          let mut ts : Array Int := #[]
          for x in [0:n] do
            if x != a && x != b then
              let t ← newVar
              emit [-t, L l a x]
              emit [-t, L l b x]
              ts := ts.push t
          for x in [0:ts.size] do
            emit ((-L l a b) :: ((List.range ts.size).filter (· != x)).map (ts[·]!))
          emit ((-L l a b) :: ts.toList)
    if has 'p' then
      -- conn[l][q]: forced true when T_l[P_q] has at least K edges (so it is connected); none for a
      -- single vertex
      let mut conn : Array (Array (Option Int)) := #[]
      for l in [0:2] do
        let mut row : Array (Option Int) := #[]
        for Q in P do
          let s := Q.size
          if s ≤ 1 then row := row.push none
          else
            let K := if s == 2 then 1 else if s == 3 then 2 else 3 * s - 8
            let rhs ← itot (inner l Q).toArray K
            row := row.push (some rhs[K - 1]!)
        conn := conn.push row
      for l in [0:2] do
        let gs (qs : List Nat) : List Int := qs.filterMap fun q => (conn[l]!)[q]!.map (- ·)
        -- Y[q][v]: v is joined in T_l to a vertex of part q
        let mut Y : Std.HashMap (Nat × Nat) Int := {}
        for pi in [0:P.size] do
          for qi in [0:P.size] do
            if qi != pi then
              for v in P[pi]! do
                let y ← newVar
                Y := Y.insert (qi, v) y
                for u in P[qi]! do emit [-L l v u, y]
        for pi in [0:P.size] do
          let Pp := P[pi]!
          if Pp.size ≥ 2 then
            let inn := inner l Pp
            let others := (List.range P.size).filter (· != pi)
            let Yq (q : Nat) : List Int := Pp.toList.map fun v => Y[(q, v)]!
            for qi in others do
              seqAtMost (inn ++ Yq qi).toArray (3 * Pp.size - 3) (gs [qi])
            match others with
            | [q1, q2] =>
              if has 'r' then
                let adj ← newVar
                for a in P[q1]! do
                  for b in P[q2]! do emit [-L l a b, adj]
                let mut zs : List Int := []
                for v in Pp do
                  let z ← newVar
                  emit [-Y[(q1, v)]!, z]
                  emit [-Y[(q2, v)]!, z]
                  zs := zs ++ [z]
                seqAtMost (inn ++ zs).toArray (3 * Pp.size - 3) (gs [q1, q2] ++ [-adj])
                seqAtMost (inn ++ Yq q1 ++ Yq q2).toArray (3 * Pp.size - 1) (gs [q1, q2] ++ [-adj])
              seqAtMost (inn ++ Yq q1 ++ Yq q2).toArray (3 * Pp.size) (gs [q1, q2])
            | _ => pure ()
  let (_, s) := act.run { top := 9 * N, cls := #[] }
  return s

def encode (n p : Nat) (sizes : List Nat) (dmin : Nat) (flags : String) : CNF Nat :=
  { clauses := (encodeSt n p sizes dmin flags).cls }


/-- The literals of a cube as unit clauses. -/
def units (cube : List Int) : CNF Nat := { clauses := (cube.map fun x => [cubeLit x]).toArray }

/-- The formula with the literals of a cube as unit clauses (after the clauses of `f`). -/
def withCube (f : CNF Nat) (cube : List Int) : CNF Nat := f ++ units cube

/-- The clauses "not all literals of the cube": unsatisfiable exactly when the cubes cover every
assignment. -/
def cover (cubes : List (List Int)) : CNF Nat :=
  { clauses := (cubes.map fun c => c.map fun x => Lit.neg (cubeLit x)).toArray }

theorem eval_units_of_cover {a : Nat → Bool} {c : List Int}
    (h : CNF.Clause.eval a (c.map fun x => Lit.neg (cubeLit x)) = false) :
    CNF.eval a (units c) = true := by
  simp only [CNF.Clause.eval, List.any_eq_false, List.mem_map] at h
  simp only [CNF.eval, units, List.all_toArray, List.all_eq_true, List.mem_map]
  rintro _ ⟨x, hx, rfl⟩
  have := h _ ⟨x, hx, rfl⟩
  simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false]
  simp only [Lit.neg] at this
  cases h1 : a (cubeLit x).1 <;> cases h2 : (cubeLit x).2 <;> simp_all

/-- Cube and conquer: if the cubes cover every assignment and the formula is refuted under each
cube, the formula is unsatisfiable. -/
theorem unsat_of_cubes (f : CNF Nat) (cubes : List (List Int)) (hcov : (cover cubes).Unsat)
    (hall : ∀ c ∈ cubes, (withCube f c).Unsat) : f.Unsat := by
  intro a
  cases hf : CNF.eval a f
  · rfl
  · exfalso
    have h1 := hcov a
    simp only [CNF.eval, cover, List.all_toArray, List.all_eq_false, List.mem_map] at h1
    obtain ⟨_, ⟨c, hc, rfl⟩, hcl⟩ := h1
    have hu := eval_units_of_cover (by simpa using hcl)
    have := hall c hc a
    simp [withCube, hf, hu] at this

/-- Every cube of the list, with its LRAT certificate, is refuted. -/
def checkCubes (f : CNF Nat) (cs : List (List Int × String)) : Bool :=
  cs.all fun (c, cert) => Std.Tactic.BVDecide.Reflect.verifyCert (withCube f c) cert

theorem of_checkCubes {f : CNF Nat} {cs : List (List Int × String)} (h : checkCubes f cs = true) :
    ∀ p ∈ cs, (withCube f p.1).Unsat := by
  intro p hp
  simp only [checkCubes, List.all_eq_true] at h
  exact Std.Tactic.BVDecide.Reflect.verifyCert_correct _ _ (h p hp)

/-- Every cube is refuted by the certificate at the same position. -/
def checkAll (f : CNF Nat) : List (List Int) → List String → Bool
  | [], _ => true
  | c :: cs, cert :: certs =>
    Std.Tactic.BVDecide.Reflect.verifyCert (withCube f c) cert && checkAll f cs certs
  | _ :: _, [] => false

theorem of_checkAll {f : CNF Nat} : ∀ {cubes : List (List Int)} {certs : List String},
    checkAll f cubes certs = true → ∀ c ∈ cubes, (withCube f c).Unsat
  | [], _, _ => by simp
  | c :: cs, cert :: certs, h => by
    simp only [checkAll, Bool.and_eq_true] at h
    intro c' hc'
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact Std.Tactic.BVDecide.Reflect.verifyCert_correct _ _ h.1
    · exact of_checkAll h.2 c' hc'
  | _ :: _, [], h => by simp [checkAll] at h

theorem forall_flatten {P : List Int → Prop} {Ls : List (List (List Int))}
    (h : ∀ L ∈ Ls, ∀ c ∈ L, P c) : ∀ c ∈ Ls.flatten, P c := by
  intro c hc
  obtain ⟨L, hL, hcL⟩ := List.mem_flatten.mp hc
  exact h L hL c hcL

end Stab

end
