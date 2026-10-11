import Std.Tactic.BVDecide
open Std.Sat

/-!
# CNF encoding of "the clique blow-up F[w] is biplanar"

`F` is a graph on bags `0, …, k-1` (the second argument, edges `a-b`). Vertices `0, …, n-1` are split
into bags of sizes `w₀, …, w_{k-1}`; two distinct vertices are adjacent when their bags are equal or
adjacent in `F`. Usage: `lean --run DumpF.lean w0,w1,… a-b,c-d,… out.cnf`.

Variables (all literals are `(var, polarity)` as in `Std.Sat.CNF`):
* `ord l i a b` (`a < b`): in layer `l ∈ {0,1}` and Schnyder order `i ∈ {0,1,2}`, `a` precedes `b`;
* `lay l a b` (`a < b`, `ab` an edge): the edge `ab` is drawn in layer `l`;
* one constant `TRUE`, and fresh gate variables.

Clauses:
1. each `ord l i` is a strict linear order (transitivity);
2. every edge lies in layer 0 or layer 1;
3. Schnyder's condition: if `uv` lies in layer `l` then every other vertex `x` is above both `u`
   and `v` in one of the three orders of layer `l` (so each layer is planar);
4. twins in a bag appear in increasing order in `ord 0 0` (an automorphism normalisation);
5. the K₉ certificates: for an 8-clique `Q` (a union of pairwise adjacent bags) and `W = V \ Q`, contracting a
   component of `L_l[W]` (or a new isolated vertex) to a vertex `z`, and adding at most one bridge
   from `z` into each component of `L_l[Q]` that `z` does not reach, must not make `z` adjacent to
   all of `Q` in `H₀ ∪ H₁` (otherwise `K₉` would be biplanar). Clauses are emitted for covers that
   use at most two bridges.
-/

namespace Biplanar

abbrev Lit := Literal Nat
@[inline] def pos (v : Nat) : Lit := (v, true)
@[inline] def Lit.neg (l : Lit) : Lit := (l.1, !l.2)

structure Inst where
  k : Nat
  n : Nat
  bag : Array Nat
  parts : Array (Array Nat)
  fadj : Array (Array Bool)

def mkInst (w : List Nat) (fe : List (Nat × Nat)) : Inst := Id.run do
  let mut bag : Array Nat := #[]
  let mut parts : Array (Array Nat) := #[]
  let mut v := 0
  for i in [0:w.length] do
    let mut P : Array Nat := #[]
    for _ in [0:w[i]!] do
      bag := bag.push i; P := P.push v; v := v + 1
    parts := parts.push P
  let k := w.length
  let fadj := Array.ofFn (n := k) fun i => Array.ofFn (n := k) fun j =>
    fe.any fun (a, b) => (a == i.1 && b == j.1) || (a == j.1 && b == i.1)
  return { k, n := v, bag, parts, fadj }

def Inst.adj (I : Inst) (a b : Nat) : Bool :=
  a != b && (I.bag[a]! == I.bag[b]! || I.fadj[I.bag[a]!]![I.bag[b]!]!)

def Inst.edges (I : Inst) : Array (Nat × Nat) := Id.run do
  let mut E := #[]
  for a in [0:I.n] do
    for b in [a+1:I.n] do
      if I.adj a b then E := E.push (a, b)
  return E

structure St where
  next : Nat
  cls : Array (CNF.Clause Nat)

abbrev M := StateM St

def fresh : M Nat := modifyGet fun s => (s.next, { s with next := s.next + 1 })
def emit (c : List Lit) : M Unit := modify fun s => { s with cls := s.cls.push c }

section
variable (I : Inst)
/-- `a` precedes `b` in order `i` of layer `l`. -/
def lt (l i a b : Nat) : Lit :=
  if a < b then pos (((l * 3 + i) * I.n + a) * I.n + b)
  else (pos (((l * 3 + i) * I.n + b) * I.n + a)).neg
/-- edge `ab` lies in layer `l`. -/
def lay (l a b : Nat) : Lit :=
  let (a, b) := if a < b then (a, b) else (b, a)
  pos (6 * I.n * I.n + (l * I.n + a) * I.n + b)
def tru : Lit := pos (8 * I.n * I.n)
end

def AND (_I : Inst) (ts : List Lit) : M Lit := do
  let a ← fresh
  for t in ts do emit [(a, false), t]
  emit ((a, true) :: ts.map Lit.neg)
  return pos a

def OR (I : Inst) (ts : List Lit) : M Lit := do
  if ts.isEmpty then return (tru I).neg
  let a ← fresh
  for t in ts do emit [(a, true), t.neg]
  emit ((a, false) :: ts)
  return pos a

/-- `R[x][y]` (indices into `S`): `S[x]` and `S[y]` are joined by a path of `L_l[S]`. -/
def reach (I : Inst) (l : Nat) (S : Array Nat) : M (Array (Array Lit)) := do
  let m := S.size
  let mut R : Array (Array Lit) :=
    Array.ofFn (n := m) fun x => Array.ofFn (n := m) fun y =>
      if x.1 == y.1 then tru I else (tru I).neg
  for _ in [0:m - 1] do
    let mut R2 : Array (Array Lit) := #[]
    for x in [0:m] do
      let mut row : Array Lit := #[]
      for y in [0:m] do
        if x == y then row := row.push (tru I)
        else
          let mut terms : List Lit := [R[x]![y]!]
          for z in [0:m] do
            if z != y && I.adj S[z]! S[y]! then
              terms := terms ++ [← AND I [R[x]![z]!, lay I l S[z]! S[y]!]]
          row := row.push (← OR I terms)
      R2 := R2.push row
    R := R2
  return R

def encode (w : List Nat) (fe : List (Nat × Nat)) : CNF Nat := Id.run do
  let I := mkInst w fe
  let n := I.n
  let E := I.edges
  let act : M Unit := do
    -- 1. linear orders
    for l in [0:2] do
      for i in [0:3] do
        for a in [0:n] do
          for b in [0:n] do
            for c in [0:n] do
              if a != b && b != c && a != c then
                emit [(lt I l i a b).neg, (lt I l i b c).neg, lt I l i a c]
    -- 2. every edge in some layer
    for (a, b) in E do emit [lay I 0 a b, lay I 1 a b]
    -- 3. Schnyder condition
    for (u, v) in E do
      for l in [0:2] do
        for x in [0:n] do
          if x != u && x != v then
            let mut zs : List Lit := []
            for i in [0:3] do
              let z ← fresh
              emit [(z, false), lt I l i u x]
              emit [(z, false), lt I l i v x]
              zs := zs ++ [pos z]
            emit ((lay I l u v).neg :: zs)
    -- 4. twins in increasing order
    for P in I.parts do
      for j in [0:P.size - 1] do emit [lt I 0 0 P[j]! P[j+1]!]
    emit [tru I]
    -- 5. K₉ certificates
    for msk in [1:2 ^ I.k] do
      let bs := (List.range I.k).filter fun i => msk.testBit i
      let isCl := bs.all fun i => bs.all fun j => i == j || I.fadj[i]![j]!
      let Q := bs.foldl (fun acc i => acc ++ I.parts[i]!) #[]
      if isCl && Q.size == 8 then
        let W := (Array.range n).filter fun x => !(Q.contains x)
        let X : Array (Option Nat) := (W.map some).push none
        -- att[l][xi][q], free[l][xi][u], cq[l][u][q2]  (xi, q, u, q2 are positions)
        let mut att : Array (Array (Array Lit)) := #[]
        let mut free : Array (Array (Array Lit)) := #[]
        let mut cq : Array (Array (Array Lit)) := #[]
        for l in [0:2] do
          let RW ← reach I l W
          let RQ ← reach I l Q
          cq := cq.push RQ
          let mut attL : Array (Array Lit) := #[]
          let mut freeL : Array (Array Lit) := #[]
          for xi in [0:X.size] do
            let mut row : Array Lit := #[]
            for q in Q do
              match X[xi]! with
              | none => row := row.push (tru I).neg
              | some _ =>
                let mut ts : List Lit := []
                for y in [0:W.size] do
                  if I.adj W[y]! q then
                    ts := ts ++ [← AND I [RW[xi]![y]!, lay I l W[y]! q]]
                row := row.push (← OR I ts)
            attL := attL.push row
            let mut frow : Array Lit := #[]
            for u in [0:Q.size] do
              let mut ts : List Lit := []
              for q2 in [0:Q.size] do
                ts := ts ++ [(← AND I [RQ[u]![q2]!, row[q2]!]).neg]
              frow := frow.push (← AND I ts)
            freeL := freeL.push frow
          att := att.push attL
          free := free.push freeL
        for x1 in [0:X.size] do
          for x2 in [0:X.size] do
            let mut cov : Array Lit := #[]
            for q in [0:Q.size] do
              cov := cov.push (← OR I [att[0]![x1]![q]!, att[1]![x2]![q]!])
            let others (ex : List Nat) : List Lit :=
              ((List.range Q.size).filter fun q => !(ex.contains q)).map fun q => cov[q]!.neg
            -- F1: z covers Q with no bridge
            emit (others [])
            -- F2: one bridge
            for u in [0:Q.size] do
              emit (others [u] ++ [free[0]![x1]![u]!.neg])
              emit (others [u] ++ [free[1]![x2]![u]!.neg])
            -- F3: two bridges
            for u in [0:Q.size] do
              for u2 in [u+1:Q.size] do
                let r := others [u, u2]
                emit (r ++ [free[0]![x1]![u]!.neg, free[1]![x2]![u2]!.neg])
                emit (r ++ [free[1]![x2]![u]!.neg, free[0]![x1]![u2]!.neg])
                emit (r ++ [free[0]![x1]![u]!.neg, free[0]![x1]![u2]!.neg, cq[0]![u]![u2]!])
                emit (r ++ [free[1]![x2]![u]!.neg, free[1]![x2]![u2]!.neg, cq[1]![u]![u2]!])
  let (_, s) := act.run { next := 8 * n * n + 1, cls := #[] }
  return { clauses := s.cls }

end Biplanar

def main (args : List String) : IO Unit := do
  let w := (args[0]!.splitOn ",").map String.toNat!
  let fe := if args[1]! == "-" then [] else (args[1]!.splitOn ",").map fun e =>
    match e.splitOn "-" with
    | [a, b] => (a.toNat!, b.toNat!)
    | _ => (0, 0)
  let f := Biplanar.encode w fe
  IO.FS.writeFile args[2]! (Std.Sat.CNF.dimacs f)
  IO.println s!"{w}: {f.clauses.size} clauses, {f.numLiterals} vars"
