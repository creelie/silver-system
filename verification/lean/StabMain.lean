import BiplanarF.Stab

/-- A literal in DIMACS form. -/
def litStr (l : Std.Sat.Literal Nat) : String :=
  if l.2 then toString (l.1 + 1) else "-" ++ toString (l.1 + 1)

/-- `stab-dump n p s1,s2,… dmin flags out.cnf` writes the formula `Stab.encode n p sizes dmin flags`
in DIMACS form, with the header `p cnf V C` where `V` counts the auxiliary variables too. -/
def main (args : List String) : IO Unit := do
  let n := args[0]!.toNat!
  let p := args[1]!.toNat!
  let sizes := (args[2]!.splitOn ",").map String.toNat!
  let dmin := args[3]!.toNat!
  let flags := if args[4]! == "-" then "" else args[4]!
  let s := Stab.encodeSt n p sizes dmin flags
  let h ← IO.FS.Handle.mk args[5]! .write
  h.putStrLn s!"p cnf {s.top} {s.cls.size}"
  for c in s.cls do
    h.putStrLn (" ".intercalate (c.map litStr) ++ " 0")
  h.flush
  IO.println s!"{n} {p} {sizes} {dmin} {flags}: {s.top} variables, {s.cls.size} clauses"
