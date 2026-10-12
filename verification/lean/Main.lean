import BiplanarF.Encode

/-- `biplanarf-dump w a-b,c-d,… out.cnf` writes the formula `Φ(F, w)` of `Biplanar.encode` in DIMACS form. -/
def main (args : List String) : IO Unit := do
  let w := (args[0]!.splitOn ",").map String.toNat!
  let fe := if args[1]! == "-" then [] else (args[1]!.splitOn ",").map fun e =>
    match e.splitOn "-" with
    | [a, b] => (a.toNat!, b.toNat!)
    | _ => (0, 0)
  let f := Biplanar.encode w fe
  IO.FS.writeFile args[2]! (Std.Sat.CNF.dimacs f)
  IO.println s!"{w}: {f.clauses.size} clauses"
