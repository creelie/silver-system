import Lake
open Lake DSL

package BiplanarF

/-- the encoder `Biplanar.encode w fe` of "the clique blow-up F[w] is biplanar" -/
@[default_target]
lean_lib BiplanarF

/-- `biplanarf-dump w edges out.cnf` writes `Biplanar.encode w edges` in DIMACS form -/
lean_exe «biplanarf-dump» where
  root := `Main
