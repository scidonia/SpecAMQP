/-
# The control server's entry point

Identical Lean to `Loopback/ServerMain.lean`, deliberately: the control binary is the
same server linked against `scripts/loopback/mutants/shim_controls.c` instead of the
shim, so what a control run changes is the C object behind the six `@[extern]` symbols
and nothing above them. Keeping the two root modules visibly the same is the evidence
that the fault being planted is at the boundary rather than in the harness.
-/

import Loopback.Server

def main (args : List String) : IO UInt32 := Loopback.Server.runMain args
