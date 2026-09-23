/-
# The control client's entry point

See `Loopback/ControlServerMain.lean`: identical Lean to the real client, linked
against the controls instead of the shim.
-/

import Loopback.Client

def main (args : List String) : IO UInt32 := Loopback.Client.runMain args
