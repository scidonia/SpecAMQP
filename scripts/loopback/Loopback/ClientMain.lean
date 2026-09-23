/-
# The client executable's entry point

See `Loopback/ServerMain.lean` for why this exists as a module of its own.
-/

import Loopback.Client

def main (args : List String) : IO UInt32 := Loopback.Client.runMain args
