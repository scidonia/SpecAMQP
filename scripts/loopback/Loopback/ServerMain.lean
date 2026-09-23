/-
# The server executable's entry point

Lean emits the C `main` wrapper only for a module that declares a *local* `main`, and
Lake allows one executable per root module, so every binary here owns a root module
whose whole content is this line. `Loopback.Server` holds the behaviour and
`Loopback.ControlServerMain` is the same line over the same function — the control
binary differs only in the C object it is linked against, which is the point of it.
-/

import Loopback.Server

def main (args : List String) : IO UInt32 := Loopback.Server.runMain args
