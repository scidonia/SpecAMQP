/-
# The transport boundary, and the whole of this implementation's unproved trust

Six operations, over a byte buffer, and nothing else: bind-and-listen, accept,
connect, receive, send, close. Every protocol decision the endpoint makes is made
in Lean above this module; every octet it moves goes through it. That is the point
of the module: the part of the implementation that this repository does not prove
is one file, and it fits on a screen.

`PLAN.md` §23.1 names four of them — `accept`, `recv`, `send`, `close` — and these
are those four, unchanged. The two extra declarations are not speculative additions
but the shortest path to `accept` and to the client side: `accept` needs a socket
that is bound and listening, and a client needs to dial before it can `send`. They
operate on sockets, not on protocol state, and an operation that does not appear
here (no `shutdown`, no `poll`/`select`, no name resolution, no non-blocking mode,
no address type, no timeout) is absent because the synchronous endpoint does not
need it. The count is now in a gate's output, so growing it is a deliberate act
rather than a convenience.

## What the shim decides, beyond making the syscall

The shim is a wrapper: each operation issues its syscall and reports what POSIX reports,
with the two results it has to keep apart — an octet count, and the error that stands
beside it. It is *not* a bare wrapper, and this section is about the difference. What
follows is what the code decides, not a claim that nothing else differs: check the list
against the shim, and where the two disagree the code is the fact.

- **Four calls retry on `EINTR`** — `accept4`, `connect`, `recv` and `send` — because a
  signal-interrupted call is not a failed one, and reporting a failure for one would make
  the harness's outcome depend on an unrelated signal. `close` is the exception and the
  reason is in its own bullet below.
- **`SO_REUSEADDR` is set on `listen`.** Not a hidden convenience: a loopback harness
  that re-runs has to rebind a port the previous run left in `TIME_WAIT`, and without
  it the second run fails on an address the first one legitimately released. It is set
  on the listening socket only, and a failure to set it is reported rather than
  ignored. `setsockopt` therefore appears in this module after all — for this one
  option, on this one call.
- **`SOCK_CLOEXEC` is set on every socket**, accepted or connected, so a descriptor
  cannot leak into a child process.
- **`recv` refuses a zero-length request** (`EINVAL`). A zero-length read returns zero
  octets exactly as an orderly close does, so allowing it would make `none` mean two
  different things.
- **`send` uses `MSG_NOSIGNAL`**, so a peer that has gone away fails the write instead
  of killing the process between a test's assertions.
- **`close` is called once and not retried on `EINTR`**; on Linux the descriptor is
  released either way, so a retry could close an unrelated descriptor that had since
  taken the same number. That is why it is the one call without a retry, and a failure
  is reported rather than swallowed.
- **An orderly close is `none`, not an error**, and **`send` performs one syscall and
  reports what the kernel accepted** — both argued in their own sections below.

## The trust, stated rather than implied

Two components are trusted to make the claims about this implementation true, and
neither is verified here. This is the same disclosure `native_decide` carries, for
the same reason: a proof about Lean source is a claim about source, and something
outside the source has to be believed for it to be a claim about a running process.

1. **Lean's compiler and its runtime.** Lean erases propositions and types before
   code generation, so what runs is the executable content of these definitions and
   not the theorems about them. Lean's C backend, its code generator, its garbage
   collector, its scheduler and its C runtime are all part of the trusted base, and
   none of them is verified. This link is named in `HANDOFF.md` and in the plan's
   three-link chain; nothing in this module changes it.

2. **The shim** — `scripts/transport_shim.c`, reached through the `@[extern]`
   declarations below. It performs the syscalls, it is written by hand in C, and no
   proof here concerns it. What this module does about that is make the shim small,
   keep its contract narrow enough to check by reading, and prove by two-process
   loopback — `scripts/loopback/` and `scripts/run-transport-loopback.sh` — that it
   delivers the octets it is given, in order, without truncation, which is a
   measurement of behaviour, not a proof, and is reported as one.

Nothing else in the implementation is unproved. In particular the six operations
below are the only `@[extern]` declarations in the tree, they are `private` to this
module so no other module can reach around the typed wrappers, and no `unsafe`
appears anywhere in it.

## Why a shim at all, when Lean already has a socket

Measured against the pinned toolchain, and worth recording because the plan's first
statement of it was wrong: Lean 4.31.0 *does* provide TCP, as `Std.Async.TCP` over
`Std.Internal.UV.TCP`'s `@[extern "lean_uv_tcp_*"]` symbols, which live in
`libleanshared.so` and work from a natively compiled binary. So this boundary is a
choice rather than a necessity. It is chosen because `Std.Async.TCP` would put
libuv and Lean's async runtime — layers that do protocol-adjacent work with no name
in this repository — inside the unproved base, and because the endpoint's frame loop
is synchronous: it reads a frame, decides, and writes. A POSIX socket wrapper of
about a hundred and fifty readable lines, trusting the kernel's socket ABI, is a
smaller thing to believe than an event loop, and it is a thing this repository can
point at.

## The contract, and the parts of it that are deliberate

- **No partial-transfer assumption in either direction.** `recv` returns *at most*
  `maxOctets` and `send` returns the count it accepted. A caller that wants all of
  a known number of octets must loop; the loop lives in Lean (`Loopback/Wire.lean`),
  where it is testable, rather than happening invisibly inside C.
- **An orderly close is not an error.** `recv` returns `none` when the peer has
  closed the connection cleanly, and raises `IO.Error` only for a real failure. POSIX
  distinguishes the two (a zero-length read against `-1` with `errno`), `Option`
  carries the distinction, and AMQP's close path treats an orderly shutdown as a
  protocol event rather than a fault. Collapsing the two into "an error" would make a
  closed peer indistinguishable from a reset one, which is the kind of near-silent
  failure this repository's rules are about.
- **Buffering is the caller's business.** Lean's stdout is block-buffered, so a
  process that prints a port and then blocks must flush explicitly; a reader that
  waits for that line will otherwise wait forever. `Loopback/Server.lean` flushes,
  and this note is here because the failure it prevents is invisible.
- **Loopback, IPv4, blocking, one thread.** `listen` and `connect` use
  `127.0.0.1`, sockets are blocking and close-on-exec, and no operation is safe to
  call concurrently from two threads. That is what a synchronous reference endpoint
  needs and no more; widening any of it is a plan question rather than a parameter.
-/

namespace SpecAMQP.Impl.Transport

/-- A bound, listening socket. The handle is an OS file descriptor; the field is
private so no other module can fabricate a listener, and the type is separate from
`Conn` so the two cannot be passed to the wrong operation. -/
structure Listener where
  private mk ::
  /-- The underlying file descriptor. -/
  handle : USize

/-- A connected socket. Distinguished from `Listener` for the same reason the
constructor is private: a handle that has not been accepted or connected cannot be
expressed. -/
structure Conn where
  private mk ::
  /-- The underlying file descriptor. -/
  handle : USize

/-!
## The boundary

Each operation is declared once, `private`, with the C symbol that implements it.
The bodies are unreachable — native code calls the symbol — and they throw rather
than returning a plausible default, so the one way to reach them (the interpreter,
where no C shim is linked) reports the missing prerequisite instead of silently
pretending to have a socket.
-/

/-- Bind to `127.0.0.1:port` and listen, with a backlog of one. Fails if the port is
taken or the process cannot open a socket. -/
@[extern "specamqp_transport_listen"]
private def listenRaw (port : UInt16) : IO USize :=
  throw <| .userError "SpecAMQP.Impl.Transport: no C shim linked for specamqp_transport_listen"

/-- Accept one pending connection, blocking until there is one. -/
@[extern "specamqp_transport_accept"]
private def acceptRaw (handle : USize) : IO USize :=
  throw <| .userError "SpecAMQP.Impl.Transport: no C shim linked for specamqp_transport_accept"

/-- Connect to `127.0.0.1:port`. -/
@[extern "specamqp_transport_connect"]
private def connectRaw (port : UInt16) : IO USize :=
  throw <| .userError "SpecAMQP.Impl.Transport: no C shim linked for specamqp_transport_connect"

/-- Read up to `maxOctets` octets into a fresh buffer: `some` of one to `maxOctets`
octets, or `none` for an orderly close by the peer. -/
@[extern "specamqp_transport_recv"]
private def recvRaw (handle : USize) (maxOctets : USize) : IO (Option ByteArray) :=
  throw <| .userError "SpecAMQP.Impl.Transport: no C shim linked for specamqp_transport_recv"

/-- Write as many octets as the kernel will take in one call and report how many
those were. Never zero on success unless `octets` is empty. -/
@[extern "specamqp_transport_send"]
private def sendRaw (handle : USize) (octets : ByteArray) : IO USize :=
  throw <| .userError "SpecAMQP.Impl.Transport: no C shim linked for specamqp_transport_send"

/-- Close a socket and release its descriptor. A second close of the same handle is
a caller defect and fails with the kernel's `EBADF` rather than being ignored. -/
@[extern "specamqp_transport_close"]
private def closeRaw (handle : USize) : IO Unit :=
  throw <| .userError "SpecAMQP.Impl.Transport: no C shim linked for specamqp_transport_close"

/-!
## The surface
-/

/-- Bind and listen on `127.0.0.1:port`. -/
def listen (port : UInt16) : IO Listener :=
  Listener.mk <$> listenRaw port

/-- Accept one connection. -/
def accept (listener : Listener) : IO Conn :=
  Conn.mk <$> acceptRaw listener.handle

/-- Connect to `127.0.0.1:port`. -/
def connect (port : UInt16) : IO Conn :=
  Conn.mk <$> connectRaw port

/-- Read up to `maxOctets` octets. `maxOctets` must be at least one: a zero-length
read would be indistinguishable from the peer's orderly close, and a shim that
returned `none` for it would report a live connection as finished. -/
def recv (conn : Conn) (maxOctets : USize) : IO (Option ByteArray) :=
  recvRaw conn.handle maxOctets

/-- Write to `conn`, returning the number of octets the kernel accepted. A caller
that must write all of `octets` loops until the counts sum to its length. -/
def send (conn : Conn) (octets : ByteArray) : IO USize :=
  sendRaw conn.handle octets

namespace Conn

/-- Close this connection. -/
def close (conn : Conn) : IO Unit :=
  closeRaw conn.handle

end Conn

namespace Listener

/-- Close this listener. -/
def close (listener : Listener) : IO Unit :=
  closeRaw listener.handle

end Listener

end SpecAMQP.Impl.Transport
