/*
 * SpecAMQP — the transport shim.
 *
 * THE UNPROVED DEPENDENCY. This file implements the six operations that
 * `lean/Impl/Transport.lean` declares with `@[extern]`: bind-and-listen, accept,
 * connect, recv, send, close. It is hand-written C, no proof in this repository
 * concerns it, and it sits at the bottom of the three-link chain in `PLAN.md`
 * §23.1 as the one component that was chosen rather than proved. Read it whole:
 * that is the point of its size.
 *
 * ## What it may and may not do
 *
 * It moves octets between a socket and a `ByteArray`, and it does nothing else. It
 * makes no protocol decision, holds no state between calls, parses nothing, and
 * has no timeout, buffer pool or partial-transfer policy — every one of those is a
 * decision belonging above the boundary, where a test and a proof can reach it.
 *
 * It is a wrapper, but not a bare one. `accept4`, `connect`, `recv` and `send` retry
 * when a signal interrupts them; `SO_REUSEADDR` is set on the listening socket,
 * `SOCK_CLOEXEC` on every socket and `MSG_NOSIGNAL` on `send`; a zero-length `recv` is
 * refused rather than performed; `close` is called once and never retried; an orderly
 * close is `none` rather than an error; and `send` makes one syscall and reports what
 * it wrote instead of looping. Each is documented at the operation it belongs to and
 * enumerated in `lean/Impl/Transport.lean`'s header, which is the disclosure to read
 * against this file. No count of them appears here: an earlier version of this comment
 * said "two places", which was true when written and stopped being true when the
 * retries went in — where prose and this code disagree, the code is the fact.
 *
 * ## Allocation and length discipline
 *
 * The shim allocates nothing it does not hand to Lean's garbage collector, and
 * frees nothing Lean owns. `recv` allocates exactly one *buffer* — one scalar array,
 * sized `maxOctets` — receives into its own storage bounded by that size, and then
 * sets its length to what arrived, so the returned buffer is never longer than either
 * the request or the data. The success path also allocates the `Option.some`
 * constructor that carries that buffer, and the error and end-of-stream paths free the
 * buffer before returning it, so every path releases what it took. Nothing is copied
 * twice and no `malloc` appears: an out-of-memory condition is `lean_alloc_object`'s,
 * which aborts loudly rather than returning a short read.
 *
 * ## The calling convention, as measured rather than assumed
 *
 * A `@[extern]` operation's object argument is passed with the *owned* convention:
 * the callee consumes the reference. Measured against this toolchain by compiling
 * a call whose buffer is uniquely owned and reading the generated C
 * (`lean --root=... -c`): the buffer is created, passed, and never decremented by
 * the caller, so the shim must `lean_dec` it. Getting this backwards in either
 * direction is a leak or a use-after-free, which is why it is written down here
 * rather than inferred from the call site being correct.
 *
 * ## Environment assumed
 *
 * POSIX sockets on Linux: `accept4`/`SOCK_CLOEXEC` are Linux, blocking mode is
 * relied on for `recv`/`accept`, and one thread is the contract — no operation
 * here is reentrant, and the shim keeps no per-connection state to make it so.
 */

#define _GNU_SOURCE

#include <lean/lean.h>

#include <arpa/inet.h>
#include <errno.h>
#include <netinet/in.h>
#include <stdio.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

/*
 * The one error shape: a user error naming the operation, the kernel's message and
 * the errno, because the caller needs to know which call failed and why in order to
 * report anything useful. `lean_mk_io_user_error` takes ownership of the string.
 */
static lean_obj_res shim_error(const char *operation, int err) {
  char message[256];
  snprintf(message, sizeof message, "transport shim: %s failed: %s (errno %d)",
           operation, strerror(err), err);
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(message)));
}

/*
 * The harness and the reference endpoint both run on the loopback interface; the
 * boundary takes a port and nothing else, so the address is fixed here rather than
 * parsed. Widening this to an arbitrary address is a boundary change (it needs a
 * resolver and an address family), not a parameter.
 */
static struct sockaddr_in loopback_address(uint16_t port) {
  struct sockaddr_in address;
  memset(&address, 0, sizeof address);
  address.sin_family = AF_INET;
  address.sin_port = htons(port);
  address.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  return address;
}

/* A fresh, close-on-exec TCP socket, or -1 with errno set. */
static int new_socket(void) {
  return socket(AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0);
}

LEAN_EXPORT lean_obj_res specamqp_transport_listen(uint16_t port) {
  int fd = new_socket();
  if (fd < 0) return shim_error("socket", errno);

  /*
   * Without SO_REUSEADDR a port left in TIME_WAIT by the previous run of the
   * harness refuses the next bind, which turns a passing test into a flaky one.
   */
  int one = 1;
  if (setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one) < 0) {
    int err = errno;
    close(fd);
    return shim_error("setsockopt(SO_REUSEADDR)", err);
  }

  struct sockaddr_in address = loopback_address(port);
  if (bind(fd, (struct sockaddr *)&address, sizeof address) < 0) {
    int err = errno;
    close(fd);
    return shim_error("bind", err);
  }
  if (listen(fd, 1) < 0) {
    int err = errno;
    close(fd);
    return shim_error("listen", err);
  }
  return lean_io_result_mk_ok(lean_box_usize((size_t)fd));
}

LEAN_EXPORT lean_obj_res specamqp_transport_accept(size_t handle) {
  int fd;
  do {
    fd = accept4((int)handle, NULL, NULL, SOCK_CLOEXEC);
  } while (fd < 0 && errno == EINTR);
  if (fd < 0) return shim_error("accept", errno);
  return lean_io_result_mk_ok(lean_box_usize((size_t)fd));
}

LEAN_EXPORT lean_obj_res specamqp_transport_connect(uint16_t port) {
  int fd = new_socket();
  if (fd < 0) return shim_error("socket", errno);

  struct sockaddr_in address = loopback_address(port);
  int rc;
  do {
    rc = connect(fd, (struct sockaddr *)&address, sizeof address);
    /*
     * Linux leaves the connect in progress after EINTR; re-entering it is how a
     * blocking connect is restarted, and the alternative — reporting failure for a
     * signal — would make the harness's outcome depend on an unrelated one.
     */
  } while (rc < 0 && errno == EINTR);
  if (rc < 0) {
    int err = errno;
    close(fd);
    return shim_error("connect", err);
  }
  return lean_io_result_mk_ok(lean_box_usize((size_t)fd));
}

LEAN_EXPORT lean_obj_res specamqp_transport_recv(size_t handle, size_t max_octets) {
  if (max_octets == 0) {
    /*
     * A zero-length read is refused rather than performed: it would return zero
     * octets in the same way an orderly close does, and the Lean contract promises
     * that `none` means the peer went away. Failing here keeps that promise
     * decidable by the caller.
     */
    return shim_error("recv (maxOctets must be at least 1)", EINVAL);
  }

  /* One allocation, of the requested capacity, handed to Lean on every path. */
  lean_object *buffer = lean_alloc_sarray(1, 0, max_octets);
  uint8_t *data = lean_sarray_cptr(buffer);

  ssize_t received;
  do {
    received = recv((int)handle, data, max_octets, 0);
  } while (received < 0 && errno == EINTR);

  if (received < 0) {
    int err = errno;
    lean_dec(buffer);
    return shim_error("recv", err);
  }
  if (received == 0) {
    /* An orderly close by the peer: `none`, not an error. See the module contract. */
    lean_dec(buffer);
    return lean_io_result_mk_ok(lean_box(0));
  }

  /* The object is exclusively ours, so the length can be narrowed in place. */
  lean_sarray_set_size(buffer, (size_t)received);
  lean_object *some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, buffer);
  return lean_io_result_mk_ok(some);
}

LEAN_EXPORT lean_obj_res specamqp_transport_send(size_t handle, lean_obj_arg octets) {
  size_t total = lean_sarray_size(octets);
  const uint8_t *data = lean_sarray_cptr(octets);

  ssize_t written;
  do {
    /*
     * MSG_NOSIGNAL: a peer that has gone away must fail the write, not kill the
     * process with SIGPIPE. Without it the harness can pass while the endpoint
     * dies, because the signal arrives between the test's assertions.
     */
    written = send((int)handle, data, total, MSG_NOSIGNAL);
  } while (written < 0 && errno == EINTR);

  int err = errno;
  lean_dec(octets); /* the owned convention: the argument is consumed here */
  if (written < 0) return shim_error("send", err);

  /*
   * A short write is reported rather than retried: the loop belongs above the
   * boundary, where a test can see it. Zero is impossible here unless `octets` was
   * empty, because a blocking socket with a non-empty buffer either accepts
   * something or fails.
   */
  return lean_io_result_mk_ok(lean_box_usize((size_t)written));
}

LEAN_EXPORT lean_obj_res specamqp_transport_close(size_t handle) {
  /*
   * Called once, not retried on EINTR: on Linux the descriptor is released even
   * when the call reports EINTR, so a retry would close an unrelated descriptor
   * that had meanwhile been given the same number. A failure is reported loudly
   * rather than swallowed, and the error text says the handle is spent.
   */
  if (close((int)handle) < 0) return shim_error("close (the handle is now spent)", errno);
  return lean_io_result_mk_ok(lean_box(0));
}
