/*
 * SpecAMQP — R1's transport-shim controls.
 *
 * A control, not shipped code. Nothing here is linked into `amqp-loopback-server`
 * or `amqp-loopback-client`; it is linked into `amqp-loopback-control-{server,client}`
 * instead, and it exists so that the evidence around the boundary can be *attacked*
 * by anyone rather than believed. A harness that has never detected a planted fault
 * is a harness whose passing runs prove nothing, and this file is how the faults get
 * planted reproducibly.
 *
 * ## What it does
 *
 * It includes the real shim verbatim — not a copy, the same file — with two symbols
 * renamed so that the definitions below can wrap them:
 *
 *   `recv` — the clean implementation is compiled as `specamqp_transport_recv_clean`
 *            and the wrapper applies whichever `recv` control is selected;
 *   `send` — likewise, for the short-write control.
 *
 * There is no second copy of the shim's logic anywhere, so a change to the shim
 * changes the controls with it and the controls cannot drift into testing a shim
 * that no longer exists.
 *
 * ## Selecting one
 *
 * At run time, from the environment:
 *
 *   SPECAMQP_SHIM_CONTROL=truncating-recv     every read loses one octet
 *   SPECAMQP_SHIM_CONTROL=reordering-recv     the first two octets of every read swap
 *   SPECAMQP_SHIM_CONTROL=short-send          every write hands the kernel at most 1024 octets
 *   unset or empty                            no control: the control binaries behave as the real ones
 *
 * An unrecognised value is an error rather than a silent fallback — a control that
 * quietly ran clean would report a harness that detects faults when it had been asked
 * to plant none.
 *
 * ## What each control is for
 *
 * The first two are the silent faults the boundary must not have: a truncation and a
 * reordering, neither of which changes a length field in a way a count-only check
 * would notice. They are expected to make the loopback *fail*, with a named octet.
 *
 * `short-send` is the opposite kind of control and the reason it is here at all: a
 * positive short write is *legal* — `Transport.send` promises only what the kernel
 * accepted — and Linux's blocking `send` returns the full length in practice, so
 * nothing in a clean run exercises `Wire.sendAll`'s loop. This control forces the
 * path deterministically, and the expected outcome is *success*: the payload must
 * still arrive intact, in hundreds of send calls rather than one. A control whose
 * expected result is success is still a control — it fails if the loop drops the
 * remainder, and the send-call count is the evidence that it ran.
 */

#define _GNU_SOURCE

/* The renames must precede the include: they are textual, and they are what turns the
   shim's own definitions into the functions the wrappers below delegate to. */
#define specamqp_transport_recv specamqp_transport_recv_clean
#define specamqp_transport_send specamqp_transport_send_clean

#include "../../transport_shim.c"

#undef specamqp_transport_recv
#undef specamqp_transport_send

#include <stdlib.h>
#include <string.h>

enum control {
  control_none,
  control_truncating_recv,
  control_reordering_recv,
  control_short_send,
};

/* The most any single write may hand the kernel under `short-send`. Small enough that
   a 300000-octet payload needs hundreds of calls, large enough that the run is quick. */
#define CONTROL_SHORT_SEND_CAP 1024u

/* Read once: the environment does not change under a running process, and the
   boundary's contract is single-threaded anyway. */
static enum control selected_control(void) {
  static int cached = 0;
  static enum control chosen;

  if (cached) return chosen;
  cached = 1;

  const char *name = getenv("SPECAMQP_SHIM_CONTROL");
  if (name == NULL || *name == '\0') {
    chosen = control_none;
  } else if (strcmp(name, "truncating-recv") == 0) {
    chosen = control_truncating_recv;
  } else if (strcmp(name, "reordering-recv") == 0) {
    chosen = control_reordering_recv;
  } else if (strcmp(name, "short-send") == 0) {
    chosen = control_short_send;
  } else {
    fprintf(stderr, "transport shim control: unknown SPECAMQP_SHIM_CONTROL '%s'\n", name);
    exit(2);
  }
  return chosen;
}

/*
 * The two `recv` controls post-process what the clean implementation returned. They
 * take the value out of the result (which consumes the result), edit the buffer the
 * `some` constructor exclusively holds, and wrap it in a fresh result. A `none` — the
 * peer's orderly close — is passed through untouched, so the controls cannot be
 * confused with the end-of-stream case.
 */
LEAN_EXPORT lean_obj_res specamqp_transport_recv(size_t handle, size_t max_octets) {
  enum control control = selected_control();
  lean_obj_res result = specamqp_transport_recv_clean(handle, max_octets);
  if (control != control_truncating_recv && control != control_reordering_recv) return result;
  if (!lean_io_result_is_ok(result)) return result;

  lean_object *value = lean_io_result_take_value(result);
  if (lean_obj_tag(value) == 1) { /* `some`
                                     the buffer is held only by this constructor, so it is
                                     exclusively ours and can be edited in place */
    lean_object *buffer = lean_ctor_get(value, 0);
    size_t size = lean_sarray_size(buffer);
    if (control == control_truncating_recv) {
      if (size > 1) lean_sarray_set_size(buffer, size - 1);
    } else if (size >= 2) {
      uint8_t *octets = lean_sarray_cptr(buffer);
      uint8_t first = octets[0];
      octets[0] = octets[1];
      octets[1] = first;
    }
  }
  return lean_io_result_mk_ok(value);
}

/*
 * `short-send` hands the clean implementation a prefix of the caller's buffer, so the
 * kernel is asked for at most the cap and accepts fewer octets than the caller
 * offered — a positive short write. The prefix is a fresh array of exactly the cap,
 * passed on with the owned convention the boundary uses throughout.
 */
LEAN_EXPORT lean_obj_res specamqp_transport_send(size_t handle, lean_obj_arg octets) {
  if (selected_control() != control_short_send) return specamqp_transport_send_clean(handle, octets);

  size_t total = lean_sarray_size(octets);
  if (total <= CONTROL_SHORT_SEND_CAP) return specamqp_transport_send_clean(handle, octets);

  lean_object *prefix = lean_alloc_sarray(1, CONTROL_SHORT_SEND_CAP, CONTROL_SHORT_SEND_CAP);
  memcpy(lean_sarray_cptr(prefix), lean_sarray_cptr(octets), CONTROL_SHORT_SEND_CAP);
  lean_dec(octets);
  return specamqp_transport_send_clean(handle, prefix);
}
