import Harness.Runner
import Ref.Message
import Ref.SessionCodec
import Ref.Vectors

/-!
`amqp-ref` — run the reference implementation over a vector corpus.

    lake exe amqp-ref vectors/primitives.ndjson [--quiet]

Prints one JSON verdict per vector on stdout and exits non-zero when any vector
fails, so the corpus is the contract and the exit status is the observable
outcome. Nothing here touches the network, a clock, or a random source.
-/

open SpecAMQP.Harness
open SpecAMQP.Ref.Message (refDeliveryCodec refMessageCodec)
open SpecAMQP.Ref.SessionCodec
open SpecAMQP.Ref.Vectors

/-- The reference implementation's codecs, one per layer of the vocabulary, bound together
so the corpus runner dispatches every vector kind to the layer that owns it. -/
def artefact : Artefact :=
  { name := "reference", values := refCodec, frames := refFrameCodec,
    exchanges := refExchangeCodec, messages := refMessageCodec,
    deliveries := refDeliveryCodec }

def main (args : List String) : IO UInt32 := do
  let quiet := args.contains "--quiet"
  let files := args.filter (fun a => !a.startsWith "--")
  match files with
  | [] =>
    IO.eprintln "usage: amqp-ref <vector-file.ndjson> [--quiet]"
    return (2 : UInt32)
  | path :: _ =>
    let text ←
      try
        IO.FS.readFile path
      catch e =>
        IO.eprintln s!"amqp-ref: cannot read {path}: {e}"
        return (2 : UInt32)
    match runCorpusArtefact artefact text with
    | .error message =>
      IO.eprintln s!"amqp-ref: {message}"
      return (2 : UInt32)
    | .ok (verdicts, allOk) =>
      let failures := verdicts.filter (fun v => !v.ok)
      if !quiet then
        for verdict in verdicts do
          IO.println (verdictJson verdict).compress
      IO.eprintln s!"{verdicts.length} vector(s), {failures.length} failure(s) in {path}"
      return if allOk then (0 : UInt32) else (1 : UInt32)
