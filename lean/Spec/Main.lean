import Harness.Runner
import Spec.Codec
import Spec.FrameCodec
import Spec.SessionCodec

/-!
`amqp-spec` — run the executable specification over a vector corpus.

    lake exe amqp-spec vectors/primitives.ndjson [--quiet]

Prints one JSON verdict per vector on stdout and exits non-zero when any vector
fails, so the corpus is the contract and the exit status is the observable
outcome. Nothing here touches the network, a clock, or a random source.
-/

open SpecAMQP.Harness
open SpecAMQP.Spec.Codec
open SpecAMQP.Spec.FrameCodec
open SpecAMQP.Spec.SessionCodec

def main (args : List String) : IO UInt32 := do
  let quiet := args.contains "--quiet"
  let files := args.filter (fun a => !a.startsWith "--")
  match files with
  | [] =>
    IO.eprintln "usage: amqp-spec <vector-file.ndjson> [--quiet]"
    return (2 : UInt32)
  | path :: _ =>
    let text ←
      try
        IO.FS.readFile path
      catch e =>
        IO.eprintln s!"amqp-spec: cannot read {path}: {e}"
        return (2 : UInt32)
    match runCorpusWith specCodec specFrameCodec specExchangeCodec text with
    | .error message =>
      IO.eprintln s!"amqp-spec: {message}"
      return (2 : UInt32)
    | .ok (verdicts, allOk) =>
      let failures := verdicts.filter (fun v => !v.ok)
      if !quiet then
        for verdict in verdicts do
          IO.println (verdictJson verdict).compress
      IO.eprintln s!"{verdicts.length} vector(s), {failures.length} failure(s) in {path}"
      return if allOk then (0 : UInt32) else (1 : UInt32)
