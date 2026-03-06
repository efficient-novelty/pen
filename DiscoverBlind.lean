import PEN.Genesis
import PEN.Select.Engine

open PEN.Select.Engine

namespace PEN.CLI.DiscoverBlind

inductive LedgerFormat where
  | jsonl
  | csv
  deriving Repr, BEq

structure BlindRunConfig where
  printConfig         : Bool := false
  ticks               : Nat := 0
  refInjection        : Bool := false
  canonicalRanking    : Bool := false
  paperFallback       : Bool := false
  stepIndexedHints    : Bool := false
  ledgerFormat        : LedgerFormat := .jsonl
  selectorPolicy      : String := "minimal_overshoot+kappa_tiebreak"
  deriving Repr

private def sourceForLine (line : PEN.Genesis.LedgerLine) : String :=
  if line.decided == "idle" then "NONE" else "ENUM"

private def boolStr (b : Bool) : String := if b then "true" else "false"

private def csvEscape (s : String) : String :=
  let s1 := s.replace "\"" "\"\""
  if s1.contains ',' then s!"\"{s1}\"" else s1

private def configLines (cfg : BlindRunConfig) : List String :=
  [ s!"mode=discover_blind"
  , s!"ticks={cfg.ticks}"
  , s!"reference_injection={cfg.refInjection}"
  , s!"canonical_name_ranking={cfg.canonicalRanking}"
  , s!"paper_table_fallback={cfg.paperFallback}"
  , s!"step_indexed_target_hints={cfg.stepIndexedHints}"
  , s!"selector_policy={cfg.selectorPolicy}"
  , s!"ledger_format={repr cfg.ledgerFormat}"
  ]

private def printConfig (cfg : BlindRunConfig) : IO Unit :=
  IO.println (String.intercalate "\n" (configLines cfg))

private def failClosed (msg : String) : IO UInt32 := do
  IO.eprintln s!"discover_blind: FAIL-CLOSED: {msg}"
  pure 1

private def validateForbidden (cfg : BlindRunConfig) : IO UInt32 := do
  if cfg.refInjection then
    failClosed "forbidden flag enabled: reference telescope/REF injection"
  else if cfg.canonicalRanking then
    failClosed "forbidden flag enabled: canonical-name ranking"
  else if cfg.paperFallback then
    failClosed "forbidden flag enabled: paper-table fallback"
  else if cfg.stepIndexedHints then
    failClosed "forbidden flag enabled: step-indexed target hints"
  else
    pure 0

private def parseNat? (s : String) : Option Nat :=
  s.toNat?

private def parseLedgerFormat? (s : String) : Option LedgerFormat :=
  if s == "jsonl" then some .jsonl
  else if s == "csv" then some .csv
  else none

def parseArgs : List String → Except String BlindRunConfig
  | [] => .ok {}
  | "--print-config" :: rest =>
      match parseArgs rest with
      | .ok cfg => .ok { cfg with printConfig := true }
      | .error e => .error e
  | "--enable-ref-injection" :: rest =>
      match parseArgs rest with
      | .ok cfg => .ok { cfg with refInjection := true }
      | .error e => .error e
  | "--enable-canonical-ranking" :: rest =>
      match parseArgs rest with
      | .ok cfg => .ok { cfg with canonicalRanking := true }
      | .error e => .error e
  | "--enable-paper-fallback" :: rest =>
      match parseArgs rest with
      | .ok cfg => .ok { cfg with paperFallback := true }
      | .error e => .error e
  | "--enable-step-index-hints" :: rest =>
      match parseArgs rest with
      | .ok cfg => .ok { cfg with stepIndexedHints := true }
      | .error e => .error e
  | "--ticks" :: n :: rest =>
      match parseNat? n, parseArgs rest with
      | some ticks, .ok cfg => .ok { cfg with ticks := ticks }
      | none, _ => .error s!"invalid value for --ticks: {n}"
      | _, .error e => .error e
  | "--ledger-format" :: s :: rest =>
      match parseLedgerFormat? s, parseArgs rest with
      | some lf, .ok cfg => .ok { cfg with ledgerFormat := lf }
      | none, _ => .error s!"invalid value for --ledger-format: {s} (expected jsonl|csv)"
      | _, .error e => .error e
  | "--help" :: _ =>
      .error "help"
  | arg :: _ =>
      .error s!"unknown argument: {arg}"

def usage : String :=
  String.intercalate "\n"
    [ "Usage: discover_blind [options]"
    , ""
    , "Options:"
    , "  --print-config              Print active discover_blind configuration"
    , "  --ticks <n>                 Run n discovery ticks (default: 0)"
    , "  --ledger-format <jsonl|csv> Machine-readable ledger format (default: jsonl)"
    , "  --enable-ref-injection      (forbidden; must fail-closed)"
    , "  --enable-canonical-ranking  (forbidden; must fail-closed)"
    , "  --enable-paper-fallback     (forbidden; must fail-closed)"
    , "  --enable-step-index-hints   (forbidden; must fail-closed)"
    , "  --help                      Show this help"
    ]

private def emitCsvHeader : IO Unit :=
  IO.println "tick,mode,source,selector_policy,hints_enabled,forbidden_checks_passed"

private def emitCsvRow (cfg : BlindRunConfig) (line : PEN.Genesis.LedgerLine)
    (forbiddenChecksPassed : Bool) : IO Unit :=
  let fields :=
    [ toString line.tick
    , "discover_blind"
    , sourceForLine line
    , cfg.selectorPolicy
    , boolStr false
    , boolStr forbiddenChecksPassed
    ]
  IO.println (String.intercalate "," (fields.map csvEscape))

private def emitJsonRow (cfg : BlindRunConfig) (line : PEN.Genesis.LedgerLine)
    (forbiddenChecksPassed : Bool) : IO Unit :=
  IO.println s!"{{\"tick\":{line.tick},\"mode\":\"discover_blind\",\"source\":\"{sourceForLine line}\",\"selector_policy\":\"{cfg.selectorPolicy}\",\"hints_enabled\":false,\"forbidden_checks_passed\":{boolStr forbiddenChecksPassed}}}"

def runBlind (cfg : BlindRunConfig) : IO UInt32 := do
  if cfg.printConfig then
    printConfig cfg

  let guardRc ← validateForbidden cfg
  if guardRc ≠ 0 then
    return guardRc

  if cfg.ticks = 0 then
    return 0

  let forbiddenChecksPassed := true
  let (_, rows) := PEN.Genesis.runDiscoverNTicksWithLedger PEN.Genesis.dcfg PEN.Genesis.st0 cfg.ticks
  match cfg.ledgerFormat with
  | .csv =>
      emitCsvHeader
      for row in rows do
        emitCsvRow cfg row forbiddenChecksPassed
  | .jsonl =>
      for row in rows do
        emitJsonRow cfg row forbiddenChecksPassed
  pure 0

end PEN.CLI.DiscoverBlind

def main (args : List String) : IO UInt32 := do
  match PEN.CLI.DiscoverBlind.parseArgs args with
  | .ok cfg => PEN.CLI.DiscoverBlind.runBlind cfg
  | .error "help" =>
      IO.println PEN.CLI.DiscoverBlind.usage
      pure 0
  | .error e =>
      IO.eprintln s!"discover_blind: {e}"
      IO.eprintln PEN.CLI.DiscoverBlind.usage
      pure 2
