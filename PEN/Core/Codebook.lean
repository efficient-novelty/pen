/-
  PEN/Core/Codebook.lean

  Canonical, prefix-free serializer for a small HoTT/term-like AST,
  together with a *length-only* parser `parseLen` that returns the size
  of the first top-level codeword using only the codeword's header
  (tag + ASCII decimal length + ';').

  Encoding schema for each node:
    [1-byte tag] · [len-decimal ASCII · ';'] · [payload bytes of that length]

  The payload is a concatenation of:
    - any scalar fields (strings and naturals, both length-prefixed),
    - a framed list of children:  count;  len1; child1  len2; child2  ...

  Because each node carries its own total payload length in the header,
  codewords are *prefix-free* and `parseLen` can skip the whole block
  without parsing its interior.

  This file is self-contained (no project imports).
-/

import Init
import Std

namespace PEN.Core.Codebook

/-! ## AST -/

inductive AST
  | var    (idx : Nat)
  | const  (name : String)
  | lam    (binder : String) (type body : AST)
  | app    (fn arg : AST)
  | arrow  (dom cod : AST)
  | pi     (binder : String) (dom cod : AST)
  | sigma  (binder : String) (fst snd : AST)
  | pair   (fst snd : AST)
  | fst    (p : AST)
  | snd    (p : AST)
  | litNat (n : Nat)
  deriving Repr, BEq, Inhabited

abbrev Program := AST

/-! ## ByteArray helpers -/

@[inline] def bAppend (a b : ByteArray) : ByteArray :=
  Id.run do
    let mut out := a
    let sz := b.size
    for i in [0:sz] do
      out := out.push (b.get! i)
    return out

@[inline] def bConcat (xs : List ByteArray) : ByteArray :=
  xs.foldl bAppend ByteArray.empty

@[inline] def semi : UInt8 := UInt8.ofNat (Char.toNat ';')

@[inline] def tag (c : Char) : UInt8 := UInt8.ofNat (Char.toNat c)

/-! ## Scalar encoders (ASCII decimal with ';' terminator) -/

@[inline] def encNatDec (n : Nat) : ByteArray :=
  (toString n).toUTF8.push semi

@[inline] def encString (s : String) : ByteArray :=
  let utf := s.toUTF8
  bAppend (encNatDec utf.size) utf

/-!
  Child framing:
    count;  len1; child1  len2; child2  ...
  (Each child is itself a framed codeword produced by `encodeAST`.)
-/
def frameChildren (cs : List ByteArray) : ByteArray :=
  let count := encNatDec cs.length
  cs.foldl
    (fun acc child => bAppend (bAppend acc (encNatDec child.size)) child)
    count

/-! ## Tags per node constructor -/

@[inline] def TAG_VAR   : UInt8 := tag 'v'
@[inline] def TAG_CONST : UInt8 := tag 'c'
@[inline] def TAG_LAM   : UInt8 := tag 'l'
@[inline] def TAG_APP   : UInt8 := tag 'a'
@[inline] def TAG_ARROW : UInt8 := tag 'r'    -- 'r' for aRRow
@[inline] def TAG_PI    : UInt8 := tag 'p'
@[inline] def TAG_SIGMA : UInt8 := tag 's'
@[inline] def TAG_PAIR  : UInt8 := tag 't'
@[inline] def TAG_FST   : UInt8 := tag 'f'
@[inline] def TAG_SND   : UInt8 := tag 'g'
@[inline] def TAG_NAT   : UInt8 := tag 'n'

@[inline] def emitTag (u : UInt8) : ByteArray :=
  ByteArray.empty.push u

/-- Wrap a payload as a codeword:
    [tag][len-decimal';'][payload]  with len = payload.size. -/
@[inline] def frameNode (tg : UInt8) (payload : ByteArray) : ByteArray :=
  bConcat [emitTag tg, encNatDec payload.size, payload]

/-!
  Encode an AST node to a prefix-free ByteArray. The encoding of each node is:

  tag · length(payload)';' · payload

  The payload itself concatenates:
    - scalar fields (length-prefixed strings and naturals),
    - a framed list of children (count; len; child bytes ...).
-/
partial def encodeAST : AST → ByteArray
| .var i =>
    let payload := bConcat [encNatDec i, encNatDec 0]  -- scalars + 0 children
    frameNode TAG_VAR payload
| .const nm =>
    let payload := bConcat [encString nm, encNatDec 0]
    frameNode TAG_CONST payload
| .lam b ty bd =>
    let kids := [encodeAST ty, encodeAST bd]
    let payload := bConcat [encString b, frameChildren kids]
    frameNode TAG_LAM payload
| .app f x =>
    let kids := [encodeAST f, encodeAST x]
    let payload := frameChildren kids
    frameNode TAG_APP payload
| .arrow a b =>
    let kids := [encodeAST a, encodeAST b]
    let payload := frameChildren kids
    frameNode TAG_ARROW payload
| .pi bnd dom cod =>
    let kids := [encodeAST dom, encodeAST cod]
    let payload := bConcat [encString bnd, frameChildren kids]
    frameNode TAG_PI payload
| .sigma bnd fst snd =>
    let kids := [encodeAST fst, encodeAST snd]
    let payload := bConcat [encString bnd, frameChildren kids]
    frameNode TAG_SIGMA payload
| .pair a b =>
    let kids := [encodeAST a, encodeAST b]
    let payload := frameChildren kids
    frameNode TAG_PAIR payload
| .fst p =>
    let kids := [encodeAST p]
    let payload := frameChildren kids
    frameNode TAG_FST payload
| .snd p =>
    let kids := [encodeAST p]
    let payload := frameChildren kids
    frameNode TAG_SND payload
| .litNat n =>
    let payload := bConcat [encNatDec n, encNatDec 0]
    frameNode TAG_NAT payload

@[simp] def bitLength (ba : ByteArray) : Nat := 8 * ba.size

/-
  readNatDec reads an ASCII decimal natural terminated by ';'
  starting at index `pos`, returning the parsed Nat and the index
  directly *after* the ';'. Returns `none` if the format is invalid.
-/
def readNatDec (bs : ByteArray) (pos : Nat) : Option (Nat × Nat) := Id.run do
  if pos ≥ bs.size then
    return none
  let zero := UInt8.ofNat (Char.toNat '0')
  let nine := UInt8.ofNat (Char.toNat '9')
  let mut acc : Nat := 0
  let mut i   : Nat := pos
  let mut sawDigit := false
  while i < bs.size do
    let c := bs.get! i
    if c = semi then
      if !sawDigit then
        -- forbid empty number like ";"
        return none
      else
        return some (acc, i + 1)
    else if c ≥ zero && c ≤ nine then
      sawDigit := true
      let d : Nat := c.toNat - zero.toNat
      acc := acc * 10 + d
      i := i + 1
    else
      return none
  return none

/--
  parseLen returns the total byte-length of the first codeword in `bs`,
  i.e. the size of: [1-byte tag] + [len-decimal + ';'] + [payload].
  It inspects only the tag and the decimal length header; it does not parse
  the payload itself.
-/
def parseLen (bs : ByteArray) : Option Nat := Id.run do
  if bs.size < 3 then
    return none
  -- skip 1-byte tag at position 0
  match readNatDec bs 1 with
  | none => return none
  | some (len, after) =>
    -- after = index just after the ';' that ends the decimal length
    -- codeword total length = (after) + payload length `len`
    if after + len ≤ bs.size then
      return some (after + len)
    else
      return none

/-- Convenience: packaged codeword. -/
structure Codeword where
  bytes : ByteArray
deriving BEq

instance : Repr Codeword where
  reprPrec cw _ := s!"Codeword({cw.bytes.size} bytes)"


namespace Codeword

@[inline] def size (cw : Codeword) : Nat := cw.bytes.size

/-- Quick check: does parseLen agree with the actual size? -/
def hasValidFraming (cw : Codeword) : Bool :=
  match parseLen cw.bytes with
  | some n => n = cw.bytes.size
  | none   => false

end Codeword

/-- Encode a program into a codeword. -/
@[inline] def toCodeword (p : Program) : Codeword :=
  { bytes := encodeAST p }

/-! ## Small examples you can `#eval` locally

-- #eval parseLen (encodeAST (AST.var 3))
-- #eval (toCodeword (AST.lam "x" (AST.const "Unit") (AST.var 0))).size
-- #eval Codeword.hasValidFraming (toCodeword (AST.lam "x" (AST.const "Unit") (AST.var 0)))

-/

end PEN.Core.Codebook
