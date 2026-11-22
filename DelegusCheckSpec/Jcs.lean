/-
Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.

Phase 6: RFC 8785 JSON Canonicalization Scheme, written in Lean, for the
Action hash (§4.3, §6.3).

RFC 8785 §3.2: literals as-is; numbers serialized as ECMAScript
`Number::toString` of the IEEE 754 double the JSON number denotes; strings
quoted as `JSON.stringify` does (`"` and `\` escaped, U+0000–U+001F as
`\b \t \n \f \r` or lowercase `\u00xx`, everything else as-is); arrays in
order; object members sorted by key as UTF-16 code-unit sequences; no
whitespace. A number too large for a double is not JSON for JCS: `none`.

The number path is exact: the JSON number's decimal value is rounded to the
nearest double (ties to even, with subnormals), and the shortest decimal
that rounds back to that double is printed in ECMAScript's format. All of it
is integer arithmetic; no floating point is used.
-/
import DelegusCheckSpec.Inputs

namespace DelegusCheck

open Lean (Json JsonNumber)

/-! ## Rationals as pairs of naturals -/

/-- `a/b < c/d` (b, d > 0). -/
def qlt (a b c d : Nat) : Bool := a * d < c * b
def qle (a b c d : Nat) : Bool := a * d ≤ c * b

/-- `x = p / q` rounded to the nearest integer, ties to even. -/
def roundHalfEven (p q : Nat) : Nat :=
  let f := p / q
  let r := p % q
  if 2 * r < q then f else if 2 * r > q then f + 1 else if f % 2 == 0 then f else f + 1

/-! ## Decimal to the nearest binary64 -/

/-- A finite positive double `m · 2^e` with `m < 2^53`, or `none` when the
    value overflows. `m = 0` is an underflow to zero. -/
structure Dbl where
  m : Nat
  e : Int

def pow2 (e : Int) : Nat × Nat := if e ≥ 0 then (2 ^ e.toNat, 1) else (1, 2 ^ (-e).toNat)

/-- `p / q` (p, q > 0) rounded to the nearest double. -/
def toDouble (p q : Nat) : Option Dbl :=
  -- binary exponent of the leading bit: 2^b ≤ p/q < 2^(b+1)
  let b0 : Int := (p.log2 : Int) - (q.log2 : Int)
  let b : Int :=
    let (n, d) := pow2 b0
    if qlt p q n d then b0 - 1 else
      let (n', d') := pow2 (b0 + 1)
      if qle n' d' p q then b0 + 1 else b0
  let e : Int := max (b - 52) (-1074)
  -- m = round(p / (q · 2^e))
  let m := if e ≥ 0 then roundHalfEven p (q * 2 ^ e.toNat) else roundHalfEven (p * 2 ^ (-e).toNat) q
  let (m, e) := if m == 2 ^ 53 then (2 ^ 52, e + 1) else (m, e)
  if e > 971 then none else some ⟨m, e⟩

/-! ## The shortest decimal that rounds back -/

/-- `10^z` as a fraction. -/
def pow10 (z : Int) : Nat × Nat := if z ≥ 0 then (10 ^ z.toNat, 1) else (1, 10 ^ (-z).toNat)

/-- `x · y` for fractions. -/
def qmul (a b c d : Nat) : Nat × Nat := (a * c, b * d)

/-- The number of decimal digits of `n > 0`. -/
def numDigits (n : Nat) : Nat := (toString n).length

/-- The exponent `n` with `10^(n-1) ≤ x < 10^n`, for `x = a/b > 0`. -/
def decExp (a b : Nat) : Int :=
  let n0 : Int := (numDigits a : Int) - (numDigits b : Int)
  let adjust (n : Int) : Int :=
    let (hn, hd) := pow10 n
    if qle hn hd a b then n + 1 else
      let (ln, ld) := pow10 (n - 1)
      if qlt a b ln ld then n - 1 else n
  adjust (adjust n0)

/-- The ECMAScript `Number::toString` digits of a positive double: `s` with
    `k` digits and exponent `n`, the value being `s · 10^(n−k)`. -/
def shortest (x : Dbl) : Nat × Nat × Int :=
  -- the double as a fraction, and the half-way points to its neighbours
  let (vn, vd) := pow2 x.e
  let a := x.m * vn
  let b := vd
  let lowerGap := x.m == 2 ^ 52 && x.e > -1074
  let (ln, ld) := if lowerGap then ((4 * x.m - 1) * vn, 4 * vd) else ((2 * x.m - 1) * vn, 2 * vd)
  let (hn, hd) := ((2 * x.m + 1) * vn, 2 * vd)
  let even := x.m % 2 == 0
  let inside (tn td : Nat) : Bool :=
    (if even then qle ln ld tn td else qlt ln ld tn td) &&
    (if even then qle tn td hn hd else qlt tn td hn hd)
  let n := decExp a b
  let rec go (k : Nat) (fuel : Nat) : Nat × Nat × Int :=
    match fuel with
    | 0 => (0, 0, 0)
    | fuel + 1 =>
      -- s1 = floor(x · 10^(k−n)), and s1 + 1
      let (pn, pd) := pow10 ((k : Int) - n)
      let s1 := (a * pn) / (b * pd)
      let cands : List (Nat × Int) := [s1, s1 + 1].filterMap fun s =>
        if s == 0 then none
        else if s == 10 ^ k then some (10 ^ (k - 1), n + 1)
        else if 10 ^ (k - 1) ≤ s && s < 10 ^ k then some (s, n)
        else none
      let valid := cands.filter fun (s, n') =>
        let (tn, td) := pow10 (n' - (k : Int))
        inside (s * tn) td
      -- the closest to x; on a tie, the even one
      let dist (c : Nat × Int) : Nat × Nat :=
        let (tn, td) := pow10 (c.2 - (k : Int))
        let t := c.1 * tn
        -- |t/td − a/b| = |t·b − a·td| / (td·b)
        (if t * b ≥ a * td then t * b - a * td else a * td - t * b, td * b)
      match valid with
      | [] => go (k + 1) fuel
      | [c] => (c.1, k, c.2)
      | c₁ :: c₂ :: _ =>
        let (d1n, d1d) := dist c₁
        let (d2n, d2d) := dist c₂
        if qlt d1n d1d d2n d2d then (c₁.1, k, c₁.2)
        else if qlt d2n d2d d1n d1d then (c₂.1, k, c₂.2)
        else if c₁.1 % 2 == 0 then (c₁.1, k, c₁.2) else (c₂.1, k, c₂.2)
  go 1 17

/-! ## ECMAScript `Number::toString` -/

def zeros (n : Nat) : String := String.ofList (List.replicate n '0')

/-- Format `s · 10^(n−k)` (`s` has `k` digits) as ECMAScript does. -/
def formatNumber (s k : Nat) (n : Int) : String :=
  let ds := toString s
  if (k : Int) ≤ n ∧ n ≤ 21 then ds ++ zeros (n - k).toNat
  else if 0 < n ∧ n ≤ 21 then
    String.ofList (ds.toList.take n.toNat) ++ "." ++ String.ofList (ds.toList.drop n.toNat)
  else if -6 < n ∧ n ≤ 0 then "0." ++ zeros (-n).toNat ++ ds
  else
    let e := n - 1
    let sign := if e ≥ 0 then "+" else "-"
    let mant := if k == 1 then ds else String.ofList (ds.toList.take 1) ++ "." ++ String.ofList (ds.toList.drop 1)
    mant ++ "e" ++ sign ++ toString e.natAbs

/-- RFC 8785 serialization of a JSON number, or `none` if it is not a finite
    double. -/
def jcsNumber (x : JsonNumber) : Option String :=
  if x.mantissa == 0 then some "0" else
  let p := x.mantissa.natAbs
  let q := 10 ^ x.exponent
  match toDouble p q with
  | none => none
  | some d =>
    if d.m == 0 then some "0" else
    let (s, k, n) := shortest d
    let body := formatNumber s k n
    some (if x.mantissa < 0 then "-" ++ body else body)

/-! ## Strings and keys -/

def hex4 (n : Nat) : String :=
  let h := "0123456789abcdef".toList
  String.ofList [h.getD (n / 4096 % 16) '0', h.getD (n / 256 % 16) '0', h.getD (n / 16 % 16) '0', h.getD (n % 16) '0']

/-- `JSON.stringify` quoting (RFC 8785 §3.2.2.2). -/
def jcsString (s : String) : String :=
  let body := s.toList.foldl (fun acc c =>
    acc ++ match c with
      | '"' => "\\\""
      | '\\' => "\\\\"
      | '\x08' => "\\b"
      | '\x0c' => "\\f"
      | '\n' => "\\n"
      | '\r' => "\\r"
      | '\t' => "\\t"
      | c => if c.toNat < 0x20 then "\\u" ++ hex4 c.toNat else String.singleton c) ""
  "\"" ++ body ++ "\""

/-- UTF-16 code units of a string (RFC 8785 §3.2.3 sorts keys by these). -/
def utf16 (s : String) : List Nat :=
  s.toList.flatMap fun c =>
    let v := c.toNat
    if v < 0x10000 then [v] else
      let u := v - 0x10000
      [0xD800 + u / 1024, 0xDC00 + u % 1024]

def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && lexLt as bs)

/-! ## Values -/

/-- RFC 8785 canonical text of a JSON value; `none` if a number is not a
    finite double. -/
partial def jcs (j : Json) : Option String :=
  match j with
  | .null => some "null"
  | .bool true => some "true"
  | .bool false => some "false"
  | .num n => jcsNumber n
  | .str s => some (jcsString s)
  | .arr xs => do
    let parts ← xs.toList.mapM jcs
    some ("[" ++ String.intercalate "," parts ++ "]")
  | .obj _ => do
    let ms := (members j).mergeSort fun a b => !lexLt (utf16 b.1) (utf16 a.1)
    let parts ← ms.mapM fun (k, v) => do return jcsString k ++ ":" ++ (← jcs v)
    some ("{" ++ String.intercalate "," parts ++ "}")

end DelegusCheck
