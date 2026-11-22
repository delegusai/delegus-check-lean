/-
Copyright 2026 Inam Haq. Licensed under the Apache License, Version 2.0.

Phase 6: the `htu` canonical form (§4.3), written in Lean.

  lowercase scheme "://" lowercase host [":" port only if non-default] path

RFC 9449 §4.3 plus RFC 3986 §6.2.2: scheme http or https only (§4.4); no
userinfo; non-empty host; numeric port ≤ 65535, dropped when it is the
scheme default; query and fragment removed (but must be well formed);
percent-encoding normalized (hex uppercased, escapes of unreserved
characters decoded); the path otherwise exact. `normalizeHtu` is `none` for
anything that is not such a URI. Attribution for restated spec text:
"Delegus Specification v0.2, © Delegus (delegus.ai)", CC BY 4.0.
-/
import DelegusCheckSpec.Syntax

namespace DelegusCheck

def isHexDigit (c : Char) : Bool := isDigit c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def hexVal (c : Char) : Nat :=
  if isDigit c then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

/-- RFC 3986 `unreserved`. -/
def isUnreserved (c : Char) : Bool := isAlnum c || c == '-' || c == '.' || c == '_' || c == '~'
def isSubDelim (c : Char) : Bool := "!$&'()*+,;=".toList.contains c
/-- `reg-name` characters. -/
def isRegNameChar (c : Char) : Bool := isUnreserved c || isSubDelim c
/-- `pchar` characters (without escapes). -/
def isPChar (c : Char) : Bool := isRegNameChar c || c == ':' || c == '@'
/-- Query and fragment characters. -/
def isQueryChar (c : Char) : Bool := isPChar c || c == '/' || c == '?'

def toUpperHex (c : Char) : Char := if 'a' ≤ c && c ≤ 'f' then Char.ofNat (c.toNat - 32) else c
def toLowerAscii (c : Char) : Char := if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- Every character allowed, every `%` followed by two hex digits. -/
def validChars (allowed : Char → Bool) : List Char → Bool
  | [] => true
  | '%' :: a :: b :: rest => isHexDigit a && isHexDigit b && validChars allowed rest
  | '%' :: _ => false
  | c :: rest => allowed c && validChars allowed rest

/-- RFC 3986 §6.2.2 on one component: check characters, uppercase hex in
    escapes, decode escapes of unreserved characters. -/
def normalizePercent (allowed : Char → Bool) : List Char → Option (List Char)
  | [] => some []
  | '%' :: a :: b :: rest =>
    if isHexDigit a && isHexDigit b then
      let d := Char.ofNat (hexVal a * 16 + hexVal b)
      (normalizePercent allowed rest).map fun r =>
        if isUnreserved d then d :: r else '%' :: toUpperHex a :: toUpperHex b :: r
    else none
  | '%' :: _ => none
  | c :: rest => if allowed c then (normalizePercent allowed rest).map (c :: ·) else none

/-- Split at the first occurrence of `c`. -/
def splitFirst (c : Char) : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | x :: xs => if x == c then ([], some xs) else
      let (a, b) := splitFirst c xs
      (x :: a, b)

def isIpLiteral (h : List Char) : Bool :=
  match h with
  | '[' :: rest =>
    match rest.reverse with
    | ']' :: inner => !inner.isEmpty && inner.all (fun c => isHexDigit c || c == ':' || c == '.')
    | _ => false
  | _ => false

def digitsValue (ds : List Char) : Nat := ds.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

/-- The decimal digits of a natural number. -/
def natDigits (n : Nat) : List Char := (toString n).toList

/-- The scheme: `[A-Za-z][A-Za-z0-9+.-]*` followed by `://`. -/
def splitScheme (cs : List Char) : Option (List Char × List Char) :=
  let (sch, rest) := splitFirst ':' cs
  match rest with
  | some ('/' :: '/' :: r) =>
    match sch with
    | c :: cs' =>
      if (('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')) &&
          cs'.all (fun x => isAlnum x || x == '+' || x == '.' || x == '-')
      then some (sch, r) else none
    | [] => none
  | _ => none

/-- §4.3 canonical form of an `htu` value, or `none` when it is not a valid
    http(s) URI. -/
def normalizeHtu (input : String) : Option String := do
  let cs := input.toList
  if cs.isEmpty then none
  if !cs.all (fun c => '!' ≤ c && c ≤ '~') then none
  let (sch, rest) ← splitScheme cs
  let scheme := sch.map toLowerAscii
  let defaultPort ← if scheme == "http".toList then some 80
    else if scheme == "https".toList then some 443 else none
  -- strip the fragment, then the query; both must be well formed
  let (rest, frag) := splitFirst '#' rest
  if !(frag.map (validChars isQueryChar)).getD true then none
  let (rest, query) := splitFirst '?' rest
  if !(query.map (validChars isQueryChar)).getD true then none
  let (authority, pathTail) := splitFirst '/' rest
  let path := match pathTail with
    | some p => '/' :: p
    | none => []
  if authority.isEmpty || authority.contains '@' then none
  let (host, port) ← match authority with
    | '[' :: _ =>
      let (inside, after) := splitFirst ']' authority
      match after with
      | none => none
      | some after =>
        let h := inside ++ [']']
        if !isIpLiteral h then none
        let port ← match after with
          | [] => some none
          | ':' :: p => some (some p)
          | _ => none
        some (h.map toLowerAscii, port)
    | _ =>
      let (h, p) := splitFirst ':' authority
      if h.isEmpty then none
      let h' ← normalizePercent isRegNameChar h
      some (h'.map toLowerAscii, p)
  let portSuffix ← match port with
    | none => some []
    | some p =>
      if p.isEmpty || p.length > 5 || !p.all isDigit then none
      else
        let v := digitsValue p
        if v > 65535 then none
        else if v == defaultPort then some [] else some (':' :: natDigits v)
  let path' ← normalizePercent (fun c => isPChar c || c == '/') path
  some (String.ofList (scheme ++ "://".toList ++ host ++ portSuffix ++ path'))

/-- The `htu` is already in canonical form. -/
def isCanonicalHtu (s : String) : Bool := normalizeHtu s == some s

end DelegusCheck
