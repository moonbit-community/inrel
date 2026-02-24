///|
/// Unknown identifiers used during unification.
///
/// Correspondence:
/// - Paper Section 4.2 uses unknowns `u`.
pub type Unknown = Int

///|
/// Match pattern grammar.
///
/// Correspondence:
/// - Paper Figure 2:
///   `type Pattern = Unknown | C Pattern`
pub enum Pattern {
  PVar(Unknown)
  PCtor(String, Array[Pattern])
} derive(Eq, Show, ToJson)

///|
pub fn pattern_var(unknown : Unknown) -> Pattern {
  Pattern::PVar(unknown)
}

///|
pub fn pattern_ctor(name : String, args : Array[Pattern]) -> Pattern {
  Pattern::PCtor(name, args)
}

///|
/// Range domain for unknowns.
///
/// Correspondence:
/// - Paper Section 4.2 grammar:
///   `r := undef τ | fixed | u | C r`
/// - Mapping:
///   - `Undef(ty)`      == `undef τ`
///   - `Fixed`          == `fixed`
///   - `Link(u)`        == `u`
///   - `Ctor(c, args)`  == `C r`
pub enum Range {
  Undef(@spec.TypeRef)
  Fixed
  Link(Unknown)
  Ctor(String, Array[Range])
} derive(Eq, Show, ToJson)

///|
pub fn range_undef(ty : @spec.TypeRef) -> Range {
  Range::Undef(ty)
}

///|
pub fn range_fixed() -> Range {
  Range::Fixed
}

///|
pub fn range_link(unknown : Unknown) -> Range {
  Range::Link(unknown)
}

///|
pub fn range_ctor(name : String, args : Array[Range]) -> Range {
  Range::Ctor(name, args)
}

///|
/// Mutable state for unification.
///
/// Correspondence:
/// - Paper Figure 2 record `UnifyState`:
///   - `constraints : Map Unknown Range`
///   - `equalities  : Set (Unknown, Unknown)`
///   - `patterns    : List (Unknown, Pattern)`
///   - `unknowns    : Set Unknown`
pub struct UnifyState {
  constraints : Map[Unknown, Range]
  equalities : Array[(Unknown, Unknown)]
  patterns : Array[(Unknown, Pattern)]
  unknowns : Array[Unknown]
  mut next_unknown : Unknown
}

///|
fn contains_unknown(xs : Array[Unknown], target : Unknown) -> Bool {
  let mut found = false
  for x in xs {
    if x == target {
      found = true
      break
    }
  }
  found
}

///|
fn contains_pair(
  xs : Array[(Unknown, Unknown)],
  target : (Unknown, Unknown),
) -> Bool {
  let mut found = false
  for x in xs {
    if x == target {
      found = true
      break
    }
  }
  found
}

///|
fn canonical_equality(left : Unknown, right : Unknown) -> (Unknown, Unknown) {
  if left <= right {
    (left, right)
  } else {
    (right, left)
  }
}

///|
fn next_unknown_id(unknowns : Array[Unknown]) -> Unknown {
  let mut max_seen = -1
  for u in unknowns {
    if u > max_seen {
      max_seen = u
    }
  }
  max_seen + 1
}

///|
/// Construct initial unification state.
pub fn UnifyState::new(
  constraints : Map[Unknown, Range],
  unknowns : Array[Unknown],
  next_unknown? : Unknown,
) -> UnifyState {
  let next_unknown = match next_unknown {
    Some(n) => n
    None => next_unknown_id(unknowns)
  }
  { constraints, equalities: [], patterns: [], unknowns, next_unknown }
}

///|
/// Register an unknown if not present.
pub fn UnifyState::ensure_unknown(self : UnifyState, unknown : Unknown) -> Unit {
  if !contains_unknown(self.unknowns, unknown) {
    self.unknowns.push(unknown)
  }
  if unknown >= self.next_unknown {
    self.next_unknown = unknown + 1
  }
}

///|
/// Figure 2 action `update : Unknown -> Range -> Unify ()`.
pub fn UnifyState::update_constraint(
  self : UnifyState,
  unknown : Unknown,
  range : Range,
) -> Unit {
  self.ensure_unknown(unknown)
  self.constraints[unknown] = range
}

///|
/// Figure 2 action `equality : Unknown -> Unknown -> Unify ()`.
pub fn UnifyState::record_equality(
  self : UnifyState,
  left : Unknown,
  right : Unknown,
) -> Unit {
  self.ensure_unknown(left)
  self.ensure_unknown(right)
  let normalized = canonical_equality(left, right)
  if !contains_pair(self.equalities, normalized) {
    self.equalities.push(normalized)
  }
}

///|
/// Figure 2 action `pattern : Unknown -> Pattern -> Unify ()`.
pub fn UnifyState::record_pattern(
  self : UnifyState,
  unknown : Unknown,
  pattern : Pattern,
) -> Unit {
  self.ensure_unknown(unknown)
  self.patterns.push((unknown, pattern))
}

///|
/// Figure 2 action `fresh : Unify Unknown`.
pub fn UnifyState::fresh_unknown(
  self : UnifyState,
  ty : @spec.TypeRef,
) -> Unknown {
  let unknown = self.next_unknown
  self.next_unknown += 1
  self.unknowns.push(unknown)
  self.constraints[unknown] = Range::Undef(ty)
  unknown
}

///|
/// Constraint lookup helper.
pub fn UnifyState::lookup(self : UnifyState, unknown : Unknown) -> Range? {
  self.constraints.get(unknown)
}

///|
pub fn UnifyState::equality_count(self : UnifyState) -> Int {
  self.equalities.length()
}

///|
pub fn UnifyState::pattern_count(self : UnifyState) -> Int {
  self.patterns.length()
}

///|
pub fn UnifyState::unknown_count(self : UnifyState) -> Int {
  self.unknowns.length()
}

///|
pub fn UnifyState::next_unknown_id(self : UnifyState) -> Unknown {
  self.next_unknown
}
