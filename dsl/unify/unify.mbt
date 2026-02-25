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
pub fn pattern_var(u : Unknown) -> Pattern {
  Pattern::PVar(u)
}

///|
pub fn pattern_ctor(c : String, ps : Array[Pattern]) -> Pattern {
  Pattern::PCtor(c, ps)
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
pub fn range_link(u : Unknown) -> Range {
  Range::Link(u)
}

///|
pub fn range_ctor(c : String, rs : Array[Range]) -> Range {
  Range::Ctor(c, rs)
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
  equalities : Set[(Unknown, Unknown)]
  patterns : Array[(Unknown, Pattern)]
  unknowns : Set[Unknown]
  mut next_unknown : Unknown
}

///|
fn next_unknown_id(us : Array[Unknown]) -> Unknown {
  let mut max_seen = -1
  for u in us {
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
  us : Array[Unknown],
  next_unknown? : Unknown = next_unknown_id(us),
) -> UnifyState {
  {
    constraints,
    equalities: Set::new(),
    patterns: [],
    unknowns: Set::from_array(us),
    next_unknown,
  }
}

///|
/// Figure 2 action `update : Unknown -> Range -> Unify ()`.
pub fn UnifyState::update_constraint(
  self : UnifyState,
  u : Unknown,
  r : Range,
) -> Unit {
  self.constraints[u] = r
}

///|
/// Figure 2 action `equality : Unknown -> Unknown -> Unify ()`.
pub fn UnifyState::record_equality(
  self : UnifyState,
  u1 : Unknown,
  u2 : Unknown,
) -> Unit {
  let eq = @cmp.minmax(u1, u2)
  self.equalities.add(eq)
}

///|
/// Figure 2 action `pattern : Unknown -> Pattern -> Unify ()`.
pub fn UnifyState::record_pattern(
  self : UnifyState,
  u : Unknown,
  p : Pattern,
) -> Unit {
  self.patterns.push((u, p))
}

///|
/// Figure 2 action `fresh : Unify Unknown`.
pub fn UnifyState::fresh_unknown(
  self : UnifyState,
  ty : @spec.TypeRef,
) -> Unknown {
  let u = self.next_unknown
  self.next_unknown += 1
  self.unknowns.add(u)
  self.constraints[u] = Range::Undef(ty)
  u
}

///|
/// Constraint lookup helper.
pub fn UnifyState::lookup(self : UnifyState, u : Unknown) -> Range? {
  self.constraints.get(u)
}

///|
fn UnifyState::match_aux_all(
  self : UnifyState,
  rs : Array[Range],
) -> Array[Pattern]? {
  let ps : Array[Pattern] = []
  for r in rs {
    match self.match_aux(r) {
      Some(p) => ps.push(p)
      None => return None
    }
  }
  Some(ps)
}

///|
fn fresh_placeholder_ty() -> @spec.TypeRef {
  // `Range::Fixed` currently carries no type payload. We keep a synthetic marker
  // type for fresh unknowns introduced by Figure 3 `matchAux` fixed-branch.
  @spec.ty("_fixed")
}

///|
/// Figure 3 top-level `unify`.
///
/// Correspondence:
/// - `unify u1 u2`
/// - `unify (C1 ...) (C2 ...)`
/// - `unify u (C ...)` / `unify (C ...) u`
///
/// Note:
/// - Unknowns are represented as `Range::Link(u)` at call-sites.
pub fn UnifyState::unify(self : UnifyState, r1 : Range, r2 : Range) -> Bool {
  match (r1, r2) {
    (Link(u1), Link(u2)) if u1 == u2 => true
    (Link(u1), Link(u2)) =>
      match (self.lookup(u1), self.lookup(u2)) {
        (Some(r1), Some(r2)) => self.unify_r(u1, r1, u2, r2)
        _ => false
      }
    (Link(u), Ctor(c, rs)) | (Ctor(c, rs), Link(u)) =>
      match self.lookup(u) {
        Some(r) => self.unify_rc(u, r, c, rs)
        None => false
      }
    (Ctor(c1, rs1), Ctor(c2, rs2)) => self.unify_c(c1, rs1, c2, rs2)
    _ => false
  }
}

///|
/// Figure 3 helper `unifyR`.
pub fn UnifyState::unify_r(
  self : UnifyState,
  u1 : Unknown,
  r1 : Range,
  u2 : Unknown,
  r2 : Range,
) -> Bool {
  match (r1, r2) {
    (Undef(_), _) => {
      self.update_constraint(u1, Link(u2))
      true
    }
    (Link(_), Undef(_)) => {
      self.update_constraint(u2, Link(u1))
      true
    }
    (Link(next_u), _) => self.unify(Link(next_u), Link(u2))
    (Ctor(_, _), Undef(_)) => {
      self.update_constraint(u2, Link(u1))
      true
    }
    (Ctor(_, _), Link(next_u)) => self.unify(Link(u1), Link(next_u))
    (Ctor(c1, rs1), Ctor(c2, rs2)) => self.unify_c(c1, rs1, c2, rs2)
    (Ctor(c, rs), Fixed) => self.match_range(u2, c, rs)
    (Fixed, Undef(_)) => {
      self.update_constraint(u2, Link(u1))
      true
    }
    (Fixed, Link(next_u)) => self.unify(Link(u1), Link(next_u))
    (Fixed, Fixed) => {
      self.record_equality(u1, u2)
      self.update_constraint(u1, Link(u2))
      true
    }
    (Fixed, Ctor(c, rs)) => self.match_range(u1, c, rs)
  }
}

///|
/// Figure 3 helper `unifyC`.
pub fn UnifyState::unify_c(
  self : UnifyState,
  c1 : String,
  rs1 : Array[Range],
  c2 : String,
  rs2 : Array[Range],
) -> Bool {
  guard c1 == c2 && rs1.length() == rs2.length() else { false }
  rs1
  .zip(rs2)
  .all(pair => {
    match pair {
      (r1, r2) => self.unify(r1, r2)
    }
  })
}

///|
/// Figure 3 helper `unifyRC`.
pub fn UnifyState::unify_rc(
  self : UnifyState,
  u : Unknown,
  r : Range,
  c : String,
  rs : Array[Range],
) -> Bool {
  match r {
    Undef(_) => {
      self.update_constraint(u, Ctor(c, rs))
      true
    }
    Link(v) =>
      match (self.lookup(v), v) {
        (Some(next_r), v) => self.unify_rc(v, next_r, c, rs)
        _ => false
      }
    Fixed => self.match_range(u, c, rs)
    Ctor(c2, rs2) => self.unify_c(c2, rs2, c, rs)
  }
}

///|
/// Figure 3 helper `match`.
pub fn UnifyState::match_range(
  self : UnifyState,
  u : Unknown,
  c : String,
  rs : Array[Range],
) -> Bool {
  match self.match_aux_all(rs) {
    Some(ps) => {
      self.record_pattern(u, PCtor(c, ps))
      true
    }
    None => false
  }
}

///|
/// Figure 3 helper `matchAux`.
pub fn UnifyState::match_aux(self : UnifyState, r : Range) -> Pattern? {
  match r {
    Ctor(c, rs) =>
      match self.match_aux_all(rs) {
        Some(ps) => Some(PCtor(c, ps))
        None => None
      }
    Link(u) =>
      match (self.lookup(u), u) {
        (None, _) => None
        (Some(Undef(_)), u) => {
          self.update_constraint(u, Fixed)
          Some(PVar(u))
        }
        (Some(Fixed), u) => {
          let v = self.fresh_unknown(fresh_placeholder_ty())
          self.record_equality(v, u)
          self.update_constraint(v, Link(u))
          Some(PVar(v))
        }
        (Some(Link(v)), _) => self.match_aux(Link(v))
        (Some(Ctor(c, rs)), _) =>
          match self.match_aux_all(rs) {
            Some(ps) => Some(PCtor(c, ps))
            None => None
          }
      }
    _ => None
  }
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
