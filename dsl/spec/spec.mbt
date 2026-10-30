///|
/// Type expression for the DSL.
///
/// Correspondence:
/// - Paper Section 4.1 assumes simply-typed inductive arguments `A1 .. Ap`.
/// - `TypeRef` is the local representation of those argument and binder types.
pub enum TypeRef {
  Named(String)
  App(String, Array[TypeRef])
} derive(Eq, ToJson)

///|
pub fn ty(name : String) -> TypeRef {
  TypeRef::Named(name)
}

///|
pub fn type_app(name : String, args : Array[TypeRef]) -> TypeRef {
  TypeRef::App(name, args)
}

///|
/// Constructor expressions used in relation conclusions and hypotheses.
///
/// Correspondence:
/// - Paper Section 4.1 uses constructor expressions `e`, `e1 .. ep` that contain
///   constructors and variables.
/// - `Term` mirrors that grammar directly.
pub enum Term {
  Var(String)
  Ctor(String, Array[Term])
} derive(Eq, ToJson)

///|
pub fn v(name : String) -> Term {
  Term::Var(name)
}

///|
pub fn term_ctor(name : String, args : Array[Term]) -> Term {
  Term::Ctor(name, args)
}

///|
/// Mode assignment for each relation parameter.
///
/// Correspondence:
/// - Paper Section 3 discusses assigning modes (`in`, `out`) to relation
///   parameters before generation.
pub enum ParamMode {
  In
  Out
} derive(Eq, ToJson)

///|
pub fn mode_in() -> ParamMode {
  ParamMode::In
}

///|
pub fn mode_out() -> ParamMode {
  ParamMode::Out
}

///|
/// A relation parameter specification `(name : type, mode)`.
pub struct ParamSpec {
  name : String
  ty : TypeRef
  mode : ParamMode
} derive(Eq, ToJson)

///|
pub fn make_param(name : String, ty : TypeRef, mode : ParamMode) -> ParamSpec {
  { name, ty, mode, }
}

///|
/// Universally quantified constructor binder `x : tx`.
///
/// Correspondence:
/// - Paper Section 4.1 constructor shape `C : forall x, ...`.
pub struct BinderSpec {
  name : String
  ty : TypeRef
} derive(Eq, ToJson)

///|
pub fn make_binder(name : String, ty : TypeRef) -> BinderSpec {
  { name, ty, }
}

///|
/// Constructor hypothesis.
///
/// `RelCall` models an inductive-precondition hypothesis (`S e` in Section 4.1).
/// `Predicate` models a decidable side condition (e.g. `x < hi` from Section 3).
pub enum HypothesisSpec {
  RelCall(String, Array[Term])
  Predicate(String, Array[Term])
} derive(Eq, ToJson)

///|
pub fn hypothesis_rel_call(name : String, args : Array[Term]) -> HypothesisSpec {
  HypothesisSpec::RelCall(name, args)
}

///|
pub fn hypothesis_predicate(
  name : String,
  args : Array[Term],
) -> HypothesisSpec {
  HypothesisSpec::Predicate(name, args)
}

///|
/// One constructor of an inductive relation.
///
/// Correspondence:
/// - Paper Section 4.1 form:
///   `C : forall x, S e -> R e1 ... ep`
/// - Fields:
///   - `binders`      := `x`
///   - `hypotheses`   := each `S e` and side conditions
///   - `conclusion`   := `e1 .. ep`
///   - `weight`       := constructor weight `wc` in Section 4.3 backtracking list
pub struct ConstructorSpec {
  name : String
  binders : Array[BinderSpec]
  hypotheses : Array[HypothesisSpec]
  conclusion : Array[Term]
  weight : Int32
} derive(Eq, ToJson)

///|
/// Whole inductive relation specification.
///
/// Correspondence:
/// - Paper Section 4.1 relation header:
///   `Inductive R : A1 -> ... -> Ap -> Prop := ...`
pub struct RelationSpec {
  name : String
  params : Array[ParamSpec]
  constructors : Array[ConstructorSpec]
} derive(Eq, ToJson)

///|
/// Convenience constructor with default weight 1.
pub fn make_constructor(
  name : String,
  binders : Array[BinderSpec],
  hypotheses : Array[HypothesisSpec],
  conclusion : Array[Term],
  weight~ : Int32 = 1,
) -> ConstructorSpec {
  { name, binders, hypotheses, conclusion, weight, }
}

///|
/// Convenience constructor for `RelationSpec`.
pub fn make_relation(
  name : String,
  params : Array[ParamSpec],
  constructors : Array[ConstructorSpec],
) -> RelationSpec {
  { name, params, constructors, }
}

///|
/// Number of parameters (`p` in Section 4.1).
pub fn RelationSpec::arity(self : RelationSpec) -> Int32 {
  self.params.length()
}

///|
/// Positions of input parameters.
pub fn RelationSpec::input_positions(self : RelationSpec) -> Array[Int32] {
  let out : Array[Int32] = []
  for i, p in self.params {
    if p.mode is In {
      out.push(i)
    }
  }
  out
}

///|
/// Positions of output parameters.
pub fn RelationSpec::output_positions(self : RelationSpec) -> Array[Int32] {
  let out : Array[Int32] = []
  for i, p in self.params {
    if p.mode is Out {
      out.push(i)
    }
  }
  out
}

///|
fn TypeRef::render(self : TypeRef) -> String {
  match self {
    Named(name) => name
    App(name, args) =>
      if args.is_empty() {
        name
      } else {
        let parts = args.map(arg => {
          match arg {
            Named(_) => arg.render()
            App(_, _) => "(\{arg.render()})"
          }
        })
        let args_text = parts.join(" ")
        "\{name} \{args_text}"
      }
  }
}

///|
fn Term::render(self : Term) -> String {
  match self {
    Var(name) => name
    Ctor(name, args) =>
      if args.is_empty() {
        name
      } else {
        let args_text = args.map(arg => arg.render()).join(" ")
        "(\{name} \{args_text})"
      }
  }
}

///|
fn HypothesisSpec::render(self : HypothesisSpec) -> String {
  match self {
    RelCall(name, args) | Predicate(name, args) =>
      if args.is_empty() {
        name
      } else {
        let args_text = args.map(arg => arg.render()).join(" ")
        "\{name} \{args_text}"
      }
  }
}

///|
fn render_relation_call(name : String, args : Array[Term]) -> String {
  if args.is_empty() {
    name
  } else {
    let args_text = args.map(arg => arg.render()).join(" ")
    "\{name} \{args_text}"
  }
}

///|
fn ConstructorSpec::render(
  self : ConstructorSpec,
  relation_name : String,
) -> String {
  let pieces : Array[String] = []
  for hypothesis in self.hypotheses {
    pieces.push(hypothesis.render())
  }
  pieces.push(render_relation_call(relation_name, self.conclusion))
  let body = pieces.join(" -> ")
  let binders = self.binders.map(b => b.name).join(" ")
  if binders is "" {
    "| \{self.name} : \{body}"
  } else {
    "| \{self.name} : forall \{binders}, \{body}"
  }
}

///|
pub fn RelationSpec::to_inductive_string(self : RelationSpec) -> String {
  let signature = if self.params.is_empty() {
    "Prop"
  } else {
    let param_types = self.params.map(param => param.ty.render()).join(" -> ")
    "\{param_types} -> Prop"
  }
  let header = "Inductive \{self.name} : \{signature} :="
  if self.constructors.is_empty() {
    "\{header}\n."
  } else {
    let constructors = self.constructors
      .map(c => c.render(self.name))
      .join("\n")
    "\{header}\n\{constructors}."
  }
}

///|
pub impl Show for RelationSpec with fn output(self, logger) {
  logger.write_string(self.to_inductive_string())
}
