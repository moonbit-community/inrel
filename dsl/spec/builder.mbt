///|
/// Variable reference used by the scoped builder API.
///
/// This is a frontend convenience wrapper and always lowers to `Term::Var`.
pub struct VarRef {
  name : String
} derive(Eq, Show, ToJson)

///|
pub fn var_ref(name : String) -> VarRef {
  { name, }
}

///|
pub fn VarRef::name(self : VarRef) -> String {
  self.name
}

///|
pub fn VarRef::term(self : VarRef) -> Term {
  v(self.name)
}

///|
/// Constructor body in the scoped builder frontend.
pub struct ConstructorBody {
  hypotheses : Array[HypothesisSpec]
  conclusion : Array[Term]
} derive(Eq, Show, ToJson)

///|
/// Build a constructor body that will be lowered into `ConstructorSpec`.
pub fn body(
  conclusion : Array[Term],
  hypotheses~ : Array[HypothesisSpec] = [],
) -> ConstructorBody {
  { hypotheses, conclusion, }
}

///|
/// Scope object passed to scoped constructor builders.
pub struct Scope {
  vars : Array[VarRef]
} derive(Eq, Show, ToJson)

///|
pub fn Scope::at(self : Scope, index : Int32) -> VarRef {
  self.vars[index]
}

///|
pub fn Scope::find(self : Scope, name : String) -> VarRef? {
  for v in self.vars {
    if v.name == name {
      return Some(v)
    }
  }
  None
}

///|
/// Find a bound variable by name.
///
/// This is the preferred API in scoped builders, compared with `Scope::at`.
/// It aborts immediately if the name is not in scope.
pub fn Scope::v(self : Scope, name : String) -> VarRef {
  match self.find(name) {
    Some(v) => v
    None => {
      let known = self.vars.map(v => v.name).join(", ")
      abort("Unknown binder '\{name}'. Known binders: [\{known}]")
    }
  }
}

///|
pub fn Scope::term(self : Scope, name : String) -> Term? {
  match self.find(name) {
    Some(v) => Some(v.term())
    None => None
  }
}

///|
pub fn Scope::term_or_abort(self : Scope, name : String) -> Term {
  self.v(name).term()
}

///|
pub fn in_param(name : String, ty : TypeRef) -> ParamSpec {
  make_param(name, ty, mode_in())
}

///|
pub fn out_param(name : String, ty : TypeRef) -> ParamSpec {
  make_param(name, ty, mode_out())
}

///|
pub fn binder(name : String, ty : TypeRef) -> BinderSpec {
  make_binder(name, ty)
}

///|
pub fn ctor(name : String, args : Array[Term]) -> Term {
  term_ctor(name, args)
}

///|
pub fn rel(name : String, args : Array[Term]) -> HypothesisSpec {
  hypothesis_rel_call(name, args)
}

///|
pub fn pred(name : String, args : Array[Term]) -> HypothesisSpec {
  hypothesis_predicate(name, args)
}

///|
pub fn inductive(
  name : String,
  params : Array[ParamSpec],
  constructors : Array[ConstructorSpec],
) -> RelationSpec {
  make_relation(name, params, constructors)
}

///|
/// Generic scoped constructor builder. The closure receives bound vars via
/// `Scope` and returns a `ConstructorBody`.
pub fn constructor_scoped(
  name : String,
  binders : Array[BinderSpec],
  build : (Scope) -> ConstructorBody,
  weight~ : Int32 = 1,
) -> ConstructorSpec {
  let vars = binders.map(b => var_ref(b.name))
  let built = build({ vars, })
  make_constructor(name, binders, built.hypotheses, built.conclusion, weight~)
}

///|
/// Scoped constructor helper for zero binders.
pub fn forall0(
  name : String,
  build : () -> ConstructorBody,
  weight~ : Int32 = 1,
) -> ConstructorSpec {
  let built = build()
  make_constructor(name, [], built.hypotheses, built.conclusion, weight~)
}

///|
/// Scoped constructor helper for one binder.
pub fn forall1(
  name : String,
  b1 : BinderSpec,
  build : (VarRef) -> ConstructorBody,
  weight~ : Int32 = 1,
) -> ConstructorSpec {
  let built = build(var_ref(b1.name))
  make_constructor(name, [b1], built.hypotheses, built.conclusion, weight~)
}

///|
/// Scoped constructor helper for two binders.
pub fn forall2(
  name : String,
  b1 : BinderSpec,
  b2 : BinderSpec,
  build : (VarRef, VarRef) -> ConstructorBody,
  weight~ : Int32 = 1,
) -> ConstructorSpec {
  let built = build(var_ref(b1.name), var_ref(b2.name))
  make_constructor(name, [b1, b2], built.hypotheses, built.conclusion, weight~)
}

///|
/// Scoped constructor helper for three binders.
pub fn forall3(
  name : String,
  b1 : BinderSpec,
  b2 : BinderSpec,
  b3 : BinderSpec,
  build : (VarRef, VarRef, VarRef) -> ConstructorBody,
  weight~ : Int32 = 1,
) -> ConstructorSpec {
  let built = build(var_ref(b1.name), var_ref(b2.name), var_ref(b3.name))
  make_constructor(
    name,
    [b1, b2, b3],
    built.hypotheses,
    built.conclusion,
    weight~,
  )
}

///|
pub fn forall4(
  name : String,
  b1 : BinderSpec,
  b2 : BinderSpec,
  b3 : BinderSpec,
  b4 : BinderSpec,
  build : (VarRef, VarRef, VarRef, VarRef) -> ConstructorBody,
  weight~ : Int32 = 1,
) -> ConstructorSpec {
  let built = build(
    var_ref(b1.name),
    var_ref(b2.name),
    var_ref(b3.name),
    var_ref(b4.name),
  )
  make_constructor(
    name,
    [b1, b2, b3, b4],
    built.hypotheses,
    built.conclusion,
    weight~,
  )
}
