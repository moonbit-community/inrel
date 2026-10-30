///|
test "public Show output remains compatible" {
  let ty = App("List", [Named("T")])
  let term = Ctor("Cons", [Var("x"), Ctor("Nil", [])])
  let hyp = RelCall("member", [term])
  inspect(
    ty,
    content=(
      #|App(List, [Named(T)])
    ),
  )
  inspect(
    term,
    content=(
      #|Ctor(Cons, [Var(x), Ctor(Nil, [])])
    ),
  )
  inspect(
    In,
    content=(
      #|In
    ),
  )
  inspect(
    Out,
    content=(
      #|Out
    ),
  )
  inspect(
    ParamSpec::{ name: "x", ty, mode: In, },
    content=(
      #|{name: x, ty: App(List, [Named(T)]), mode: In}
    ),
  )
  inspect(
    BinderSpec::{ name: "x", ty, },
    content=(
      #|{name: x, ty: App(List, [Named(T)])}
    ),
  )
  inspect(
    hyp,
    content=(
      #|RelCall(member, [Ctor(Cons, [Var(x), Ctor(Nil, [])])])
    ),
  )
  inspect(
    Predicate("p", [Var("x")]),
    content=(
      #|Predicate(p, [Var(x)])
    ),
  )
  inspect(
    ConstructorSpec::{
      name: "C",
      binders: [],
      hypotheses: [hyp],
      conclusion: [term],
      weight: 2,
    },
    content=(
      #|{name: C, binders: [], hypotheses: [RelCall(member, [Ctor(Cons, [Var(x), Ctor(Nil, [])])])], conclusion: [Ctor(Cons, [Var(x), Ctor(Nil, [])])], weight: 2}
    ),
  )
  inspect(
    VarRef::{ name: "x\n\"", },
    content=(
      #|{name: x
      #|"}
    ),
  )
  inspect(
    ConstructorBody::{ hypotheses: [hyp], conclusion: [term], },
    content=(
      #|{hypotheses: [RelCall(member, [Ctor(Cons, [Var(x), Ctor(Nil, [])])])], conclusion: [Ctor(Cons, [Var(x), Ctor(Nil, [])])]}
    ),
  )
  inspect(
    Scope::{ vars: [VarRef::{ name: "x", }], },
    content=(
      #|{vars: [{name: x}]}
    ),
  )
}
