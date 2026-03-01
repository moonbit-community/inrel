# inrel

`inrel` is a MoonBit workspace for compiling inductive relations into practical generators.

It is inspired by:

- *Generating Good Generators for Inductive Relations*  
  <https://dl.acm.org/doi/abs/10.1145/3158133>

## What Is Special Here

- Paper-aligned DSL for inductive relations, constructors, hypotheses, and modes.
- eDSL for compilation pipeline from relation specs to generator AST.
- Implemented sound unification core and hypothesis handling.
- Two execution paths:
  - runtime AST interpreter (`RuntimeValue`)
  - denotational interpreter that compiles directly to typed MoonBit `Gen[T]`.
- Strong end-to-end tests on nontrivial examples:
  - STLC well-typed term generation and evaluation sanity
  - BST boundedness
  - complete tree shape constraints

## Core Principles (From the Paper)

The input relation follows the paper's core shape:

$$
\text{Inductive } R : A_1 \to \cdots \to A_p \to \mathrm{Prop} :=\\
\cdots \mid C : \forall \bar{x},\; S\,\bar{e} \to R\,e_1\,\cdots\,e_p \mid \cdots
$$

The generated bounded generator follows the size split:

$$
\text{Fixpoint } aux\_arb\ size\ in_1\ \cdots\ in_n :=\\
\text{match } size\ \text{with}\\
\mid O \Rightarrow backtrack[(w_C, g_C)\dots]\\
\mid S\ size' \Rightarrow backtrack[(w_C, g_C)\dots]
\text{end}
$$

Unification ranges are represented in the same spirit as the paper:

$$
r ::= \mathrm{undef}_\tau \mid \mathrm{fixed} \mid u \mid C(r_1,\dots,r_n)
$$

> "The core contribution of this paper is a method for compiling a large class of logical conditions, expressed as Coq inductive relations, into random generators together with soundness and completeness proofs for these generators."

> "A side benefit of this approach is that, by compiling inductive relations into generators, we avoid the interpretive overhead of existing narrowing-based generators."

In this MoonBit project, proof generation is currently out of scope; compilation + execution are the focus.

## How This Maps to Code

- Relation DSL (`dsl/spec/spec.mbt`)
  - `RelationSpec`, `ConstructorSpec`, `HypothesisSpec`, `Term`, `ParamMode`.
  - `Show`/rendering support to print paper-like inductive declarations.

- Unification core (`dsl/unify/unify.mbt`)
  - `Unknown`, `Range`, `Pattern`, `UnifyState`.
  - Core algorithms aligned with Figure 3 naming:
    - `unify`, `unify_r`, `unify_c`, `unify_rc`, `match_range`, `match_aux`.

- Generator AST and compilation (`dsl/gen/ast.mbt`, `dsl/gen/compile.mbt`)
  - AST nodes like `Backtrack`, `MatchPattern`, `IfGuard`, `Bind`, `RetSome`, `RetNone`.
  - Constructor-case pipeline follows Figure 4 order:
    - unification -> pattern checks -> equality checks -> hypothesis emission -> final assembly.

- Hypothesis handling (`dsl/gen/hypothesis.mbt`)
  - Implements Section 4.5-style handling and integrates with unification constraints.

- Execution
  - Runtime interpreter: `dsl/gen/runtime.mbt`
  - Denotational interpreter to typed generators: `dsl/gen/denotation.mbt`
  - Denotation environment builder DSL: `dsl/gen/denotation_builder.mbt`

## Promising Results in This Repository

- STLC (simply-typed lambda calculus) generation (`dsl/gen/lambda_integration_wbtest.mbt`)
  - Generates well-typed terms under contexts and target types.
  - Includes arithmetic nodes (`Add`/`Mul`) and application/lambda structure.
  - Includes evaluator checks for "well-typed closed terms never go wrong" style sanity tests.

- BST relation generation (`dsl/gen/runtime_wbtest.mbt`, `dsl/gen/compile_wbtest.mbt`)
  - Generated trees satisfy bounds (`lo < x < hi`) recursively.

- Complete tree generation (`dsl/gen/runtime_wbtest.mbt`, `dsl/gen/compile_wbtest.mbt`)
  - Size-aware branch behavior (`O` vs `S n`) and recursive structural shape are validated.

- Additional relation pipeline coverage (`dsl/gen/compile_wbtest.mbt`, `dsl/gen/hypothesis_wbtest.mbt`)
  - Covers constructor assembly, weighted backtracking, and hypothesis emission details.

## Packages

- `CAIMEOX/inrel/dsl/spec`
- `CAIMEOX/inrel/dsl/unify`
- `CAIMEOX/inrel/dsl/gen`
