/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# Algebraic and normed fibres of pullback bundles

The fibres of `f *ᵖ E` inherit their additive group, topological module, normed and inner product
structures from `E (f x)`. Mathlib supplies the additive monoid and module structures. The
topological group structures let fibrewise linear equivalences between pullbacks, such as the
pullback `x ↦ e (f x)` of a family of fibrewise linear equivalences `e`, induce maps of total
spaces with continuous inverses. The normed instances allow the orthonormal frame bundle of a
pullback to use exactly the original fibre metrics, with no transport or renorming.
-/

public section

namespace Bundle.Pullback

variable {B B' : Type*} {E : B → Type*} (f : B' → B)

/-- A pullback fibre carries the additive group structure of the original fibre. -/
instance instAddCommGroup [∀ b, AddCommGroup (E b)] (x : B') : AddCommGroup ((f *ᵖ E) x) :=
  inferInstanceAs (AddCommGroup (E (f x)))

/-- Addition and negation on a pullback fibre are continuous when they are on the original
fibre. -/
instance instIsTopologicalAddGroup [∀ b, AddCommGroup (E b)] [∀ b, TopologicalSpace (E b)]
    [∀ b, IsTopologicalAddGroup (E b)] (x : B') : IsTopologicalAddGroup ((f *ᵖ E) x) :=
  inferInstanceAs (IsTopologicalAddGroup (E (f x)))

/-- Scalar multiplication on a pullback fibre is continuous when it is on the original fibre. -/
instance instContinuousSMul {R : Type*} [Semiring R] [TopologicalSpace R]
    [∀ b, AddCommMonoid (E b)] [∀ b, Module R (E b)] [∀ b, TopologicalSpace (E b)]
    [∀ b, ContinuousSMul R (E b)] (x : B') : ContinuousSMul R ((f *ᵖ E) x) :=
  inferInstanceAs (ContinuousSMul R (E (f x)))

/-- A pullback fibre carries the normed additive group structure of the original fibre. -/
instance instNormedAddCommGroup [∀ b, NormedAddCommGroup (E b)] (x : B') :
    NormedAddCommGroup ((f *ᵖ E) x) :=
  inferInstanceAs (NormedAddCommGroup (E (f x)))

/-- Scalar multiplication on a normed pullback fibre has the original norm bound. -/
instance instNormedSpace {𝕜 : Type*} [NormedField 𝕜]
    [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace 𝕜 (E b)] (x : B') :
    NormedSpace 𝕜 ((f *ᵖ E) x) :=
  inferInstanceAs (NormedSpace 𝕜 (E (f x)))

/-- The inner product on a pullback fibre is the original fibre inner product. -/
instance instInnerProductSpace {𝕜 : Type*} [RCLike 𝕜]
    [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace 𝕜 (E b)] (x : B') :
    InnerProductSpace 𝕜 ((f *ᵖ E) x) :=
  inferInstanceAs (InnerProductSpace 𝕜 (E (f x)))

end Bundle.Pullback
