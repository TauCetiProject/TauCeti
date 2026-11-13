/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.Basic

/-!
# Pointwise additive-group evaluation on abstract measures

`AbstractMeasure X R E` inherits its additive-group structure from `C(X, R) →L[R] E`, so `0`,
negation, subtraction, and finite sums evaluate pointwise on continuous test functions
`f : C(X, R)`. `Mathlib.NumberTheory.Padics.Measure.Basic` registers `IsAddApply` and `IsSMulApply`
on `AbstractMeasure X R E`, making `add_apply` and `smul_apply` available, while omitting
`IsZeroApply`, `IsNegApply`, and `IsSubApply`. Registering these instances makes `zero_apply`,
`neg_apply`, `sub_apply`, and — together with `IsAddApply` — Mathlib's `@[simp]` finite-sum
evaluation lemma `sum_apply` (`(∑ i ∈ s, ν i) f = ∑ i ∈ s, ν i f`) and `FunLike.coe_sum` available
on `AbstractMeasure X R E` without passing through `AbstractMeasure.toCLMEquiv`.
-/

public section

namespace AbstractMeasure

variable {X R E : Type*} [TopologicalSpace X]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Module R E]

/-- Evaluating the zero measure at any continuous test function gives `0`. Together with
`AbstractMeasure.isAddApply`, this activates the generic `@[simp]` lemma `sum_apply` for finite
sums of measures. -/
instance isZeroApply : IsZeroApply (AbstractMeasure X R E) where

/-- Evaluating `-μ` at a continuous test function negates `μ f`. -/
instance isNegApply : IsNegApply (AbstractMeasure X R E) where

/-- Evaluating `μ - ν` at a continuous test function subtracts `ν f` from `μ f`. -/
instance isSubApply : IsSubApply (AbstractMeasure X R E) where

section Examples

example {ι : Type*} (s : Finset ι) (ν : ι → AbstractMeasure X R E) (f : C(X, R)) :
    (∑ i ∈ s, ν i) f = ∑ i ∈ s, ν i f := by
  simp

example (μ ν : AbstractMeasure X R E) (f : C(X, R)) :
    (μ - ν) f = μ f - ν f := by
  simp

end Examples

end AbstractMeasure
