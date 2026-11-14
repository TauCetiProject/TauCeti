/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Ideals
public import Mathlib.Topology.ContinuousMap.Star

/-!
# Point evaluation and evaluation-kernel star subalgebras on `C(K, A)`

Mathlib constructs the vanishing ideal `ContinuousMap.idealOfSet` on `C(X, R)` and the evaluation
homeomorphism `WeakDual.CharacterSpace.homeoEval : X ≃ₜ characterSpace 𝕜 C(X, 𝕜)` for compact
Hausdorff `X` and `RCLike 𝕜`.

This file provides:
* `WeakDual.CharacterSpace.homeoEval_apply`: the `@[simp]` evaluation formula
  `homeoEval X 𝕜 x f = f x`;
* `ContinuousMap.evalKerSubalgebra`: the nonunital star subalgebra `{F ∈ C(K, A) : F x₀ = 0}` of
  continuous functions vanishing at `x₀ : K` for any topological semiring `A` with continuous star,
  which is closed when `A` is `T₁` (`ContinuousMap.isClosed_evalKerSubalgebra`) and has the same
  carrier as Mathlib's vanishing-ideal construction `ContinuousMap.idealOfSet A ({x₀}ᶜ)` when `A` is
  unital (`ContinuousMap.coe_evalKerSubalgebra_eq_idealOfSet`).
-/

public section

namespace WeakDual.CharacterSpace

/-- `WeakDual.CharacterSpace.homeoEval` evaluates a continuous function at the given point. -/
@[simp]
theorem homeoEval_apply {X 𝕜 : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [RCLike 𝕜] (x : X) (f : C(X, 𝕜)) :
    homeoEval X 𝕜 x f = f x := (rfl)

end WeakDual.CharacterSpace

namespace ContinuousMap

variable {K S A : Type*} [TopologicalSpace K]

variable (S A) in
/-- The evaluation-kernel nonunital star subalgebra `{F ∈ C(K, A) : F x₀ = 0}` of continuous
functions vanishing at a point `x₀ : K`. -/
def evalKerSubalgebra [CommSemiring S] [NonUnitalNonAssocSemiring A] [TopologicalSpace A]
    [IsTopologicalSemiring A] [StarAddMonoid A] [ContinuousStar A] [Module S A]
    [ContinuousConstSMul S A] (x₀ : K) :
    NonUnitalStarSubalgebra S C(K, A) where
  carrier := {F : C(K, A) | F x₀ = 0}
  mul_mem' {f g} hf hg := by simp_all
  add_mem' {f g} hf hg := by simp_all
  zero_mem' := rfl
  smul_mem' c {f} hf := by simp_all
  star_mem' {f} hf := by simp_all

/-- Membership in `evalKerSubalgebra S A x₀` means vanishing at `x₀`. -/
@[simp]
theorem mem_evalKerSubalgebra [CommSemiring S] [NonUnitalNonAssocSemiring A] [TopologicalSpace A]
    [IsTopologicalSemiring A] [StarAddMonoid A] [ContinuousStar A] [Module S A]
    [ContinuousConstSMul S A] {x₀ : K} {F : C(K, A)} :
    F ∈ evalKerSubalgebra S A x₀ ↔ F x₀ = 0 :=
  Iff.rfl

/-- The underlying set of `evalKerSubalgebra S A x₀` is `{F : C(K, A) | F x₀ = 0}`. -/
@[simp, norm_cast]
theorem coe_evalKerSubalgebra [CommSemiring S] [NonUnitalNonAssocSemiring A] [TopologicalSpace A]
    [IsTopologicalSemiring A] [StarAddMonoid A] [ContinuousStar A] [Module S A]
    [ContinuousConstSMul S A] (x₀ : K) :
    (evalKerSubalgebra S A x₀ : Set C(K, A)) = {F : C(K, A) | F x₀ = 0} := (rfl)

/-- For `T₁` codomain `A`, `evalKerSubalgebra S A x₀` is closed in `C(K, A)`. -/
theorem isClosed_evalKerSubalgebra [CommSemiring S] [NonUnitalNonAssocSemiring A]
    [TopologicalSpace A] [T1Space A] [IsTopologicalSemiring A] [StarAddMonoid A] [ContinuousStar A]
    [Module S A] [ContinuousConstSMul S A] (x₀ : K) :
    IsClosed (evalKerSubalgebra S A x₀ : Set C(K, A)) :=
  isClosed_singleton.preimage (continuous_eval_const x₀)

/-- When `A` is unital, `evalKerSubalgebra S A x₀` has the same carrier as Mathlib's vanishing-ideal
construction `ContinuousMap.idealOfSet A ({x₀}ᶜ)`. -/
theorem coe_evalKerSubalgebra_eq_idealOfSet [CommSemiring S] [Semiring A] [TopologicalSpace A]
    [IsTopologicalSemiring A] [StarAddMonoid A] [ContinuousStar A] [Module S A]
    [ContinuousConstSMul S A] (x₀ : K) :
    (evalKerSubalgebra S A x₀ : Set C(K, A)) = (idealOfSet A ({x₀}ᶜ : Set K) : Set C(K, A)) := by
  ext F
  simp

end ContinuousMap
