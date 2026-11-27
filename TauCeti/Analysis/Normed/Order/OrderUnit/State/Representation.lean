/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Order.OrderUnit.State.Basic

/-!
# Norm attainment and evaluation representation by states

This file proves norm attainment by states on an order-unit space `(E, e)`, and constructs the
canonical unital isometric order embedding `E →ₗᵢ[ℝ] C(stateSpace e, ℝ)`.

## Main definitions and results

* `TauCeti.IsOrderUnitNorm.exists_mem_stateSpace_abs_apply_eq_norm`: norm attainment by states.
* `TauCeti.OrderUnit.evalContinuousMap`, `TauCeti.OrderUnit.evalContinuousMap_apply_convexCombo`,
  `TauCeti.IsOrderUnitNorm.evalContinuousMap_le_iff`,
  `TauCeti.IsOrderUnitNorm.norm_evalContinuousMap`,
  `TauCeti.IsOrderUnitNorm.nnNorm_eq_iSup_nnNorm_state_apply`,
  `TauCeti.IsOrderUnitNorm.evalLinearIsometry`,
  `TauCeti.IsOrderUnitNorm.evalLinearIsometry_le_iff`: the unital isometric order embedding
  `E →ₗᵢ[ℝ] C(stateSpace e, ℝ)`.

## References

* Marc A. Rieffel, *Metrics on state spaces*, Doc. Math. 4 (1999), 559–600, Section 1.
* Richard V. Kadison, *A representation theory for commutative topological algebra*,
  Mem. Amer. Math. Soc. 7 (1951).
-/

public section

open Set WeakDual
open scoped NNReal

namespace TauCeti

/-! ### Norm attainment by states -/

section Attainment

open OrderUnit

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e)

include he

/-- **Norm attainment by states.** For every element `a` of an order-unit space, there exists a
state `φ` attaining `|φ a| = ‖a‖`. -/
theorem IsOrderUnitNorm.exists_mem_stateSpace_abs_apply_eq_norm (a : E) :
    ∃ φ ∈ stateSpace e, |φ a| = ‖a‖ := by
  have hcont : Continuous (fun φ : WeakDual ℝ E => |φ a|) :=
    continuous_abs.comp (eval_continuous a)
  obtain ⟨φ₀, hφ₀, hmax⟩ := he.isCompact_stateSpace.exists_isMaxOn he.stateSpace_nonempty
    hcont.continuousOn
  refine ⟨φ₀, hφ₀, le_antisymm (he.abs_apply_le_of_mem_stateSpace hφ₀ a) ?_⟩
  exact (he.norm_le_iff_forall_mem_stateSpace (abs_nonneg _)).2 fun φ hφ => hmax hφ

end Attainment

/-! ### The evaluation embedding -/

section EvalEmbedding

namespace OrderUnit

/-- The canonical evaluation map `E →ₗ[ℝ] C(stateSpace e, ℝ)`, sending `a` to `φ ↦ φ a`. -/
noncomputable def evalContinuousMap {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [Preorder E] (e : E) : E →ₗ[ℝ] C(stateSpace e, ℝ) where
  toFun a := ⟨fun φ => φ.val a, (eval_continuous a).comp continuous_subtypeVal⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- Evaluating `evalContinuousMap e a` at a state `φ` gives `φ.val a`. -/
@[simp]
theorem evalContinuousMap_apply {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [Preorder E] (e : E) (a : E) (φ : stateSpace e) :
    evalContinuousMap e a φ = φ.val a :=
  (rfl)

/-- The evaluation embedding sends the order unit `e` to the constant function `1`. -/
@[simp]
theorem evalContinuousMap_unit {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [Preorder E] (e : E) : evalContinuousMap e e = 1 := by
  ext φ
  exact apply_eq_one_of_mem_stateSpace φ.property

/-- Evaluating `evalContinuousMap e a` preserves convex combinations of states. -/
theorem evalContinuousMap_apply_convexCombo {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [Preorder E] (e : E) (a : E) {φ ψ : stateSpace e} {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    evalContinuousMap e a
        ⟨s • φ.val + t • ψ.val, convex_stateSpace φ.property ψ.property hs ht hst⟩ =
      s * evalContinuousMap e a φ + t * evalContinuousMap e a ψ := by
  simp

end OrderUnit

open OrderUnit

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e)

include he

/-- The evaluation map preserves and reflects the partial order. -/
theorem IsOrderUnitNorm.evalContinuousMap_le_iff {a b : E} :
    evalContinuousMap e a ≤ evalContinuousMap e b ↔ a ≤ b := by
  rw [ContinuousMap.le_def, he.le_iff_forall_mem_stateSpace]
  simp

/-- The evaluation map into `C(stateSpace e, ℝ)` is isometric. -/
theorem IsOrderUnitNorm.norm_evalContinuousMap (a : E) :
    @norm C(stateSpace e, ℝ)
      (@ContinuousMap.instNorm _ _ _ he.compactSpace_stateSpace _)
      (evalContinuousMap e a) = ‖a‖ := by
  let : CompactSpace (stateSpace e) := he.compactSpace_stateSpace
  rw [ContinuousMap.norm_eq_iSup_norm, he.norm_eq_iSup_states a]
  simp [Real.norm_eq_abs]

/-- **Norm detection by states** (in `ℝ≥0`): `‖a‖₊ = ⨆ φ : stateSpace e, ‖φ.val a‖₊`. -/
theorem IsOrderUnitNorm.nnNorm_eq_iSup_nnNorm_state_apply (a : E) :
    ‖a‖₊ = ⨆ φ : stateSpace e, ‖φ.val a‖₊ := by
  let : CompactSpace (stateSpace e) := he.compactSpace_stateSpace
  have h : ‖a‖₊ = ‖evalContinuousMap e a‖₊ := NNReal.eq (he.norm_evalContinuousMap a).symm
  rw [h, ContinuousMap.nnNorm_eq_iSup_nnNorm]
  simp [evalContinuousMap_apply]

/-- The canonical unital isometric order embedding `E →ₗᵢ[ℝ] C(stateSpace e, ℝ)`. -/
noncomputable def IsOrderUnitNorm.evalLinearIsometry :
    @LinearIsometry ℝ ℝ _ _ (RingHom.id ℝ) E C(stateSpace e, ℝ) _
      (@ContinuousMap.instSeminormedAddCommGroup _ _ _ he.compactSpace_stateSpace _) _ _ :=
  letI : CompactSpace (stateSpace e) := he.compactSpace_stateSpace
  { toLinearMap := evalContinuousMap e
    norm_map' := he.norm_evalContinuousMap }

/-- The underlying linear map of `evalLinearIsometry` is `evalContinuousMap e`. -/
@[simp]
theorem IsOrderUnitNorm.evalLinearIsometry_toLinearMap :
    @LinearIsometry.toLinearMap ℝ ℝ _ _ (RingHom.id ℝ) E C(stateSpace e, ℝ) _
      (@ContinuousMap.instSeminormedAddCommGroup _ _ _ he.compactSpace_stateSpace _) _ _
      he.evalLinearIsometry = evalContinuousMap e := by
  rfl

/-- Evaluating `evalLinearIsometry` agrees with `evalContinuousMap`. -/
@[simp]
theorem IsOrderUnitNorm.evalLinearIsometry_apply
    (a : E) (φ : stateSpace e) : he.evalLinearIsometry a φ = φ.val a := by
  rfl

/-- The evaluation isometry sends the order unit `e` to `1`. -/
@[simp]
theorem IsOrderUnitNorm.evalLinearIsometry_unit :
    he.evalLinearIsometry e = 1 := by
  simp [evalLinearIsometry]

/-- The evaluation isometry preserves and reflects the partial order. -/
@[simp]
theorem IsOrderUnitNorm.evalLinearIsometry_le_iff {a b : E} :
    he.evalLinearIsometry a ≤ he.evalLinearIsometry b ↔ a ≤ b := by
  simpa [evalLinearIsometry] using he.evalContinuousMap_le_iff

end EvalEmbedding

end TauCeti
