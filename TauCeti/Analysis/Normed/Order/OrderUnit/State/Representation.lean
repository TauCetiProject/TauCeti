/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Order.OrderUnit.State.Basic
import Mathlib.Analysis.Convex.Cone.Dual
import TauCeti.Analysis.Normed.Order.OrderUnit.State.Extension

/-!
# Order separation, norm detection, and evaluation representation by states

This file proves order separation and norm detection by states on an order-unit space `(E, e)`,
and constructs the canonical unital isometric order embedding `E →ₗᵢ[ℝ] C(stateSpace e, ℝ)`.

## Main definitions and results

* `TauCeti.IsOrderUnitNorm.nonneg_iff_forall_stateSpace`,
  `TauCeti.IsOrderUnitNorm.le_iff_forall_stateSpace`,
  `TauCeti.IsOrderUnitNorm.eq_of_forall_stateSpace`: states detect the partial order and separate
  points.
* `TauCeti.IsOrderUnitNorm.exists_mem_stateSpace_abs_apply_eq_norm`,
  `TauCeti.IsOrderUnitNorm.norm_eq_iSup_abs_state_apply`,
  `TauCeti.IsOrderUnitNorm.nnNorm_eq_iSup_nnNorm_state_apply`: norm attainment and detection by
  states.
* `TauCeti.OrderUnit.evalContinuousMap`, `TauCeti.OrderUnit.evalContinuousMap_apply_convexCombo`,
  `TauCeti.IsOrderUnitNorm.evalContinuousMap_le_iff`,
  `TauCeti.IsOrderUnitNorm.norm_evalContinuousMap`,
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

/-! ### Order separation and norm detection -/

section Separation

open OrderUnit

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e)

include he

/-- **Order separation by states.** An element of an order-unit space is nonnegative iff every
state evaluates nonnegatively on it. -/
theorem IsOrderUnitNorm.nonneg_iff_forall_stateSpace {a : E} :
    0 ≤ a ↔ ∀ φ ∈ stateSpace e, 0 ≤ φ a := by
  refine ⟨fun ha φ hφ => map_nonneg_of_mem_stateSpace hφ ha, fun h => ?_⟩
  by_contra ha
  let : PosSMulMono ℝ E := he.posSMulMono
  have : OrderClosedTopology E := he.orderClosedTopology
  obtain ⟨f, hf_pos, hfa⟩ :=
    (ProperCone.positive ℝ E).hyperplane_separation_point (x₀ := a) ha
  have hf_mono : Monotone f := (monotone_iff_map_nonneg f).mpr fun x hx =>
    hf_pos x (ProperCone.mem_positive.mpr hx)
  have hfnorm : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg f) fun h0 => by
    have hle := f.le_opNorm a
    rw [← h0, zero_mul, Real.norm_eq_abs] at hle
    linarith [neg_le_abs (f a)]
  have hfe : 0 < f e := by
    rwa [← he.opNorm_eq_apply_unit_of_monotone f hf_mono]
  let φ : WeakDual ℝ E := StrongDual.toWeakDual ((f e)⁻¹ • f)
  have hφmem : φ ∈ stateSpace e := by
    refine mem_stateSpace_iff.mpr ⟨fun x y hxy => ?_, ?_⟩
    · simp only [φ, StrongDual.toWeakDual_apply, smul_apply, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (hf_mono hxy) (inv_nonneg.mpr hfe.le)
    · simp only [φ, StrongDual.toWeakDual_apply, smul_apply, smul_eq_mul]
      exact inv_mul_cancel₀ hfe.ne'
  have hφa : φ a < 0 := mul_neg_of_pos_of_neg (inv_pos.mpr hfe) hfa
  exact not_lt_of_ge (h φ hφmem) hφa

/-- States detect the partial order: `a ≤ b` iff `φ a ≤ φ b` for every state `φ`. -/
theorem IsOrderUnitNorm.le_iff_forall_stateSpace {a b : E} :
    a ≤ b ↔ ∀ φ ∈ stateSpace e, φ a ≤ φ b := by
  rw [← sub_nonneg, he.nonneg_iff_forall_stateSpace]
  simp only [map_sub, sub_nonneg]

/-- States separate points of an order-unit space. -/
theorem IsOrderUnitNorm.eq_of_forall_stateSpace {a b : E}
    (h : ∀ φ ∈ stateSpace e, φ a = φ b) : a = b :=
  le_antisymm
    (he.le_iff_forall_stateSpace.mpr fun φ hφ => (h φ hφ).le)
    (he.le_iff_forall_stateSpace.mpr fun φ hφ => (h φ hφ).ge)

/-- **Norm attainment by states.** For every element `a` of an order-unit space, there exists a
state `φ` attaining `|φ a| = ‖a‖`. -/
theorem IsOrderUnitNorm.exists_mem_stateSpace_abs_apply_eq_norm (a : E) :
    ∃ φ ∈ stateSpace e, |φ a| = ‖a‖ := by
  have hcont : Continuous (fun φ : WeakDual ℝ E => |φ a|) :=
    continuous_abs.comp (eval_continuous a)
  obtain ⟨φ₀, hφ₀, hmax⟩ := he.isCompact_stateSpace.exists_isMaxOn he.stateSpace_nonempty
    hcont.continuousOn
  refine ⟨φ₀, hφ₀, le_antisymm (he.abs_apply_le_norm_of_mem_stateSpace hφ₀ a) ?_⟩
  refine (he.norm_le_iff (abs_nonneg _)).mpr ⟨?_, ?_⟩
  · refine he.le_iff_forall_stateSpace.mpr fun φ hφ => ?_
    have hle : |φ a| ≤ |φ₀ a| := hmax hφ
    rw [map_neg, map_smul, smul_eq_mul, map_unit_of_mem_stateSpace hφ, mul_one]
    exact (abs_le.mp hle).1
  · refine he.le_iff_forall_stateSpace.mpr fun φ hφ => ?_
    have hle : |φ a| ≤ |φ₀ a| := hmax hφ
    rw [map_smul, smul_eq_mul, map_unit_of_mem_stateSpace hφ, mul_one]
    exact (abs_le.mp hle).2

/-- **Norm detection by states** (in `ℝ`): `‖a‖ = ⨆ φ : stateSpace e, |φ.val a|`. -/
theorem IsOrderUnitNorm.norm_eq_iSup_abs_state_apply (a : E) :
    ‖a‖ = ⨆ φ : stateSpace e, |φ.val a| := by
  obtain ⟨φ₀, hφ₀, hval⟩ := he.exists_mem_stateSpace_abs_apply_eq_norm a
  have hmax : IsMaxOn (fun φ : WeakDual ℝ E => |φ a|) (stateSpace e) φ₀ := fun φ hφ =>
    (he.abs_apply_le_norm_of_mem_stateSpace hφ a).trans_eq hval.symm
  exact ((hmax.iSup_eq hφ₀).trans hval).symm

end Separation

/-! ### The evaluation embedding -/

section EvalEmbedding

namespace OrderUnit

/-- The canonical evaluation map `E →ₗ[ℝ] C(stateSpace e, ℝ)`, sending `a` to `φ ↦ φ a`. -/
noncomputable def evalContinuousMap {E : Type*} [AddCommMonoid E] [Module ℝ E]
    [TopologicalSpace E] [Preorder E] (e : E) : E →ₗ[ℝ] C(stateSpace e, ℝ) where
  toFun a := ⟨fun φ => φ.val a, (eval_continuous a).comp continuous_subtypeVal⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- Evaluating `evalContinuousMap e a` at a state `φ` gives `φ.val a`. -/
@[simp]
theorem evalContinuousMap_apply {E : Type*} [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E]
    [Preorder E] (e : E) (a : E) (φ : stateSpace e) :
    evalContinuousMap e a φ = φ.val a :=
  (rfl)

/-- The evaluation embedding sends the order unit `e` to the constant function `1`. -/
@[simp]
theorem evalContinuousMap_unit {E : Type*} [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E]
    [Preorder E] (e : E) : evalContinuousMap e e = 1 := by
  ext φ
  exact map_unit_of_mem_stateSpace φ.property

/-- Evaluating `evalContinuousMap e a` preserves convex combinations of states. -/
theorem evalContinuousMap_apply_convexCombo {E : Type*} [AddCommMonoid E] [Module ℝ E]
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
  rw [ContinuousMap.le_def, he.le_iff_forall_stateSpace]
  simp

/-- The evaluation map into `C(stateSpace e, ℝ)` is isometric. -/
theorem IsOrderUnitNorm.norm_evalContinuousMap (a : E) :
    let : CompactSpace (stateSpace e) := he.compactSpace_stateSpace
    ‖evalContinuousMap e a‖ = ‖a‖ := by
  dsimp only
  let : CompactSpace (stateSpace e) := he.compactSpace_stateSpace
  rw [ContinuousMap.norm_eq_iSup_norm, he.norm_eq_iSup_abs_state_apply a]
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
    letI : CompactSpace (stateSpace e) := he.compactSpace_stateSpace
    E →ₗᵢ[ℝ] C(stateSpace e, ℝ) :=
  letI : CompactSpace (stateSpace e) := he.compactSpace_stateSpace
  { toLinearMap := evalContinuousMap e
    norm_map' := he.norm_evalContinuousMap }

/-- The underlying linear map of `evalLinearIsometry` is `evalContinuousMap e`. -/
@[simp]
theorem IsOrderUnitNorm.evalLinearIsometry_toLinearMap :
    let : CompactSpace (stateSpace e) := he.compactSpace_stateSpace
    he.evalLinearIsometry.toLinearMap = evalContinuousMap e := by
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
