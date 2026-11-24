/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.WeakDual
public import TauCeti.Analysis.Normed.Order.OrderUnit.PositiveLinearMap
public import TauCeti.Topology.Algebra.Module.Spaces.WeakDual

/-!
# State spaces of order-unit spaces

This file defines the state space of an order-unit space and develops its basic topological and
functorial properties: convexity, weak-star closedness, weak-star compactness, characterization via
positive linear maps or operator norm, and pullback along unital positive continuous linear maps.

A **state** of an order-unit space `(E, e)` is a monotone continuous real-linear functional `φ`
with `φ e = 1`. The **state space** `TauCeti.OrderUnit.stateSpace e` is defined as a subset of the
weak-star dual `WeakDual ℝ E`, carrying the weak-star subspace topology.

Further results are in sibling modules:

* `TauCeti.Analysis.Normed.Order.OrderUnit.State.Extension`: norm-preserving state extension and
  nonemptiness of the state space.
* `TauCeti.Analysis.Normed.Order.OrderUnit.State.Representation`: order separation, norm detection,
  and the unital isometric order embedding into `C(stateSpace e, ℝ)`.
* `TauCeti.Analysis.Normed.Order.OrderUnit.State.Completion`: unique weak-star homeomorphic
  extension of states to the norm completion.

## Main definitions and results

* `TauCeti.OrderUnit.stateSpace`: the state space `{φ : WeakDual ℝ E | Monotone φ ∧ φ e = 1}`.
* `TauCeti.OrderUnit.convex_stateSpace`, `TauCeti.OrderUnit.isClosed_stateSpace`,
  `TauCeti.IsOrderUnitNorm.isCompact_stateSpace`,
  `TauCeti.IsOrderUnitNorm.compactSpace_stateSpace`: convexity, weak-star closedness, and
  weak-star compactness (by Banach–Alaoglu).
* `ContinuousLinearMap.mapsTo_pullbackFunctional_stateSpace`: pullback along unital positive
  continuous linear maps (via `ContinuousLinearMap.pullbackFunctional`).

## References

* Marc A. Rieffel, *Metrics on state spaces*, Doc. Math. 4 (1999), 559–600, Section 1.
* Richard V. Kadison, *A representation theory for commutative topological algebra*,
  Mem. Amer. Math. Soc. 7 (1951).
-/

public section

open Set Metric WeakDual
open scoped Topology

namespace TauCeti

/-! ### The state space -/

section StateSpace

namespace OrderUnit

/-- The **state space** of an order-unit space `(E, e)`: the set of monotone functionals in
`WeakDual ℝ E` normalized by `φ e = 1`, equipped with the inherited weak-star topology. -/
def stateSpace {E : Type*} [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E] [Preorder E]
    (e : E) : Set (WeakDual ℝ E) :=
  {φ | Monotone φ ∧ φ e = 1}

section GeneralStateSpace

variable {E : Type*} [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E] [Preorder E]
  {e : E} {φ : WeakDual ℝ E}

/-- Membership in `stateSpace e` unfolds to monotonicity and `φ e = 1`. -/
theorem mem_stateSpace_iff : φ ∈ stateSpace e ↔ Monotone φ ∧ φ e = 1 :=
  Iff.rfl

/-- Every state is monotone. -/
theorem monotone_of_mem_stateSpace (hφ : φ ∈ stateSpace e) : Monotone φ :=
  hφ.1

/-- Every state takes the value `1` at the order unit `e`. -/
theorem map_unit_of_mem_stateSpace (hφ : φ ∈ stateSpace e) : φ e = 1 :=
  hφ.2

/-- Every state is nonnegative on nonnegative elements. -/
theorem map_nonneg_of_mem_stateSpace (hφ : φ ∈ stateSpace e) {a : E} (ha : 0 ≤ a) :
    0 ≤ φ a := by
  simpa using hφ.1 ha

/-- The state space is convex. -/
theorem convex_stateSpace : Convex ℝ (stateSpace e) := by
  intro φ hφ ψ hψ s t hs ht hst
  refine ⟨fun a b hab => ?_, ?_⟩
  · simp only [add_apply, smul_apply, smul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (hφ.1 hab) hs)
      (mul_le_mul_of_nonneg_left (hψ.1 hab) ht)
  · simp [hφ.2, hψ.2, hst]

/-- The state space is weak-star closed. -/
theorem isClosed_stateSpace : IsClosed (stateSpace e) :=
  (isClosed_monotone.preimage WeakDual.coeFn_continuous).inter
    (isClosed_eq (eval_continuous e) continuous_const)

end GeneralStateSpace

section PositiveContinuousStateSpace

variable {E : Type*} [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E] [PartialOrder E]

/-- A positive continuous real-linear functional belongs to `stateSpace e` iff `ω e = 1`. -/
@[simp]
theorem _root_.PositiveContinuousLinearMap.toWeakDual_mem_stateSpace_iff_apply_eq_one
    (ω : E →P[ℝ] ℝ) (e : E) :
    StrongDual.toWeakDual (ω : E →L[ℝ] ℝ) ∈ stateSpace e ↔ ω e = 1 := by
  simp only [mem_stateSpace_iff, StrongDual.toWeakDual_apply,
    PositiveContinuousLinearMap.coe_toContinuousLinearMap, and_iff_right_iff_imp]
  exact fun _ _ _ hab => ω.mono hab

/-- The canonical bijection between `stateSpace e` and normalized positive continuous linear
functionals `{ω : E →P[ℝ] ℝ // ω e = 1}`. -/
noncomputable def stateSpaceEquivPositiveContinuousLinearMap (e : E) :
    stateSpace e ≃ {ω : E →P[ℝ] ℝ // ω e = 1} where
  toFun φ := ⟨⟨⟨(toStrongDual φ.val).toLinearMap, φ.property.1⟩,
    (toStrongDual φ.val).continuous⟩, φ.property.2⟩
  invFun ω := ⟨StrongDual.toWeakDual (ω.val : E →L[ℝ] ℝ),
    (ω.val.toWeakDual_mem_stateSpace_iff_apply_eq_one e).mpr ω.property⟩
  left_inv _ := Subtype.ext (DFunLike.ext _ _ fun _ => rfl)
  right_inv _ := Subtype.ext (DFunLike.ext _ _ fun _ => rfl)

/-- Evaluating `stateSpaceEquivPositiveContinuousLinearMap` at `a` gives `φ.val a`. -/
@[simp]
theorem stateSpaceEquivPositiveContinuousLinearMap_apply (e : E) (φ : stateSpace e) (a : E) :
    (stateSpaceEquivPositiveContinuousLinearMap e φ).val a = φ.val a :=
  (rfl)

/-- Evaluating the inverse of `stateSpaceEquivPositiveContinuousLinearMap` at `a` gives
`ω.val a`. -/
@[simp]
theorem stateSpaceEquivPositiveContinuousLinearMap_symm_apply (e : E)
    (ω : {ω : E →P[ℝ] ℝ // ω e = 1}) (a : E) :
    ((stateSpaceEquivPositiveContinuousLinearMap e).symm ω).val a = ω.val a :=
  (rfl)

end PositiveContinuousStateSpace

section OrderedGroupStateSpace

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E} {φ : WeakDual ℝ E}

/-- On an ordered additive group, membership in `stateSpace e` is equivalent to nonnegativity on
nonnegative elements together with `φ e = 1`. -/
theorem mem_stateSpace_iff_map_nonneg :
    φ ∈ stateSpace e ↔ (∀ a : E, 0 ≤ a → 0 ≤ φ a) ∧ φ e = 1 := by
  refine and_congr_left fun _ => ?_
  simpa [Monotone, toStrongDual_apply] using monotone_iff_map_nonneg (toStrongDual φ)

end OrderedGroupStateSpace

end OrderUnit

section NormedStateSpace

open OrderUnit

/-- States correspond to normalized positive linear functionals `E →ₚ[ℝ] ℝ`, via automatic
continuity. -/
theorem IsOrderUnitNorm.mem_stateSpace_iff_exists_positiveLinearMap {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E] {e : E}
    (he : IsOrderUnitNorm e) {φ : WeakDual ℝ E} :
    φ ∈ stateSpace e ↔ ∃ ω : E →ₚ[ℝ] ℝ, ω e = 1 ∧
      StrongDual.toWeakDual (he.toPositiveContinuousLinearMap isOrderUnitNorm_real_one ω :
        E →L[ℝ] ℝ) = φ := by
  refine ⟨fun hφ => ?_, fun ⟨ω, hω, h⟩ =>
    h ▸ ((he.toPositiveContinuousLinearMap isOrderUnitNorm_real_one
      ω).toWeakDual_mem_stateSpace_iff_apply_eq_one e).mpr (by simpa using hω)⟩
  let ω : E →ₚ[ℝ] ℝ := { toLinearMap := (toStrongDual φ).toLinearMap, monotone' := hφ.1 }
  have hω_apply (a : E) : ω a = toStrongDual φ a := rfl
  exact ⟨ω, hφ.2, DFunLike.ext _ _ fun a => by simp [hω_apply]⟩

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  {e : E} (he : IsOrderUnitNorm e)

include he

/-- Every state has operator norm `1`. -/
theorem IsOrderUnitNorm.norm_toStrongDual_of_mem_stateSpace {φ : WeakDual ℝ E}
    (hφ : φ ∈ stateSpace e) : ‖toStrongDual φ‖ = 1 :=
  (he.opNorm_eq_apply_unit_of_monotone (toStrongDual φ) hφ.1).trans hφ.2

/-- Every state satisfies `|φ a| ≤ ‖a‖`. -/
theorem IsOrderUnitNorm.abs_apply_le_norm_of_mem_stateSpace {φ : WeakDual ℝ E}
    (hφ : φ ∈ stateSpace e) (a : E) : |φ a| ≤ ‖a‖ := by
  simpa [Real.norm_eq_abs, he.norm_toStrongDual_of_mem_stateSpace hφ] using
    (toStrongDual φ).le_opNorm a

/-- The state space is contained in the weak-star closed unit ball. -/
theorem IsOrderUnitNorm.stateSpace_subset_closedBall :
    stateSpace e ⊆ toStrongDual ⁻¹' closedBall 0 1 := by
  intro φ hφ
  simp [he.norm_toStrongDual_of_mem_stateSpace hφ]

/-- **Weak-star compactness of the state space.** By the Banach–Alaoglu theorem, `stateSpace e`
is compact in the weak-star topology. -/
theorem IsOrderUnitNorm.isCompact_stateSpace : IsCompact (stateSpace e) :=
  (WeakDual.isCompact_closedBall (𝕜 := ℝ) (E := E) 0 1).of_isClosed_subset
    isClosed_stateSpace he.stateSpace_subset_closedBall

/-- `CompactSpace` witness for `stateSpace e` as a subtype of `WeakDual ℝ E`. -/
theorem IsOrderUnitNorm.compactSpace_stateSpace : CompactSpace (stateSpace e) :=
  isCompact_iff_compactSpace.mp he.isCompact_stateSpace

variable [IsOrderedAddMonoid E]

/-- A functional in `WeakDual ℝ E` is a state iff its strong norm is `1` and `φ e = 1`. -/
theorem IsOrderUnitNorm.mem_stateSpace_iff_norm_eq_one_and_map_unit {φ : WeakDual ℝ E} :
    φ ∈ stateSpace e ↔ ‖toStrongDual φ‖ = 1 ∧ φ e = 1 := by
  rw [mem_stateSpace_iff]
  exact and_congr_left fun h => by
    simpa [h] using (show Monotone φ ↔ ‖toStrongDual φ‖ = φ e from
      he.monotone_iff_opNorm_eq_apply_unit (toStrongDual φ))

end NormedStateSpace

end StateSpace

/-! ### Pullback -/

section Functoriality

open OrderUnit

/-- Composing a state with a unital positive continuous linear map yields a state. -/
theorem _root_.ContinuousLinearMap.mapsTo_pullbackFunctional_stateSpace {E F : Type*}
    [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E] [Preorder E]
    [AddCommMonoid F] [Module ℝ F] [TopologicalSpace F] [Preorder F]
    {e : E} {f : F} (T : E →L[ℝ] F) (hT : Monotone T) (hTe : T e = f) :
    MapsTo T.pullbackFunctional (stateSpace f) (stateSpace e) := by
  intro φ hφ
  refine ⟨fun _ _ hab => ?_, ?_⟩
  · simpa [ContinuousLinearMap.pullbackFunctional_apply] using hφ.1 (hT hab)
  · simpa [hTe] using hφ.2

end Functoriality

namespace OrderUnit

/-! ### Concrete example -/

/-- The only state of `(ℝ, 1)` is the identity functional. -/
theorem stateSpace_one_real :
    stateSpace (1 : ℝ) = {StrongDual.toWeakDual (ContinuousLinearMap.id ℝ ℝ)} := by
  ext φ
  rw [mem_stateSpace_iff, mem_singleton_iff]
  refine ⟨fun ⟨_, h1⟩ => DFunLike.ext _ _ fun r => ?_, ?_⟩
  · simpa [h1] using (toStrongDual φ).map_smul r (1 : ℝ)
  · rintro rfl
    exact ⟨fun _ _ h => h, rfl⟩

end OrderUnit

end TauCeti
