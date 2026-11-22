/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
public import TauCeti.Analysis.CStarAlgebra.State.Space
public import TauCeti.Analysis.LocallyConvex.WeakDual.SelfAdjoint
public import TauCeti.Analysis.Normed.Order.OrderUnit.Basic
public import TauCeti.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Complex.Module
import TauCeti.Analysis.LocallyConvex.WeakDual.Basic
import TauCeti.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.Normed.Order.PositiveLinearMap

/-!
# Positive maps and state spaces of order-unit spaces

This file develops the theory of positive linear maps and states on order-unit spaces, and proves
weak-star compactness of the state space, order separation, norm detection by states, the unital
isometric order embedding into continuous functions on the state space, and the correspondence with
C⋆-algebra states.

Every positive linear map `T : E → F` between order-unit spaces is automatically Lipschitz with
constant `‖T e‖`, and when `T` is continuous its operator norm equals `‖T e‖`; in particular,
unital positive linear maps are contractive (`‖T‖ = 1`). For real-valued continuous linear
functionals, positivity is equivalent to `‖φ‖ = φ e`.

A **state** of an order-unit space `(E, e)` is a monotone continuous real-linear functional `φ`
with `φ e = 1`. The **state space** `TauCeti.OrderUnit.stateSpace e` is defined as a subset of the
weak-star dual `WeakDual ℝ E`, carrying the weak-star subspace topology.

## Main definitions and results

* `TauCeti.OrderUnit.IsOrderUnitNorm.norm_map_le`, `continuous_of_positive`,
  `opNorm_eq_norm_apply_unit`, `opNorm_eq_one_of_monotone_of_map_unit`: automatic boundedness and
  operator-norm formulas for positive linear maps between order-unit spaces.
* `TauCeti.OrderUnit.IsOrderUnitNorm.monotone_iff_opNorm_eq_apply_unit`: a continuous real-linear
  functional is monotone iff `‖φ‖ = φ e`.
* `TauCeti.OrderUnit.stateSpace`: the state space `{φ : WeakDual ℝ E | Monotone φ ∧ φ e = 1}`.
* `TauCeti.OrderUnit.IsOrderUnitNorm.stateSpace_nonempty`, `convex_stateSpace`,
  `isClosed_stateSpace`, `isCompact_stateSpace`: nonemptiness (by Hahn–Banach), convexity,
  weak-star closedness, and weak-star compactness (by Banach–Alaoglu).
* `ContinuousLinearMap.mapsTo_pullbackFunctional_stateSpace`,
  `TauCeti.OrderUnit.IsOrderUnitNorm.surjOn_pullbackFunctional_subtypeL`,
  `TauCeti.OrderUnit.IsOrderUnitNorm.existsUnique_state_extension_completion`,
  `TauCeti.OrderUnit.IsOrderUnitNorm.completionStateSpaceHomeomorph`: pullback along unital positive
  maps (via `ContinuousLinearMap.pullbackFunctional`), extension from unital subspaces, and unique
  weak-star homeomorphic extension to the norm completion.
* `TauCeti.OrderUnit.IsOrderUnitNorm.nonneg_iff_forall_stateSpace`,
  `exists_mem_stateSpace_abs_apply_eq_norm`, `norm_eq_iSup_states`, `nnNorm_eq_iSup_states`,
  `evalContinuousMap`, `IsOrderUnitNorm.evalLinearIsometry`: order separation, norm detection by
  states, and the isometric unital order embedding `E → C(stateSpace e, ℝ)`.
* `TauCeti.OrderUnit.cstarStateSpaceHomeomorph`,
  `TauCeti.OrderUnit.cstarPositiveLinearMapEquivStateSpace`: weak-star homeomorphic correspondence
  between states of a unital C⋆-algebra `A` and states of `selfAdjoint A`, induced by
  `WeakDual.restrictToSelfAdjoint` and `WeakDual.extendFromSelfAdjoint`.

## References

* Marc A. Rieffel, *Metrics on state spaces*, Doc. Math. 4 (1999), 559–600, Section 1.
* Richard V. Kadison, *A representation theory for commutative topological algebra*,
  Mem. Amer. Math. Soc. 7 (1951).
-/

public section

open Set Metric WeakDual
open scoped NNReal Topology ComplexOrder ComplexStarModule

namespace TauCeti.OrderUnit

/-! ### Positive linear maps between order-unit spaces -/

section PositiveMaps

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F]
  [IsOrderedAddMonoid F] {e : E} {f : F}

/-- A positive linear map between order-unit spaces satisfies `‖T a‖ ≤ ‖T e‖ * ‖a‖`, with no
continuity hypothesis. -/
theorem IsOrderUnitNorm.norm_map_le {M : Type*} [FunLike M E F] [LinearMapClass M ℝ E F]
    [OrderHomClass M E F] (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) (T : M) (a : E) :
    ‖T a‖ ≤ ‖T e‖ * ‖a‖ := by
  have hlo : -(‖a‖ • T e) ≤ T a := by
    have h := OrderHomClass.mono T (he.neg_norm_smul_le a)
    rwa [map_smul, neg_smul] at h
  have hhi : T a ≤ ‖a‖ • T e := by
    have h := OrderHomClass.mono T (he.le_norm_smul a)
    rwa [map_smul] at h
  calc
    ‖T a‖ ≤ ‖‖a‖ • T e‖ := hf.norm_le_norm_of_le hlo hhi
    _ = ‖T e‖ * ‖a‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a), mul_comm]

/-- A positive linear map between order-unit spaces is `‖T e‖`-Lipschitz. -/
theorem IsOrderUnitNorm.lipschitzWith_of_positive {M : Type*} [FunLike M E F]
    [LinearMapClass M ℝ E F] [OrderHomClass M E F] (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (T : M) : LipschitzWith ‖T e‖₊ T := by
  have h := AddMonoidHomClass.lipschitz_of_bound T ‖T e‖ fun a => he.norm_map_le hf T a
  have hnn : ‖T e‖.toNNReal = ‖T e‖₊ := NNReal.eq (by simp)
  rwa [hnn] at h

/-- Every positive linear map between order-unit spaces is automatically continuous. -/
theorem IsOrderUnitNorm.continuous_of_positive {M : Type*} [FunLike M E F]
    [LinearMapClass M ℝ E F] [OrderHomClass M E F] (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (T : M) : Continuous T :=
  (he.lipschitzWith_of_positive hf T).continuous

/-- Upgrade a positive linear map `E →ₚ[ℝ] F` between order-unit spaces to a positive continuous
linear map `E →P[ℝ] F`. -/
def IsOrderUnitNorm.toPositiveContinuousLinearMap (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (T : E →ₚ[ℝ] F) : E →P[ℝ] F :=
  PositiveContinuousLinearMap.mk T (he.continuous_of_positive hf T)

/-- Evaluating `toPositiveContinuousLinearMap` agrees with the underlying positive linear map. -/
@[simp]
theorem IsOrderUnitNorm.toPositiveContinuousLinearMap_apply (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (T : E →ₚ[ℝ] F) (a : E) :
    he.toPositiveContinuousLinearMap hf T a = T a :=
  (rfl)

/-- A monotone continuous linear map between order-unit spaces has operator norm `‖T e‖`. -/
theorem IsOrderUnitNorm.opNorm_eq_norm_apply_unit (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (T : E →L[ℝ] F) (hT : Monotone T) : ‖T‖ = ‖T e‖ := by
  let Tpos : E →ₚ[ℝ] F := { toLinearMap := T.toLinearMap, monotone' := hT }
  refine le_antisymm (T.opNorm_le_bound (norm_nonneg _) fun a => he.norm_map_le hf Tpos a) ?_
  calc
    ‖T e‖ ≤ ‖T‖ * ‖e‖ := T.le_opNorm e
    _ = ‖T‖ := by rw [he.norm_e, mul_one]

/-- A unital monotone continuous linear map between order-unit spaces has operator norm `1`. -/
theorem IsOrderUnitNorm.opNorm_eq_one_of_monotone_of_map_unit (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (T : E →L[ℝ] F) (hT : Monotone T) (hTe : T e = f) : ‖T‖ = 1 := by
  rw [he.opNorm_eq_norm_apply_unit hf T hT, hTe, hf.norm_e]

/-- Every unital positive continuous linear map between order-unit spaces is contractive. -/
theorem IsOrderUnitNorm.norm_apply_le_of_monotone_of_map_unit (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (T : E →L[ℝ] F) (hT : Monotone T) (hTe : T e = f) (a : E) :
    ‖T a‖ ≤ ‖a‖ := by
  simpa [he.opNorm_eq_one_of_monotone_of_map_unit hf T hT hTe] using T.le_opNorm a

end PositiveMaps

/-! ### Positive real-linear functionals -/

section Functionals

/-- A monotone continuous real-linear functional on an order-unit space has operator norm `φ e`. -/
theorem IsOrderUnitNorm.opNorm_eq_apply_unit_of_monotone {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [PartialOrder E] {e : E} (he : IsOrderUnitNorm e)
    (φ : E →L[ℝ] ℝ) (hφ : Monotone φ) : ‖φ‖ = φ e :=
  ContinuousLinearMap.opNorm_eq_apply_of_monotone φ hφ he.le_norm_smul he.norm_e.le

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e)

include he

/-- A continuous real-linear functional on an order-unit space is monotone iff `‖φ‖ = φ e`. -/
theorem IsOrderUnitNorm.monotone_iff_opNorm_eq_apply_unit (φ : E →L[ℝ] ℝ) :
    Monotone φ ↔ ‖φ‖ = φ e := by
  refine ⟨he.opNorm_eq_apply_unit_of_monotone φ, fun h => ?_⟩
  refine (monotone_iff_map_nonneg φ).mpr fun a ha =>
    LinearMap.apply_nonneg_of_abs_apply_le_mul_norm φ.toLinearMap
      (fun g => by simpa [Real.norm_eq_abs, h] using φ.le_opNorm g) (he.nonneg_iff.mp ha)

/-- A continuous real-linear functional is positive and normalized at `e` iff `‖φ‖ = 1` and
`φ e = 1`. -/
theorem IsOrderUnitNorm.monotone_and_apply_unit_eq_one_iff (φ : E →L[ℝ] ℝ) :
    (Monotone φ ∧ φ e = 1) ↔ ‖φ‖ = 1 ∧ φ e = 1 := by
  refine ⟨fun ⟨hmono, h1⟩ => ⟨by rw [he.opNorm_eq_apply_unit_of_monotone φ hmono, h1], h1⟩,
    fun ⟨hnorm, h1⟩ => ⟨(he.monotone_iff_opNorm_eq_apply_unit φ).mpr (by rw [hnorm, h1]), h1⟩⟩

end Functionals

/-! ### The state space -/

section StateSpace

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

end GeneralStateSpace

section PositiveContinuousStateSpace

variable {E : Type*} [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E] [PartialOrder E]

/-- A positive continuous real-linear functional belongs to `stateSpace e` iff `ω e = 1`. -/
@[simp]
theorem toWeakDual_mem_stateSpace_iff (e : E) (ω : E →P[ℝ] ℝ) :
    StrongDual.toWeakDual (ω : E →L[ℝ] ℝ) ∈ stateSpace e ↔ ω e = 1 := by
  simp only [mem_stateSpace_iff, StrongDual.toWeakDual_apply,
    PositiveContinuousLinearMap.coe_toContinuousLinearMap, and_iff_right_iff_imp]
  exact fun _ _ _ hab => ω.mono hab

/-- The canonical bijection between `stateSpace e` and normalized positive continuous linear
functionals `{ω : E →P[ℝ] ℝ // ω e = 1}`. -/
noncomputable def stateSpaceEquivPositiveContinuousLinearMap (e : E) :
    stateSpace e ≃ {ω : E →P[ℝ] ℝ // ω e = 1} where
  toFun φ := ⟨⟨⟨(toStrongDual φ.1).toLinearMap, φ.2.1⟩, (toStrongDual φ.1).continuous⟩, φ.2.2⟩
  invFun ω := ⟨StrongDual.toWeakDual (ω.1 : E →L[ℝ] ℝ),
    (toWeakDual_mem_stateSpace_iff e ω.1).mpr ω.2⟩
  left_inv _ := Subtype.ext (DFunLike.ext _ _ fun _ => rfl)
  right_inv _ := Subtype.ext (DFunLike.ext _ _ fun _ => rfl)

/-- Evaluating `stateSpaceEquivPositiveContinuousLinearMap` at `a` gives `φ.1 a`. -/
@[simp]
theorem stateSpaceEquivPositiveContinuousLinearMap_apply (e : E) (φ : stateSpace e) (a : E) :
    (stateSpaceEquivPositiveContinuousLinearMap e φ).1 a = φ.1 a :=
  (rfl)

/-- Evaluating the inverse of `stateSpaceEquivPositiveContinuousLinearMap` at `a` gives `ω.1 a`. -/
@[simp]
theorem stateSpaceEquivPositiveContinuousLinearMap_symm_apply (e : E)
    (ω : {ω : E →P[ℝ] ℝ // ω e = 1}) (a : E) :
    ((stateSpaceEquivPositiveContinuousLinearMap e).symm ω).1 a = ω.1 a :=
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
  have h := monotone_iff_map_nonneg (toStrongDual φ)
  exact h

/-- The state space is convex. -/
theorem convex_stateSpace : Convex ℝ (stateSpace e) := by
  intro φ hφ ψ hψ s t hs ht hst
  rw [mem_stateSpace_iff_map_nonneg] at hφ hψ ⊢
  refine ⟨fun a ha => ?_, ?_⟩
  · simpa using add_nonneg (mul_nonneg hs (hφ.1 a ha)) (mul_nonneg ht (hψ.1 a ha))
  · simp [hφ.2, hψ.2, hst]

/-- The state space is weak-star closed. -/
theorem isClosed_stateSpace : IsClosed (stateSpace e) := by
  have h : stateSpace e = {φ : WeakDual ℝ E | ∀ a : E, 0 ≤ a → 0 ≤ φ a} ∩ {φ | φ e = 1} :=
    Set.ext fun _ => mem_stateSpace_iff_map_nonneg
  rw [h]
  exact isClosed_setOf_map_nonneg.inter (isClosed_eq (eval_continuous e) continuous_const)

end OrderedGroupStateSpace

/-- States correspond to normalized positive linear functionals `E →ₚ[ℝ] ℝ`, via automatic
continuity. -/
theorem IsOrderUnitNorm.mem_stateSpace_iff_exists_positiveLinearMap {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E] {e : E}
    (he : IsOrderUnitNorm e) {φ : WeakDual ℝ E} :
    φ ∈ stateSpace e ↔ ∃ ω : E →ₚ[ℝ] ℝ, ω e = 1 ∧
      StrongDual.toWeakDual (he.toPositiveContinuousLinearMap isOrderUnitNorm_one_real ω :
        E →L[ℝ] ℝ) = φ := by
  refine ⟨fun hφ => ?_, fun ⟨ω, hω, h⟩ =>
    h ▸ (toWeakDual_mem_stateSpace_iff e _).mpr hω⟩
  let ω : E →ₚ[ℝ] ℝ := { toLinearMap := (toStrongDual φ).toLinearMap, monotone' := hφ.1 }
  have hω : (he.toPositiveContinuousLinearMap isOrderUnitNorm_one_real ω : E →L[ℝ] ℝ) =
      toStrongDual φ := by
    ext a
    rfl
  exact ⟨ω, hφ.2, by rw [hω, toWeakDual_toStrongDual]⟩

section NormedStateSpace

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e)

include he

/-- A functional in `WeakDual ℝ E` is a state iff its strong norm is `1` and `φ e = 1`. -/
theorem IsOrderUnitNorm.mem_stateSpace_iff_norm_eq_one {φ : WeakDual ℝ E} :
    φ ∈ stateSpace e ↔ ‖toStrongDual φ‖ = 1 ∧ φ e = 1 :=
  he.monotone_and_apply_unit_eq_one_iff (toStrongDual φ)

/-- Every state has operator norm `1`. -/
theorem IsOrderUnitNorm.norm_toStrongDual_of_mem_stateSpace {φ : WeakDual ℝ E}
    (hφ : φ ∈ stateSpace e) : ‖toStrongDual φ‖ = 1 :=
  (he.mem_stateSpace_iff_norm_eq_one.mp hφ).1

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

/-- **Existence of states.** Every order-unit space admits at least one state, obtained by
extending `r • e ↦ r` with norm `1` via Hahn–Banach. -/
theorem IsOrderUnitNorm.stateSpace_nonempty : (stateSpace e).Nonempty := by
  let i : ℝ →ₗᵢ[ℝ] E :=
    { toFun := fun r => r • e
      map_add' := fun r s => add_smul r s e
      map_smul' := fun r s => by simp [mul_smul]
      norm_map' := fun r => by simpa [Real.norm_eq_abs] using he.norm_smul_unit r }
  obtain ⟨g, hg, hnorm⟩ :=
    LinearIsometry.exists_extension_norm_eq i (ContinuousLinearMap.id ℝ ℝ)
  have hge : g e = 1 := by
    have h1 := DFunLike.congr_fun hg 1
    simpa [i] using h1
  have hgnorm : ‖g‖ = 1 := by simpa using hnorm
  exact ⟨StrongDual.toWeakDual g, he.mem_stateSpace_iff_norm_eq_one.mpr ⟨hgnorm, hge⟩⟩

end NormedStateSpace

end StateSpace

/-! ### Pullback, subspace extension, and completion extension -/

section Functoriality

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

/-- **Extension of states from a unital subspace.** Restriction of states from `E` to a unital
subspace `S` is surjective, by Hahn–Banach. -/
theorem IsOrderUnitNorm.surjOn_pullbackFunctional_subtypeL {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [PartialOrder E] [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e)
    (S : Submodule ℝ E) (heS : e ∈ S) :
    SurjOn S.subtypeL.pullbackFunctional (stateSpace e) (stateSpace (⟨e, heS⟩ : S)) := by
  intro φ hφ
  have hS := he.submodule S heS
  have hφnorm : ‖toStrongDual φ‖ = 1 := hS.norm_toStrongDual_of_mem_stateSpace hφ
  obtain ⟨g, hg, hgnorm⟩ := _root_.exists_extension_norm_eq S (toStrongDual φ)
  have hge : g e = 1 := by
    simpa [hφ.2] using hg ⟨e, heS⟩
  refine ⟨StrongDual.toWeakDual g,
    he.mem_stateSpace_iff_norm_eq_one.mpr ⟨hgnorm.trans hφnorm, hge⟩, ?_⟩
  exact DFunLike.ext _ _ fun x => by simpa using hg x

section CompletionStates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e)

include he

/-- **Unique extension of states to the norm completion.** Every state on an order-unit space `E`
extends uniquely to a state on `UniformSpace.Completion E`. -/
theorem IsOrderUnitNorm.existsUnique_state_extension_completion {φ : WeakDual ℝ E}
    (hφ : φ ∈ stateSpace e) :
    ∃! ψ ∈ @stateSpace (UniformSpace.Completion E) _ _ _ he.completionPartialOrder.toPreorder
      (e : UniformSpace.Completion E),
      (UniformSpace.Completion.toComplL (S := ℝ) (α := E)).pullbackFunctional ψ = φ := by
  let : PartialOrder (UniformSpace.Completion E) := he.completionPartialOrder
  have : IsOrderedAddMonoid (UniformSpace.Completion E) := he.completionIsOrderedAddMonoid
  have hcompl := he.isOrderUnitNorm_completion
  let g : UniformSpace.Completion E →L[ℝ] ℝ := (toStrongDual φ).fromCompletion
  have hg_coe (a : E) : g a = φ a := (toStrongDual φ).fromCompletion_apply_coe a
  have hge : g (e : UniformSpace.Completion E) = 1 := (hg_coe e).trans hφ.2
  have hbound : ∀ x : UniformSpace.Completion E, ‖g x‖ ≤ 1 * ‖x‖ := by
    intro x
    induction x using UniformSpace.Completion.induction_on with
    | hp =>
      exact isClosed_le (continuous_norm.comp g.continuous) (continuous_const.mul continuous_norm)
    | ih a =>
      rw [hg_coe, UniformSpace.Completion.norm_coe, one_mul, Real.norm_eq_abs]
      exact he.abs_apply_le_norm_of_mem_stateSpace hφ a
  have hgnorm : ‖g‖ = 1 := by
    refine le_antisymm (g.opNorm_le_bound zero_le_one hbound) ?_
    have hle := g.le_opNorm (e : UniformSpace.Completion E)
    rwa [hge, norm_one, UniformSpace.Completion.norm_coe, he.norm_e, mul_one] at hle
  have hψmem : StrongDual.toWeakDual g ∈ stateSpace (e : UniformSpace.Completion E) :=
    hcompl.mem_stateSpace_iff_norm_eq_one.mpr ⟨hgnorm, hge⟩
  have hψeq : (UniformSpace.Completion.toComplL (S := ℝ) (α := E)).pullbackFunctional
      (StrongDual.toWeakDual g) = φ :=
    DFunLike.ext _ _ fun a => by simpa using hg_coe a
  refine ⟨StrongDual.toWeakDual g, ⟨hψmem, hψeq⟩, fun ψ' ⟨_, hψ'eq⟩ => ?_⟩
  have huniq := (toStrongDual φ).fromCompletion_unique (toStrongDual ψ') fun a => by
    have h := DFunLike.congr_fun hψ'eq a
    simpa [UniformSpace.Completion.toComplL] using h.symm
  exact DFunLike.ext _ _ fun x => (DFunLike.congr_fun huniq x).symm

/-- Restriction along `E → UniformSpace.Completion E` induces a weak-star homeomorphism between the
state space of the completion and `stateSpace e`. -/
noncomputable def IsOrderUnitNorm.completionStateSpaceHomeomorph :
    @stateSpace (UniformSpace.Completion E) _ _ _ he.completionPartialOrder.toPreorder
      (e : UniformSpace.Completion E) ≃ₜ stateSpace e := by
  letI : PartialOrder (UniformSpace.Completion E) := he.completionPartialOrder
  haveI : IsOrderedAddMonoid (UniformSpace.Completion E) := he.completionIsOrderedAddMonoid
  have hcompl := he.isOrderUnitNorm_completion
  haveI : CompactSpace (stateSpace (e : UniformSpace.Completion E)) :=
    hcompl.compactSpace_stateSpace
  let T := UniformSpace.Completion.toComplL (S := ℝ) (α := E)
  have hTmono : Monotone T := fun a b hab => he.completion_coe_le_coe_iff.mpr hab
  have hmaps : MapsTo T.pullbackFunctional
      (stateSpace (e : UniformSpace.Completion E)) (stateSpace e) :=
    T.mapsTo_pullbackFunctional_stateSpace hTmono rfl
  let f : stateSpace (e : UniformSpace.Completion E) → stateSpace e :=
    fun ψ => ⟨T.pullbackFunctional ψ.1, hmaps ψ.2⟩
  have hbij : Function.Bijective f := by
    refine ⟨fun ψ₁ ψ₂ h => ?_, fun φ => ?_⟩
    · obtain ⟨_, _, huniq⟩ := he.existsUnique_state_extension_completion (f ψ₂).2
      have h1 : ψ₁.1 = _ := huniq ψ₁.1 ⟨ψ₁.2, congrArg Subtype.val h⟩
      have h2 : ψ₂.1 = _ := huniq ψ₂.1 ⟨ψ₂.2, rfl⟩
      exact Subtype.ext (h1.trans h2.symm)
    · obtain ⟨ψ, ⟨hψmem, hψeq⟩, _⟩ := he.existsUnique_state_extension_completion φ.2
      exact ⟨⟨ψ, hψmem⟩, Subtype.ext hψeq⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hbij)
    ((T.pullbackFunctional.continuous.comp continuous_subtype_val).subtype_mk _)

/-- Evaluating `completionStateSpaceHomeomorph` restricts a completion state to `E`. -/
@[simp]
theorem IsOrderUnitNorm.completionStateSpaceHomeomorph_apply
    (ψ : @stateSpace (UniformSpace.Completion E) _ _ _ he.completionPartialOrder.toPreorder
      (e : UniformSpace.Completion E)) (a : E) :
    (he.completionStateSpaceHomeomorph ψ).1 a = ψ.1 (a : UniformSpace.Completion E) := by
  change (UniformSpace.Completion.toComplL (S := ℝ) (α := E)).pullbackFunctional ψ.1 a = _
  simp

/-- Evaluating the inverse of `completionStateSpaceHomeomorph` on a coerced element recovers the
original state. -/
@[simp]
theorem IsOrderUnitNorm.completionStateSpaceHomeomorph_symm_apply
    (φ : stateSpace e) (a : E) :
    (he.completionStateSpaceHomeomorph.symm φ).1 (a : UniformSpace.Completion E) = φ.1 a := by
  rw [← he.completionStateSpaceHomeomorph_apply,
    he.completionStateSpaceHomeomorph.apply_symm_apply]

end CompletionStates

end Functoriality

/-! ### Order separation, norm detection, and the evaluation embedding -/

section Separation

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
    refine ⟨fun x y hxy => ?_, ?_⟩
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
  refine (he.norm_le_iff a |φ₀ a| (abs_nonneg _)).mpr ⟨?_, ?_⟩
  · refine he.le_iff_forall_stateSpace.mpr fun φ hφ => ?_
    have hle : |φ a| ≤ |φ₀ a| := hmax hφ
    rw [map_smul, smul_eq_mul, hφ.2, mul_one]
    exact (abs_le.mp hle).1
  · refine he.le_iff_forall_stateSpace.mpr fun φ hφ => ?_
    have hle : |φ a| ≤ |φ₀ a| := hmax hφ
    rw [map_smul, smul_eq_mul, hφ.2, mul_one]
    exact (abs_le.mp hle).2

/-- **Norm detection by states** (in `ℝ`): `‖a‖ = ⨆ φ : stateSpace e, |φ.1 a|`. -/
theorem IsOrderUnitNorm.norm_eq_iSup_states (a : E) :
    ‖a‖ = ⨆ φ : stateSpace e, |φ.1 a| := by
  have : Nonempty (stateSpace e) := he.stateSpace_nonempty.to_subtype
  have hbdd : BddAbove (Set.range fun φ : stateSpace e => |φ.1 a|) :=
    ⟨‖a‖, by rintro _ ⟨φ, rfl⟩; exact he.abs_apply_le_norm_of_mem_stateSpace φ.2 a⟩
  obtain ⟨φ₀, hφ₀, hval⟩ := he.exists_mem_stateSpace_abs_apply_eq_norm a
  refine le_antisymm ?_ (ciSup_le fun φ => he.abs_apply_le_norm_of_mem_stateSpace φ.2 a)
  exact hval ▸ le_ciSup hbdd ⟨φ₀, hφ₀⟩

end Separation

section EvalEmbedding

/-- The canonical evaluation map `E →ₗ[ℝ] C(stateSpace e, ℝ)`, sending `a` to `φ ↦ φ a`. -/
noncomputable def evalContinuousMap {E : Type*} [AddCommMonoid E] [Module ℝ E]
    [TopologicalSpace E] [Preorder E] (e : E) : E →ₗ[ℝ] C(stateSpace e, ℝ) where
  toFun a := ⟨fun φ => φ.1 a, (eval_continuous a).comp continuous_subtype_val⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- Evaluating `evalContinuousMap e a` at a state `φ` gives `φ.1 a`. -/
@[simp]
theorem evalContinuousMap_apply {E : Type*} [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E]
    [Preorder E] (e : E) (a : E) (φ : stateSpace e) :
    evalContinuousMap e a φ = φ.1 a :=
  (rfl)

/-- The evaluation embedding sends the order unit `e` to the constant function `1`. -/
@[simp]
theorem evalContinuousMap_unit {E : Type*} [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E]
    [Preorder E] (e : E) : evalContinuousMap e e = 1 := by
  ext φ
  exact φ.2.2

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e)

include he

/-- The evaluation map preserves and reflects the partial order. -/
theorem IsOrderUnitNorm.evalContinuousMap_le_iff {a b : E} :
    evalContinuousMap e a ≤ evalContinuousMap e b ↔ a ≤ b := by
  rw [ContinuousMap.le_def, he.le_iff_forall_stateSpace]
  simp

/-- The evaluation map into `C(stateSpace e, ℝ)` is isometric. -/
theorem IsOrderUnitNorm.norm_evalContinuousMap [CompactSpace (stateSpace e)] (a : E) :
    ‖evalContinuousMap e a‖ = ‖a‖ := by
  rw [ContinuousMap.norm_eq_iSup_norm, he.norm_eq_iSup_states a]
  simp [Real.norm_eq_abs]

/-- **Norm detection by states** (in `ℝ≥0`): `‖a‖₊ = ⨆ φ : stateSpace e, ‖φ.1 a‖₊`. -/
theorem IsOrderUnitNorm.nnNorm_eq_iSup_states (a : E) :
    ‖a‖₊ = ⨆ φ : stateSpace e, ‖φ.1 a‖₊ := by
  have : CompactSpace (stateSpace e) := he.compactSpace_stateSpace
  have h : ‖a‖₊ = ‖evalContinuousMap e a‖₊ := NNReal.eq (he.norm_evalContinuousMap a).symm
  rw [h, ContinuousMap.nnNorm_eq_iSup_nnNorm]
  rfl

/-- The canonical unital isometric order embedding `E →ₗᵢ[ℝ] C(stateSpace e, ℝ)`. -/
noncomputable def IsOrderUnitNorm.evalLinearIsometry [CompactSpace (stateSpace e)] :
    E →ₗᵢ[ℝ] C(stateSpace e, ℝ) where
  toLinearMap := evalContinuousMap e
  norm_map' := he.norm_evalContinuousMap

/-- Evaluating `evalLinearIsometry` agrees with `evalContinuousMap`. -/
@[simp]
theorem IsOrderUnitNorm.evalLinearIsometry_apply [CompactSpace (stateSpace e)]
    (a : E) (φ : stateSpace e) : he.evalLinearIsometry a φ = φ.1 a :=
  (rfl)

/-- The evaluation isometry sends the order unit `e` to `1`. -/
@[simp]
theorem IsOrderUnitNorm.evalLinearIsometry_unit [CompactSpace (stateSpace e)] :
    he.evalLinearIsometry e = 1 :=
  evalContinuousMap_unit e

end EvalEmbedding

/-! ### Correspondence with states of a unital C⋆-algebra -/

section CStarCorrespondence

section CStarStates

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Restricting a C⋆-algebra state to `selfAdjoint A` yields an order-unit state. -/
theorem mapsTo_restrictToSelfAdjoint_stateSpace :
    MapsTo (restrictToSelfAdjoint (A := A))
      (TauCeti.stateSpace A) (stateSpace (1 : selfAdjoint A)) := by
  intro φ hφ
  rw [mem_stateSpace_iff_map_nonneg]
  refine ⟨fun a ha => ?_, ?_⟩
  · have hpos : 0 ≤ φ (a : A) := TauCeti.map_nonneg_of_mem_stateSpace hφ ha
    simpa using (Complex.le_def.mp hpos).1
  · simp [TauCeti.map_one_of_mem_stateSpace hφ]

/-- Extending an order-unit state of `selfAdjoint A` by complex linearity yields a C⋆-algebra
state of `A`. -/
theorem mapsTo_extendFromSelfAdjoint_stateSpace :
    MapsTo (extendFromSelfAdjoint (A := A))
      (stateSpace (1 : selfAdjoint A)) (TauCeti.stateSpace A) := by
  intro ψ hψ
  rw [TauCeti.mem_stateSpace_iff_map_one]
  refine ⟨fun a ha => ?_, ?_⟩
  · let a' : selfAdjoint A := ⟨a, IsSelfAdjoint.of_nonneg ha⟩
    have ha' : (0 : selfAdjoint A) ≤ a' := ha
    have hre : ℜ a = a' := selfAdjoint.realPart_coe (x := a')
    have him : ℑ a = 0 := selfAdjoint.imaginaryPart_coe (x := a')
    rw [extendFromSelfAdjoint_apply, hre, him, map_zero, Complex.ofReal_zero, mul_zero, add_zero]
    exact Complex.le_def.mpr ⟨map_nonneg_of_mem_stateSpace hψ ha', rfl⟩
  · have hre : ℜ (1 : A) = (1 : selfAdjoint A) :=
      selfAdjoint.realPart_coe (x := (1 : selfAdjoint A))
    have him : ℑ (1 : A) = 0 := selfAdjoint.imaginaryPart_coe (x := (1 : selfAdjoint A))
    rw [extendFromSelfAdjoint_apply, hre, him, map_zero, Complex.ofReal_zero, mul_zero, add_zero,
      hψ.2, Complex.ofReal_one]

/-- On any C⋆-algebra state `φ`, extending the restriction to `selfAdjoint A` recovers `φ`. -/
theorem extendFromSelfAdjoint_restrictToSelfAdjoint_of_mem_stateSpace {φ : WeakDual ℂ A}
    (hφ : φ ∈ TauCeti.stateSpace A) :
    extendFromSelfAdjoint (restrictToSelfAdjoint φ) = φ := by
  let ω : A →P[ℂ] ℂ := .mk₀ (toStrongDual φ) fun _ => TauCeti.map_nonneg_of_mem_stateSpace hφ
  have hreal (x : selfAdjoint A) : ((φ (x : A)).re : ℂ) = φ (x : A) := by
    have hstar : star (ω (x : A)) = ω (x : A) := by
      rw [← map_star, x.2.star_eq]
    have him : (φ (x : A)).im = 0 := Complex.conj_eq_iff_im.mp hstar
    exact Complex.ext rfl (by simp [him])
  refine DFunLike.ext _ _ fun a => ?_
  calc
    extendFromSelfAdjoint (restrictToSelfAdjoint φ) a
        = ((φ (ℜ a : A)).re : ℂ) + Complex.I * ((φ (ℑ a : A)).re : ℂ) := by simp
    _ = φ (ℜ a : A) + Complex.I * φ (ℑ a : A) := by rw [hreal (ℜ a), hreal (ℑ a)]
    _ = φ ((ℜ a : A) + Complex.I • (ℑ a : A)) := by rw [map_add, map_smul, smul_eq_mul]
    _ = φ a := by rw [realPart_add_I_smul_imaginaryPart]

/-- **C⋆-algebra state correspondence.** Restriction to `selfAdjoint A` and complex-linear
extension define a weak-star homeomorphism between `TauCeti.stateSpace A` and
`OrderUnit.stateSpace (1 : selfAdjoint A)`. -/
noncomputable def cstarStateSpaceHomeomorph :
    TauCeti.stateSpace A ≃ₜ stateSpace (1 : selfAdjoint A) where
  toFun φ := ⟨restrictToSelfAdjoint φ.1, mapsTo_restrictToSelfAdjoint_stateSpace φ.2⟩
  invFun ψ := ⟨extendFromSelfAdjoint ψ.1, mapsTo_extendFromSelfAdjoint_stateSpace ψ.2⟩
  left_inv φ := Subtype.ext (extendFromSelfAdjoint_restrictToSelfAdjoint_of_mem_stateSpace φ.2)
  right_inv ψ := Subtype.ext (restrictToSelfAdjoint_extendFromSelfAdjoint ψ.1)
  continuous_toFun :=
    (restrictToSelfAdjoint.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (extendFromSelfAdjoint.continuous.comp continuous_subtype_val).subtype_mk _

/-- Evaluating `cstarStateSpaceHomeomorph` takes the real part on self-adjoint elements. -/
@[simp]
theorem cstarStateSpaceHomeomorph_apply (φ : TauCeti.stateSpace A) (a : selfAdjoint A) :
    (cstarStateSpaceHomeomorph φ).1 a = (φ.1 (a : A)).re := by
  simp [cstarStateSpaceHomeomorph]

/-- Evaluating the inverse of `cstarStateSpaceHomeomorph` recovers the complex-linear extension. -/
@[simp]
theorem cstarStateSpaceHomeomorph_symm_apply (ψ : stateSpace (1 : selfAdjoint A)) (a : A) :
    (cstarStateSpaceHomeomorph.symm ψ).1 a = (ψ.1 (ℜ a) : ℂ) + Complex.I * (ψ.1 (ℑ a) : ℂ) := by
  simp [cstarStateSpaceHomeomorph]

/-- The bijection between normalized positive continuous complex-linear functionals
`{ω : A →P[ℂ] ℂ // ω 1 = 1}` and `OrderUnit.stateSpace (1 : selfAdjoint A)`. -/
noncomputable def cstarPositiveLinearMapEquivStateSpace :
    {ω : A →P[ℂ] ℂ // ω 1 = 1} ≃ stateSpace (1 : selfAdjoint A) where
  toFun ω := cstarStateSpaceHomeomorph
    ⟨StrongDual.toWeakDual (ω.1 : A →L[ℂ] ℂ),
      TauCeti.mem_stateSpace_iff_map_one.mpr ⟨fun _ ha => ω.1.map_nonneg ha, ω.2⟩⟩
  invFun ψ :=
    let φ := cstarStateSpaceHomeomorph.symm ψ
    ⟨PositiveContinuousLinearMap.mk₀ (toStrongDual φ.1)
      (fun _ ha => TauCeti.map_nonneg_of_mem_stateSpace φ.2 ha),
      TauCeti.map_one_of_mem_stateSpace φ.2⟩
  left_inv ω := by
    refine Subtype.ext (DFunLike.ext _ _ fun a => ?_)
    have h := congrArg (fun x : TauCeti.stateSpace A => x.1 a)
      (cstarStateSpaceHomeomorph.left_inv
        ⟨StrongDual.toWeakDual (ω.1 : A →L[ℂ] ℂ),
          TauCeti.mem_stateSpace_iff_map_one.mpr ⟨fun _ ha => ω.1.map_nonneg ha, ω.2⟩⟩)
    exact h
  right_inv ψ := by
    refine Subtype.ext (DFunLike.ext _ _ fun a => ?_)
    have h := congrArg (fun x : stateSpace (1 : selfAdjoint A) => x.1 a)
      (cstarStateSpaceHomeomorph.right_inv ψ)
    exact h

/-- Evaluating `cstarPositiveLinearMapEquivStateSpace` restricts `ω` to `selfAdjoint A`. -/
@[simp]
theorem cstarPositiveLinearMapEquivStateSpace_apply (ω : {ω : A →P[ℂ] ℂ // ω 1 = 1})
    (a : selfAdjoint A) :
    (cstarPositiveLinearMapEquivStateSpace ω).1 a = (ω.1 (a : A)).re := by
  simp [cstarPositiveLinearMapEquivStateSpace]

/-- Evaluating the inverse of `cstarPositiveLinearMapEquivStateSpace` gives the complex-linear
extension of `ψ`. -/
@[simp]
theorem cstarPositiveLinearMapEquivStateSpace_symm_apply (ψ : stateSpace (1 : selfAdjoint A))
    (a : A) :
    (cstarPositiveLinearMapEquivStateSpace.symm ψ).1 a =
      (ψ.1 (ℜ a) : ℂ) + Complex.I * (ψ.1 (ℑ a) : ℂ) :=
  cstarStateSpaceHomeomorph_symm_apply ψ a

end CStarStates

end CStarCorrespondence

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

end TauCeti.OrderUnit
