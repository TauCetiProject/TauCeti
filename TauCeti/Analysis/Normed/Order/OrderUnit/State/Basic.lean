/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.WeakDual
public import TauCeti.Analysis.Normed.Order.OrderUnit.PositiveLinearMap
public import TauCeti.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.Convex.Cone.Dual
import TauCeti.Analysis.Normed.Module.HahnBanach.Basic

/-!
# State spaces of order-unit spaces

This file develops the state space of an order-unit space, proving weak-star compactness,
functoriality and extension results, order separation, norm detection by states, and the unital
isometric order embedding into continuous functions on the state space.

A **state** of an order-unit space `(E, e)` is a monotone continuous real-linear functional `φ`
with `φ e = 1`. The **state space** `TauCeti.OrderUnit.stateSpace e` is defined as a subset of the
weak-star dual `WeakDual ℝ E`, carrying the weak-star subspace topology.

Unique weak-star homeomorphic extension of states to the norm completion is treated in
`TauCeti.Analysis.Normed.Order.OrderUnit.State.Completion`.

## Main definitions and results

* `TauCeti.OrderUnit.stateSpace`: the state space `{φ : WeakDual ℝ E | Monotone φ ∧ φ e = 1}`.
* `TauCeti.IsOrderUnitNorm.stateSpace_nonempty`, `TauCeti.OrderUnit.convex_stateSpace`,
  `TauCeti.OrderUnit.isClosed_stateSpace`, `TauCeti.IsOrderUnitNorm.isCompact_stateSpace`:
  nonemptiness (by Hahn–Banach), convexity, weak-star closedness, and weak-star compactness (by
  Banach–Alaoglu).
* `ContinuousLinearMap.mapsTo_pullbackFunctional_stateSpace`,
  `TauCeti.IsOrderUnitNorm.surjOn_pullbackFunctional_stateSpace`,
  `TauCeti.IsOrderUnitNorm.surjOn_pullbackFunctional_subtypeL`: pullback along unital positive
  maps (via `ContinuousLinearMap.pullbackFunctional`) and extension along unit-preserving linear
  isometries and from unital subspaces.
* `TauCeti.IsOrderUnitNorm.nonneg_iff_forall_stateSpace`,
  `exists_mem_stateSpace_abs_apply_eq_norm`, `norm_eq_iSup_states`, `nnNorm_eq_iSup_states`,
  `TauCeti.OrderUnit.evalContinuousMap`, `evalContinuousMap_apply_convexCombo`,
  `TauCeti.IsOrderUnitNorm.evalLinearIsometry`: order separation, norm detection by states, and
  the isometric unital order embedding `E → C(stateSpace e, ℝ)`.

## References

* Marc A. Rieffel, *Metrics on state spaces*, Doc. Math. 4 (1999), 559–600, Section 1.
* Richard V. Kadison, *A representation theory for commutative topological algebra*,
  Mem. Amer. Math. Soc. 7 (1951).
-/

public section

open Set Metric WeakDual
open scoped NNReal Topology

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
  · change s * φ a + t * ψ a ≤ s * φ b + t * ψ b
    exact add_le_add (mul_le_mul_of_nonneg_left (hφ.1 hab) hs)
      (mul_le_mul_of_nonneg_left (hψ.1 hab) ht)
  · change s * φ e + t * ψ e = 1
    simp [hφ.2, hψ.2, hst]

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
  have h := monotone_iff_map_nonneg (toStrongDual φ)
  exact h

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
  have hω : (he.toPositiveContinuousLinearMap isOrderUnitNorm_real_one ω : E →L[ℝ] ℝ) =
      toStrongDual φ := by
    ext a
    simp [ω]
    rfl
  exact ⟨ω, hφ.2, by rw [hω, toWeakDual_toStrongDual]⟩

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

/-! ### Pullback, subspace extension, and nonemptiness -/

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

/-- **Extension of states along a unit-preserving linear isometry.** Every state on the domain of
a unit-preserving linear isometry between order-unit spaces extends to a state on the codomain. -/
theorem IsOrderUnitNorm.surjOn_pullbackFunctional_stateSpace {E F : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F] [IsOrderedAddMonoid F]
    {e : E} {f : F} (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f)
    (T : E →ₗᵢ[ℝ] F) (hTe : T e = f) :
    SurjOn T.toContinuousLinearMap.pullbackFunctional (stateSpace f) (stateSpace e) := by
  intro φ hφ
  let _ : NormedAddCommGroup E :=
    { ‹SeminormedAddCommGroup E› with
      eq_of_dist_eq_zero := fun h =>
        sub_eq_zero.mp (he.norm_eq_zero_iff.mp (by simpa [dist_eq_norm] using h)) }
  have hφnorm : ‖toStrongDual φ‖ = 1 := he.norm_toStrongDual_of_mem_stateSpace hφ
  obtain ⟨g, hg, hgnorm⟩ := T.exists_extension_norm_eq (toStrongDual φ)
  have hgf : g f = 1 := by
    simpa [hTe, hφ.2] using DFunLike.congr_fun hg e
  refine ⟨StrongDual.toWeakDual g,
    hf.mem_stateSpace_iff_norm_eq_one_and_map_unit.mpr ⟨hgnorm.trans hφnorm, hgf⟩, ?_⟩
  exact DFunLike.ext _ _ fun x => by simpa using DFunLike.congr_fun hg x

/-- **Extension of states from a unital subspace.** Restriction of states from `E` to a unital
subspace `S` is surjective, by Hahn–Banach. -/
theorem IsOrderUnitNorm.surjOn_pullbackFunctional_subtypeL {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [PartialOrder E] [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e)
    (S : Submodule ℝ E) (heS : e ∈ S) :
    SurjOn S.subtypeL.pullbackFunctional (stateSpace e) (stateSpace (⟨e, heS⟩ : S)) := by
  simpa [Submodule.subtypeₗᵢ_toContinuousLinearMap] using
    (he.submodule S heS).surjOn_pullbackFunctional_stateSpace he S.subtypeₗᵢ rfl

/-- **Existence of states.** Every order-unit space admits at least one state, obtained by
extending `r • e ↦ r` with norm `1` via Hahn–Banach. -/
theorem IsOrderUnitNorm.stateSpace_nonempty {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [PartialOrder E] [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e) :
    (stateSpace e).Nonempty := by
  let i : ℝ →ₗᵢ[ℝ] E := LinearIsometry.toSpanSingleton ℝ E he.norm_eq_one
  have hi : i 1 = e := by simp [i, LinearIsometry.toSpanSingleton_apply]
  have hid : StrongDual.toWeakDual (ContinuousLinearMap.id ℝ ℝ) ∈ stateSpace (1 : ℝ) :=
    ⟨fun _ _ h => h, rfl⟩
  obtain ⟨φ, hφ, _⟩ := isOrderUnitNorm_real_one.surjOn_pullbackFunctional_stateSpace he i hi hid
  exact ⟨φ, hφ⟩

end Functoriality

/-! ### Order separation, norm detection, and the evaluation embedding -/

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
  refine (he.norm_le_iff (abs_nonneg _)).mpr ⟨?_, ?_⟩
  · refine he.le_iff_forall_stateSpace.mpr fun φ hφ => ?_
    have hle : |φ a| ≤ |φ₀ a| := hmax hφ
    rw [map_neg, map_smul, smul_eq_mul, hφ.2, mul_one]
    exact (abs_le.mp hle).1
  · refine he.le_iff_forall_stateSpace.mpr fun φ hφ => ?_
    have hle : |φ a| ≤ |φ₀ a| := hmax hφ
    rw [map_smul, smul_eq_mul, hφ.2, mul_one]
    exact (abs_le.mp hle).2

/-- **Norm detection by states** (in `ℝ`): `‖a‖ = ⨆ φ : stateSpace e, |φ.val a|`. -/
theorem IsOrderUnitNorm.norm_eq_iSup_states (a : E) :
    ‖a‖ = ⨆ φ : stateSpace e, |φ.val a| := by
  have : Nonempty (stateSpace e) := he.stateSpace_nonempty.to_subtype
  have hbdd : BddAbove (Set.range fun φ : stateSpace e => |φ.val a|) :=
    ⟨‖a‖, by rintro _ ⟨φ, rfl⟩; exact he.abs_apply_le_norm_of_mem_stateSpace φ.property a⟩
  obtain ⟨φ₀, hφ₀, hval⟩ := he.exists_mem_stateSpace_abs_apply_eq_norm a
  refine le_antisymm ?_ (ciSup_le fun φ => he.abs_apply_le_norm_of_mem_stateSpace φ.property a)
  exact hval ▸ le_ciSup hbdd ⟨φ₀, hφ₀⟩

end Separation

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
  exact φ.property.2

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
theorem IsOrderUnitNorm.norm_evalContinuousMap [CompactSpace (stateSpace e)] (a : E) :
    ‖evalContinuousMap e a‖ = ‖a‖ := by
  rw [ContinuousMap.norm_eq_iSup_norm, he.norm_eq_iSup_states a]
  simp [Real.norm_eq_abs]

/-- **Norm detection by states** (in `ℝ≥0`): `‖a‖₊ = ⨆ φ : stateSpace e, ‖φ.val a‖₊`. -/
theorem IsOrderUnitNorm.nnNorm_eq_iSup_states (a : E) :
    ‖a‖₊ = ⨆ φ : stateSpace e, ‖φ.val a‖₊ := by
  have : CompactSpace (stateSpace e) := he.compactSpace_stateSpace
  have h : ‖a‖₊ = ‖evalContinuousMap e a‖₊ := NNReal.eq (he.norm_evalContinuousMap a).symm
  rw [h, ContinuousMap.nnNorm_eq_iSup_nnNorm]
  rfl

/-- The canonical unital isometric order embedding `E →ₗᵢ[ℝ] C(stateSpace e, ℝ)`. -/
noncomputable def IsOrderUnitNorm.evalLinearIsometry [CompactSpace (stateSpace e)] :
    E →ₗᵢ[ℝ] C(stateSpace e, ℝ) where
  toLinearMap := evalContinuousMap e
  norm_map' := he.norm_evalContinuousMap

/-- The underlying linear map of `evalLinearIsometry` is `evalContinuousMap e`. -/
@[simp]
theorem IsOrderUnitNorm.evalLinearIsometry_toLinearMap [CompactSpace (stateSpace e)] :
    he.evalLinearIsometry.toLinearMap = evalContinuousMap e :=
  (rfl)

/-- Evaluating `evalLinearIsometry` agrees with `evalContinuousMap`. -/
@[simp]
theorem IsOrderUnitNorm.evalLinearIsometry_apply [CompactSpace (stateSpace e)]
    (a : E) (φ : stateSpace e) : he.evalLinearIsometry a φ = φ.val a :=
  (rfl)

/-- The evaluation isometry sends the order unit `e` to `1`. -/
@[simp]
theorem IsOrderUnitNorm.evalLinearIsometry_unit [CompactSpace (stateSpace e)] :
    he.evalLinearIsometry e = 1 :=
  evalContinuousMap_unit e

end EvalEmbedding

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
