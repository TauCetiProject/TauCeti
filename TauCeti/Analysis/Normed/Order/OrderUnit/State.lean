/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
public import TauCeti.Analysis.Convex.Cone.PositiveDual
public import TauCeti.Analysis.CStarAlgebra.State.Space
public import TauCeti.Analysis.Normed.Module.HahnBanach
public import TauCeti.Analysis.Normed.Order.OrderUnit.Completion
public import TauCeti.Analysis.Normed.Order.PositiveLinearMap

/-!
# Positive maps, states, compactness, and norm detection on order-unit spaces

Let `(E, e)` be a real order-unit space (`he : TauCeti.IsOrderUnitNorm e`). Every positive linear
map `T : E → F` into another order-unit space is automatically bounded with `‖T‖ = ‖T e‖`, and in
particular unital positive maps are contractive. For a continuous real linear functional
`φ : E →L[ℝ] ℝ`, Kadison's characterization gives `Monotone φ ↔ ‖φ‖ = φ e`.

A **state** of `(E, e)` is a monotone weak-star dual functional `φ : WeakDual ℝ E` normalized by
`φ e = 1`. The **state space** `TauCeti.OrderUnit.stateSpace e` carries the inherited weak-star
subspace topology. Using Hahn–Banach extension, Banach–Alaoglu (`WeakDual.isCompact_closedBall`),
and hyperplane separation for the closed positive cone (`TauCeti.le_iff_forall_monotone_dual_le`),
we establish:

* state existence (`TauCeti.IsOrderUnitNorm.stateSpace_nonempty`),
* weak-star compactness and convexity (`TauCeti.IsOrderUnitNorm.isCompact_stateSpace`,
  `TauCeti.OrderUnit.convex_stateSpace`),
* restriction, Hahn–Banach extension, contravariant pullback along unital positive maps,
  and weak-star homeomorphism with the states of `TauCeti.OrderUnitCompletion he`,
* order and point separation (`TauCeti.IsOrderUnitNorm.le_iff_forall_state_le`,
  `TauCeti.IsOrderUnitNorm.eq_iff_forall_state_eq`),
* norm attainment and detection (`TauCeti.IsOrderUnitNorm.exists_state_abs_apply_eq_norm`,
  `TauCeti.IsOrderUnitNorm.norm_eq_iSup_states`,
  `TauCeti.IsOrderUnitNorm.nnNorm_eq_iSup_states`),
* the weak-star homeomorphism between the C⋆-algebra states `TauCeti.stateSpace A` of a unital
  C⋆-algebra `A` (equipped with a compatible star order, supplied as `PartialOrder A` and
  `StarOrderedRing A`) and the real order-unit states
  `TauCeti.OrderUnit.stateSpace (1 : selfAdjoint A)`
  (`TauCeti.OrderUnit.cstarStateSpaceHomeomorph`).

## References

* R. V. Kadison, *A representation theory for commutative topological algebra*, Mem. Amer. Math.
  Soc. **7** (1951).
* M. A. Rieffel, *Metrics on state spaces*, Doc. Math. **4** (1999), 559–600, §1.
-/

public section

noncomputable section

open Set Filter Topology
open scoped NNReal ComplexOrder ComplexStarModule

namespace TauCeti

/-! ### Positive linear maps between order-unit spaces -/

namespace IsOrderUnitNorm

section PositiveMaps

variable {E F : Type*} [SeminormedAddCommGroup E] [Module ℝ E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F] [Preorder F] [IsOrderedAddMonoid F]
  {e : E} {f : F}

private theorem norm_map_le_of_monotone [LE E] (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f)
    (T : E →ₗ[ℝ] F) (hT : ∀ ⦃a b : E⦄, a ≤ b → T a ≤ T b) (a : E) :
    ‖T a‖ ≤ ‖T e‖ * ‖a‖ := by
  have h1 : -(‖a‖ • T e) ≤ T a := by
    simpa [map_smul, neg_smul] using hT (he.neg_norm_smul_le a)
  have h2 : T a ≤ ‖a‖ • T e := by
    simpa [map_smul] using hT (he.le_norm_smul a)
  calc ‖T a‖ ≤ ‖‖a‖ • T e‖ := hf.norm_le_of_neg_le_of_le h1 h2
    _ = ‖T e‖ * ‖a‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a), mul_comm]

/-- Every positive linear map between order-unit spaces satisfies `‖T a‖ ≤ ‖T e‖ * ‖a‖`.
Stated for a bundled map type `G` carrying both `LinearMapClass G ℝ E F` and `OrderHomClass G E F`
(such as `PositiveLinearMap`, written `E →ₚ[ℝ] F`), rather than a plain linear map with a separate
monotonicity proof. -/
theorem norm_map_le [LE E] {G : Type*} [FunLike G E F] [LinearMapClass G ℝ E F]
    [OrderHomClass G E F] (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) (T : G) (a : E) :
    ‖T a‖ ≤ ‖T e‖ * ‖a‖ :=
  he.norm_map_le_of_monotone hf (T : E →ₗ[ℝ] F) (fun _ _ hab => map_rel T hab) a

/-- Every positive linear map between order-unit spaces is automatically continuous.
Stated for a bundled map type `G` carrying both `LinearMapClass G ℝ E F` and `OrderHomClass G E F`
(such as `PositiveLinearMap`, written `E →ₚ[ℝ] F`), rather than a plain linear map with a separate
monotonicity proof. -/
theorem continuous_of_monotone [LE E] {G : Type*} [FunLike G E F] [LinearMapClass G ℝ E F]
    [OrderHomClass G E F] (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) (T : G) :
    Continuous T :=
  (LinearMap.mkContinuous (T : E →ₗ[ℝ] F) ‖T e‖ (he.norm_map_le hf T)).continuous

/-- Every unital positive linear map between order-unit spaces is contractive: `‖T a‖ ≤ ‖a‖`.
Stated for a bundled map type `G` carrying both `LinearMapClass G ℝ E F` and `OrderHomClass G E F`
(such as `PositiveLinearMap`, written `E →ₚ[ℝ] F`), rather than a plain linear map with a separate
monotonicity proof. -/
theorem norm_map_le_of_map_unit [LE E] {G : Type*} [FunLike G E F] [LinearMapClass G ℝ E F]
    [OrderHomClass G E F] (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f)
    (T : G) (hunit : T e = f) (a : E) : ‖T a‖ ≤ ‖a‖ := by
  simpa [hunit, hf.norm_e] using he.norm_map_le hf T a

/-- Bundle a positive linear map between order-unit spaces as a `PositiveContinuousLinearMap`.
Takes a bundled map type `G` carrying both `LinearMapClass G ℝ E F` and `OrderHomClass G E F`
(such as `PositiveLinearMap`, written `E →ₚ[ℝ] F`), rather than a plain linear map with a separate
monotonicity proof. -/
def toPositiveContinuousLinearMap {E F : Type*} [SeminormedAddCommGroup E] [Module ℝ E]
    [PartialOrder E] [SeminormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F]
    [IsOrderedAddMonoid F] {e : E} {f : F} {G : Type*} [FunLike G E F] [LinearMapClass G ℝ E F]
    [OrderHomClass G E F] (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) (T : G) :
    E →P[ℝ] F where
  toContinuousLinearMap := LinearMap.mkContinuous (T : E →ₗ[ℝ] F) ‖T e‖ (he.norm_map_le hf T)
  monotone' := OrderHomClass.mono T

@[simp]
theorem toPositiveContinuousLinearMap_apply {E F : Type*} [SeminormedAddCommGroup E] [Module ℝ E]
    [PartialOrder E] [SeminormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F]
    [IsOrderedAddMonoid F] {e : E} {f : F} {G : Type*} [FunLike G E F] [LinearMapClass G ℝ E F]
    [OrderHomClass G E F] (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) (T : G) (a : E) :
    he.toPositiveContinuousLinearMap hf T a = T a := (rfl)

end PositiveMaps

section PositiveCLMs

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [Preorder E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F] [Preorder F] [IsOrderedAddMonoid F]
  {e : E} {f : F}

/-- A monotone continuous linear map between order-unit spaces has operator norm `‖T e‖`. -/
theorem opNorm_eq_norm_apply (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f)
    {T : E →L[ℝ] F} (hT : Monotone T) : ‖T‖ = ‖T e‖ := by
  refine le_antisymm
    (T.opNorm_le_bound (norm_nonneg _) (he.norm_map_le_of_monotone hf (T : E →ₗ[ℝ] F) hT)) ?_
  simpa [he.norm_e] using T.le_opNorm e

/-- A unital positive continuous linear map between order-unit spaces has operator norm `1`. -/
theorem opNorm_eq_one_of_monotone_of_map_unit (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f)
    {T : E →L[ℝ] F} (hT : Monotone T) (hunit : T e = f) : ‖T‖ = 1 := by
  rw [he.opNorm_eq_norm_apply hf hT, hunit, hf.norm_e]

end PositiveCLMs

/-! ### Positive linear functionals and Kadison's norm characterization -/

section Functionals

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E] {e : E}

/-- A monotone continuous real linear functional on an order-unit space has operator norm equal to
its value at `e`. -/
theorem opNorm_functional_eq_apply (he : IsOrderUnitNorm e) {φ : E →L[ℝ] ℝ} (hφ : Monotone φ) :
    ‖φ‖ = φ e :=
  ContinuousLinearMap.opNorm_eq_apply_of_monotone φ hφ he.le_norm_smul he.norm_e.le

/-- **Kadison's characterization of positivity:** a continuous real linear functional `φ` on an
order-unit space is monotone if and only if `‖φ‖ = φ e`. -/
theorem monotone_iff_opNorm_eq_apply [IsOrderedAddMonoid E] (he : IsOrderUnitNorm e)
    {φ : E →L[ℝ] ℝ} : Monotone φ ↔ ‖φ‖ = φ e := by
  refine ⟨he.opNorm_functional_eq_apply, fun hnorm => ?_⟩
  rw [monotone_iff_map_nonneg]
  intro a ha
  refine LinearMap.apply_nonneg_of_abs_apply_le_mul_norm (u := e) φ.toLinearMap (fun g => ?_)
    ((he.nonneg_iff_norm_sub_le a).mp ha)
  simpa [← hnorm, Real.norm_eq_abs] using φ.le_opNorm g

/-- A normalized continuous real linear functional (`φ e = 1`) on an order-unit space is monotone
if and only if `‖φ‖ = 1`. -/
theorem monotone_iff_opNorm_eq_one [IsOrderedAddMonoid E] (he : IsOrderUnitNorm e)
    {φ : E →L[ℝ] ℝ} (hφ : φ e = 1) : Monotone φ ↔ ‖φ‖ = 1 := by
  rw [he.monotone_iff_opNorm_eq_apply, hφ]

end Functionals

end IsOrderUnitNorm

/-! ### The order-unit state space: basic API, convexity, and pullback -/

namespace OrderUnit

/-- The **state space** of an ordered topological real vector space with distinguished element `e`:
the set of monotone weak-star dual functionals normalized by `φ e = 1`, carrying the inherited
weak-star subspace topology from `WeakDual ℝ E`. -/
def stateSpace {E : Type*} [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E] [Preorder E]
    (e : E) : Set (WeakDual ℝ E) :=
  {φ | Monotone φ ∧ φ e = 1}

section StateSpaceBasic

variable {E : Type*} [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E] [Preorder E] {e : E}

@[simp]
theorem mem_stateSpace_iff {φ : WeakDual ℝ E} : φ ∈ stateSpace e ↔ Monotone φ ∧ φ e = 1 :=
  Iff.rfl

theorem stateSpace_monotone {φ : WeakDual ℝ E} (hφ : φ ∈ stateSpace e) : Monotone φ :=
  hφ.1

theorem stateSpace_apply_self {φ : WeakDual ℝ E} (hφ : φ ∈ stateSpace e) : φ e = 1 :=
  hφ.2

theorem stateSpace_apply_nonneg {φ : WeakDual ℝ E} (hφ : φ ∈ stateSpace e) {a : E} (ha : 0 ≤ a) :
    0 ≤ φ a := by
  simpa only [map_zero] using hφ.1 ha

/-- The order-unit state space is a convex subset of `WeakDual ℝ E`. -/
theorem convex_stateSpace (e : E) : Convex ℝ (stateSpace e) := by
  intro φ hφ ψ hψ s t hs ht hst
  refine ⟨fun a b hab => ?_, ?_⟩
  · exact add_le_add (mul_le_mul_of_nonneg_left (hφ.1 hab) hs)
      (mul_le_mul_of_nonneg_left (hψ.1 hab) ht)
  · rw [← WeakDual.toStrongDual_apply]
    simp [hφ.2, hψ.2, hst]

/-- The order-unit state space is weak-star closed in `WeakDual ℝ E`. -/
theorem isClosed_stateSpace (e : E) : IsClosed (stateSpace e) := by
  have hset : stateSpace e =
      (⋂ (a : E) (b : E) (_ : a ≤ b), {φ : WeakDual ℝ E | φ a ≤ φ b}) ∩
        {φ : WeakDual ℝ E | φ e = 1} := by
    ext φ
    simp [stateSpace, Monotone]
  rw [hset]
  refine IsClosed.inter ?_ (isClosed_eq (WeakDual.eval_continuous e) continuous_const)
  refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ => ?_
  exact isClosed_le (WeakDual.eval_continuous a) (WeakDual.eval_continuous b)

/-- Evaluation at any `a : E` is weak-star continuous on `OrderUnit.stateSpace e`. -/
theorem continuous_eval_stateSpace (a : E) : Continuous (fun φ : stateSpace e => φ.1 a) :=
  (WeakDual.eval_continuous a).comp continuous_subtype_val

end StateSpaceBasic

/-- Equivalence between `OrderUnit.stateSpace e` and Mathlib's `PositiveContinuousLinearMap`s
normalized at `e`. -/
def stateSpaceEquivPositive {E : Type*} [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E]
    [PartialOrder E] (e : E) : stateSpace e ≃ {φ : E →P[ℝ] ℝ // φ e = 1} where
  toFun φ := ⟨{ toContinuousLinearMap := WeakDual.toStrongDual φ.1, monotone' := φ.2.1 }, φ.2.2⟩
  invFun φ := ⟨WeakDual.toStrongDual.symm φ.1.toContinuousLinearMap, φ.1.monotone', φ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem stateSpaceEquivPositive_apply {E : Type*} [AddCommMonoid E] [Module ℝ E]
    [TopologicalSpace E] [PartialOrder E] {e : E} (φ : stateSpace e) (a : E) :
    (stateSpaceEquivPositive e φ).1 a = φ.1 a := (rfl)

@[simp]
theorem stateSpaceEquivPositive_symm_apply {E : Type*} [AddCommMonoid E] [Module ℝ E]
    [TopologicalSpace E] [PartialOrder E] {e : E} (φ : {φ : E →P[ℝ] ℝ // φ e = 1}) (a : E) :
    ((stateSpaceEquivPositive e).symm φ).1 a = φ.1 a := (rfl)

section Pullback

variable {E F G : Type*} [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E] [Preorder E]
  [AddCommMonoid F] [Module ℝ F] [TopologicalSpace F] [Preorder F]
  [AddCommMonoid G] [Module ℝ G] [TopologicalSpace G] [Preorder G]

/-- Pullback of states `φ ↦ φ ∘ T` along a unital monotone continuous linear map `T : E →L[ℝ] F`.
-/
def statePullback {e : E} {f : F} (T : E →L[ℝ] F) (hT : Monotone T) (hunit : T e = f)
    (φ : stateSpace f) : stateSpace e :=
  ⟨WeakDual.toStrongDual.symm ((WeakDual.toStrongDual φ.1).comp T),
    fun _ _ hab => φ.2.1 (hT hab), by simp [hunit, φ.2.2]⟩

@[simp]
theorem statePullback_apply {e : E} {f : F} (T : E →L[ℝ] F) (hT : Monotone T) (hunit : T e = f)
    (φ : stateSpace f) (a : E) : (statePullback T hT hunit φ).1 a = φ.1 (T a) := (rfl)

/-- Pullback of states along a unital monotone continuous linear map is weak-star continuous. -/
theorem continuous_statePullback {e : E} {f : F} (T : E →L[ℝ] F) (hT : Monotone T)
    (hunit : T e = f) : Continuous (statePullback T hT hunit) := by
  refine Continuous.subtype_mk ?_ _
  refine WeakDual.continuous_of_continuous_eval fun a => ?_
  simpa using continuous_eval_stateSpace (e := f) (T a)

/-- Pulling back along the identity map fixes every state. -/
@[simp]
theorem statePullback_id {e : E} (φ : stateSpace e) :
    statePullback (ContinuousLinearMap.id ℝ E) monotone_id rfl φ = φ :=
  Subtype.ext (DFunLike.ext _ _ fun a => by
    simpa using statePullback_apply (ContinuousLinearMap.id ℝ E) monotone_id rfl φ a)

/-- Pulling back along a composition `S.comp T` reverses the order of composition: it applies the
pullback along `S` first, then the pullback along `T`. -/
theorem statePullback_comp {e : E} {f : F} {g : G}
    (S : F →L[ℝ] G) (hS : Monotone S) (hSu : S f = g)
    (T : E →L[ℝ] F) (hT : Monotone T) (hTu : T e = f) (φ : stateSpace g) :
    statePullback (S.comp T) (hS.comp hT) (by simp [hTu, hSu]) φ =
      statePullback T hT hTu (statePullback S hS hSu φ) :=
  Subtype.ext (DFunLike.ext _ _ fun a => by
    simpa [statePullback_apply] using
      statePullback_apply (S.comp T) (hS.comp hT) (by simp [hTu, hSu]) φ a)

end Pullback

end OrderUnit

/-! ### Compactness, extension, existence, and completion of states -/

namespace IsOrderUnitNorm

section Compactness

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E] {e : E}

/-- Every state in `OrderUnit.stateSpace e` has strong-dual operator norm `1`. -/
theorem opNorm_eq_one_of_mem_stateSpace (he : IsOrderUnitNorm e) {φ : WeakDual ℝ E}
    (hφ : φ ∈ OrderUnit.stateSpace e) : ‖WeakDual.toStrongDual φ‖ = 1 := by
  simpa [hφ.2] using he.opNorm_functional_eq_apply (φ := WeakDual.toStrongDual φ) hφ.1

/-- Evaluation of a state at `a : E` is bounded in absolute value by `‖a‖`. -/
theorem abs_apply_le_norm_of_mem_stateSpace (he : IsOrderUnitNorm e) {φ : WeakDual ℝ E}
    (hφ : φ ∈ OrderUnit.stateSpace e) (a : E) : |φ a| ≤ ‖a‖ := by
  have h := (WeakDual.toStrongDual φ).le_opNorm a
  simpa [he.opNorm_eq_one_of_mem_stateSpace hφ, Real.norm_eq_abs] using h

/-- A weak-star dual functional belongs to `OrderUnit.stateSpace e` if and only if its strong-dual
operator norm is `1` and it is normalized by `φ e = 1`. -/
theorem mem_stateSpace_iff_opNorm_eq_one [IsOrderedAddMonoid E] (he : IsOrderUnitNorm e)
    {φ : WeakDual ℝ E} :
    φ ∈ OrderUnit.stateSpace e ↔ ‖WeakDual.toStrongDual φ‖ = 1 ∧ φ e = 1 := by
  refine ⟨fun h => ⟨he.opNorm_eq_one_of_mem_stateSpace h, h.2⟩, fun ⟨hnorm, he1⟩ => ?_⟩
  refine ⟨(he.monotone_iff_opNorm_eq_one (φ := WeakDual.toStrongDual φ) he1).mpr hnorm, he1⟩

/-- Every state has a strong-dual representative in the closed unit ball of `StrongDual ℝ E`. -/
theorem stateSpace_subset_closedBall (he : IsOrderUnitNorm e) :
    OrderUnit.stateSpace e ⊆
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) 1 := by
  intro φ hφ
  simp [Metric.mem_closedBall, dist_zero_right, he.opNorm_eq_one_of_mem_stateSpace hφ]

/-- **Compactness of the state space:** `OrderUnit.stateSpace e` is weak-star compact, by
Banach–Alaoglu applied to the closed dual unit ball. -/
theorem isCompact_stateSpace (he : IsOrderUnitNorm e) : IsCompact (OrderUnit.stateSpace e) :=
  (WeakDual.isCompact_closedBall (0 : StrongDual ℝ E) 1).of_isClosed_subset
    (OrderUnit.isClosed_stateSpace e) he.stateSpace_subset_closedBall

end Compactness

/-- **State extension along a unital linear isometry:** every state on `E` extends along any unital
linear isometry `i : E →ₗᵢ[ℝ] F` into an order-unit space `(F, f)`. -/
theorem exists_state_extension_linearIsometry {E F : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [PartialOrder E] [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    [PartialOrder F] [IsOrderedAddMonoid F] {e : E} {f : F} (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (i : E →ₗᵢ[ℝ] F) (hunit : i e = f) {ψ : WeakDual ℝ E}
    (hψ : ψ ∈ OrderUnit.stateSpace e) :
    ∃ φ ∈ OrderUnit.stateSpace f, ∀ a : E, φ (i a) = ψ a := by
  let : NormedAddCommGroup E := NormedAddCommGroup.ofSeparation fun _ => he.eq_zero_of_norm_eq_zero
  obtain ⟨g, hg_comp, hg_norm⟩ :=
    LinearIsometry.exists_extension_norm_eq i (WeakDual.toStrongDual ψ)
  have hg_apply : ∀ a : E, g (i a) = ψ a := fun a => DFunLike.congr_fun hg_comp a
  have hg_one : g f = 1 := by rw [← hunit, hg_apply, hψ.2]
  have hg_norm_one : ‖g‖ = 1 := hg_norm.trans (he.opNorm_eq_one_of_mem_stateSpace hψ)
  refine ⟨WeakDual.toStrongDual.symm g, ?_, hg_apply⟩
  exact (hf.mem_stateSpace_iff_opNorm_eq_one).mpr ⟨hg_norm_one, hg_one⟩

/-- **State extension from a unital subspace:** every state on a real subspace `S` containing `e`
extends to a state on `E` via norm-preserving Hahn–Banach extension. -/
theorem exists_state_extension_submodule {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [PartialOrder E] [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e)
    (S : Submodule ℝ E) (hmem : e ∈ S) {ψ : WeakDual ℝ S}
    (hψ : ψ ∈ OrderUnit.stateSpace (⟨e, hmem⟩ : S)) :
    ∃ φ ∈ OrderUnit.stateSpace e, ∀ x : S, φ x = ψ x :=
  (he.submodule S hmem).exists_state_extension_linearIsometry he S.subtypeₗᵢ rfl hψ

/-- Restriction of states from `E` to a unital subspace `S` is surjective. -/
theorem surjective_statePullback_subtype {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [PartialOrder E] [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e)
    (S : Submodule ℝ E) (hmem : e ∈ S) :
    Function.Surjective (OrderUnit.statePullback (e := (⟨e, hmem⟩ : S)) (f := e)
      S.subtypeL (fun _ _ h => h) rfl) := by
  intro ψ
  obtain ⟨φ, hφ, hext⟩ := he.exists_state_extension_submodule S hmem ψ.2
  exact ⟨⟨φ, hφ⟩, Subtype.ext <| DFunLike.ext _ _ fun x => hext x⟩

/-- **State existence:** every order-unit space admits at least one state. -/
theorem stateSpace_nonempty {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [PartialOrder E] [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e) :
    (OrderUnit.stateSpace e).Nonempty := by
  let i : ℝ →ₗᵢ[ℝ] E :=
    { toFun := fun r => r • e
      map_add' := fun r s => add_smul r s e
      map_smul' := fun r s => mul_smul r s e
      norm_map' := fun r => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [he.norm_smul_self, Real.norm_eq_abs] }
  let idState : WeakDual ℝ ℝ := WeakDual.toStrongDual.symm (ContinuousLinearMap.id ℝ ℝ)
  have hid : idState ∈ OrderUnit.stateSpace (1 : ℝ) := ⟨monotone_id, rfl⟩
  obtain ⟨φ, hφ, -⟩ :=
    IsOrderUnitNorm.real_one.exists_state_extension_linearIsometry he i (one_smul ℝ e) hid
  exact ⟨φ, hφ⟩

end IsOrderUnitNorm

namespace OrderUnitCompletion

/-- Restriction along `coe he` and unique continuous extension define a weak-star homeomorphism
between the states of `OrderUnitCompletion he` and the states of `E`. -/
def stateHomeomorph {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [Preorder E]
    [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e) :
    OrderUnit.stateSpace (coe he e) ≃ₜ OrderUnit.stateSpace e := by
  haveI : CompactSpace (OrderUnit.stateSpace (coe he e)) :=
    isCompact_iff_compactSpace.mp (isOrderUnitNorm he).isCompact_stateSpace
  have hmono : Monotone (coe he).toContinuousLinearMap := fun _ _ h => (coe_le_coe_iff _ _).mpr h
  have hunit : (coe he).toContinuousLinearMap e = coe he e := rfl
  let toFun : OrderUnit.stateSpace (coe he e) → OrderUnit.stateSpace e :=
    OrderUnit.statePullback (coe he).toContinuousLinearMap hmono hunit
  let invFun : OrderUnit.stateSpace e → OrderUnit.stateSpace (coe he e) := fun φ =>
    ⟨WeakDual.toStrongDual.symm (extend he (WeakDual.toStrongDual φ.1)),
      monotone_extend φ.2.1, by simp [φ.2.2]⟩
  have hleft : Function.LeftInverse invFun toFun := by
    intro φ
    apply Subtype.ext
    apply WeakDual.toStrongDual.injective
    dsimp only [invFun]
    rw [WeakDual.toStrongDual.apply_symm_apply]
    exact (extend_unique _ (S := WeakDual.toStrongDual φ.1) fun a => by
      simp [toFun, OrderUnit.statePullback_apply]).symm
  have hright : Function.RightInverse invFun toFun := fun φ =>
    Subtype.ext (DFunLike.ext _ _ fun a => by
      simp [toFun, invFun, OrderUnit.statePullback_apply, extend_coe])
  exact Continuous.homeoOfEquivCompactToT2
    (f := { toFun := toFun, invFun := invFun, left_inv := hleft, right_inv := hright })
    (OrderUnit.continuous_statePullback (coe he).toContinuousLinearMap hmono hunit)

@[simp]
theorem stateHomeomorph_apply {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [Preorder E] [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e)
    (φ : OrderUnit.stateSpace (coe he e)) (a : E) :
    (stateHomeomorph he φ).1 a = φ.1 (coe he a) := (rfl)

@[simp]
theorem stateHomeomorph_symm_apply_coe {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [Preorder E] [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e)
    (φ : OrderUnit.stateSpace e) (a : E) :
    ((stateHomeomorph he).symm φ).1 (coe he a) = φ.1 a :=
  extend_coe (WeakDual.toStrongDual φ.1) a

end OrderUnitCompletion

/-! ### Order separation and norm detection by states -/

namespace IsOrderUnitNorm

section SeparationAndNorm

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e)

include he

/-- **Order determination by states:** `a ≤ b` if and only if `φ a ≤ φ b` for every state `φ`. -/
theorem le_iff_forall_state_le {a b : E} :
    a ≤ b ↔ ∀ φ ∈ OrderUnit.stateSpace e, φ a ≤ φ b := by
  have := he.posSMulMono
  have := he.orderClosedTopology
  rw [TauCeti.le_iff_forall_monotone_dual_le]
  refine ⟨fun h φ hφ => h (WeakDual.toStrongDual φ) hφ.1, fun h f hf => ?_⟩
  have hfe : 0 ≤ f e := by simpa only [map_zero] using hf he.nonneg
  rcases hfe.eq_or_lt with h0 | hpos
  · have hf_norm : ‖f‖ = 0 := (he.opNorm_functional_eq_apply hf).trans h0.symm
    have hf0 : ∀ x : E, f x = 0 := fun x =>
      norm_eq_zero.mp (le_antisymm (by simpa [hf_norm] using f.le_opNorm x) (norm_nonneg _))
    rw [hf0 a, hf0 b]
  · let φ : WeakDual ℝ E := WeakDual.toStrongDual.symm ((f e)⁻¹ • f)
    have hφ_apply (x : E) : φ x = (f e)⁻¹ * f x := by
      rw [← WeakDual.toStrongDual_apply]
      simp [φ]
    have hφ : φ ∈ OrderUnit.stateSpace e := by
      refine ⟨fun x y hxy => ?_, ?_⟩
      · simpa [hφ_apply] using mul_le_mul_of_nonneg_left (hf hxy) (inv_nonneg.mpr hpos.le)
      · simpa [hφ_apply] using inv_mul_cancel₀ hpos.ne'
    have hle := h φ hφ
    rw [hφ_apply, hφ_apply] at hle
    exact le_of_mul_le_mul_left hle (inv_pos.mpr hpos)

/-- **Positivity detection by states:** `0 ≤ a` if and only if `0 ≤ φ a` for every state `φ`. -/
theorem nonneg_iff_forall_state_nonneg {a : E} :
    0 ≤ a ↔ ∀ φ ∈ OrderUnit.stateSpace e, 0 ≤ φ a := by
  simpa only [map_zero] using he.le_iff_forall_state_le (a := 0) (b := a)

/-- **Point separation by states:** two elements are equal if and only if every state agrees on
them. -/
theorem eq_iff_forall_state_eq {a b : E} :
    a = b ↔ ∀ φ ∈ OrderUnit.stateSpace e, φ a = φ b :=
  ⟨fun h _ _ => congrArg _ h, fun h =>
    le_antisymm (he.le_iff_forall_state_le.mpr fun φ hφ => (h φ hφ).le)
      (he.le_iff_forall_state_le.mpr fun φ hφ => (h φ hφ).ge)⟩

/-- **Norm attainment by a state:** for every `a : E`, there exists a state
`φ ∈ OrderUnit.stateSpace e` such that `|φ a| = ‖a‖`. -/
theorem exists_state_abs_apply_eq_norm (a : E) :
    ∃ φ ∈ OrderUnit.stateSpace e, |φ a| = ‖a‖ := by
  have hcont : ContinuousOn (fun φ : WeakDual ℝ E => |φ a|) (OrderUnit.stateSpace e) :=
    (WeakDual.eval_continuous a).abs.continuousOn
  obtain ⟨φ₀, hφ₀, hmax⟩ := he.isCompact_stateSpace.exists_isMaxOn he.stateSpace_nonempty hcont
  refine ⟨φ₀, hφ₀, le_antisymm (he.abs_apply_le_norm_of_mem_stateSpace hφ₀ a) ?_⟩
  rw [he.norm_le_iff a |φ₀ a| (abs_nonneg _)]
  refine ⟨he.le_iff_forall_state_le.mpr fun φ hφ => ?_,
    he.le_iff_forall_state_le.mpr fun φ hφ => ?_⟩
  · have hbound : |φ a| ≤ |φ₀ a| := hmax hφ
    simpa [map_smul, hφ.2] using (abs_le.mp hbound).1
  · have hbound : |φ a| ≤ |φ₀ a| := hmax hφ
    simpa [map_smul, hφ.2] using (abs_le.mp hbound).2

/-- **Norm detection by states (`ℝ`-valued):** `‖a‖ = ⨆ φ : OrderUnit.stateSpace e, |φ.1 a|`. -/
theorem norm_eq_iSup_states (a : E) : ‖a‖ = ⨆ φ : OrderUnit.stateSpace e, |φ.1 a| := by
  have : Nonempty (OrderUnit.stateSpace e) := he.stateSpace_nonempty.to_subtype
  obtain ⟨φ₀, hφ₀, hnorm⟩ := he.exists_state_abs_apply_eq_norm a
  have hbdd : BddAbove (Set.range fun φ : OrderUnit.stateSpace e => |φ.1 a|) :=
    ⟨‖a‖, by rintro _ ⟨φ, rfl⟩; exact he.abs_apply_le_norm_of_mem_stateSpace φ.2 a⟩
  refine le_antisymm ?_ (ciSup_le fun φ => he.abs_apply_le_norm_of_mem_stateSpace φ.2 a)
  rw [← hnorm]
  exact le_ciSup hbdd ⟨φ₀, hφ₀⟩

/-- **Norm detection by states (`ℝ≥0`-valued):** `‖a‖₊ = ⨆ φ : OrderUnit.stateSpace e, ‖φ.1 a‖₊`.
-/
theorem nnNorm_eq_iSup_states (a : E) : ‖a‖₊ = ⨆ φ : OrderUnit.stateSpace e, ‖φ.1 a‖₊ := by
  rw [← NNReal.coe_inj, coe_nnNorm, NNReal.coe_iSup]
  simpa [coe_nnNorm, Real.norm_eq_abs] using he.norm_eq_iSup_states a

end SeparationAndNorm

end IsOrderUnitNorm

/-! ### C⋆-algebra state dictionary

Throughout this section, `A` is a unital C⋆-algebra equipped with a compatible star order,
supplied via `[PartialOrder A] [StarOrderedRing A]`; this applies to `cstarStateRestrict`,
`cstarStateExtend`, and `cstarStateSpaceHomeomorph`. -/

namespace OrderUnit

section CStarStates

variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Restrict a C⋆-algebra state on `A` (with compatible star order `PartialOrder A` and
`StarOrderedRing A`) to a real order-unit state on `selfAdjoint A`. -/
def cstarStateRestrict (ψ : TauCeti.stateSpace A) : OrderUnit.stateSpace (1 : selfAdjoint A) :=
  let f : selfAdjoint A →L[ℝ] ℝ :=
    { toFun := fun a => (ψ.1 a).re
      map_add' := fun a b => by simp
      map_smul' := fun r a => by
        simp [selfAdjoint.val_smul, ← Complex.coe_smul]
      cont := Complex.continuous_re.comp ((WeakDual.toStrongDual ψ.1).continuous.comp
        continuous_subtype_val) }
  -- Local helper lemma unfolding the evaluation of the local `ContinuousLinearMap` literal `f`.
  have hf (x : selfAdjoint A) : f x = (ψ.1 x).re := rfl
  ⟨WeakDual.toStrongDual.symm f,
    fun a b hab => by
      have hpos : 0 ≤ ψ.1 ((b : A) - (a : A)) :=
        map_nonneg_of_mem_stateSpace ψ.2 (sub_nonneg.mpr hab)
      have hre : 0 ≤ (ψ.1 b - ψ.1 a).re := by
        simpa only [map_sub, Complex.zero_re] using (Complex.le_def.mp hpos).1
      simpa [hf, sub_nonneg] using hre,
    by simp [hf, map_one_of_mem_stateSpace ψ.2]⟩

@[simp]
theorem cstarStateRestrict_apply (ψ : TauCeti.stateSpace A) (a : selfAdjoint A) :
    (cstarStateRestrict A ψ).1 a = (ψ.1 a).re := (rfl)

/-- Extend a real order-unit state on `selfAdjoint A` to a C⋆-algebra state on `A` (with
compatible star order `PartialOrder A` and `StarOrderedRing A`) via the Cartesian decomposition
`a = ℜ a + I • ℑ a`. -/
def cstarStateExtend (φ : OrderUnit.stateSpace (1 : selfAdjoint A)) : TauCeti.stateSpace A :=
  let g : A →L[ℂ] ℂ :=
    { toFun := fun a => (φ.1 (ℜ a) : ℂ) + Complex.I * (φ.1 (ℑ a) : ℂ)
      map_add' := fun a b => by simp [map_add]; ring
      map_smul' := fun z a => by
        have hre : φ.1 (ℜ (z • a)) = z.re * φ.1 (ℜ a) - z.im * φ.1 (ℑ a) := by
          simp [realPart_smul, map_sub, map_smul]
        have him : φ.1 (ℑ (z • a)) = z.re * φ.1 (ℑ a) + z.im * φ.1 (ℜ a) := by
          simp [imaginaryPart_smul, map_add, map_smul]
        apply Complex.ext <;> simp [hre, him]
      cont :=
        have hre : Continuous (fun a : A => ℜ a) := Continuous.subtype_mk (by fun_prop) _
        have him : Continuous (fun a : A => ℑ a) :=
          Continuous.subtype_mk (by simp only [skewAdjointPart_apply_coe]; fun_prop) _
        (Complex.continuous_ofReal.comp ((WeakDual.toStrongDual φ.1).continuous.comp hre)).add
          (continuous_const.mul (Complex.continuous_ofReal.comp
            ((WeakDual.toStrongDual φ.1).continuous.comp him))) }
  -- Local helper lemma unfolding the evaluation of the local `ContinuousLinearMap` literal `g`.
  have hg (x : A) : g x = (φ.1 (ℜ x) : ℂ) + Complex.I * (φ.1 (ℑ x) : ℂ) := rfl
  ⟨WeakDual.toStrongDual.symm g,
    mem_stateSpace_iff_map_one.mpr ⟨fun a ha => by
      have hsa : IsSelfAdjoint a := ha.isSelfAdjoint
      have him : ℑ a = 0 := hsa.imaginaryPart
      have hre : 0 ≤ ℜ a := by
        rw [← Subtype.coe_le_coe, hsa.coe_realPart, ZeroMemClass.coe_zero]
        exact ha
      have hre_nonneg : 0 ≤ φ.1 (ℜ a) := stateSpace_apply_nonneg φ.2 hre
      simpa [hg, him, Complex.le_def] using hre_nonneg,
    by
      have hre : ℜ (1 : A) = (1 : selfAdjoint A) :=
        selfAdjoint.realPart_coe (x := (1 : selfAdjoint A))
      have him : ℑ (1 : A) = 0 := selfAdjoint.imaginaryPart_coe (x := (1 : selfAdjoint A))
      simp [hg, hre, him, φ.2.2]⟩⟩

@[simp]
theorem cstarStateExtend_apply (φ : OrderUnit.stateSpace (1 : selfAdjoint A)) (a : A) :
    (cstarStateExtend A φ).1 a = (φ.1 (ℜ a) : ℂ) + Complex.I * (φ.1 (ℑ a) : ℂ) := (rfl)

/-- Restriction to `selfAdjoint A` and unique complex-linear extension via `a = ℜ a + I • ℑ a`
form a weak-star homeomorphism between the C⋆-states `TauCeti.stateSpace A` of a unital
C⋆-algebra `A` (equipped with a compatible star order, supplied as `PartialOrder A` and
`StarOrderedRing A`) and the real order-unit states
`TauCeti.OrderUnit.stateSpace (1 : selfAdjoint A)`. -/
def cstarStateSpaceHomeomorph :
    TauCeti.stateSpace A ≃ₜ OrderUnit.stateSpace (1 : selfAdjoint A) where
  toFun := cstarStateRestrict A
  invFun := cstarStateExtend A
  left_inv ψ := by
    apply Subtype.ext
    apply DFunLike.ext
    intro a
    let ψp : A →ₚ[ℂ] ℂ :=
      PositiveLinearMap.mk₀ (WeakDual.toStrongDual ψ.1 : A →ₗ[ℂ] ℂ)
        fun _ ha => map_nonneg_of_mem_stateSpace ψ.2 ha
    -- `PositiveLinearMap.mk₀` has no evaluation lemma; it evaluates as `ψ.1` by definition.
    have hψp (y : A) : ψp y = ψ.1 y := rfl
    have him_sa : ∀ x : selfAdjoint A, (ψ.1 x).im = 0 := fun x => by
      have h : star (ψp x) = ψp x := by rw [← map_star ψp, x.2.star_eq]
      rw [hψp] at h
      exact Complex.conj_eq_iff_im.mp (by simpa [Complex.star_def] using h)
    have hreal : ∀ x : selfAdjoint A, ((ψ.1 x).re : ℂ) = ψ.1 x := fun x =>
      Complex.ext rfl (by simp [him_sa x])
    have hdecomp : ψ.1 a = ψ.1 (ℜ a) + Complex.I * ψ.1 (ℑ a) := by
      simpa only [map_add, map_smul, smul_eq_mul] using
        congrArg ψ.1 (realPart_add_I_smul_imaginaryPart a).symm
    simp only [cstarStateExtend_apply, cstarStateRestrict_apply, hreal, hdecomp]
  right_inv φ := by
    apply Subtype.ext
    apply DFunLike.ext
    intro a
    simp only [cstarStateRestrict_apply, cstarStateExtend_apply, selfAdjoint.realPart_coe,
      selfAdjoint.imaginaryPart_coe, map_zero, Complex.ofReal_zero, mul_zero, add_zero,
      Complex.ofReal_re]
  continuous_toFun := continuous_induced_rng.mpr <|
    WeakDual.continuous_of_continuous_eval fun a => by
      simpa only [Function.comp_def, cstarStateRestrict_apply] using
        Complex.continuous_re.comp ((WeakDual.eval_continuous (a : A)).comp continuous_subtype_val)
  continuous_invFun := continuous_induced_rng.mpr <|
    WeakDual.continuous_of_continuous_eval fun a => by
      simpa only [Function.comp_def, Pi.add_def, Pi.mul_def, cstarStateExtend_apply] using
        (Complex.continuous_ofReal.comp (continuous_eval_stateSpace (ℜ a))).add
          (continuous_const.mul (Complex.continuous_ofReal.comp
            (continuous_eval_stateSpace (ℑ a))))

@[simp]
theorem cstarStateSpaceHomeomorph_apply (ψ : TauCeti.stateSpace A) (a : selfAdjoint A) :
    (cstarStateSpaceHomeomorph A ψ).1 a = (ψ.1 a).re := (rfl)

@[simp]
theorem cstarStateSpaceHomeomorph_symm_apply (φ : OrderUnit.stateSpace (1 : selfAdjoint A))
    (a : A) :
    ((cstarStateSpaceHomeomorph A).symm φ).1 a =
      (φ.1 (ℜ a) : ℂ) + Complex.I * (φ.1 (ℑ a) : ℂ) := (rfl)

end CStarStates

end OrderUnit

end TauCeti
