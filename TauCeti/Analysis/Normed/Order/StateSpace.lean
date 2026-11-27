/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
public import TauCeti.Analysis.Normed.Order.OrderUnit
public import TauCeti.Analysis.Normed.Order.PositiveLinearMap
public import TauCeti.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.Convex.Cone.PositiveDual

/-!
# States of an order-unit space

Let `E` be a real ordered vector space with a distinguished element `e`. A *state* of `(E, e)` is
a monotone (equivalently, positive) continuous linear functional `φ` with `φ e = 1`. This file
defines the state space `TauCeti.OrderUnit.stateSpace e` as a subset of the weak-* dual
`WeakDual ℝ E`, so that convexity, closedness and compactness refer to the weak-* topology. It is
the space of points of a compact quantum metric space: the metric geometry of an order-unit space
with a Lipschitz seminorm, in the sense of Rieffel, lives on its states.

Without a norm, the state space is convex and weak-* closed, and its points are exactly the
normalized positive continuous linear functionals `E →P[ℝ] ℝ`. When the norm of `E` is the
order-unit norm of `e` (`TauCeti.IsOrderUnitNorm e`):

* a functional is a state exactly when `‖φ‖ = φ e = 1`;
* states exist, by the Hahn–Banach theorem, and every state of a subspace containing `e` extends
  to a state of `E`;
* the state space is weak-* compact, by the Banach–Alaoglu theorem;
* states detect the order and the norm: `0 ≤ a` exactly when `0 ≤ φ a` for every state `φ`, and
  `‖a‖ = sup_φ |φ a|`, by separating `a` from the closed positive cone with a monotone
  functional (`TauCeti.le_iff_forall_monotone_dual_le`).

The name `stateSpace` lives in the namespace `TauCeti.OrderUnit` because the state space of a
C⋆-algebra, normalized by the norm rather than by a unit, is `TauCeti.stateSpace`.

## Main definitions

* `TauCeti.OrderUnit.stateSpace e`: the monotone functionals in `WeakDual ℝ E` with `φ e = 1`.
* `TauCeti.OrderUnit.stateSpaceEquivPositiveContinuousLinearMap`: bijection between `stateSpace e`
  and `{ω : E →P[ℝ] ℝ // ω e = 1}`.

## Main results

* `TauCeti.OrderUnit.convex_stateSpace`, `TauCeti.OrderUnit.isClosed_stateSpace`: the state space
  is convex and weak-* closed.
* `TauCeti.OrderUnit.mem_stateSpace_iff_exists_positiveContinuousLinearMap`,
  `TauCeti.IsOrderUnitNorm.mem_stateSpace_iff_exists_positiveLinearMap`: states are the
  normalized positive (continuous) linear functionals.
* `TauCeti.OrderUnit.toWeakDual_comp_mem_stateSpace`,
  `ContinuousLinearMap.mapsTo_pullbackFunctional_stateSpace`: states pull back along unital
  monotone continuous linear maps; in particular they restrict to subspaces containing `e`.
* `TauCeti.OrderUnit.toWeakDual_inv_smul_mem_stateSpace`: a monotone functional `g` with
  `0 < g e` normalizes to a state.
* `TauCeti.IsOrderUnitNorm.mem_stateSpace_iff_norm_eq_one_and_apply_eq_one`: `φ` is a state iff
  `‖φ‖ = φ e = 1`.
* `TauCeti.IsOrderUnitNorm.stateSpace_nonempty`: existence of states.
* `TauCeti.IsOrderUnitNorm.exists_extension_mem_stateSpace`: extension of states from subspaces
  containing `e`.
* `TauCeti.IsOrderUnitNorm.isCompact_stateSpace`,
  `TauCeti.IsOrderUnitNorm.compactSpace_stateSpace`: weak-* compactness.
* `TauCeti.IsOrderUnitNorm.nonneg_iff_forall_mem_stateSpace`,
  `TauCeti.IsOrderUnitNorm.le_iff_forall_mem_stateSpace`,
  `TauCeti.IsOrderUnitNorm.eq_iff_forall_mem_stateSpace`: states detect the order and separate
  points.
* `TauCeti.IsOrderUnitNorm.norm_le_iff_forall_mem_stateSpace`,
  `TauCeti.IsOrderUnitNorm.norm_eq_iSup_states`: the norm is the supremum of `|φ a|` over states.
* `TauCeti.OrderUnit.stateSpace_one_real`: the unique state of `(ℝ, 1)`.

## References

* R. V. Kadison, *A representation theory for commutative topological algebra*, Mem. Amer.
  Math. Soc. 7 (1951).
* M. A. Rieffel, *Metrics on state spaces*, Doc. Math. 4 (1999), 559–600, §1.
-/

public section

open Set WeakDual

namespace TauCeti

namespace OrderUnit

section Preorder

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [Preorder E]
  {e : E} {φ : WeakDual ℝ E}

variable (e) in
/-- The **state space** of a real ordered topological vector space `E` with distinguished element
`e`: the monotone continuous linear functionals `φ` with `φ e = 1`, as a subset of the weak-* dual
`WeakDual ℝ E`. When `e` is an order unit, these are the states of the order-unit space
`(E, e)`. -/
def stateSpace : Set (WeakDual ℝ E) :=
  {φ | Monotone φ ∧ φ e = 1}

/-- Membership in the state space unfolds to monotonicity and normalization at `e`. -/
theorem mem_stateSpace_iff : φ ∈ stateSpace e ↔ Monotone φ ∧ φ e = 1 :=
  Iff.rfl

/-- A state is monotone. -/
theorem monotone_of_mem_stateSpace (hφ : φ ∈ stateSpace e) : Monotone φ :=
  hφ.1

/-- A state takes the value `1` at `e`. -/
theorem apply_eq_one_of_mem_stateSpace (hφ : φ ∈ stateSpace e) : φ e = 1 :=
  hφ.2

/-- A state is nonnegative on nonnegative vectors. -/
theorem map_nonneg_of_mem_stateSpace (hφ : φ ∈ stateSpace e) {a : E} (ha : 0 ≤ a) : 0 ≤ φ a := by
  simpa using hφ.1 ha

/-- **Convexity of the state space.** Real convex combinations of states are states. -/
theorem convex_stateSpace : Convex ℝ (stateSpace e) := by
  intro φ hφ ψ hψ s t hs ht hst
  refine ⟨fun a b hab => ?_, ?_⟩
  · simp only [add_apply, smul_apply, smul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (hφ.1 hab) hs)
      (mul_le_mul_of_nonneg_left (hψ.1 hab) ht)
  · simp [hφ.2, hψ.2, hst]

/-- The state space is weak-* closed. -/
theorem isClosed_stateSpace : IsClosed (stateSpace e) :=
  (isClosed_monotone.preimage coeFn_continuous).inter
    (isClosed_eq (eval_continuous e) continuous_const)

/-- **Pullback of states.** Composing a state of `F` with a monotone continuous linear map
`T : E →L[ℝ] F` sending `e` to `f` gives a state of `E`. For the inclusion of a subspace
containing `e`, this is the restriction of states. -/
theorem toWeakDual_comp_mem_stateSpace {F : Type*} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] [Preorder F] {f : F} {T : E →L[ℝ] F} (hT : Monotone T) (hTe : T e = f)
    {φ : WeakDual ℝ F} (hφ : φ ∈ stateSpace f) :
    StrongDual.toWeakDual ((toStrongDual φ).comp T) ∈ stateSpace e :=
  ⟨by simpa [StrongDual.coe_toWeakDual, ContinuousLinearMap.coe_comp, coe_toStrongDual] using
    hφ.1.comp hT, by simpa [hTe] using hφ.2⟩

/-- Composing a state with a unital positive continuous linear map via `pullbackFunctional`
yields a state. -/
theorem _root_.ContinuousLinearMap.mapsTo_pullbackFunctional_stateSpace {F : Type*}
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [Preorder F] {f : F} (T : E →L[ℝ] F)
    (hT : Monotone T) (hTe : T e = f) :
    MapsTo T.pullbackFunctional (stateSpace f) (stateSpace e) := fun φ hφ => by
  rw [← toWeakDual_toStrongDual (T.pullbackFunctional φ), T.toStrongDual_pullbackFunctional]
  exact toWeakDual_comp_mem_stateSpace hT hTe hφ

/-- **Normalization.** A monotone continuous linear functional `g` with `0 < g e`, divided by its
value at `e`, is a state. -/
theorem toWeakDual_inv_smul_mem_stateSpace {g : StrongDual ℝ E} (hg : Monotone g)
    (hge : 0 < g e) : StrongDual.toWeakDual ((g e)⁻¹ • g) ∈ stateSpace e :=
  ⟨fun x y hxy => by simpa using mul_le_mul_of_nonneg_left (hg hxy) (inv_nonneg.2 hge.le),
    by simp [hge.ne']⟩

end Preorder

section PartialOrder

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [PartialOrder E]
  {e : E} {φ : WeakDual ℝ E}

/-- A functional is a state exactly when it is nonnegative on nonnegative vectors and takes the
value `1` at `e`. -/
theorem mem_stateSpace_iff_map_nonneg [IsOrderedAddMonoid E] :
    φ ∈ stateSpace e ↔ (∀ a, 0 ≤ a → 0 ≤ φ a) ∧ φ e = 1 := by
  rw [mem_stateSpace_iff, monotone_iff_map_nonneg]

/-- A positive continuous linear functional is a state exactly when it takes the value `1`
at `e`. -/
@[simp]
theorem toWeakDual_mem_stateSpace_iff {ω : E →P[ℝ] ℝ} :
    StrongDual.toWeakDual (ω : E →L[ℝ] ℝ) ∈ stateSpace e ↔ ω e = 1 := by
  simpa [mem_stateSpace_iff, StrongDual.coe_toWeakDual] using fun _ => OrderHomClass.mono ω

/-- The states of `(E, e)` are exactly the positive continuous linear functionals `E →P[ℝ] ℝ`
with `ω e = 1`, viewed in the weak-* dual. -/
theorem mem_stateSpace_iff_exists_positiveContinuousLinearMap :
    φ ∈ stateSpace e ↔
      ∃ ω : E →P[ℝ] ℝ, ω e = 1 ∧ StrongDual.toWeakDual (ω : E →L[ℝ] ℝ) = φ := by
  refine ⟨fun hφ => ?_, fun ⟨ω, hω, h⟩ => h ▸ toWeakDual_mem_stateSpace_iff.2 hω⟩
  let ω : E →P[ℝ] ℝ :=
    { toLinearMap := (toStrongDual φ : E →ₗ[ℝ] ℝ)
      monotone' := by simpa [coe_toStrongDual] using hφ.1
      cont := (toStrongDual φ).cont }
  exact ⟨ω, hφ.2, toWeakDual_toStrongDual φ⟩

/-- The canonical bijection between `stateSpace e` and normalized positive continuous linear
functionals `{ω : E →P[ℝ] ℝ // ω e = 1}`. -/
noncomputable def stateSpaceEquivPositiveContinuousLinearMap (e : E) :
    stateSpace e ≃ {ω : E →P[ℝ] ℝ // ω e = 1} where
  toFun φ := ⟨⟨⟨(toStrongDual φ.val).toLinearMap, by simpa [coe_toStrongDual] using φ.property.1⟩,
    (toStrongDual φ.val).cont⟩, φ.property.2⟩
  invFun ω := ⟨StrongDual.toWeakDual (ω.val : E →L[ℝ] ℝ),
    toWeakDual_mem_stateSpace_iff.2 ω.property⟩
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

end PartialOrder

end OrderUnit

namespace IsOrderUnitNorm

section State

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  {e a b : E} {r : ℝ} {φ : WeakDual ℝ E}

/-- A state of an order-unit space has norm one. -/
theorem norm_toStrongDual_of_mem_stateSpace (h : IsOrderUnitNorm e)
    (hφ : φ ∈ OrderUnit.stateSpace e) : ‖toStrongDual φ‖ = 1 := by
  rw [ContinuousLinearMap.opNorm_eq_apply_of_monotone (toStrongDual φ)
    (by simpa [coe_toStrongDual] using hφ.1) h.le_norm_smul h.norm_eq_one.le, toStrongDual_apply]
  exact hφ.2

/-- A state of an order-unit space is contractive: `|φ a| ≤ ‖a‖`. -/
theorem abs_apply_le_of_mem_stateSpace (h : IsOrderUnitNorm e)
    (hφ : φ ∈ OrderUnit.stateSpace e) (a : E) : |φ a| ≤ ‖a‖ := by
  simpa [hφ.2] using PositiveLinearMap.abs_apply_le_mul_norm φ hφ.1 h.le_norm_smul a

/-- **Weak-* compactness of the state space**, by the Banach–Alaoglu theorem. -/
theorem isCompact_stateSpace (h : IsOrderUnitNorm e) : IsCompact (OrderUnit.stateSpace e) :=
  (WeakDual.isCompact_closedBall 0 1).of_isClosed_subset OrderUnit.isClosed_stateSpace
    fun φ hφ => by simp [h.norm_toStrongDual_of_mem_stateSpace hφ]

/-- `CompactSpace` witness for `OrderUnit.stateSpace e` as a subtype of `WeakDual ℝ E`. -/
theorem compactSpace_stateSpace (h : IsOrderUnitNorm e) : CompactSpace (OrderUnit.stateSpace e) :=
  isCompact_iff_compactSpace.mp h.isCompact_stateSpace

/-- States correspond to normalized positive linear functionals `E →ₚ[ℝ] ℝ`, via automatic
continuity. -/
theorem mem_stateSpace_iff_exists_positiveLinearMap (he : IsOrderUnitNorm e)
    {φ : WeakDual ℝ E} :
    φ ∈ OrderUnit.stateSpace e ↔ ∃ ω : E →ₚ[ℝ] ℝ, ω e = 1 ∧
      StrongDual.toWeakDual (he.toPositiveContinuousLinearMap isOrderUnitNorm_real_one ω :
        E →L[ℝ] ℝ) = φ := by
  refine ⟨fun hφ => ?_, fun ⟨ω, hω, h⟩ =>
    h ▸ OrderUnit.toWeakDual_mem_stateSpace_iff.2 (by simpa using hω)⟩
  let ω : E →ₚ[ℝ] ℝ :=
    { toLinearMap := (toStrongDual φ).toLinearMap
      monotone' := by simpa [coe_toStrongDual] using hφ.1 }
  have hω_apply (a : E) : ω a = toStrongDual φ a := rfl
  exact ⟨ω, hφ.2, DFunLike.ext _ _ fun a => by simp [hω_apply]⟩

variable [IsOrderedAddMonoid E]

/-- A continuous linear functional on an order-unit space is a state exactly when
`‖φ‖ = φ e = 1`; positivity is then automatic. -/
theorem mem_stateSpace_iff_norm_eq_one_and_apply_eq_one (h : IsOrderUnitNorm e) :
    φ ∈ OrderUnit.stateSpace e ↔ ‖toStrongDual φ‖ = 1 ∧ φ e = 1 := by
  refine ⟨fun hφ => ⟨h.norm_toStrongDual_of_mem_stateSpace hφ, hφ.2⟩, fun ⟨hn, h1⟩ =>
    OrderUnit.mem_stateSpace_iff_map_nonneg.2 ⟨fun a ha => ?_, h1⟩⟩
  rw [← toStrongDual_apply]
  refine LinearMapClass.apply_nonneg_of_abs_apply_le_mul_norm (u := e) (toStrongDual φ)
    (fun g => ?_) (h.nonneg_iff_norm_smul_sub_le.1 ha)
  simpa [h1, hn] using (toStrongDual φ).le_opNorm g

/-- **Existence of states.** An order-unit space has a state, by the Hahn–Banach theorem. -/
theorem stateSpace_nonempty (h : IsOrderUnitNorm e) : (OrderUnit.stateSpace e).Nonempty := by
  -- a functional of norm one attaining the norm `‖e‖ = 1` at `e` is a state
  obtain ⟨g, hg, hge⟩ := exists_dual_vector ℝ e (by simp [h.norm_eq_one])
  exact ⟨StrongDual.toWeakDual g, h.mem_stateSpace_iff_norm_eq_one_and_apply_eq_one.2
    ⟨hg, by simpa [h.norm_eq_one] using hge⟩⟩

/-- **Extension of states.** Every state of a subspace `p` containing `e` extends to a state of
`E`, by the Hahn–Banach theorem. The extension need not be unique. -/
theorem exists_extension_mem_stateSpace (h : IsOrderUnitNorm e) (p : Submodule ℝ E)
    (hp : e ∈ p) {ψ : WeakDual ℝ p} (hψ : ψ ∈ OrderUnit.stateSpace (⟨e, hp⟩ : p)) :
    ∃ φ ∈ OrderUnit.stateSpace e, ∀ x : p, φ x = ψ x := by
  obtain ⟨g, hgx, hg⟩ := exists_extension_norm_eq p (toStrongDual ψ)
  refine ⟨StrongDual.toWeakDual g, h.mem_stateSpace_iff_norm_eq_one_and_apply_eq_one.2 ⟨?_, ?_⟩,
    fun x => by simpa [StrongDual.toWeakDual_apply, toStrongDual_apply] using hgx x⟩
  · rw [StrongDual.toStrongDual_toWeakDual, hg]
    exact (h.submodule p hp).norm_toStrongDual_of_mem_stateSpace hψ
  · simpa using (hgx ⟨e, hp⟩).trans hψ.2

/-- **States detect the order.** A vector of an order-unit space is nonnegative exactly when every
state is nonnegative on it. -/
theorem nonneg_iff_forall_mem_stateSpace (h : IsOrderUnitNorm e) :
    0 ≤ a ↔ ∀ φ ∈ OrderUnit.stateSpace e, 0 ≤ φ a := by
  refine ⟨fun ha φ hφ => OrderUnit.map_nonneg_of_mem_stateSpace hφ ha, fun H => ?_⟩
  have := h.posSMulMono
  have := h.orderClosedTopology
  -- every monotone functional `g` is a positive multiple of a state, or vanishes
  refine le_iff_forall_monotone_dual_le.2 fun g hmono => ?_
  rw [map_zero]
  rcases (by simpa using hmono h.nonneg : 0 ≤ g e).eq_or_lt with hge | hge
  · exact (PositiveLinearMap.apply_eq_zero_of_apply_eq_zero g hmono h.le_norm_smul hge.symm a).ge
  have := H _ (OrderUnit.toWeakDual_inv_smul_mem_stateSpace hmono hge)
  simp only [StrongDual.toWeakDual_apply, smul_apply, smul_eq_mul] at this
  exact (mul_nonneg_iff_of_pos_left (inv_pos.2 hge)).1 this

/-- **States detect the order.** In an order-unit space, `a ≤ b` exactly when `φ a ≤ φ b` for
every state `φ`. -/
theorem le_iff_forall_mem_stateSpace (h : IsOrderUnitNorm e) :
    a ≤ b ↔ ∀ φ ∈ OrderUnit.stateSpace e, φ a ≤ φ b := by
  rw [← sub_nonneg, h.nonneg_iff_forall_mem_stateSpace]
  simp only [map_sub, sub_nonneg]

/-- **States separate points** of an order-unit space. -/
theorem eq_iff_forall_mem_stateSpace (h : IsOrderUnitNorm e) :
    a = b ↔ ∀ φ ∈ OrderUnit.stateSpace e, φ a = φ b :=
  ⟨fun hab _ _ => hab ▸ rfl, fun H =>
    le_antisymm ((h.le_iff_forall_mem_stateSpace).2 fun φ hφ => (H φ hφ).le)
      ((h.le_iff_forall_mem_stateSpace).2 fun φ hφ => (H φ hφ).ge)⟩

/-- **States detect the norm.** For `r ≥ 0`, `‖a‖ ≤ r` exactly when `|φ a| ≤ r` for every
state `φ`. -/
theorem norm_le_iff_forall_mem_stateSpace (h : IsOrderUnitNorm e) (hr : 0 ≤ r) :
    ‖a‖ ≤ r ↔ ∀ φ ∈ OrderUnit.stateSpace e, |φ a| ≤ r := by
  refine ⟨fun ha φ hφ => (h.abs_apply_le_of_mem_stateSpace hφ a).trans ha, fun H =>
    (h.norm_le_iff hr).2 ⟨(h.le_iff_forall_mem_stateSpace).2 fun φ hφ => ?_,
      (h.le_iff_forall_mem_stateSpace).2 fun φ hφ => ?_⟩⟩ <;>
  · simp only [map_neg, map_smul, hφ.2, smul_eq_mul, mul_one]
    linarith [abs_le.1 (H φ hφ)]

/-- **Kadison's norm formula.** The norm of an order-unit space is the supremum of `|φ a|` over
the states `φ`. -/
theorem norm_eq_iSup_states (h : IsOrderUnitNorm e) (a : E) :
    ‖a‖ = ⨆ φ : OrderUnit.stateSpace e, |(φ : WeakDual ℝ E) a| := by
  obtain ⟨φ₀, hφ₀⟩ := h.stateSpace_nonempty
  have : Nonempty (OrderUnit.stateSpace e) := ⟨⟨φ₀, hφ₀⟩⟩
  let g (φ : OrderUnit.stateSpace e) : ℝ := |(φ : WeakDual ℝ E) a|
  have hb : BddAbove (range g) :=
    ⟨‖a‖, by rintro _ ⟨φ, rfl⟩; exact h.abs_apply_le_of_mem_stateSpace φ.property a⟩
  refine le_antisymm ?_ (ciSup_le fun φ => h.abs_apply_le_of_mem_stateSpace φ.property a)
  exact (h.norm_le_iff_forall_mem_stateSpace ((abs_nonneg _).trans (le_ciSup hb ⟨φ₀, hφ₀⟩))).2
    fun φ hφ => le_ciSup (f := g) hb ⟨φ, hφ⟩

end State

end IsOrderUnitNorm

namespace OrderUnit

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
