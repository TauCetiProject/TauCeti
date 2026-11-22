/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.OpenSet
public import Mathlib.Topology.MetricSpace.Bounded
import TauCeti.Topology.MetricSpace.Holder

/-!
# Exponent and order inclusions for `C^{k,α}(Ω, F)`

This file provides the continuous exponent-lowering inclusions for `TauCeti.CkHolderSpaceOn` and
`TauCeti.CkHolderSpace`, and the whole-space order inclusion `TauCeti.CkHolderSpace.inclusionSuccL`:

* `TauCeti.CkHolderSpaceOn.ofExponentLEL`: for `β ≤ α` on any open set `Ω`,
  `CkHolderSpaceOn k α Ω F →L[ℝ] CkHolderSpaceOn k β Ω F` has operator norm at most `3`, and at
  most `max 1 (diam Ω ^ (α - β))` when `Ω` is bounded (`norm_ofExponentLEL_le_of_isBounded`).
* `TauCeti.CkHolderSpace.ofExponentLEL`: whole-space specialization via `equivTop`, of operator
  norm at most `3`.
* `TauCeti.CkHolderSpace.inclusionSuccL`: whole-space order inclusion
  `CkHolderSpace (k + 1) α E F →L[ℝ] CkHolderSpace k α E F` for `α ≤ 1`, of operator norm at
  most `3`. For the counterexample showing that convexity cannot be dropped on open sets, see
  `TauCeti.not_exists_ckHolderSpaceOn_zero_eq_sign` in `TauCeti.Analysis.Holder.Examples`.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 4.1.
-/

public section

noncomputable section

namespace TauCeti

open TopologicalSpace
open scoped NNReal BoundedContinuousFunction

namespace CkHolderSpaceOn

variable {k : ℕ} {α : ℝ≥0} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : Opens E} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### Decreasing the Hölder exponent -/

private theorem holderOnWith_of_exponent_le {β : ℝ≥0} (hβα : β ≤ α)
    (f : CkHolderSpaceOn k α Ω F) :
    HolderOnWith
        (nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) +
          2 * ‖f.iteratedFDeriv (Fin.last k)‖₊) β
        (_root_.iteratedFDeriv ℝ k f.extend) (Ω : Set E) := by
  have hdiam : ∀ x ∈ (Ω : Set E), ∀ y ∈ (Ω : Set E),
      dist (_root_.iteratedFDeriv ℝ k f.extend x)
        (_root_.iteratedFDeriv ℝ k f.extend y) ≤
        ((2 * ‖f.iteratedFDeriv (Fin.last k)‖₊ : ℝ≥0) : ℝ) := by
    intro x hx y hy
    have hEq (z : Ω) : _root_.iteratedFDeriv ℝ k f.extend z =
        f.iteratedFDeriv (Fin.last k) z := by
      simpa only [Fin.val_last] using f.iteratedFDeriv_extend (Fin.last k) z
    rw [dist_eq_norm, hEq ⟨x, hx⟩, hEq ⟨y, hy⟩]
    have hx' := (f.iteratedFDeriv (Fin.last k)).norm_coe_le_norm ⟨x, hx⟩
    have hy' := (f.iteratedFDeriv (Fin.last k)).norm_coe_le_norm ⟨y, hy⟩
    exact (norm_sub_le _ _).trans (by push_cast; linarith)
  simpa using HolderOnWith.of_le_of_dist_le
    (fun x hx y hy _ ↦ f.holderOnWith_iteratedFDeriv_extend.dist_le hx hy)
    hdiam hβα (by norm_num : (0 : ℝ≥0) < 1)

private theorem holderOnWith_of_bounded (hΩ : Bornology.IsBounded (Ω : Set E)) {β : ℝ≥0}
    (hβα : β ≤ α) (f : CkHolderSpaceOn k α Ω F) :
    HolderOnWith (nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) *
        (Metric.diam (Ω : Set E)).toNNReal ^ ((α : ℝ) - β)) β
      (_root_.iteratedFDeriv ℝ k f.extend) (Ω : Set E) := by
  refine f.holderOnWith_iteratedFDeriv_extend.of_le (fun x hx y hy ↦ ?_) hβα
  rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ Metric.diam_nonneg]
  exact ENNReal.ofReal_le_ofReal (Metric.dist_le_diam_of_mem hΩ hx hy)

private def ofExponentLE {β : ℝ≥0} (hβα : β ≤ α) (f : CkHolderSpaceOn k α Ω F) :
    CkHolderSpaceOn k β Ω F :=
  ofContDiffOn f.extend f.contDiffOn_extend
    (fun _ hi ↦ ⟨‖f‖, fun x ↦ f.norm_iteratedFDeriv_extend_le hi x⟩)
    (HolderWith.memHolder fun x y ↦ holderOnWith_of_exponent_le hβα f x x.property y y.property)

private theorem ofExponentLE_apply {β : ℝ≥0} (hβα : β ≤ α)
    (f : CkHolderSpaceOn k α Ω F) (x : Ω) : ofExponentLE hβα f x = f x :=
  (ofContDiffOn_apply ..).trans (f.extend_apply x)

private theorem iteratedFDeriv_ofExponentLE {β : ℝ≥0} (hβα : β ≤ α)
    (f : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1)) (x : Ω) :
    (ofExponentLE hβα f).iteratedFDeriv i x = f.iteratedFDeriv i x := by
  rw [ofExponentLE, iteratedFDeriv_ofContDiffOn, f.iteratedFDeriv_extend i x]

private theorem norm_ofExponentLE_le {β : ℝ≥0} (hβα : β ≤ α) (f : CkHolderSpaceOn k α Ω F) :
    ‖ofExponentLE hβα f‖ ≤ 3 * ‖f‖ := by
  refine (norm_le_sum_add_of_norm_iteratedFDeriv_le_of_holderWith
    (M := fun i ↦ ‖f.iteratedFDeriv i‖) (fun i ↦ norm_nonneg (f.iteratedFDeriv i))
    (fun i x ↦ ?_)
    (K := nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) +
      2 * ‖f.iteratedFDeriv (Fin.last k)‖₊) (fun x y ↦ ?_)).trans ?_
  · rw [iteratedFDeriv_ofExponentLE]
    exact (f.iteratedFDeriv i).norm_coe_le_norm x
  · rw [iteratedFDeriv_ofExponentLE, iteratedFDeriv_ofExponentLE,
      ← f.iteratedFDeriv_extend (Fin.last k) x, ← f.iteratedFDeriv_extend (Fin.last k) y]
    exact holderOnWith_of_exponent_le hβα f x x.property y y.property
  · have hlast : ‖f.iteratedFDeriv (Fin.last k)‖ ≤ ‖f‖ := f.norm_iteratedFDeriv_le (Fin.last k)
    have hnorm : ‖f‖ = ∑ i : Fin (k + 1), ‖f.iteratedFDeriv i‖ +
        nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) := f.norm_eq
    push_cast
    linarith

private theorem norm_ofExponentLE_le_of_isBounded (hΩ : Bornology.IsBounded (Ω : Set E))
    {β : ℝ≥0} (hβα : β ≤ α) (f : CkHolderSpaceOn k α Ω F) :
    ‖ofExponentLE hβα f‖ ≤
      max 1 (Metric.diam (Ω : Set E) ^ ((α : ℝ) - β)) * ‖f‖ := by
  set C : ℝ := max 1 (Metric.diam (Ω : Set E) ^ ((α : ℝ) - β))
  refine (norm_le_sum_add_of_norm_iteratedFDeriv_le_of_holderWith
    (M := fun i ↦ ‖f.iteratedFDeriv i‖) (fun i ↦ norm_nonneg (f.iteratedFDeriv i))
    (fun i x ↦ ?_)
    (K := nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) *
      (Metric.diam (Ω : Set E)).toNNReal ^ ((α : ℝ) - β)) (fun x y ↦ ?_)).trans ?_
  · rw [iteratedFDeriv_ofExponentLE]
    exact (f.iteratedFDeriv i).norm_coe_le_norm x
  · rw [iteratedFDeriv_ofExponentLE, iteratedFDeriv_ofExponentLE,
      ← f.iteratedFDeriv_extend (Fin.last k) x, ← f.iteratedFDeriv_extend (Fin.last k) y]
    exact holderOnWith_of_bounded hΩ hβα f x x.property y y.property
  · rw [f.norm_eq, mul_add]
    have hsum : ∑ i : Fin (k + 1), ‖f.iteratedFDeriv i‖ ≤
        C * ∑ i : Fin (k + 1), ‖f.iteratedFDeriv i‖ :=
      (one_mul _).symm.trans_le (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Finset.sum_nonneg fun i _ ↦ norm_nonneg (f.iteratedFDeriv i)))
    have htop : ((nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) *
          (Metric.diam (Ω : Set E)).toNNReal ^ ((α : ℝ) - β) : ℝ≥0) : ℝ) ≤
        C * nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) := by
      rw [NNReal.coe_mul, NNReal.coe_rpow, Real.coe_toNNReal _ Metric.diam_nonneg, mul_comm C]
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) (NNReal.coe_nonneg _)
    exact add_le_add hsum htop

/-- Continuous linear inclusion `CkHolderSpaceOn k α Ω F →L[ℝ] CkHolderSpaceOn k β Ω F` for
`β ≤ α` on any open set `Ω`, of operator norm at most `3`. -/
def ofExponentLEL {β : ℝ≥0} (hβα : β ≤ α) :
    CkHolderSpaceOn k α Ω F →L[ℝ] CkHolderSpaceOn k β Ω F :=
  LinearMap.mkContinuous
    { toFun := ofExponentLE hβα
      map_add' f g := ext fun x ↦ by simp [ofExponentLE_apply]
      map_smul' c f := ext fun x ↦ by simp [ofExponentLE_apply] }
    3 (norm_ofExponentLE_le hβα)

/-- Pointwise evaluation of the exponent-lowering inclusion `ofExponentLEL`. -/
@[simp] theorem ofExponentLEL_apply {β : ℝ≥0} (hβα : β ≤ α)
    (f : CkHolderSpaceOn k α Ω F) (x : Ω) : ofExponentLEL hβα f x = f x :=
  ofExponentLE_apply hβα f x

/-- Lowering the Hölder exponent from `α` to `β ≤ α` on any open set has norm at most `3`. -/
theorem norm_ofExponentLEL_le {β : ℝ≥0} (hβα : β ≤ α) :
    ‖ofExponentLEL (k := k) (Ω := Ω) (F := F) hβα‖ ≤ 3 :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- On a bounded open set `Ω`, lowering the Hölder exponent from `α` to `β ≤ α` has operator norm
at most `max 1 (diam Ω ^ (α - β))`. -/
theorem norm_ofExponentLEL_le_of_isBounded (hΩ : Bornology.IsBounded (Ω : Set E)) {β : ℝ≥0}
    (hβα : β ≤ α) :
    ‖ofExponentLEL (k := k) (Ω := Ω) (F := F) hβα‖ ≤
      max 1 (Metric.diam (Ω : Set E) ^ ((α : ℝ) - β)) :=
  ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans (le_max_left _ _))
    (norm_ofExponentLE_le_of_isBounded hΩ hβα)

/-- The exponent-lowering inclusion `ofExponentLEL` is injective. -/
theorem ofExponentLEL_injective {β : ℝ≥0} (hβα : β ≤ α) :
    Function.Injective (ofExponentLEL (k := k) (Ω := Ω) (F := F) hβα) :=
  fun _ _ h ↦ ext fun x ↦ by simpa using DFunLike.congr_fun h x

/-- Lowering the exponent along the reflexive inequality `α ≤ α` is the identity map. -/
@[simp] theorem ofExponentLEL_rfl :
    ofExponentLEL (k := k) (Ω := Ω) (F := F) (le_refl α) =
      ContinuousLinearMap.id ℝ (CkHolderSpaceOn k α Ω F) := by ext f x; simp

/-- Lowering the Hölder exponent along `γ ≤ β ≤ α` composes functorially. -/
@[simp] theorem ofExponentLEL_comp {β γ : ℝ≥0} (hγβ : γ ≤ β) (hβα : β ≤ α) :
    (ofExponentLEL (k := k) (Ω := Ω) (F := F) hγβ).comp (ofExponentLEL hβα) =
      ofExponentLEL (hγβ.trans hβα) := by ext f x; simp

end CkHolderSpaceOn

/-! ### Specializations for `CkHolderSpace` on the whole space -/

namespace CkHolderSpace

variable {k : ℕ} {α : ℝ≥0} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Continuous linear inclusion `CkHolderSpace k α E F →L[ℝ] CkHolderSpace k β E F` on the whole
space for `β ≤ α`, of operator norm at most `3`. -/
def ofExponentLEL {β : ℝ≥0} (hβα : β ≤ α) :
    CkHolderSpace k α E F →L[ℝ] CkHolderSpace k β E F :=
  ((CkHolderSpaceOn.equivTop (k := k) (α := β) (E := E) (F := F)) : _ →L[ℝ] _).comp
    ((CkHolderSpaceOn.ofExponentLEL (k := k) (Ω := (⊤ : Opens E)) (F := F) hβα).comp
      ((CkHolderSpaceOn.equivTop (k := k) (α := α) (E := E) (F := F)).symm : _ →L[ℝ] _))

/-- Pointwise evaluation of the whole-space exponent-lowering inclusion `ofExponentLEL`. -/
@[simp] theorem ofExponentLEL_apply {β : ℝ≥0} (hβα : β ≤ α)
    (g : CkHolderSpace k α E F) (x : E) : ofExponentLEL hβα g x = g x := by simp [ofExponentLEL]

/-- On the whole space, lowering the Hölder exponent from `α` to `β ≤ α` has norm at most `3`. -/
theorem norm_ofExponentLEL_le {β : ℝ≥0} (hβα : β ≤ α) :
    ‖ofExponentLEL (k := k) (E := E) (F := F) hβα‖ ≤ 3 := by
  rw [ofExponentLEL, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]
  exact CkHolderSpaceOn.norm_ofExponentLEL_le hβα

/-- The whole-space exponent-lowering inclusion `ofExponentLEL` is injective. -/
theorem ofExponentLEL_injective {β : ℝ≥0} (hβα : β ≤ α) :
    Function.Injective (ofExponentLEL (k := k) (E := E) (F := F) hβα) :=
  fun _ _ h ↦ ext fun x ↦ by simpa using DFunLike.congr_fun h x

/-- Lowering the exponent along `α ≤ α` on `CkHolderSpace` is the identity map. -/
@[simp] theorem ofExponentLEL_rfl :
    ofExponentLEL (k := k) (E := E) (F := F) (le_refl α) =
      ContinuousLinearMap.id ℝ (CkHolderSpace k α E F) := by ext g x; simp

/-- Lowering the exponent along `γ ≤ β ≤ α` on `CkHolderSpace` composes functorially. -/
@[simp] theorem ofExponentLEL_comp {β γ : ℝ≥0} (hγβ : γ ≤ β) (hβα : β ≤ α) :
    (ofExponentLEL (k := k) (E := E) (F := F) hγβ).comp (ofExponentLEL hβα) =
      ofExponentLEL (hγβ.trans hβα) := by ext g x; simp

/-- Continuous linear inclusion `CkHolderSpace (k + 1) α E F →L[ℝ] CkHolderSpace k α E F` on the
whole space for `α ≤ 1`, of operator norm at most `3`. -/
def inclusionSuccL (hα : α ≤ 1) :
    CkHolderSpace (k + 1) α E F →L[ℝ] CkHolderSpace k α E F :=
  ((CkHolderSpaceOn.equivTop (k := k) (α := α) (E := E) (F := F)) : _ →L[ℝ] _).comp
    ((CkHolderSpaceOn.inclusionSuccL (k := k) (Ω := (⊤ : Opens E)) (F := F)
        convex_univ hα).comp
      ((CkHolderSpaceOn.equivTop (k := k + 1) (α := α) (E := E) (F := F)).symm : _ →L[ℝ] _))

/-- Pointwise evaluation of the whole-space order-lowering inclusion `inclusionSuccL`. -/
@[simp] theorem inclusionSuccL_apply (hα : α ≤ 1) (g : CkHolderSpace (k + 1) α E F) (x : E) :
    inclusionSuccL hα g x = g x := by simp [inclusionSuccL]

/-- On the whole space, lowering the order from `k + 1` to `k` has operator norm at most `3`. -/
theorem norm_inclusionSuccL_le (hα : α ≤ 1) :
    ‖inclusionSuccL (k := k) (E := E) (F := F) hα‖ ≤ 3 := by
  rw [inclusionSuccL, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]
  exact CkHolderSpaceOn.norm_inclusionSuccL_le convex_univ hα

/-- The ambient order-lowering inclusion `CkHolderSpace.inclusionSuccL` is injective. -/
theorem inclusionSuccL_injective (hα : α ≤ 1) :
    Function.Injective (inclusionSuccL (k := k) (E := E) (F := F) hα) :=
  fun _ _ h ↦ ext fun x ↦ by simpa using DFunLike.congr_fun h x

end CkHolderSpace

end TauCeti
