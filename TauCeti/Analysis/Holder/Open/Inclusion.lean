/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Open.Basic
public import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.Holder.JetBounds
import TauCeti.Topology.MetricSpace.Holder

/-!
# Restriction and continuous inclusions for `C^{k,α}(Ω, F)`

This file constructs the natural continuous linear maps between bounded Hölder spaces on open sets:

* **Domain restriction** `TauCeti.CkHolderOnSpace.restrictL`: for `Ω' ≤ Ω`, restricting from `Ω` to
  `Ω'` is a linear contraction of operator norm at most `1`, without any convexity or boundedness
  hypothesis. Specializing `Ω = ⊤` yields `TauCeti.CkHolderSpace.restrictOpenL` from the ambient
  space `CkHolderSpace k α E F` to `CkHolderOnSpace k α Ω F`.
* **Exponent inclusion** `TauCeti.CkHolderOnSpace.ofExponentLEL`: on any open set `Ω` (bounded or
  unbounded), for `β ≤ α`, `CkHolderOnSpace k α Ω F` embeds continuously into
  `CkHolderOnSpace k β Ω F` with operator norm at most `3`, and with operator norm at most
  `max 1 (diam Ω ^ (α - β))` when `Ω` is bounded (`norm_ofExponentLEL_le_of_isBounded`).
  Specializing `Ω = ⊤` yields `TauCeti.CkHolderSpace.ofExponentLEL`.
* **Order inclusion** `TauCeti.CkHolderOnSpace.ofSuccL`: on a convex open set `Ω`, for `α ≤ 1`,
  `CkHolderOnSpace (k + 1) α Ω F` embeds continuously into `CkHolderOnSpace k α Ω F` with operator
  norm at most `3` (independent of `k`), via the mean-value Hölder estimate
  `ContDiffOn.holderOnWith_iteratedFDeriv_of_lt`. Specializing `Ω = ⊤` gives
  `TauCeti.CkHolderSpace.ofSuccL`.

Finally, `TauCeti.not_exists_ckHolderOnSpace_zero_eq_slitSign` shows that convexity of `Ω` cannot
be dropped in `ofSuccL`: on the bounded disconnected open set `(-1, 0) ∪ (0, 1) ⊆ ℝ`, the locally
constant sign function belongs to `CkHolderOnSpace (k + 1) α` for every `k` and `α` (since all of
its derivatives of positive order vanish on the open set), yet fails to be `α`-Hölder of order `0`
across `0` whenever `0 < α`.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 4.1.
-/

public section

noncomputable section

namespace TauCeti

open Filter Set Topology
open scoped NNReal BoundedContinuousFunction

namespace CkHolderOnSpace

variable {k : ℕ} {α : ℝ≥0} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω Ω' Ω'' : TopologicalSpace.Opens E} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Local shortcut instance for bounded continuous fields of `n`-multilinear maps on an open set
`U`, avoiding synthesis-depth blowup when summing norms indexed by `Fin (k + 1)`. -/
local instance instNormedAddCommGroupBCF (U : TopologicalSpace.Opens E) (n : ℕ) :
    NormedAddCommGroup (U →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

/-! ### Restriction to a smaller open set -/

private def restrict (h : Ω' ≤ Ω) (f : CkHolderOnSpace k α Ω F) : CkHolderOnSpace k α Ω' F :=
  ofContDiffOn f.extendByZero (f.contDiffOn_extendByZero.mono h)
    (fun _ hi ↦ ⟨‖f‖, fun x hx ↦ f.norm_iteratedFDeriv_extendByZero_le hi ⟨x, h hx⟩⟩)
    ⟨_, f.holderOnWith_iteratedFDeriv_extendByZero.mono h⟩

private theorem restrict_apply (h : Ω' ≤ Ω) (f : CkHolderOnSpace k α Ω F) (x : Ω') :
    restrict h f x = f ⟨x.1, h x.2⟩ :=
  (ofContDiffOn_apply ..).trans (f.extendByZero_coe ⟨x.1, h x.2⟩)

private theorem norm_restrict_le (h : Ω' ≤ Ω) (f : CkHolderOnSpace k α Ω F) :
    ‖restrict h f‖ ≤ ‖f‖ := by
  have heq : ∀ x : Ω', f.extendByZero x = restrict h f x := fun x ↦ (ofContDiffOn_apply ..).symm
  rw [norm_eq, f.norm_eq]
  gcongr with i
  · refine (BoundedContinuousFunction.norm_le (norm_nonneg (f.iteratedFDeriv i))).2 fun x ↦ ?_
    rw [← (restrict h f).iteratedFDeriv_of_eq heq i x,
      f.iteratedFDeriv_extendByZero i ⟨x.1, h x.2⟩]
    exact (f.iteratedFDeriv i).norm_coe_le_norm ⟨x.1, h x.2⟩
  · have hdom : ((restrict h f).iteratedFDeriv (Fin.last k) : Ω' → E [×k]→L[ℝ] F) =
        (Ω' : Set E).domRestrict (_root_.iteratedFDeriv ℝ k f.extendByZero) :=
      funext fun x ↦ ((restrict h f).iteratedFDeriv_of_eq heq (Fin.last k) x).symm
    rw [hdom]
    exact_mod_cast (f.holderOnWith_iteratedFDeriv_extendByZero.mono h).holderWith.nnholderNorm_le

/-- Restriction from `Ω` to an open subset `Ω' ≤ Ω` as a contraction (`‖·‖ ≤ 1`). -/
def restrictL (h : Ω' ≤ Ω) : CkHolderOnSpace k α Ω F →L[ℝ] CkHolderOnSpace k α Ω' F :=
  LinearMap.mkContinuous
    { toFun := restrict h
      map_add' f g := ext fun x ↦ by simp [restrict_apply]
      map_smul' c f := ext fun x ↦ by simp [restrict_apply] } 1 fun f ↦ by
        rw [one_mul]; exact norm_restrict_le h f

/-- Pointwise evaluation of the restriction map `restrictL`. -/
@[simp] theorem restrictL_apply (h : Ω' ≤ Ω) (f : CkHolderOnSpace k α Ω F) (x : Ω') :
    restrictL h f x = f ⟨x.1, h x.2⟩ := restrict_apply h f x

/-- Restriction to an open subset has operator norm at most `1`. -/
theorem norm_restrictL_le_one (h : Ω' ≤ Ω) : ‖restrictL (k := k) (α := α) (F := F) h‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Restriction along the reflexive inclusion `Ω ≤ Ω` is the identity map. -/
@[simp] theorem restrictL_rfl :
    restrictL (le_refl Ω) = ContinuousLinearMap.id ℝ (CkHolderOnSpace k α Ω F) := by ext f x; simp

/-- Restriction along `Ω'' ≤ Ω' ≤ Ω` composes functorially. -/
@[simp] theorem restrictL_comp (h₁ : Ω'' ≤ Ω') (h₂ : Ω' ≤ Ω) :
    (restrictL (k := k) (α := α) (F := F) h₁).comp (restrictL h₂) = restrictL (h₁.trans h₂) := by
  ext f x; simp

/-! ### Decreasing the Hölder exponent -/

private theorem domRestrict_iteratedFDeriv_extendByZero (f : CkHolderOnSpace k α Ω F) :
    (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) =
      (Ω : Set E).domRestrict (_root_.iteratedFDeriv ℝ k f.extendByZero) :=
  funext fun x ↦ by
    simpa only [Set.domRestrict_apply, Fin.val_last] using
      (f.iteratedFDeriv_extendByZero (Fin.last k) x).symm

private theorem holderOnWith_of_exponent_le {β : ℝ≥0} (hβα : β ≤ α)
    (f : CkHolderOnSpace k α Ω F) :
    HolderOnWith
        (nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) +
          2 * ‖f.iteratedFDeriv (Fin.last k)‖₊) β
        (_root_.iteratedFDeriv ℝ k f.extendByZero) (Ω : Set E) := by
  have hdiam : ∀ x ∈ (Ω : Set E), ∀ y ∈ (Ω : Set E),
      dist (_root_.iteratedFDeriv ℝ k f.extendByZero x)
        (_root_.iteratedFDeriv ℝ k f.extendByZero y) ≤
        ((2 * ‖f.iteratedFDeriv (Fin.last k)‖₊ : ℝ≥0) : ℝ) := by
    intro x hx y hy
    have hEq (z : Ω) : _root_.iteratedFDeriv ℝ k f.extendByZero z =
        f.iteratedFDeriv (Fin.last k) z := by
      simpa only [Fin.val_last] using f.iteratedFDeriv_extendByZero (Fin.last k) z
    rw [dist_eq_norm, hEq ⟨x, hx⟩, hEq ⟨y, hy⟩]
    have hx' := (f.iteratedFDeriv (Fin.last k)).norm_coe_le_norm ⟨x, hx⟩
    have hy' := (f.iteratedFDeriv (Fin.last k)).norm_coe_le_norm ⟨y, hy⟩
    exact (norm_sub_le _ _).trans (by push_cast; linarith)
  simpa using HolderOnWith.of_le_of_dist_le
    (fun x hx y hy _ ↦ f.holderOnWith_iteratedFDeriv_extendByZero.dist_le hx hy)
    hdiam hβα (by norm_num : (0 : ℝ≥0) < 1)

private theorem holderOnWith_of_bounded (hΩ : Bornology.IsBounded (Ω : Set E)) {β : ℝ≥0}
    (hβα : β ≤ α) (f : CkHolderOnSpace k α Ω F) :
    HolderOnWith (nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) *
        (Metric.diam (Ω : Set E)).toNNReal ^ ((α : ℝ) - β)) β
      (_root_.iteratedFDeriv ℝ k f.extendByZero) (Ω : Set E) := by
  refine f.holderOnWith_iteratedFDeriv_extendByZero.of_le (fun x hx y hy ↦ ?_) hβα
  rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ Metric.diam_nonneg]
  exact ENNReal.ofReal_le_ofReal (Metric.dist_le_diam_of_mem hΩ hx hy)

private def ofExponentLE {β : ℝ≥0} (hβα : β ≤ α) (f : CkHolderOnSpace k α Ω F) :
    CkHolderOnSpace k β Ω F :=
  ofContDiffOn f.extendByZero f.contDiffOn_extendByZero
    (fun _ hi ↦ ⟨‖f‖, fun x hx ↦ f.norm_iteratedFDeriv_extendByZero_le hi ⟨x, hx⟩⟩)
    ⟨_, holderOnWith_of_exponent_le hβα f⟩

private theorem ofExponentLE_apply {β : ℝ≥0} (hβα : β ≤ α)
    (f : CkHolderOnSpace k α Ω F) (x : Ω) : ofExponentLE hβα f x = f x :=
  (ofContDiffOn_apply ..).trans (f.extendByZero_coe x)

private theorem iteratedFDeriv_ofExponentLE {β : ℝ≥0} (hβα : β ≤ α)
    (f : CkHolderOnSpace k α Ω F) (i : Fin (k + 1)) :
    (ofExponentLE hβα f).iteratedFDeriv i = f.iteratedFDeriv i := by
  have heq : ∀ x : Ω, f.extendByZero x = ofExponentLE hβα f x :=
    fun x ↦ (ofContDiffOn_apply ..).symm
  exact BoundedContinuousFunction.ext fun x ↦
    ((ofExponentLE hβα f).iteratedFDeriv_of_eq heq i x).symm.trans
      (f.iteratedFDeriv_extendByZero i x)

private theorem norm_ofExponentLE_le {β : ℝ≥0} (hβα : β ≤ α) (f : CkHolderOnSpace k α Ω F) :
    ‖ofExponentLE hβα f‖ ≤ 3 * ‖f‖ := by
  have htop : (nnHolderNorm β (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) : ℝ) ≤
      nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) +
        2 * ‖f.iteratedFDeriv (Fin.last k)‖ := by
    conv_lhs => rw [domRestrict_iteratedFDeriv_extendByZero]
    exact_mod_cast (holderOnWith_of_exponent_le hβα f).holderWith.nnholderNorm_le
  have hlast : ‖f.iteratedFDeriv (Fin.last k)‖ ≤ ‖f‖ := f.norm_iteratedFDeriv_le (Fin.last k)
  rw [norm_eq]
  simp_rw [iteratedFDeriv_ofExponentLE]
  linarith [f.norm_eq]

private theorem norm_ofExponentLE_le_of_isBounded (hΩ : Bornology.IsBounded (Ω : Set E))
    {β : ℝ≥0} (hβα : β ≤ α) (f : CkHolderOnSpace k α Ω F) :
    ‖ofExponentLE hβα f‖ ≤
      max 1 (Metric.diam (Ω : Set E) ^ ((α : ℝ) - β)) * ‖f‖ := by
  set C : ℝ := max 1 (Metric.diam (Ω : Set E) ^ ((α : ℝ) - β))
  have htop : (nnHolderNorm β (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) : ℝ) ≤
      C * nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) := by
    conv_lhs => rw [domRestrict_iteratedFDeriv_extendByZero]
    have hle : (nnHolderNorm β
        ((Ω : Set E).domRestrict (_root_.iteratedFDeriv ℝ k f.extendByZero)) : ℝ) ≤
        nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) *
          Metric.diam (Ω : Set E) ^ ((α : ℝ) - β) :=
      (NNReal.coe_le_coe.mpr (holderOnWith_of_bounded hΩ hβα f).holderWith.nnholderNorm_le).trans_eq
        (by rw [NNReal.coe_mul, NNReal.coe_rpow, Real.coe_toNNReal _ Metric.diam_nonneg])
    exact hle.trans ((mul_comm _ _).trans_le
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (NNReal.coe_nonneg _)))
  rw [norm_eq, f.norm_eq, mul_add]
  simp_rw [iteratedFDeriv_ofExponentLE]
  exact add_le_add ((one_mul _).symm.trans_le
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _))) htop

/-- Continuous linear inclusion `CkHolderOnSpace k α Ω F →L[ℝ] CkHolderOnSpace k β Ω F` for
`β ≤ α` on any open set `Ω`, of operator norm at most `3`. -/
def ofExponentLEL {β : ℝ≥0} (hβα : β ≤ α) :
    CkHolderOnSpace k α Ω F →L[ℝ] CkHolderOnSpace k β Ω F :=
  LinearMap.mkContinuous
    { toFun := ofExponentLE hβα
      map_add' f g := ext fun x ↦ by simp [ofExponentLE_apply]
      map_smul' c f := ext fun x ↦ by simp [ofExponentLE_apply] }
    3 (norm_ofExponentLE_le hβα)

/-- Pointwise evaluation of the exponent-lowering inclusion `ofExponentLEL`. -/
@[simp] theorem ofExponentLEL_apply {β : ℝ≥0} (hβα : β ≤ α)
    (f : CkHolderOnSpace k α Ω F) (x : Ω) : ofExponentLEL hβα f x = f x :=
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
      ContinuousLinearMap.id ℝ (CkHolderOnSpace k α Ω F) := by ext f x; simp

/-- Lowering the Hölder exponent along `γ ≤ β ≤ α` composes functorially. -/
@[simp] theorem ofExponentLEL_comp {β γ : ℝ≥0} (hγβ : γ ≤ β) (hβα : β ≤ α) :
    (ofExponentLEL (k := k) (Ω := Ω) (F := F) hγβ).comp (ofExponentLEL hβα) =
      ofExponentLEL (hγβ.trans hβα) := by ext f x; simp

/-! ### Lowering the derivative order on a convex open set -/

/-- On a convex open set `Ω`, when `α ≤ 1`, every iterated derivative through order `k` of
`f.extendByZero` is `α`-Hölder on `Ω` with constant `3 * ‖f‖₊`. -/
theorem holderOnWith_iteratedFDeriv_extendByZero_of_le (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1)
    (f : CkHolderOnSpace k α Ω F) {j : ℕ} (hj : j ≤ k) :
    HolderOnWith (3 * ‖f‖₊) α (_root_.iteratedFDeriv ℝ j f.extendByZero) (Ω : Set E) := by
  rcases hj.eq_or_lt with rfl | hj
  · exact f.holderOnWith_iteratedFDeriv_extendByZero.mono_const (by
      exact_mod_cast (f.nnHolderNorm_iteratedFDeriv_le.trans
        (by nlinarith [norm_nonneg f] : ‖f‖ ≤ 3 * ‖f‖)))
  · have h := f.contDiffOn_extendByZero.holderOnWith_iteratedFDeriv_of_lt Ω.isOpen hΩ
      (M := ‖f‖₊) (L := ‖f‖₊) hj hα
      (fun x hx ↦ f.norm_iteratedFDeriv_extendByZero_le hj.le ⟨x, hx⟩)
      (fun x hx ↦ f.norm_iteratedFDeriv_extendByZero_le hj ⟨x, hx⟩)
    convert h using 1; ring

private theorem holderOnWith_iteratedFDeriv_of_succ (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1)
    (f : CkHolderOnSpace (k + 1) α Ω F) :
    HolderOnWith (‖f.iteratedFDeriv (Fin.last (k + 1))‖₊ +
        2 * ‖f.iteratedFDeriv (Fin.last k).castSucc‖₊) α
      (_root_.iteratedFDeriv ℝ k f.extendByZero) (Ω : Set E) :=
  f.contDiffOn_extendByZero.holderOnWith_iteratedFDeriv_of_lt Ω.isOpen hΩ (Nat.lt_succ_self k) hα
    (fun x hx ↦ by
      have h := f.iteratedFDeriv_extendByZero (Fin.last k).castSucc ⟨x, hx⟩
      simp only [Fin.val_castSucc, Fin.val_last] at h
      rw [h]
      exact (f.iteratedFDeriv (Fin.last k).castSucc).norm_coe_le_norm ⟨x, hx⟩)
    (fun x hx ↦ by
      have h := f.iteratedFDeriv_extendByZero (Fin.last (k + 1)) ⟨x, hx⟩
      simp only [Fin.val_last] at h
      rw [h]
      exact (f.iteratedFDeriv (Fin.last (k + 1))).norm_coe_le_norm ⟨x, hx⟩)

private def ofSucc (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1)
    (f : CkHolderOnSpace (k + 1) α Ω F) : CkHolderOnSpace k α Ω F :=
  ofContDiffOn f.extendByZero (f.contDiffOn_extendByZero.of_le (by norm_cast; omega))
    (fun _ hi ↦ ⟨‖f‖, fun x hx ↦ f.norm_iteratedFDeriv_extendByZero_le (by omega) ⟨x, hx⟩⟩)
    ⟨_, holderOnWith_iteratedFDeriv_of_succ hΩ hα f⟩

private theorem ofSucc_apply (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1)
    (f : CkHolderOnSpace (k + 1) α Ω F) (x : Ω) :
    ofSucc hΩ hα f x = f x :=
  (ofContDiffOn_apply ..).trans (f.extendByZero_coe x)

private theorem norm_ofSucc_le (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1)
    (f : CkHolderOnSpace (k + 1) α Ω F) :
    ‖ofSucc hΩ hα f‖ ≤ 3 * ‖f‖ := by
  have heq : ∀ x : Ω, f.extendByZero x = ofSucc hΩ hα f x := fun x ↦ (ofContDiffOn_apply ..).symm
  have hfield (i : Fin (k + 1)) :
      (ofSucc hΩ hα f).iteratedFDeriv i = f.iteratedFDeriv i.castSucc :=
    BoundedContinuousFunction.ext fun x ↦
      ((ofSucc hΩ hα f).iteratedFDeriv_of_eq heq i x).symm.trans
        (f.iteratedFDeriv_extendByZero i.castSucc x)
  have htop : (nnHolderNorm α ((ofSucc hΩ hα f).iteratedFDeriv (Fin.last k) :
        Ω → E [×k]→L[ℝ] F) : ℝ) ≤
      ‖f.iteratedFDeriv (Fin.last (k + 1))‖ + 2 * ‖f.iteratedFDeriv (Fin.last k).castSucc‖ := by
    have hdom : ((ofSucc hΩ hα f).iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) =
        (Ω : Set E).domRestrict (_root_.iteratedFDeriv ℝ k f.extendByZero) :=
      funext fun x ↦ ((ofSucc hΩ hα f).iteratedFDeriv_of_eq heq (Fin.last k) x).symm
    rw [hdom]
    exact_mod_cast (holderOnWith_iteratedFDeriv_of_succ hΩ hα f).holderWith.nnholderNorm_le
  have hsum : (∑ i : Fin (k + 1), ‖f.iteratedFDeriv i.castSucc‖) +
      ‖f.iteratedFDeriv (Fin.last (k + 1))‖ ≤ ‖f‖ := by
    rw [← Fin.sum_univ_castSucc (f := fun i : Fin (k + 2) ↦ ‖f.iteratedFDeriv i‖), f.norm_eq]
    exact le_add_of_nonneg_right (NNReal.coe_nonneg _)
  have hlast : ‖f.iteratedFDeriv (Fin.last k).castSucc‖ ≤ ‖f‖ := f.norm_iteratedFDeriv_le _
  have hnorm : ‖ofSucc hΩ hα f‖ ≤ (∑ i : Fin (k + 1), ‖f.iteratedFDeriv i.castSucc‖) +
      (‖f.iteratedFDeriv (Fin.last (k + 1))‖ + 2 * ‖f.iteratedFDeriv (Fin.last k).castSucc‖) := by
    rw [norm_eq]
    refine add_le_add ?_ htop
    simp_rw [hfield]
    exact le_rfl
  linarith

/-- Continuous linear inclusion `CkHolderOnSpace (k + 1) α Ω F →L[ℝ] CkHolderOnSpace k α Ω F` on a
convex open set `Ω` for `α ≤ 1`, of operator norm at most `3`. -/
def ofSuccL (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) :
    CkHolderOnSpace (k + 1) α Ω F →L[ℝ] CkHolderOnSpace k α Ω F :=
  LinearMap.mkContinuous
    { toFun := ofSucc hΩ hα
      map_add' f g := ext fun x ↦ by simp [ofSucc_apply]
      map_smul' c f := ext fun x ↦ by simp [ofSucc_apply] } 3 (norm_ofSucc_le hΩ hα)

/-- Pointwise evaluation of the order-lowering inclusion `ofSuccL`. -/
@[simp] theorem ofSuccL_apply (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1)
    (f : CkHolderOnSpace (k + 1) α Ω F) (x : Ω) : ofSuccL hΩ hα f x = f x :=
  ofSucc_apply hΩ hα f x

/-- Lowering the order from `k + 1` to `k` on a convex open set has norm at most `3`. -/
theorem norm_ofSuccL_le (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) :
    ‖ofSuccL (k := k) (F := F) hΩ hα‖ ≤ 3 :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- The order-lowering inclusion `ofSuccL` is injective. -/
theorem ofSuccL_injective (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) :
    Function.Injective (ofSuccL (k := k) (F := F) hΩ hα) :=
  fun _ _ h ↦ ext fun x ↦ by simpa using DFunLike.congr_fun h x

end CkHolderOnSpace

/-! ### Specializations for `CkHolderSpace` on the whole space -/

namespace CkHolderSpace

variable {k : ℕ} {α : ℝ≥0} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω Ω' : TopologicalSpace.Opens E} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem norm_conj_equivTop_le {k₁ k₂ : ℕ} {α₁ α₂ : ℝ≥0} {C : ℝ}
    (L : CkHolderOnSpace k₁ α₁ (⊤ : TopologicalSpace.Opens E) F →L[ℝ]
      CkHolderOnSpace k₂ α₂ (⊤ : TopologicalSpace.Opens E) F) (hL : ‖L‖ ≤ C) :
    ‖CkHolderOnSpace.equivTop.toLinearIsometry.toContinuousLinearMap.comp
      (L.comp CkHolderOnSpace.equivTop.symm.toLinearIsometry.toContinuousLinearMap)‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg L).trans hL) fun g ↦ by
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.norm_map]
    exact (L.le_opNorm _).trans (by rw [LinearIsometryEquiv.norm_map]; gcongr)

/-- Restriction from `CkHolderSpace k α E F` to an open set `Ω`, of operator norm at most `1`. -/
def restrictOpenL (Ω : TopologicalSpace.Opens E) :
    CkHolderSpace k α E F →L[ℝ] CkHolderOnSpace k α Ω F :=
  (CkHolderOnSpace.restrictL (le_top : Ω ≤ ⊤)).comp
    CkHolderOnSpace.equivTop.symm.toLinearIsometry.toContinuousLinearMap

/-- Pointwise evaluation of restriction from `CkHolderSpace` to an open set `Ω`. -/
@[simp] theorem restrictOpenL_apply (Ω : TopologicalSpace.Opens E)
    (g : CkHolderSpace k α E F) (x : Ω) : restrictOpenL Ω g x = g x := by simp [restrictOpenL]

/-- Restriction from `CkHolderSpace k α E F` to `CkHolderOnSpace k α Ω F` has norm at most `1`. -/
theorem norm_restrictOpenL_le_one (Ω : TopologicalSpace.Opens E) :
    ‖restrictOpenL (k := k) (α := α) (F := F) Ω‖ ≤ 1 :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans <| by
    simpa using mul_le_mul (CkHolderOnSpace.norm_restrictL_le_one (le_top : Ω ≤ ⊤))
      (LinearIsometry.norm_toContinuousLinearMap_le _) (norm_nonneg _) zero_le_one

/-- Restricting from `E` to `Ω` and then to `Ω' ≤ Ω` agrees with restricting directly to `Ω'`. -/
@[simp] theorem restrictL_comp_restrictOpenL (h : Ω' ≤ Ω) :
    (CkHolderOnSpace.restrictL (k := k) (α := α) (F := F) h).comp (restrictOpenL Ω) =
      restrictOpenL Ω' := by ext g x; simp

/-- Continuous linear inclusion `CkHolderSpace k α E F →L[ℝ] CkHolderSpace k β E F` on the whole
space for `β ≤ α`, of operator norm at most `3`. -/
def ofExponentLEL {β : ℝ≥0} (hβα : β ≤ α) :
    CkHolderSpace k α E F →L[ℝ] CkHolderSpace k β E F :=
  CkHolderOnSpace.equivTop.toLinearIsometry.toContinuousLinearMap.comp
    ((CkHolderOnSpace.ofExponentLEL (Ω := (⊤ : TopologicalSpace.Opens E)) hβα).comp
      CkHolderOnSpace.equivTop.symm.toLinearIsometry.toContinuousLinearMap)

/-- Pointwise evaluation of the whole-space exponent-lowering inclusion `ofExponentLEL`. -/
@[simp] theorem ofExponentLEL_apply {β : ℝ≥0} (hβα : β ≤ α)
    (g : CkHolderSpace k α E F) (x : E) : ofExponentLEL hβα g x = g x := by simp [ofExponentLEL]

/-- On the whole space, lowering the Hölder exponent from `α` to `β ≤ α` has norm at most `3`. -/
theorem norm_ofExponentLEL_le {β : ℝ≥0} (hβα : β ≤ α) :
    ‖ofExponentLEL (k := k) (E := E) (F := F) hβα‖ ≤ 3 :=
  norm_conj_equivTop_le _ (CkHolderOnSpace.norm_ofExponentLEL_le hβα)

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
def ofSuccL (hα : α ≤ 1) :
    CkHolderSpace (k + 1) α E F →L[ℝ] CkHolderSpace k α E F :=
  CkHolderOnSpace.equivTop.toLinearIsometry.toContinuousLinearMap.comp
    ((CkHolderOnSpace.ofSuccL (Ω := (⊤ : TopologicalSpace.Opens E)) convex_univ hα).comp
      CkHolderOnSpace.equivTop.symm.toLinearIsometry.toContinuousLinearMap)

/-- Pointwise evaluation of the whole-space order-lowering inclusion `ofSuccL`. -/
@[simp] theorem ofSuccL_apply (hα : α ≤ 1) (g : CkHolderSpace (k + 1) α E F) (x : E) :
    ofSuccL hα g x = g x := by simp [ofSuccL]

/-- On the whole space, lowering the order from `k + 1` to `k` has operator norm at most `3`. -/
theorem norm_ofSuccL_le (hα : α ≤ 1) : ‖ofSuccL (k := k) (E := E) (F := F) hα‖ ≤ 3 :=
  norm_conj_equivTop_le _ (CkHolderOnSpace.norm_ofSuccL_le convex_univ hα)

/-- The ambient order-lowering inclusion `CkHolderSpace.ofSuccL` is injective. -/
theorem ofSuccL_injective (hα : α ≤ 1) :
    Function.Injective (ofSuccL (k := k) (E := E) (F := F) hα) :=
  fun _ _ h ↦ ext fun x ↦ by simpa using DFunLike.congr_fun h x

end CkHolderSpace

/-! ### Non-convex counterexample to order inclusion -/

/-- The punctured interval `(-1, 0) ∪ (0, 1)`, a bounded disconnected open subset of `ℝ`. -/
def slitUnitInterval : TopologicalSpace.Opens ℝ :=
  ⟨Set.Ioo (-1) 0 ∪ Set.Ioo 0 1, isOpen_Ioo.union isOpen_Ioo⟩

private def signFn (x : ℝ) : ℝ := if 0 < x then 1 else -1

private theorem signFn_eventuallyEq_const {x : ℝ} (hx : x ∈ (slitUnitInterval : Set ℝ)) :
    ∃ c : ℝ, ‖c‖ = 1 ∧ signFn =ᶠ[𝓝 x] fun _ ↦ c := by
  rcases hx with hx | hx
  · refine ⟨-1, by norm_num, ?_⟩
    filter_upwards [isOpen_Iio.mem_nhds hx.2] with y (hy : y < 0)
    simp [signFn, not_lt.mpr hy.le]
  · refine ⟨1, by norm_num, ?_⟩
    filter_upwards [isOpen_Ioi.mem_nhds hx.1] with y (hy : 0 < y)
    simp [signFn, hy]

private theorem iteratedFDeriv_signFn_pos {i : ℕ} (hi : i ≠ 0) {x : ℝ}
    (hx : x ∈ (slitUnitInterval : Set ℝ)) :
    _root_.iteratedFDeriv ℝ i signFn x = 0 := by
  obtain ⟨c, -, heq⟩ := signFn_eventuallyEq_const hx
  rw [(heq.iteratedFDeriv ℝ i).eq_of_nhds, iteratedFDeriv_const_of_ne hi, Pi.zero_apply]

private theorem norm_iteratedFDeriv_signFn_le (i : ℕ) {x : ℝ}
    (hx : x ∈ (slitUnitInterval : Set ℝ)) :
    ‖_root_.iteratedFDeriv ℝ i signFn x‖ ≤ 1 := by
  rcases eq_or_ne i 0 with rfl | hi
  · obtain ⟨c, hc, heq⟩ := signFn_eventuallyEq_const hx
    rw [norm_iteratedFDeriv_zero, heq.eq_of_nhds, hc]
  · simp [iteratedFDeriv_signFn_pos hi hx]

private theorem contDiffOn_signFn (k : ℕ) :
    ContDiffOn ℝ ((k + 1 : ℕ)) signFn (slitUnitInterval : Set ℝ) := fun _ hx ↦ by
  obtain ⟨_, -, heq⟩ := signFn_eventuallyEq_const hx
  exact (contDiffAt_const.congr_of_eventuallyEq heq).contDiffWithinAt

private theorem holderOnWith_signFn (k : ℕ) (α : ℝ≥0) :
    HolderOnWith 0 α (_root_.iteratedFDeriv ℝ (k + 1) signFn) (slitUnitInterval : Set ℝ) :=
  fun _ hx _ hy ↦ by
    simp [iteratedFDeriv_signFn_pos (Nat.succ_ne_zero k) hx,
      iteratedFDeriv_signFn_pos (Nat.succ_ne_zero k) hy]

/-- The locally constant sign function `(x ↦ ±1)` on `(-1, 0) ∪ (0, 1)` as an element of
`CkHolderOnSpace (k + 1) α slitUnitInterval ℝ`. Every derivative of positive order vanishes on
`slitUnitInterval`, so the `(k + 1)`-st derivative has `α`-Hölder seminorm `0`. -/
def slitSign (k : ℕ) (α : ℝ≥0) : CkHolderOnSpace (k + 1) α slitUnitInterval ℝ :=
  CkHolderOnSpace.ofContDiffOn signFn (contDiffOn_signFn k)
    (fun i _ ↦ ⟨1, fun _ hx ↦ norm_iteratedFDeriv_signFn_le i hx⟩)
    ⟨0, holderOnWith_signFn k α⟩

/-- On the positive half `(0, 1)`, `slitSign` equals `1`. -/
@[simp] theorem slitSign_of_pos (k : ℕ) (α : ℝ≥0) {x : slitUnitInterval} (hx : 0 < (x : ℝ)) :
    slitSign k α x = 1 := by simp [slitSign, signFn, hx]

/-- On the negative half `(-1, 0)`, `slitSign` equals `-1`. -/
@[simp] theorem slitSign_of_neg (k : ℕ) (α : ℝ≥0) {x : slitUnitInterval} (hx : (x : ℝ) < 0) :
    slitSign k α x = -1 := by simp [slitSign, signFn, not_lt.mpr hx.le]

/-- Convexity of `Ω` cannot be dropped in `CkHolderOnSpace.ofSuccL`: for every `k : ℕ` and every
`0 < α`, `slitSign k α` belongs to `CkHolderOnSpace (k + 1) α slitUnitInterval ℝ`, yet no element
of `CkHolderOnSpace 0 α slitUnitInterval ℝ` agrees with it on `slitUnitInterval`. -/
theorem not_exists_ckHolderOnSpace_zero_eq_slitSign (k : ℕ) {α : ℝ≥0} (hα : 0 < α) :
    ¬ ∃ g : CkHolderOnSpace 0 α slitUnitInterval ℝ, ∀ x, g x = slitSign k α x := by
  rintro ⟨g, hg⟩
  obtain ⟨C, hC⟩ := (CkHolderOnSpace.equivHolderSpace g).memHolder
  have hbound (n : ℕ) : (2 : ℝ) ≤ (C : ℝ) * ((2⁻¹ : ℝ) ^ (α : ℝ)) ^ n := by
    set t : ℝ := (2⁻¹ : ℝ) ^ (n + 1)
    have ht0 : 0 < t := by positivity
    have ht1 : t < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero n)
    let xp : slitUnitInterval := ⟨t, Or.inr ⟨ht0, ht1⟩⟩
    let xm : slitUnitInterval := ⟨-t, Or.inl ⟨by linarith, by linarith⟩⟩
    have hxp : CkHolderOnSpace.equivHolderSpace g xp = 1 := by
      rw [CkHolderOnSpace.equivHolderSpace_apply, hg xp, slitSign_of_pos k α ht0]
    have hxm : CkHolderOnSpace.equivHolderSpace g xm = -1 := by
      rw [CkHolderOnSpace.equivHolderSpace_apply, hg xm, slitSign_of_neg k α (by linarith)]
    have hdist := hC.dist_le xp xm
    rw [HolderSpace.toBoundedContinuousFunction_apply,
      HolderSpace.toBoundedContinuousFunction_apply] at hdist
    have hxy : dist xp xm = (2⁻¹ : ℝ) ^ n := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_of_pos (by linarith : 0 < t - -t)]
      dsimp only [t]
      ring
    have h11 : |(1 : ℝ) - -1| = 2 := by norm_num
    rw [hxp, hxm, Real.dist_eq, h11, hxy,
      ← Real.rpow_natCast (2⁻¹ : ℝ) n, ← Real.rpow_mul (by norm_num),
      mul_comm _ (α : ℝ), Real.rpow_mul (by norm_num), Real.rpow_natCast] at hdist
    exact hdist
  have hq : (2⁻¹ : ℝ) ^ (α : ℝ) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (NNReal.coe_pos.mpr hα)
  have hlim : Tendsto (fun n : ℕ ↦ (C : ℝ) * ((2⁻¹ : ℝ) ^ (α : ℝ)) ^ n) atTop (𝓝 ((C : ℝ) * 0)) :=
    tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hq)
  have hle : (2 : ℝ) ≤ (C : ℝ) * 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hbound
  linarith

end TauCeti
