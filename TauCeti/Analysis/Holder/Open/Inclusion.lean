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

/-!
# Restriction and continuous inclusions for `C^{k,α}(Ω, F)`

This file constructs the natural continuous linear maps between bounded Hölder spaces on open sets:

* **Domain restriction** `TauCeti.CkHolderOnSpace.restrictL`: for `Ω' ≤ Ω`, restricting from `Ω` to
  `Ω'` is a linear contraction of operator norm at most `1`, without any convexity or boundedness
  hypothesis. Specializing `Ω = ⊤` yields `TauCeti.CkHolderSpace.restrictOpenL` from the ambient
  space `CkHolderSpace k α E F` to `CkHolderOnSpace k α Ω F`.
* **Exponent inclusion** `TauCeti.CkHolderOnSpace.ofExponentLEL`: on a bounded open set `Ω`, for
  `β ≤ α`, `CkHolderOnSpace k α Ω F` embeds continuously into `CkHolderOnSpace k β Ω F` with
  operator norm at most `max 1 (diam Ω ^ (α - β))`, extending `TauCeti.HolderSpace.inclusionL` to
  higher derivative orders.
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
open scoped NNReal BoundedContinuousFunction ContDiff

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

/-- Restriction from `Ω` to an open subset `Ω' ≤ Ω` as a continuous linear map of norm at most
`1`. -/
def restrictL (h : Ω' ≤ Ω) : CkHolderOnSpace k α Ω F →L[ℝ] CkHolderOnSpace k α Ω' F :=
  LinearMap.mkContinuous
    { toFun := restrict h
      map_add' f g := ext fun x ↦ by simp [restrict_apply]
      map_smul' c f := ext fun x ↦ by simp [restrict_apply] } 1 fun f ↦ by
        rw [one_mul]
        exact norm_restrict_le h f

@[simp]
theorem restrictL_apply (h : Ω' ≤ Ω) (f : CkHolderOnSpace k α Ω F) (x : Ω') :
    restrictL h f x = f ⟨x.1, h x.2⟩ :=
  restrict_apply h f x

/-- Restriction to an open subset has operator norm at most `1`. -/
theorem norm_restrictL_le_one (h : Ω' ≤ Ω) :
    ‖restrictL (k := k) (α := α) (F := F) h‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

@[simp]
theorem restrictL_rfl :
    restrictL (le_refl Ω) = ContinuousLinearMap.id ℝ (CkHolderOnSpace k α Ω F) := by
  ext f x
  simp

/-- Restriction along `Ω'' ≤ Ω' ≤ Ω` composes functorially. -/
theorem restrictL_comp (h₁ : Ω'' ≤ Ω') (h₂ : Ω' ≤ Ω) :
    (restrictL (k := k) (α := α) (F := F) h₁).comp (restrictL h₂) = restrictL (h₁.trans h₂) := by
  ext f x
  simp

/-- Restriction from the ambient space `CkHolderSpace k α E F` to an open set `Ω`, of operator norm
at most `1`. -/
def _root_.TauCeti.CkHolderSpace.restrictOpenL (Ω : TopologicalSpace.Opens E) :
    CkHolderSpace k α E F →L[ℝ] CkHolderOnSpace k α Ω F :=
  (restrictL (le_top : Ω ≤ ⊤)).comp equivTop.symm.toLinearIsometry.toContinuousLinearMap

@[simp]
theorem _root_.TauCeti.CkHolderSpace.restrictOpenL_apply (Ω : TopologicalSpace.Opens E)
    (g : CkHolderSpace k α E F) (x : Ω) :
    g.restrictOpenL Ω x = g x := by
  simp [CkHolderSpace.restrictOpenL]

/-- Restriction from `CkHolderSpace k α E F` to `CkHolderOnSpace k α Ω F` has operator norm at most
`1`. -/
theorem _root_.TauCeti.CkHolderSpace.norm_restrictOpenL_le_one (Ω : TopologicalSpace.Opens E) :
    ‖CkHolderSpace.restrictOpenL (k := k) (α := α) (F := F) Ω‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g ↦ by
    rw [CkHolderSpace.restrictOpenL, ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      restrictL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk, one_mul]
    exact (norm_restrict_le (le_top : Ω ≤ ⊤) (equivTop.symm g)).trans_eq (equivTop.symm.norm_map g)

/-! ### Decreasing the Hölder exponent on a bounded open set -/

private theorem holderOnWith_of_bounded (hΩ : Bornology.IsBounded (Ω : Set E)) {β : ℝ≥0}
    (hβα : β ≤ α) (f : CkHolderOnSpace k α Ω F) :
    HolderOnWith (nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) *
        (Metric.diam (Ω : Set E)).toNNReal ^ ((α : ℝ) - β)) β
      (_root_.iteratedFDeriv ℝ k f.extendByZero) (Ω : Set E) := by
  refine f.holderOnWith_iteratedFDeriv_extendByZero.of_le (fun x hx y hy ↦ ?_) hβα
  rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ Metric.diam_nonneg]
  exact ENNReal.ofReal_le_ofReal (Metric.dist_le_diam_of_mem hΩ hx hy)

private def ofExponentLE (hΩ : Bornology.IsBounded (Ω : Set E)) {β : ℝ≥0} (hβα : β ≤ α)
    (f : CkHolderOnSpace k α Ω F) : CkHolderOnSpace k β Ω F :=
  ofContDiffOn f.extendByZero f.contDiffOn_extendByZero
    (fun _ hi ↦ ⟨‖f‖, fun x hx ↦ f.norm_iteratedFDeriv_extendByZero_le hi ⟨x, hx⟩⟩)
    ⟨_, holderOnWith_of_bounded hΩ hβα f⟩

private theorem ofExponentLE_apply (hΩ : Bornology.IsBounded (Ω : Set E)) {β : ℝ≥0} (hβα : β ≤ α)
    (f : CkHolderOnSpace k α Ω F) (x : Ω) :
    ofExponentLE hΩ hβα f x = f x :=
  (ofContDiffOn_apply ..).trans (f.extendByZero_coe x)

private theorem norm_ofExponentLE_le (hΩ : Bornology.IsBounded (Ω : Set E)) {β : ℝ≥0}
    (hβα : β ≤ α) (f : CkHolderOnSpace k α Ω F) :
    ‖ofExponentLE hΩ hβα f‖ ≤
      max 1 (Metric.diam (Ω : Set E) ^ ((α : ℝ) - β)) * ‖f‖ := by
  set C : ℝ := max 1 (Metric.diam (Ω : Set E) ^ ((α : ℝ) - β))
  have heq : ∀ x : Ω, f.extendByZero x = ofExponentLE hΩ hβα f x :=
    fun x ↦ (ofContDiffOn_apply ..).symm
  have hfield (i : Fin (k + 1)) : (ofExponentLE hΩ hβα f).iteratedFDeriv i = f.iteratedFDeriv i :=
    BoundedContinuousFunction.ext fun x ↦
      ((ofExponentLE hΩ hβα f).iteratedFDeriv_of_eq heq i x).symm.trans
        (f.iteratedFDeriv_extendByZero i x)
  have htop : (nnHolderNorm β ((ofExponentLE hΩ hβα f).iteratedFDeriv (Fin.last k) :
        Ω → E [×k]→L[ℝ] F) : ℝ) ≤
      C * nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) := by
    have hdom : ((ofExponentLE hΩ hβα f).iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) =
        (Ω : Set E).domRestrict (_root_.iteratedFDeriv ℝ k f.extendByZero) :=
      funext fun x ↦ ((ofExponentLE hΩ hβα f).iteratedFDeriv_of_eq heq (Fin.last k) x).symm
    rw [hdom]
    have hnn := (holderOnWith_of_bounded hΩ hβα f).holderWith.nnholderNorm_le
    have hle : (nnHolderNorm β
        ((Ω : Set E).domRestrict (_root_.iteratedFDeriv ℝ k f.extendByZero)) : ℝ) ≤
        nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) *
          Metric.diam (Ω : Set E) ^ ((α : ℝ) - β) :=
      (NNReal.coe_le_coe.mpr hnn).trans_eq (by
        rw [NNReal.coe_mul, NNReal.coe_rpow, Real.coe_toNNReal _ Metric.diam_nonneg])
    exact hle.trans ((mul_comm _ _).trans_le
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (NNReal.coe_nonneg _)))
  rw [norm_eq, f.norm_eq, mul_add]
  refine add_le_add ?_ htop
  simp_rw [hfield]
  exact (one_mul _).symm.trans_le
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _))

/-- Continuous linear inclusion `CkHolderOnSpace k α Ω F →L[ℝ] CkHolderOnSpace k β Ω F` for `β ≤ α`
on a bounded open set `Ω`. -/
def ofExponentLEL (hΩ : Bornology.IsBounded (Ω : Set E)) {β : ℝ≥0} (hβα : β ≤ α) :
    CkHolderOnSpace k α Ω F →L[ℝ] CkHolderOnSpace k β Ω F :=
  LinearMap.mkContinuous
    { toFun := ofExponentLE hΩ hβα
      map_add' f g := ext fun x ↦ by simp [ofExponentLE_apply]
      map_smul' c f := ext fun x ↦ by simp [ofExponentLE_apply] }
    (max 1 (Metric.diam (Ω : Set E) ^ ((α : ℝ) - β)))
    (norm_ofExponentLE_le hΩ hβα)

@[simp]
theorem ofExponentLEL_apply (hΩ : Bornology.IsBounded (Ω : Set E)) {β : ℝ≥0} (hβα : β ≤ α)
    (f : CkHolderOnSpace k α Ω F) (x : Ω) :
    ofExponentLEL hΩ hβα f x = f x :=
  ofExponentLE_apply hΩ hβα f x

/-- On a bounded open set `Ω`, lowering the Hölder exponent from `α` to `β ≤ α` has operator norm
at most `max 1 (diam Ω ^ (α - β))`. -/
theorem norm_ofExponentLEL_le (hΩ : Bornology.IsBounded (Ω : Set E)) {β : ℝ≥0} (hβα : β ≤ α) :
    ‖ofExponentLEL (k := k) (F := F) hΩ hβα‖ ≤
      max 1 (Metric.diam (Ω : Set E) ^ ((α : ℝ) - β)) :=
  LinearMap.mkContinuous_norm_le _ (zero_le_one.trans (le_max_left _ _)) _

/-- The exponent-lowering inclusion `ofExponentLEL` is injective. -/
theorem ofExponentLEL_injective (hΩ : Bornology.IsBounded (Ω : Set E)) {β : ℝ≥0} (hβα : β ≤ α) :
    Function.Injective (ofExponentLEL (k := k) (F := F) hΩ hβα) :=
  fun _ _ h ↦ ext fun x ↦ by simpa using DFunLike.congr_fun h x

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
      have hk := f.iteratedFDeriv_extendByZero ⟨k, by omega⟩ ⟨x, hx⟩
      have hidx : (⟨k, by omega⟩ : Fin (k + 2)) = (Fin.last k).castSucc := rfl
      rw [hidx] at hk
      exact (congrArg norm hk).le.trans
        ((f.iteratedFDeriv (Fin.last k).castSucc).norm_coe_le_norm ⟨x, hx⟩))
    (fun x hx ↦ by
      have hk := f.iteratedFDeriv_extendByZero ⟨k + 1, by omega⟩ ⟨x, hx⟩
      have hidx : (⟨k + 1, by omega⟩ : Fin (k + 2)) = Fin.last (k + 1) := rfl
      rw [hidx] at hk
      exact (congrArg norm hk).le.trans
        ((f.iteratedFDeriv (Fin.last (k + 1))).norm_coe_le_norm ⟨x, hx⟩))

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

@[simp]
theorem ofSuccL_apply (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1)
    (f : CkHolderOnSpace (k + 1) α Ω F) (x : Ω) :
    ofSuccL hΩ hα f x = f x :=
  ofSucc_apply hΩ hα f x

/-- Lowering the order from `k + 1` to `k` on a convex open set has operator norm at most `3`,
independent of `k`. -/
theorem norm_ofSuccL_le (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) :
    ‖ofSuccL (k := k) (F := F) hΩ hα‖ ≤ 3 :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- The order-lowering inclusion `ofSuccL` is injective. -/
theorem ofSuccL_injective (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) :
    Function.Injective (ofSuccL (k := k) (F := F) hΩ hα) :=
  fun _ _ h ↦ ext fun x ↦ by simpa using DFunLike.congr_fun h x

/-- Continuous linear inclusion `CkHolderSpace (k + 1) α E F →L[ℝ] CkHolderSpace k α E F` on the
whole space for `α ≤ 1`, of operator norm at most `3`. -/
def _root_.TauCeti.CkHolderSpace.ofSuccL (hα : α ≤ 1) :
    CkHolderSpace (k + 1) α E F →L[ℝ] CkHolderSpace k α E F :=
  equivTop.toLinearIsometry.toContinuousLinearMap.comp
    ((CkHolderOnSpace.ofSuccL (Ω := (⊤ : TopologicalSpace.Opens E)) convex_univ hα).comp
      equivTop.symm.toLinearIsometry.toContinuousLinearMap)

@[simp]
theorem _root_.TauCeti.CkHolderSpace.ofSuccL_apply (hα : α ≤ 1)
    (g : CkHolderSpace (k + 1) α E F) (x : E) :
    CkHolderSpace.ofSuccL hα g x = g x := by
  simp [CkHolderSpace.ofSuccL]

/-- On the whole space, lowering the order from `k + 1` to `k` has operator norm at most `3`. -/
theorem _root_.TauCeti.CkHolderSpace.norm_ofSuccL_le (hα : α ≤ 1) :
    ‖CkHolderSpace.ofSuccL (k := k) (E := E) (F := F) hα‖ ≤ 3 :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun g ↦ by
    rw [CkHolderSpace.ofSuccL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.coe_toLinearIsometry,
      equivTop.norm_map, CkHolderOnSpace.ofSuccL, LinearMap.mkContinuous_apply, LinearMap.coe_mk,
      AddHom.coe_mk]
    exact (norm_ofSucc_le convex_univ hα (equivTop.symm g)).trans_eq
      (congrArg (3 * ·) (equivTop.symm.norm_map g))

/-- The ambient order-lowering inclusion `CkHolderSpace.ofSuccL` is injective. -/
theorem _root_.TauCeti.CkHolderSpace.ofSuccL_injective (hα : α ≤ 1) :
    Function.Injective (CkHolderSpace.ofSuccL (k := k) (E := E) (F := F) hα) :=
  fun _ _ h ↦ CkHolderSpace.ext fun x ↦ by simpa using DFunLike.congr_fun h x

end CkHolderOnSpace

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
    (fun i _ ↦ ⟨1, fun x hx ↦ by
      rcases eq_or_ne i 0 with rfl | hi
      · obtain ⟨c, hc, heq⟩ := signFn_eventuallyEq_const hx
        rw [norm_iteratedFDeriv_zero, heq.eq_of_nhds, hc]
      · simp [iteratedFDeriv_signFn_pos hi hx]⟩)
    ⟨0, holderOnWith_signFn k α⟩

@[simp]
theorem slitSign_of_pos (k : ℕ) (α : ℝ≥0) {x : slitUnitInterval} (hx : 0 < (x : ℝ)) :
    slitSign k α x = 1 := by
  rw [slitSign, CkHolderOnSpace.ofContDiffOn_apply]
  simp [signFn, hx]

@[simp]
theorem slitSign_of_neg (k : ℕ) (α : ℝ≥0) {x : slitUnitInterval} (hx : (x : ℝ) < 0) :
    slitSign k α x = -1 := by
  rw [slitSign, CkHolderOnSpace.ofContDiffOn_apply]
  simp [signFn, not_lt.mpr hx.le]

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
