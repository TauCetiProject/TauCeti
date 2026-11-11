/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Leibniz
public import TauCeti.Analysis.Holder.Iterated
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Data.Nat.Choose.Sum

/-!
# Quantitative localization of finite-order Hölder maps

A globally smooth supported cutoff turns local `C^{k,α}` data on an open convex set into an
actual bounded `C^{k,α}` map on the ambient space. Only the top source jet needs an explicit
Hölder hypothesis; the lower jets are controlled by the mean-value inequality.
-/

public section

open Set
open scoped NNReal Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The cutoff product has a bounded derivative of every available order, with the binomial
Leibniz bound. The source function is unrestricted outside the open set. -/
theorem norm_iteratedFDeriv_cutoff_smul_le {k j : ℕ} {s : Set E} {f : E → F} {χ : E → ℝ}
    {M N : ℝ≥0} (hf : ContDiffOn ℝ k f s) (hχ : ContDiff ℝ k χ) (hs : IsOpen s)
    (hχs : tsupport χ ⊆ s) (hj : j ≤ k)
    (hfb : ∀ i ≤ k, ∀ x ∈ s, ‖iteratedFDeriv ℝ i f x‖ ≤ M)
    (hχb : ∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ N) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y => χ y • f y) x‖ ≤ (2 : ℝ)^j * N * M := by
  by_cases hx : x ∈ s
  · have hjorder : (j : WithTop ℕ∞) ≤ k := by exact_mod_cast hj
    have h := norm_iteratedFDerivWithin_smul_le hχ.contDiffOn hf hs.uniqueDiffOn hx hjorder
    simp_rw [iteratedFDerivWithin_of_isOpen _ hs hx] at h
    refine h.trans ?_
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * N * M := by
        apply Finset.sum_le_sum
        intro i hi
        gcongr
        · exact hχb i (by have := Finset.mem_range.mp hi; omega) x
        · exact hfb (j-i) (by omega) x hx
      _ = (2 : ℝ)^j * N * M := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 2
        exact_mod_cast Nat.sum_range_choose j
  · have h0 : (fun y => χ y • f y) =ᶠ[𝓝 x] 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 fun h => hx (hχs h)] with y hy
      simp [hy]
    rw [(h0.iteratedFDeriv (𝕜 := ℝ) j).self_of_nhds]
    have hnonneg : (0 : ℝ) ≤ 2^j * N * M := by positivity
    simpa using hnonneg

/-- The top derivative of a cutoff product is globally Hölder. The constant involves only the
source jet bound, its top Hölder constant, and the cutoff jets through order `k + 1`. -/
theorem holderWith_iteratedFDeriv_cutoff_smul {k : ℕ} {s : Set E} {f : E → F} {χ : E → ℝ}
    {M N H α : ℝ≥0} (hf : ContDiffOn ℝ k f s) (hχ : ContDiff ℝ (k + 1) χ)
    (hs : IsOpen s) (hc : Convex ℝ s) (hχs : tsupport χ ⊆ s) (hα : α ≤ 1)
    (hfb : ∀ i ≤ k, ∀ x ∈ s, ‖iteratedFDeriv ℝ i f x‖ ≤ M)
    (hχb : ∀ i ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ N)
    (hfH : HolderOnWith H α (iteratedFDeriv ℝ k f) s) :
    HolderWith ((2 : ℝ≥0)^k * N * (H + 6 * M)) α
      (iteratedFDeriv ℝ k (fun x => χ x • f x)) := by
  have hall : ∀ j ≤ k, HolderOnWith (H + 3 * M) α (iteratedFDeriv ℝ j f) s := by
    intro j hj
    rcases hj.eq_or_lt with rfl | hj
    · exact hfH.mono_const (le_self_add)
    · have hlow := hf.holderOnWith_iteratedFDeriv_of_lt hs hc hj hα
        (hfb j hj.le) (hfb (j + 1) (by omega))
      have hconstant : M + 2 * M = 3 * M := by ring
      rw [hconstant] at hlow
      exact hlow.mono_const le_add_self
  have hcut : ∀ j ≤ k, HolderWith (3 * N) α (iteratedFDeriv ℝ j χ) := by
    intro j hj
    have hlow := hχ.contDiffOn.holderOnWith_iteratedFDeriv_of_lt (k := k + 1)
      isOpen_univ convex_univ (by omega : j < k + 1) hα
      (fun x _ => hχb j (by omega) x) (fun x _ => hχb (j + 1) (by omega) x)
    convert holderOnWith_univ.mp hlow using 1
    ring
  let L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip
  have hL : ‖L‖₊ ≤ 1 := by
    dsimp [L]
    rw [ContinuousLinearMap.opNNNorm_flip]
    exact ContinuousLinearMap.opNNNorm_lsmul_le
  have h := L.holderWith_iteratedFDeriv_of_tsupport_subset_right hf
    (hχ.of_le (by simp)) hs hχs hfb (fun i hi => hχb i (by omega)) hall hcut
  apply h.mono
  calc
    _ ≤ (2 : ℝ≥0)^k * 1 * (M * (3 * N) + N * (H + 3 * M)) := by
      gcongr
    _ = _ := by ring

namespace CkHolderSpace

variable {k : ℕ} {s : Set E} {f : E → F} {χ : E → ℝ} {M N H α : ℝ≥0}
    (hf : ContDiffOn ℝ k f s) (hχ : ContDiff ℝ (k + 1) χ)
    (hs : IsOpen s) (hc : Convex ℝ s) (hχs : tsupport χ ⊆ s) (hα : α ≤ 1)
    (hfb : ∀ i ≤ k, ∀ x ∈ s, ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ M)
    (hχb : ∀ i ≤ k + 1, ∀ x, ‖_root_.iteratedFDeriv ℝ i χ x‖ ≤ N)
    (hfH : HolderOnWith H α (_root_.iteratedFDeriv ℝ k f) s)

/-- Globalize local `C^{k,α}` data by multiplication by a supported `C^{k + 1}` cutoff.
The result is the actual product, with its actual iterated Fréchet derivatives. -/
noncomputable def cutoff : CkHolderSpace k α E F :=
  ofContDiff (fun x => χ x • f x)
    (hf.contDiff_smul_of_tsupport_subset hs (hχ.of_le (by simp)).contDiffOn hχs)
    (fun j hj => ⟨(2 : ℝ)^j * N * M,
      norm_iteratedFDeriv_cutoff_smul_le hf (hχ.of_le (by simp)) hs hχs hj hfb
        (fun i hi => hχb i (by omega))⟩)
    ⟨_, holderWith_iteratedFDeriv_cutoff_smul hf hχ hs hc hχs hα hfb hχb hfH⟩

@[simp]
theorem coe_cutoff : ⇑(cutoff hf hχ hs hc hχs hα hfb hχb hfH) = fun x => χ x • f x := by
  exact coe_ofContDiff _ _ _ _

@[simp]
theorem cutoff_apply (x : E) : cutoff hf hχ hs hc hχs hα hfb hχb hfH x = χ x • f x :=
  congrFun (coe_cutoff hf hχ hs hc hχs hα hfb hχb hfH) x

/-- Every derivative field of the localized map satisfies the quantitative Leibniz bound. -/
theorem norm_iteratedFDeriv_cutoff_le {j : ℕ} (hj : j ≤ k) (x : E) :
    ‖_root_.iteratedFDeriv ℝ j (cutoff hf hχ hs hc hχs hα hfb hχb hfH) x‖ ≤
      (2 : ℝ)^j * N * M := by
  rw [coe_cutoff]
  exact norm_iteratedFDeriv_cutoff_smul_le hf (hχ.of_le (by simp)) hs hχs hj hfb
    (fun i hi => hχb i (by omega)) x

/-- The complete native supremum-plus-top-seminorm is controlled by local data. -/
theorem norm_cutoff_le : ‖cutoff hf hχ hs hc hχs hα hfb hχb hfH‖ ≤
    (2 : ℝ)^k * N * (H + (k + 7) * M) := by
  let u := cutoff hf hχ hs hc hχs hα hfb hχb hfH
  have hb (i : Fin (k + 1)) : ‖u.iteratedFDeriv i‖ ≤ (2 : ℝ)^k * N * M := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).2
    intro x
    rw [coe_iteratedFDeriv]
    exact (norm_iteratedFDeriv_cutoff_le hf hχ hs hc hχs hα hfb hχb hfH
      (by omega : i.val ≤ k) x).trans (by
        gcongr
        · norm_num
        · omega)
  have hh : (nnHolderNorm α (_root_.iteratedFDeriv ℝ k u) : ℝ) ≤
      (2 : ℝ)^k * N * (H + 6 * M) := by
    have h := (holderWith_iteratedFDeriv_cutoff_smul hf hχ hs hc hχs hα hfb hχb hfH).nnholderNorm_le
    rw [coe_cutoff]
    exact_mod_cast h
  rw [norm_eq]
  calc
    _ ≤ ∑ _ : Fin (k + 1), ((2 : ℝ)^k * N * M) + (2 : ℝ)^k * N * (H + 6 * M) :=
      add_le_add (Finset.sum_le_sum fun i _ => hb i) hh
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring

/-- The localized map has topological support inside that of the cutoff. -/
theorem tsupport_cutoff_subset : tsupport (cutoff hf hχ hs hc hχs hα hfb hχb hfH) ⊆
    tsupport χ := by
  rw [coe_cutoff]
  exact tsupport_smul_subset_left _ _

/-- Localization lands in the native submodule supported in the local domain. -/
theorem cutoff_mem_supported : cutoff hf hχ hs hc hχs hα hfb hχb hfH ∈
    supportedCkHolderSubmodule k α s := by
  rw [mem_supportedCkHolderSubmodule_iff]
  intro x hx
  rw [cutoff_apply, image_eq_zero_of_notMem_tsupport (fun h => hx (hχs h)), zero_smul]

/-- Where the cutoff is one on a neighborhood, localization preserves every actual derivative,
including derivatives beyond the regularity assumed in the construction. -/
theorem iteratedFDeriv_cutoff_eq {x : E} (hχone : χ =ᶠ[𝓝 x] 1) (j : ℕ) :
    _root_.iteratedFDeriv ℝ j (cutoff hf hχ hs hc hχs hα hfb hχb hfH) x =
      _root_.iteratedFDeriv ℝ j f x := by
  rw [coe_cutoff]
  have h : (fun y => χ y • f y) =ᶠ[𝓝 x] f := by
    filter_upwards [hχone] with y hy
    simp [hy]
  exact (h.iteratedFDeriv ℝ j).self_of_nhds

end CkHolderSpace

end TauCeti
