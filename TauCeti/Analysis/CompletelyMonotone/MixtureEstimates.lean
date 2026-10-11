/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Basic

/-! # Values and finite mixtures of completely monotone functions

This file develops nonnegative weighted values, finite mixtures, and ordered value estimates
for the closed smooth, open positive, and continuous closed-half-line predicates.
-/

public section

noncomputable section

open Set Filter
open scoped Topology

namespace TauCeti

namespace IsCompletelyMonotone

/-- The absolute value equals the value on the domain of complete monotonicity. -/
theorem abs_value_eq {f : ℝ → ℝ} (hf : IsCompletelyMonotone f) {t
    : ℝ} (ht : 0 ≤ t) :
    |f t| = f t := by
  exact abs_of_nonneg (hf.nonneg ht)

/-- A nonnegative weight times a completely monotone value is nonnegative. -/
theorem nonnegative_weighted_value {f : ℝ → ℝ} (hf :
    IsCompletelyMonotone f) {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    0 ≤ c * f t := by exact mul_nonneg hc (IsCompletelyMonotone.nonneg hf ht)

/-- Multiplication by a nonnegative weight preserves the comparison of ordered values. -/
theorem weighted_value_le {f : ℝ → ℝ} (hf : IsCompletelyMonotone
    f) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {c : ℝ} (hc : 0 ≤ c) :
    c * f t ≤ c * f s := by
  have h := hf.antitoneOn (mem_Ici.mpr hs) (mem_Ici.mpr (le_trans hs hst)) hst
  exact mul_le_mul_of_nonneg_left h hc

/-- Normalizing a later value by a positive earlier value gives a number in `[0, 1]`. -/
theorem normalized_value_mem_Icc {f : ℝ → ℝ} (hf :
    IsCompletelyMonotone f) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (hfs : 0 < f s) :
    f t / f s ∈ Icc 0 1 := by
  have ht : 0 ≤ t := le_trans hs hst
  have hnt : 0 ≤ f t := hf.nonneg ht
  have hanti : f t ≤ f s := hf.antitoneOn (mem_Ici.mpr hs) (mem_Ici.mpr ht) hst
  exact ⟨div_nonneg hnt hfs.le, (div_le_one hfs).mpr hanti⟩

/-- The difference between ordered values is bounded by the earlier value. -/
theorem abs_difference_bound {f : ℝ → ℝ} (hf :
    IsCompletelyMonotone f) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    |f s - f t| ≤ f s := by
  have ht : 0 ≤ t := by linarith
  have h1 : f t ≤ f s := hf.antitoneOn hs ht hst
  have h2 : 0 ≤ f t := hf.nonneg ht
  rw [abs_of_nonneg (by linarith [hf.nonneg hs])]
  linarith

/-- A sum of two nonnegative completely monotone values vanishes exactly when both vanish. -/
theorem sum_zero_iff {f g : ℝ → ℝ} (hf : IsCompletelyMonotone f)
    (hg : IsCompletelyMonotone g) {t : ℝ} (ht : 0 ≤ t) :
    f t + g t = 0 ↔ f t = 0 ∧ g t = 0 := by
  constructor
  · intro h
    have hf0 : 0 ≤ f t := hf.nonneg ht
    have hg0 : 0 ≤ g t := hg.nonneg ht
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    simp

/-- A finite sum of completely monotone values vanishes exactly when every term vanishes. -/
theorem finite_sum_zero_iff {ι : Type*} (u : Finset ι) (f : ι → ℝ →
    ℝ) (hf : ∀ i ∈ u, IsCompletelyMonotone (f i)) {t : ℝ} (ht : 0 ≤ t) :
    (∑ i ∈ u, f i t) = 0 ↔ ∀ i ∈ u, f i t = 0 := by
  exact Finset.sum_eq_zero_iff_of_nonneg fun i hi => (hf i hi).nonneg ht

/-- Finite mixtures with nonnegative weights preserve complete monotonicity. -/
theorem finite_weighted_mixture {ι : Type*} (u : Finset ι) (f : ι →
    ℝ → ℝ) (w : ι → ℝ) (hf : ∀ i ∈ u, IsCompletelyMonotone (f i)) (hw : ∀ i ∈ u, 0 ≤ w i) :
    IsCompletelyMonotone (fun t => ∑ i ∈ u, w i * f i t) := by
  refine (IsCompletelyMonotone.sum fun i hi => (hf i hi).smul (hw i hi)).congr ?_
  intro t _
  simp [Pi.smul_apply]

/-- The product of two completely monotone functions is antitone on their domain. -/
theorem product_value_antitone {f g : ℝ → ℝ} (hf :
    IsCompletelyMonotone f) (hg : IsCompletelyMonotone g) :
    AntitoneOn (fun t => f t * g t) (Ici 0) := by
  intro a ha b hb hab
  exact mul_le_mul (hf.antitoneOn ha hb hab) (hg.antitoneOn ha hb hab)
    (hg.nonneg (mem_Ici.mp hb)) (hf.nonneg (mem_Ici.mp ha))

/-- Distinct values at ordered points strictly decrease. -/
theorem strict_decrease_of_ne {f : ℝ → ℝ} (hf :
    IsCompletelyMonotone f) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (hne : f s ≠ f t) :
    f t < f s := by
  have h := hf.antitoneOn (mem_Ici.mpr hs) (mem_Ici.mpr (hs.trans hst)) hst
  exact lt_of_le_of_ne h hne.symm

/-- Positivity at a later point implies positivity at an earlier point of the domain. -/
theorem positive_of_positive_later {f : ℝ → ℝ} (hf :
    IsCompletelyMonotone f) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : 0 < f t) :
    0 < f s := by
  have h_ant := hf.antitoneOn
  have hts : f t ≤ f s := h_ant (mem_Ici.mpr hs) (mem_Ici.mpr (hs.trans hst)) hst
  exact lt_of_lt_of_le ht hts

/-- Positivity at a later point implies positivity on the preceding interval in the domain. -/
theorem positive_on_initial_interval {f : ℝ → ℝ} (hf :
    IsCompletelyMonotone f) {t : ℝ} (ht : 0 ≤ t) (hft : 0 < f t) :
    ∀ s ∈ Icc 0 t, 0 < f s := by
  intro s hs
  have hanti := hf.antitoneOn
  have hs_mem : s ∈ Ici (0 : ℝ) := mem_Ici.mpr hs.1
  have ht_mem : t ∈ Ici (0 : ℝ) := mem_Ici.mpr ht
  have hfs : f t ≤ f s := hanti hs_mem ht_mem hs.2
  linarith

/-- Equal endpoint values force constancy throughout the intervening interval. -/
theorem constant_of_equal_endpoints {f : ℝ → ℝ} (hf :
    IsCompletelyMonotone f) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (heq : f s = f t) :
    EqOn f (fun _ => f s) (Icc s t) := by
  intro x hx
  have hcm := hf.antitoneOn
  have hxs : s ≤ x := hx.1
  have hxt : x ≤ t := hx.2
  have hx0 : 0 ≤ x := le_trans hs hxs
  have h1 : f x ≤ f s := hcm hs hx0 hxs
  have h2 : f t ≤ f x := hcm hx0 (le_trans hs hst) hxt
  have h3 : f s ≤ f x := by rw [heq]; exact h2
  exact le_antisymm h1 h3

/-- Absolute differences add exactly along three ordered points in the domain. -/
theorem difference_subadditive {f : ℝ → ℝ} (hf :
    IsCompletelyMonotone f) {r s t : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hst : s ≤ t) :
    |f r - f t| = |f r - f s| + |f s - f t| := by
  have hs' : 0 ≤ s := hr.trans hrs
  have ht' : 0 ≤ t := hs'.trans hst
  have h1 := hf.antitoneOn (mem_Ici.mpr hr) (mem_Ici.mpr hs') hrs
  have h2 := hf.antitoneOn (mem_Ici.mpr hs') (mem_Ici.mpr ht') hst
  have h3 := hf.antitoneOn (mem_Ici.mpr hr) (mem_Ici.mpr ht') (hrs.trans hst)
  rw [abs_of_nonneg (sub_nonneg.mpr h3), abs_of_nonneg (sub_nonneg.mpr h1),
    abs_of_nonneg (sub_nonneg.mpr h2)]
  ring

end IsCompletelyMonotone

namespace IsCompletelyMonotoneOnIoi

/-- The absolute value equals the value on the domain of complete monotonicity. -/
theorem abs_value_eq {f : ℝ → ℝ} (hf :
    IsCompletelyMonotoneOnIoi f) {t : ℝ} (ht : 0 < t) :
    |f t| = f t := by rw [abs_of_nonneg (hf.nonneg ht)]

/-- A nonnegative weight times a completely monotone value is nonnegative. -/
theorem nonnegative_weighted_value {f : ℝ → ℝ} (hf :
    IsCompletelyMonotoneOnIoi f) {c t : ℝ} (hc : 0 ≤ c) (ht : 0 < t) :
    0 ≤ c * f t := by exact mul_nonneg hc (hf.nonneg ht)

/-- Multiplication by a nonnegative weight preserves the comparison of ordered values. -/
theorem weighted_value_le {f : ℝ → ℝ} (hf :
    IsCompletelyMonotoneOnIoi f) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) {c : ℝ} (hc : 0 ≤ c) :
    c * f t ≤ c * f s := by
  have hcm :=
    IsCompletelyMonotoneOnIoi.isCompletelyMonotone_comp_add_const hf hs
  have h := IsCompletelyMonotone.antitoneOn hcm
  have h3 : f t ≤ f s := by
    simpa using h (by simp) (sub_nonneg.mpr hst) (sub_nonneg.mpr hst)
  exact mul_le_mul_of_nonneg_left h3 hc

/-- Normalizing a later value by a positive earlier value gives a number in `[0, 1]`. -/
theorem normalized_value_mem_Icc {f : ℝ → ℝ} (hf :
    IsCompletelyMonotoneOnIoi f) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (hfs : 0 < f s) :
    f t / f s ∈ Icc 0 1 := by
  have ht : 0 < t := by linarith
  have hanti : AntitoneOn f (Ioi 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) hf.contDiffOn.continuousOn
      (hf.contDiffOn.differentiableOn (by simp) |>.mono interior_subset)
      fun x hx => by
        rw [interior_Ioi] at hx
        exact hf.deriv_nonpos hx
  refine ⟨div_nonneg (hf.nonneg ht) (le_of_lt hfs), ?_⟩
  exact (div_le_one hfs).mpr (hanti (mem_Ioi.mpr hs) (mem_Ioi.mpr ht) hst)

/-- The difference between ordered values is bounded by the earlier value. -/
theorem abs_difference_bound {f : ℝ → ℝ} (hf :
    IsCompletelyMonotoneOnIoi f) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    |f s - f t| ≤ f s := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hft : 0 ≤ f t := hf.nonneg ht
  have := hf.isCompletelyMonotone_comp_add_const hs
  have h_antitone := this.antitoneOn
  have h_ft_le_fs : f t ≤ f s := by
    have := h_antitone (by simp : (0 : ℝ) ∈ Ici (0 : ℝ))
      (by simpa using hst : (t - s : ℝ) ∈ Ici (0 : ℝ)) (by linarith)
    simpa using this
  rw [abs_of_nonneg (by linarith : 0 ≤ f s - f t)]
  linarith

/-- A sum of two nonnegative completely monotone values vanishes exactly when both vanish. -/
theorem sum_zero_iff {f g : ℝ → ℝ} (hf :
    IsCompletelyMonotoneOnIoi f) (hg : IsCompletelyMonotoneOnIoi g) {t : ℝ} (ht : 0 < t) :
    f t + g t = 0 ↔ f t = 0 ∧ g t = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : 0 ≤ f t := hf.nonneg ht
    have h2 : 0 ≤ g t := hg.nonneg ht
    exact ⟨by linarith, by linarith⟩
  · rcases h with ⟨h1, h2⟩
    rw [h1, h2]
    norm_num

/-- A finite sum of completely monotone values vanishes exactly when every term vanishes. -/
theorem finite_sum_zero_iff {ι : Type*} (u : Finset ι) (f : ι
    → ℝ → ℝ) (hf : ∀ i ∈ u, IsCompletelyMonotoneOnIoi (f i)) {t : ℝ} (ht : 0 < t) :
    (∑ i ∈ u, f i t) = 0 ↔ ∀ i ∈ u, f i t = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => (hf i hi).nonneg ht)).mp h
  · exact Finset.sum_eq_zero h

/-- Finite mixtures with nonnegative weights preserve complete monotonicity. -/
theorem finite_weighted_mixture {ι : Type*} (u : Finset ι) (f
    : ι → ℝ → ℝ) (w : ι → ℝ) (hf : ∀ i ∈ u, IsCompletelyMonotoneOnIoi (f i)) (hw : ∀ i ∈ u, 0 ≤
    w i) :
    IsCompletelyMonotoneOnIoi (fun t => ∑ i ∈ u, w i * f i t) := by classical
  induction u using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (isCompletelyMonotone_const le_rfl).isCompletelyMonotoneOnIoi
  | insert a s has ih =>
    have h1 : IsCompletelyMonotoneOnIoi (w a • f a) :=
      (hf a (Finset.mem_insert_self a s)).smul
        (hw a (Finset.mem_insert_self a s))
    have h2 :
        IsCompletelyMonotoneOnIoi (fun t => ∑ i ∈ s, w i * f i t) :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => hw i (Finset.mem_insert_of_mem hi))
    have h3 :
        (fun t => ∑ i ∈ insert a s, w i * f i t) =
          (w a • f a) + (fun t => ∑ i ∈ s, w i * f i t) := by
      funext t
      rw [Finset.sum_insert has]
      simp
    rw [h3]
    exact h1.add h2

/-- The product of two completely monotone functions is antitone on their domain. -/
theorem product_value_antitone {f g : ℝ → ℝ} (hf :
    IsCompletelyMonotoneOnIoi f) (hg : IsCompletelyMonotoneOnIoi g) :
    AntitoneOn (fun t => f t * g t) (Ioi 0) := by
  intro x hx y hy hxy
  have hf_anti : AntitoneOn f (Ioi 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) hf.contDiffOn.continuousOn ?_ ?_
    · simpa [interior_Ioi] using hf.contDiffOn.differentiableOn (by simp)
    · intro z hz
      exact hf.deriv_nonpos (by simpa [interior_Ioi] using hz)
  have hg_anti : AntitoneOn g (Ioi 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) hg.contDiffOn.continuousOn ?_ ?_
    · simpa [interior_Ioi] using hg.contDiffOn.differentiableOn (by simp)
    · intro z hz
      exact hg.deriv_nonpos (by simpa [interior_Ioi] using hz)
  exact le_trans (mul_le_mul_of_nonneg_right (hf_anti hx hy hxy) (hg.nonneg hy))
    (mul_le_mul_of_nonneg_left (hg_anti hx hy hxy) (hf.nonneg hx))

/-- Positivity at a later point implies positivity on the preceding interval in the domain. -/
theorem positive_on_initial_interval {f : ℝ → ℝ} (hf :
    IsCompletelyMonotoneOnIoi f) {t : ℝ} (ht : 0 < t) (hft : 0 < f t) :
    ∀ s ∈ Ioc 0 t, 0 < f s := by
  intro s hs
  obtain ⟨hs0, hst⟩ := mem_Ioc.mp hs
  have hanti : AntitoneOn f (Ioi 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) hf.contDiffOn.continuousOn
      (by simpa [interior_Ioi] using hf.contDiffOn.differentiableOn (by simp)) ?_
    rw [interior_Ioi]
    intro x hx
    exact hf.deriv_nonpos hx
  exact lt_of_lt_of_le hft (hanti (mem_Ioi.mpr hs0) (mem_Ioi.mpr ht) hst)

/-- Absolute differences add exactly along three ordered points in the domain. -/
theorem difference_subadditive {f : ℝ → ℝ} (hf :
    IsCompletelyMonotoneOnIoi f) {r s t : ℝ} (hr : 0 < r) (hrs : r ≤ s) (hst : s ≤ t) :
    |f r - f t| = |f r - f s| + |f s - f t| := by
  have hanti : AntitoneOn f (Ioi 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) hf.contDiffOn.continuousOn ?_ ?_
    · rw [interior_Ioi]
      exact hf.contDiffOn.differentiableOn (by simp)
    · rw [interior_Ioi]
      intro x hx
      exact hf.deriv_nonpos hx
  have h1 : f s ≤ f r := hanti (mem_Ioi.mpr hr) (mem_Ioi.mpr (by linarith)) hrs
  have h2 : f t ≤ f s := hanti (mem_Ioi.mpr (by linarith)) (mem_Ioi.mpr (by linarith)) hst
  calc |f r - f t| = f r - f t := abs_of_nonneg (by linarith)
    _ = (f r - f s) + (f s - f t) := by ring
    _ = |f r - f s| + |f s - f t| := by
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]

end IsCompletelyMonotoneOnIoi

namespace IsContinuousCompletelyMonotoneOnIoi

/-- The absolute value equals the value on the domain of complete monotonicity. -/
theorem abs_value_eq {f : ℝ → ℝ} (hf :
    IsContinuousCompletelyMonotoneOnIoi f) {t : ℝ} (ht : 0 ≤ t) :
    |f t| = f t := by
  exact abs_of_nonneg (hf.nonneg ht)

/-- A nonnegative weight times a completely monotone value is nonnegative. -/
theorem nonnegative_weighted_value {f : ℝ → ℝ} (hf
    : IsContinuousCompletelyMonotoneOnIoi f) {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    0 ≤ c * f t := by exact mul_nonneg hc (hf.nonneg ht)

/-- The difference between ordered values is bounded by the earlier value. -/
theorem abs_difference_bound {f : ℝ → ℝ} (hf :
    IsContinuousCompletelyMonotoneOnIoi f) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    |f s - f t| ≤ f s := by
  have h1 : f t ≤ f s := hf.antitoneOn (mem_Ici.mpr hs) (mem_Ici.mpr (hs.trans hst)) hst
  have h2 : 0 ≤ f t := hf.nonneg (hs.trans hst)
  have h3 : 0 ≤ f s := hf.nonneg hs
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- A sum of two nonnegative completely monotone values vanishes exactly when both vanish. -/
theorem sum_zero_iff {f g : ℝ → ℝ} (hf :
    IsContinuousCompletelyMonotoneOnIoi f) (hg : IsContinuousCompletelyMonotoneOnIoi g) {t : ℝ}
    (ht : 0 ≤ t) :
    f t + g t = 0 ↔ f t = 0 ∧ g t = 0 := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · linarith [hf.nonneg ht, hg.nonneg ht, h]
  · linarith [hf.nonneg ht, hg.nonneg ht, h]
  · obtain ⟨h1, h2⟩ := h
    rw [h1, h2]
    norm_num

/-- A finite sum of completely monotone values vanishes exactly when every term vanishes. -/
theorem finite_sum_zero_iff {ι : Type*} (u : Finset
    ι) (f : ι → ℝ → ℝ) (hf : ∀ i ∈ u, IsContinuousCompletelyMonotoneOnIoi (f i)) {t : ℝ} (ht : 0
    ≤ t) :
    (∑ i ∈ u, f i t) = 0 ↔ ∀ i ∈ u, f i t = 0 := by
  refine Finset.sum_eq_zero_iff_of_nonneg ?_
  intro i hi
  exact (hf i hi).nonneg ht

/-- Finite mixtures with nonnegative weights preserve complete monotonicity. -/
theorem finite_weighted_mixture {ι : Type*} (u :
    Finset ι) (f : ι → ℝ → ℝ) (w : ι → ℝ) (hf : ∀ i ∈ u, IsContinuousCompletelyMonotoneOnIoi (f
    i)) (hw : ∀ i ∈ u, 0 ≤ w i) :
    IsContinuousCompletelyMonotoneOnIoi (fun t => ∑ i ∈ u, w i * f i t) := by
  refine (IsContinuousCompletelyMonotoneOnIoi.sum fun i hi => (hf i hi).smul (hw i hi)).congr ?_
  intro t _
  simp

/-- The product of two completely monotone functions is antitone on their domain. -/
theorem product_value_antitone {f g : ℝ → ℝ} (hf :
    IsContinuousCompletelyMonotoneOnIoi f) (hg : IsContinuousCompletelyMonotoneOnIoi g) :
    AntitoneOn (fun t => f t * g t) (Ici 0) := by
  intro a ha b hb hab
  have h1 : f b ≤ f a := hf.antitoneOn ha hb hab
  have h2 : g b ≤ g a := hg.antitoneOn ha hb hab
  have h3 : 0 ≤ g b := hg.nonneg (mem_Ici.mp hb)
  have h4 : 0 ≤ f a := hf.nonneg (mem_Ici.mp ha)
  exact le_trans (mul_le_mul_of_nonneg_right h1 h3) (mul_le_mul_of_nonneg_left h2 h4)

/-- The square of a completely monotone function is antitone on its domain. -/
theorem square_value_antitone {f : ℝ → ℝ} (hf :
    IsContinuousCompletelyMonotoneOnIoi f) :
    AntitoneOn (fun t => f t ^ 2) (Ici 0) := by
  intro a ha b hb hab
  have hfab : f b ≤ f a := hf.antitoneOn ha hb hab
  have hb0 : 0 ≤ f b := hf.nonneg (mem_Ici.mp hb)
  have ha0 : 0 ≤ f a := hf.nonneg (mem_Ici.mp ha)
  calc f b ^ 2 = f b * f b := by ring
    _ ≤ f a * f a := mul_le_mul hfab hfab hb0 ha0
    _ = f a ^ 2 := by ring

/-- Nonnegative weights summing to one preserve a common normalized value in a finite mixture. -/
theorem finite_normalized_mixture {ι : Type*} (u :
    Finset ι) (f : ι → ℝ → ℝ) (w : ι → ℝ) (hf : ∀ i ∈ u, IsContinuousCompletelyMonotoneOnIoi (f
    i)) (hw : ∀ i ∈ u, 0 ≤ w i) (hws : ∑ i ∈ u, w i = 1) {s : ℝ} (hfs : ∀ i ∈ u, f i s = 1) :
    IsContinuousCompletelyMonotoneOnIoi (fun t => ∑ i ∈ u, w i * f i t) ∧ (∑ i ∈ u, w i * f i s)
    = 1 := by
  refine ⟨?_, ?_⟩
  · have h1 : (fun t => ∑ i ∈ u, w i * f i t) = fun t => ∑ i ∈ u, (w i • f i) t := by
      funext t
      simp [smul_eq_mul]
    rw [h1]
    exact IsContinuousCompletelyMonotoneOnIoi.sum fun i hi => (hf i hi).smul (hw i hi)
  · have h2 : (∑ i ∈ u, w i * f i s) = ∑ i ∈ u, w i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hfs i hi, mul_one]
    rw [h2, hws]

/-- Distinct values at ordered points strictly decrease. -/
theorem strict_decrease_of_ne {f : ℝ → ℝ} (hf :
    IsContinuousCompletelyMonotoneOnIoi f) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (hne : f s ≠ f
    t) :
    f t < f s := by
  have h_le : f t ≤ f s := hf.antitoneOn hs (hs.trans hst) hst
  exact lt_of_le_of_ne h_le (Ne.symm hne)

/-- Positivity at a later point implies positivity at an earlier point of the domain. -/
theorem positive_of_positive_later {f : ℝ → ℝ} (hf
    : IsContinuousCompletelyMonotoneOnIoi f) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : 0 < f t)
    :
    0 < f s := by
  exact lt_of_lt_of_le ht (hf.antitoneOn (Set.mem_Ici.mpr hs)
    (Set.mem_Ici.mpr (hs.trans hst)) hst)

/-- Positivity at a later point implies positivity on the preceding interval in the domain. -/
theorem positive_on_initial_interval {f : ℝ → ℝ}
    (hf : IsContinuousCompletelyMonotoneOnIoi f) {t : ℝ} (ht : 0 ≤ t) (hft : 0 < f t) :
    ∀ s ∈ Icc 0 t, 0 < f s := by
  intro s hs
  have hs0 : 0 ≤ s := hs.1
  have hst : s ≤ t := hs.2
  have h := hf.antitoneOn (mem_Ici.mpr hs0) (mem_Ici.mpr ht) hst
  linarith [h]

/-- Equal endpoint values force constancy throughout the intervening interval. -/
theorem constant_of_equal_endpoints {f : ℝ → ℝ}
    (hf : IsContinuousCompletelyMonotoneOnIoi f) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (heq : f s
    = f t) :
    EqOn f (fun _ => f s) (Icc s t) := by
  intro x hx
  have hanti := hf.antitoneOn
  have hx0 : 0 ≤ x := le_trans hs hx.1
  have ht0 : 0 ≤ t := le_trans hs hst
  have h1 : f x ≤ f s := hanti (mem_Ici.mpr hs) (mem_Ici.mpr hx0) hx.1
  have h2 : f t ≤ f x := hanti (mem_Ici.mpr hx0) (mem_Ici.mpr ht0) hx.2
  have h3 : f s ≤ f x := by linarith [heq, h2]
  linarith

/-- Absolute differences add exactly along three ordered points in the domain. -/
theorem difference_subadditive {f : ℝ → ℝ} (hf :
    IsContinuousCompletelyMonotoneOnIoi f) {r s t : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hst : s ≤ t)
    :
    |f r - f t| = |f r - f s| + |f s - f t| := by
  have h := hf.antitoneOn
  have hr' : r ∈ Ici 0 := hr
  have hs' : s ∈ Ici 0 := le_trans hr hrs
  have ht' : t ∈ Ici 0 := le_trans hs' hst
  have h1 : 0 ≤ f r - f t := sub_nonneg.mpr (h hr' ht' (hrs.trans hst))
  have h2 : 0 ≤ f r - f s := sub_nonneg.mpr (h hr' hs' hrs)
  have h3 : 0 ≤ f s - f t := sub_nonneg.mpr (h hs' ht' hst)
  simp only [abs_of_nonneg h1, abs_of_nonneg h2, abs_of_nonneg h3]
  linarith

end IsContinuousCompletelyMonotoneOnIoi

end TauCeti
