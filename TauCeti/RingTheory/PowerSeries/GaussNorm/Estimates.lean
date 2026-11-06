/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.GaussNorm

/-!
# Estimates for the Gauss norm of restricted series

Elementary bounds on the Gauss norm of restricted power series over a normed ring: the Gauss norm
of a product of restricted series with a bounded first factor, the ultrametric bound for a
difference, and the approximation of a restricted series by a truncation leaving a small tail.

## Main results

* `TauCeti.PowerSeries.gaussNorm_mul_le_of_le`: the Gauss norm of a product of restricted series
  is bounded by a bound on the first factor times the Gauss norm of the second.
* `TauCeti.PowerSeries.gaussNorm_sub_le_of_le`: the Gauss norm of a difference is bounded by a
  common bound on the two Gauss norms, over an ultrametric ring.
* `TauCeti.PowerSeries.exists_gaussNorm_trunc_sub_le`: some truncation of a restricted series has
  Gauss norm at most that of the series and leaves a tail of Gauss norm at most `θ` times it.
-/

public section

namespace TauCeti.PowerSeries

variable {R : Type*} [NormedRing R] {c : ℝ} {f : PowerSeries R}

section Ultrametric

variable [IsUltrametricDist R]

/-- The Gauss norm of a product of restricted series is bounded by a bound on the first factor
times the Gauss norm of the second. -/
theorem gaussNorm_mul_le_of_le (hc : 0 ≤ c) {a b : PowerSeries R} (ha : a.IsRestricted c)
    (hb : b.IsRestricted c) {C : ℝ} (h : a.gaussNorm norm c ≤ C) :
    (a * b).gaussNorm norm c ≤ C * b.gaussNorm norm c := by
  refine le_trans (gaussNorm_mul_le hc (hasGaussNorm_of_isRestricted ha)
    (hasGaussNorm_of_isRestricted hb)) ?_
  exact mul_le_mul_of_nonneg_right h (PowerSeries.gaussNorm_nonneg norm c _ norm_nonneg)

/-- The Gauss norm of a difference of series with Gauss norm is bounded when both Gauss norms
are. -/
theorem gaussNorm_sub_le_of_le (hc : 0 ≤ c) {a b : PowerSeries R} (ha : a.HasGaussNorm norm c)
    (hb : b.HasGaussNorm norm c) {C : ℝ} (ha' : a.gaussNorm norm c ≤ C)
    (hb' : b.gaussNorm norm c ≤ C) :
    (a - b).gaussNorm norm c ≤ C := by
  rw [sub_eq_add_neg]
  have hbneg : (-b).HasGaussNorm norm c := by
    simpa only [PowerSeries.HasGaussNorm, map_neg, norm_neg] using hb
  refine le_trans (PowerSeries.gaussNorm_add_le_max norm c a (-b) hc norm_nonneg
    IsUltrametricDist.isNonarchimedean_norm ha hbneg) (max_le ha' ?_)
  exact (MvPowerSeries.gaussNorm_neg norm (fun _ ↦ c) (fun x ↦ norm_neg x) b).trans_le hb'

end Ultrametric

/-- Some truncation of a restricted series `f` has Gauss norm at most `‖f‖` and leaves a tail of
Gauss norm at most `θ * ‖f‖`. -/
theorem exists_gaussNorm_trunc_sub_le (hf : f.IsRestricted c) {θ : ℝ} (hθ : 0 < θ)
    (hfpos : 0 < f.gaussNorm norm c) :
    ∃ N, ((f.trunc N : Polynomial R) : PowerSeries R).gaussNorm norm c ≤ f.gaussNorm norm c ∧
      (f - ((f.trunc N : Polynomial R) : PowerSeries R)).gaussNorm norm c
        ≤ θ * f.gaussNorm norm c := by
  obtain ⟨N, hN⟩ : ∃ N, ∀ m, N ≤ m → ‖f.coeff m‖ * c ^ m ≤ θ * f.gaussNorm norm c := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (((PowerSeries.isRestricted_iff' c f).mp hf).eventually
        (gt_mem_nhds (mul_pos hθ hfpos)))
    exact ⟨N, fun m hm ↦ (hN m hm).le⟩
  have hfcoeff (m : ℕ) : ((f.trunc N : Polynomial R) : PowerSeries R).coeff m =
      if m < N then f.coeff m else 0 := by
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  have hFn : ((f.trunc N : Polynomial R) : PowerSeries R).gaussNorm norm c
      ≤ f.gaussNorm norm c := by
    rw [PowerSeries.gaussNorm_eq]
    refine ciSup_le fun m ↦ ?_
    rw [hfcoeff m]
    split_ifs
    · exact PowerSeries.le_gaussNorm norm c f (hasGaussNorm_of_isRestricted hf) m
    · simpa using PowerSeries.gaussNorm_nonneg norm c f norm_nonneg
  have hsmall : (f - ((f.trunc N : Polynomial R) : PowerSeries R)).gaussNorm norm c
      ≤ θ * f.gaussNorm norm c := by
    rw [PowerSeries.gaussNorm_eq]
    refine ciSup_le fun m ↦ ?_
    rw [map_sub, hfcoeff m]
    split_ifs with hm
    · simp only [sub_self, norm_zero, zero_mul]
      exact mul_nonneg hθ.le hfpos.le
    · rw [sub_zero]
      exact hN m (by omega)
  exact ⟨N, hFn, hsmall⟩

end TauCeti.PowerSeries
