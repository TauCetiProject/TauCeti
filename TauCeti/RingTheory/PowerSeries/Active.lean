/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.GaussNorm

/-!
# Uniform finite control of active coefficients

A coefficient is active at a radius if its weighted norm equals the Gauss norm. For a
nonzero series restricted at `s`, only finitely many coefficient indices can be active
as the radius varies in `[r, s]`, where `r > 0`. More precisely, all sufficiently late
coefficients have weighted norm strictly below the Gauss norm throughout this interval.
Consequently one finite family of weighted coefficient norms computes every Gauss norm
on the interval.

These results supply finite coefficient data for the local variation of Newton
supporting values. They hold over any normed ring: no completeness, ultrametricity, or
valuation normalisation is needed. Restrictedness at the upper radius is essential;
bounded weighted coefficients alone need not give finite active sets at that radius.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

open Set Filter

namespace PowerSeries

variable {R : Type*} [NormedRing R] {f : PowerSeries R} {r s : ℝ}

/-- On a closed interval of positive radii up to a restricted radius, every sufficiently
late coefficient has weighted norm strictly smaller than the Gauss norm, uniformly in
the radius. -/
theorem exists_nat_norm_coeff_mul_pow_lt_gaussNorm (hf : f.IsRestricted s) (hf0 : f ≠ 0)
    (hr : 0 < r) :
    ∃ N : ℕ, ∀ t ∈ Icc r s, ∀ n, N < n →
      ‖f.coeff n‖ * t ^ n < f.gaussNorm norm t := by
  obtain ⟨k, hk⟩ : ∃ k, f.coeff k ≠ 0 := by
    simpa only [not_forall] using (forall_coeff_eq_zero f).not.mpr hf0
  have hpos : 0 < ‖f.coeff k‖ * r ^ k := mul_pos (norm_pos_iff.mpr hk) (pow_pos hr _)
  have htail := ((isRestricted_iff s f).mp hf).eventually (gt_mem_nhds hpos)
  rw [Nat.cofinite_eq_atTop] at htail
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  refine ⟨N, fun t ht n hn => ?_⟩
  have htf : f.HasGaussNorm norm t := TauCeti.PowerSeries.hasGaussNorm_of_isRestricted
    (TauCeti.PowerSeries.isRestricted_of_abs_le hf (abs_le_abs_of_nonneg (hr.le.trans ht.1) ht.2))
  calc
    ‖f.coeff n‖ * t ^ n ≤ ‖f.coeff n‖ * s ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hr.le.trans ht.1) ht.2 n) (norm_nonneg _)
    _ < ‖f.coeff k‖ * r ^ k := hN n hn.le
    _ ≤ ‖f.coeff k‖ * t ^ k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le ht.1 k) (norm_nonneg _)
    _ ≤ f.gaussNorm norm t := le_gaussNorm norm t f htf k

/-- Only finitely many indices can attain the Gauss norm anywhere in a closed interval
of positive radii up to a restricted radius. The nonzero hypothesis excludes the zero
series, for which every coefficient is active. -/
theorem finite_setOf_exists_norm_coeff_mul_pow_eq_gaussNorm (hf : f.IsRestricted s)
    (hf0 : f ≠ 0) (hr : 0 < r) :
    {n | ∃ t ∈ Icc r s, ‖f.coeff n‖ * t ^ n = f.gaussNorm norm t}.Finite := by
  obtain ⟨N, hN⟩ := exists_nat_norm_coeff_mul_pow_lt_gaussNorm hf hf0 hr
  apply (finite_Iic N).subset
  rintro n ⟨t, ht, hn⟩
  exact le_of_not_gt fun h => (hN t ht n h).ne hn

/-- On a closed interval of positive radii up to a restricted radius, one finite initial
family of coefficients computes every Gauss norm as a maximum. -/
theorem exists_nat_gaussNorm_eq_sup' (hf : f.IsRestricted s) (hr : 0 < r) :
    ∃ N : ℕ, ∀ t ∈ Icc r s, f.gaussNorm norm t =
      (Finset.range (N + 1)).sup' (by simp) (fun n => ‖f.coeff n‖ * t ^ n) := by
  obtain rfl | hf0 := eq_or_ne f 0
  · refine ⟨0, fun t _ => ?_⟩
    simp [gaussNorm_zero norm t (norm_zero : ‖(0 : R)‖ = 0)]
  obtain ⟨N, hN⟩ := exists_nat_norm_coeff_mul_pow_lt_gaussNorm hf hf0 hr
  refine ⟨N, fun t ht => ?_⟩
  have htf := TauCeti.PowerSeries.isRestricted_of_abs_le hf
    (abs_le_abs_of_nonneg (hr.le.trans ht.1) ht.2)
  have hbd := TauCeti.PowerSeries.hasGaussNorm_of_isRestricted htf
  obtain ⟨k, hk⟩ := TauCeti.PowerSeries.exists_isDistinguished (hr.trans_le ht.1) htf hf0
  have hkN : k ≤ N := hk.le_of_forall_lt (hN t ht)
  apply le_antisymm
  · rw [← hk.norm_coeff_mul_pow_eq]
    exact Finset.le_sup' (fun n => ‖f.coeff n‖ * t ^ n) (Finset.mem_range.mpr (by omega))
  · exact Finset.sup'_le _ _ fun n _ => le_gaussNorm norm t f hbd n

end PowerSeries
