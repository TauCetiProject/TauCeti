/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.GaussNorm

/-!
# Active coefficients as the radius varies

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

At two positive radii `r < s`, every coefficient attaining the positive Gauss norm at `r`
has index at most every coefficient attaining it at `s`. Thus the last dominant index at `r`
is at most the first at `s`, and both extremal indices are nondecreasing with the radius.
These comparisons underlie the monotonicity of disc zero counts.

If one coefficient of a nonzero series attains the Gauss norm at both ends of a radius
interval, it is the unique attaining coefficient at every interior radius, provided the weighted
coefficients are bounded at the upper endpoint. The endpoints may have several attaining
coefficients. The order comparison needs only a seminormed ring; the interval statement uses
a normed ring to ensure that a nonzero series has positive Gauss norm and that the norm is
attained at interior radii.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

open Set Filter

namespace PowerSeries.IsRestricted

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
  obtain ⟨N, hN⟩ := hf.exists_nat_norm_coeff_mul_pow_lt_gaussNorm hf0 hr
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
  obtain ⟨N, hN⟩ := hf.exists_nat_norm_coeff_mul_pow_lt_gaussNorm hf0 hr
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

end PowerSeries.IsRestricted

namespace TauCeti.PowerSeries

open _root_.PowerSeries

section SeminormedRing

variable {R : Type*} [SeminormedRing R] {f : PowerSeries R} {r s : ℝ} {i j : ℕ}

/-- Active coefficient indices are ordered across strictly increasing positive radii.
Boundedness suffices; the Gauss supremum need not be attained at other indices or radii.
Positivity excludes series all of whose coefficients have seminorm zero. -/
theorem index_le_of_norm_coeff_mul_pow_eq (hr : 0 < r) (hrs : r < s)
    (hfs : f.HasGaussNorm norm s)
    (hpos : 0 < f.gaussNorm norm r)
    (hi : ‖f.coeff i‖ * r ^ i = f.gaussNorm norm r)
    (hj : ‖f.coeff j‖ * s ^ j = f.gaussNorm norm s) : i ≤ j := by
  by_contra hij
  have hji : j < i := Nat.lt_of_not_ge hij
  have hcoeff : 0 < ‖f.coeff i‖ := by
    have := hi ▸ hpos
    exact pos_of_mul_pos_left this (pow_nonneg hr.le i)
  have hri : r ^ i = r ^ (i - j) * r ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hji.le]
  have hsi : s ^ i = s ^ (i - j) * s ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hji.le]
  have hfr := hfs.of_le norm_nonneg hr.le hrs.le
  have h₁ := le_gaussNorm norm r f hfr j
  have h₂ := le_gaussNorm norm s f hfs i
  rw [← hi, hri, ← mul_assoc, mul_le_mul_iff_left₀ (pow_pos hr j)] at h₁
  rw [← hj, hsi, ← mul_assoc,
    mul_le_mul_iff_left₀ (pow_pos (hr.trans hrs) j)] at h₂
  have hpow := (mul_le_mul_iff_right₀ hcoeff).mp (h₂.trans h₁)
  exact (pow_lt_pow_left₀ hrs hr.le (Nat.sub_ne_zero_of_lt hji)).not_ge hpow

/-- The last dominant index at a smaller positive radius is at most the first dominant index
at a larger radius. In zero-counting applications this compares a closed smaller disc
with an open larger disc. -/
theorem IsDistinguished.le_isLowestDominant_of_lt (hi : IsDistinguished r i f)
    (hj : IsLowestDominant s j f) (hr : 0 < r) (hrs : r < s) : i ≤ j :=
  index_le_of_norm_coeff_mul_pow_eq hr hrs hj.hasGaussNorm
    hi.gaussNorm_pos hi.norm_coeff_mul_pow_eq hj.norm_coeff_mul_pow_eq

/-- The last dominant index is nondecreasing with the positive radius. -/
theorem IsDistinguished.le_of_le (hi : IsDistinguished r i f) (hj : IsDistinguished s j f)
    (hr : 0 < r) (hrs : r ≤ s) : i ≤ j := by
  rcases hrs.eq_or_lt with rfl | hrs
  · exact (hi.unique hj).le
  · exact index_le_of_norm_coeff_mul_pow_eq hr hrs hj.hasGaussNorm
      hi.gaussNorm_pos hi.norm_coeff_mul_pow_eq hj.norm_coeff_mul_pow_eq

/-- The first dominant index is nondecreasing with the positive radius. -/
theorem IsLowestDominant.le_of_le (hi : IsLowestDominant r i f) (hj : IsLowestDominant s j f)
    (hr : 0 < r) (hrs : r ≤ s) : i ≤ j := by
  rcases hrs.eq_or_lt with rfl | hrs
  · exact (hi.unique hj).le
  · exact index_le_of_norm_coeff_mul_pow_eq hr hrs hj.hasGaussNorm
      hi.gaussNorm_pos hi.norm_coeff_mul_pow_eq hj.norm_coeff_mul_pow_eq

end SeminormedRing

section NormedRing

variable {R : Type*} [NormedRing R] {f : PowerSeries R} {r s t : ℝ} {i : ℕ}

/-- A coefficient attaining the Gauss norm at both ends of an interval is the unique attaining
coefficient at every interior radius. Boundedness at the upper endpoint ensures restrictedness
and attainment at interior radii, even when the series is not restricted at that endpoint. -/
theorem norm_coeff_mul_pow_eq_iff_of_attains_at_endpoints (hr : 0 < r)
    (hrt : r < t) (hts : t < s) (hf : f.HasGaussNorm norm s) (hf0 : f ≠ 0)
    (hi : ‖f.coeff i‖ * r ^ i = f.gaussNorm norm r)
    (hi' : ‖f.coeff i‖ * s ^ i = f.gaussNorm norm s) (j : ℕ) :
    ‖f.coeff j‖ * t ^ j = f.gaussNorm norm t ↔ j = i := by
  have ht : 0 < t := hr.trans hrt
  have hfr := hf.of_le norm_nonneg hr.le (hrt.trans hts).le
  have hft := hf.isRestricted_of_abs_lt (c := t) (by simpa [abs_of_pos ht] using hts)
  have hbt := hf.of_le norm_nonneg ht.le hts.le
  have hpr := gaussNorm_pos hr hfr hf0
  have hpt := gaussNorm_pos ht hbt hf0
  have heq (k : ℕ) (hk : ‖f.coeff k‖ * t ^ k = f.gaussNorm norm t) : k = i :=
    le_antisymm (index_le_of_norm_coeff_mul_pow_eq ht hts hf hpt hk hi')
      (index_le_of_norm_coeff_mul_pow_eq hr hrt hbt hpr hi hk)
  constructor
  · exact heq j
  · rintro rfl
    obtain ⟨k, hk⟩ := exists_isDistinguished ht hft hf0
    simpa only [heq k hk.norm_coeff_mul_pow_eq] using hk.norm_coeff_mul_pow_eq

end NormedRing

end TauCeti.PowerSeries
