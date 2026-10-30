/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.GaussNorm

/-!
# Dominant coefficients as the radius varies

At two positive radii `r < s`, every coefficient attaining the positive Gauss norm at `r`
has index at most every coefficient attaining it at `s`. In particular, the last dominant
index at `r` is at most the first at `s`, and both extremal indices are nondecreasing
with the radius. These comparisons underlie the monotonicity of disc zero counts.

If one coefficient of a nonzero series attains the Gauss norm at both ends of a radius
interval, it is the unique attaining coefficient at every interior radius, provided the weighted
coefficients are bounded at the upper endpoint. The endpoints themselves may have several attaining
coefficients.

The order comparison needs only bounded weighted coefficients and a seminormed ring;
there is no ultrametricity, completeness, or valuation hypothesis. A normed ring enters
only to ensure attainment at interior radii in the interval statement.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

namespace PowerSeries

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
  have hfr : f.HasGaussNorm norm r :=
    ⟨f.gaussNorm norm s, Set.forall_mem_range.mpr fun n =>
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hrs.le n) (norm_nonneg _)).trans
        (le_gaussNorm norm s f hfs n)⟩
  have h₁ := le_gaussNorm norm r f hfr j
  have h₂ := le_gaussNorm norm s f hfs i
  rw [← hi, hri, ← mul_assoc, mul_le_mul_iff_left₀ (pow_pos hr j)] at h₁
  rw [← hj, hsi, ← mul_assoc,
    mul_le_mul_iff_left₀ (pow_pos (hr.trans hrs) j)] at h₂
  have hpow := (mul_le_mul_iff_right₀ hcoeff).mp (h₂.trans h₁)
  exact (pow_lt_pow_left₀ hrs hr.le (Nat.sub_ne_zero_of_lt hji)).not_ge hpow

end PowerSeries

namespace TauCeti.PowerSeries

variable {R : Type*} [SeminormedRing R] {f : PowerSeries R} {r s : ℝ} {i j : ℕ}

/-- The last dominant index at a smaller positive radius is at most the first dominant index
at a larger radius. In zero-counting applications this compares a closed smaller disc
with an open larger disc. -/
theorem IsDistinguished.le_isLowestDominant_of_lt (hi : IsDistinguished r i f)
    (hj : IsLowestDominant s j f) (hr : 0 < r) (hrs : r < s)
    (hfs : f.HasGaussNorm norm s) : i ≤ j :=
  PowerSeries.index_le_of_norm_coeff_mul_pow_eq hr hrs hfs
    hi.gaussNorm_pos hi.norm_coeff_mul_pow_eq hj.norm_coeff_mul_pow_eq

/-- The last dominant index is nondecreasing with the positive radius. -/
theorem IsDistinguished.mono (hi : IsDistinguished r i f) (hj : IsDistinguished s j f)
    (hr : 0 < r) (hrs : r ≤ s) : i ≤ j := by
  rcases hrs.eq_or_lt with rfl | hrs
  · exact (hi.unique hj).le
  · exact PowerSeries.index_le_of_norm_coeff_mul_pow_eq hr hrs hj.hasGaussNorm
      hi.gaussNorm_pos hi.norm_coeff_mul_pow_eq hj.norm_coeff_mul_pow_eq

/-- The first dominant index is nondecreasing with the positive radius. Weighted coefficient
boundedness is explicit because lowest dominance alone does not bound the later coefficients. -/
theorem IsLowestDominant.mono (hi : IsLowestDominant r i f) (hj : IsLowestDominant s j f)
    (hr : 0 < r) (hrs : r ≤ s) (hfs : f.HasGaussNorm norm s) : i ≤ j := by
  rcases hrs.eq_or_lt with rfl | hrs
  · exact (hi.unique hj).le
  · exact PowerSeries.index_le_of_norm_coeff_mul_pow_eq hr hrs hfs
      hi.gaussNorm_pos hi.norm_coeff_mul_pow_eq hj.norm_coeff_mul_pow_eq

end TauCeti.PowerSeries

namespace PowerSeries

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
  have hfr := TauCeti.PowerSeries.hasGaussNorm_of_isRestricted
    (hf.isRestricted_of_abs_lt (c := r) (by simpa [abs_of_pos hr] using hrt.trans hts))
  have hft := hf.isRestricted_of_abs_lt (c := t) (by simpa [abs_of_pos ht] using hts)
  have hbt := TauCeti.PowerSeries.hasGaussNorm_of_isRestricted hft
  have hpr := TauCeti.PowerSeries.gaussNorm_pos hr hfr hf0
  have hpt := TauCeti.PowerSeries.gaussNorm_pos ht hbt hf0
  have heq (k : ℕ) (hk : ‖f.coeff k‖ * t ^ k = f.gaussNorm norm t) : k = i :=
    le_antisymm (index_le_of_norm_coeff_mul_pow_eq ht hts hf hpt hk hi')
      (index_le_of_norm_coeff_mul_pow_eq hr hrt hbt hpr hi hk)
  constructor
  · exact heq j
  · rintro rfl
    obtain ⟨k, hk⟩ := TauCeti.PowerSeries.exists_isDistinguished ht hft hf0
    simpa only [heq k hk.norm_coeff_mul_pow_eq] using hk.norm_coeff_mul_pow_eq

end PowerSeries
