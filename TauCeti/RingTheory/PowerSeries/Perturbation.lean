/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.GaussNorm
import TauCeti.Analysis.Normed.Group.Ultra

/-!
# Stability of Gauss norms and dominant coefficients

Over an ultrametric seminormed ring, a perturbation smaller than a power series in the Gauss
norm preserves its Gauss norm and every degree attaining that norm. Consequently it preserves
both the distinguished degree and the lowest dominant degree. These statements require only
bounded weighted coefficients, so apply in particular to restricted power series without any
completeness assumption.
-/

public section

namespace TauCeti.PowerSeries

variable {R : Type*} [SeminormedRing R] [IsUltrametricDist R]
  {c : ℝ} {f g : PowerSeries R} {s : ℕ}

/-- A perturbation strictly smaller in Gauss norm preserves the Gauss norm, at any nonnegative
radius where both series have bounded weighted coefficients. -/
theorem gaussNorm_eq_of_gaussNorm_sub_lt (hc : 0 ≤ c)
    (hf : f.HasGaussNorm norm c) (hg : g.HasGaussNorm norm c)
    (h : (f - g).gaussNorm norm c < f.gaussNorm norm c) :
    f.gaussNorm norm c = g.gaussNorm norm c := by
  have hneg : (-g).HasGaussNorm norm c := by
    simpa only [PowerSeries.HasGaussNorm, map_neg, norm_neg] using hg
  have hsub : (f - g).HasGaussNorm norm c := by
    simpa only [sub_eq_add_neg] using hasGaussNorm_add hc hf hneg
  have hrev : (g - f).HasGaussNorm norm c := by
    simpa only [PowerSeries.HasGaussNorm, map_sub, norm_sub_rev] using hsub
  have heq : (g - f).gaussNorm norm c = (f - g).gaussNorm norm c := by
    simp_rw [PowerSeries.gaussNorm_eq, map_sub, norm_sub_rev (g.coeff _)]
  have hfle := PowerSeries.gaussNorm_add_le_max norm c (f - g) g hc norm_nonneg
    IsUltrametricDist.isNonarchimedean_norm hsub hg
  rw [sub_add_cancel] at hfle
  have hgle := PowerSeries.gaussNorm_add_le_max norm c (g - f) f hc norm_nonneg
    IsUltrametricDist.isNonarchimedean_norm hrev hf
  rw [sub_add_cancel, heq, max_eq_right h.le] at hgle
  exact le_antisymm (le_of_not_gt fun hlt ↦ (max_lt h hlt).not_ge hfle) hgle

/-- A perturbation strictly smaller in Gauss norm preserves exactly the degrees at which the
weighted coefficient norm attains the Gauss norm. -/
theorem norm_coeff_mul_pow_eq_gaussNorm_iff_of_gaussNorm_sub_lt (hc : 0 ≤ c)
    (hf : f.HasGaussNorm norm c) (hg : g.HasGaussNorm norm c)
    (h : (f - g).gaussNorm norm c < f.gaussNorm norm c) (n : ℕ) :
    ‖f.coeff n‖ * c ^ n = f.gaussNorm norm c ↔
      ‖g.coeff n‖ * c ^ n = g.gaussNorm norm c := by
  have hnorm := gaussNorm_eq_of_gaussNorm_sub_lt hc hf hg h
  have hneg : (-g).HasGaussNorm norm c := by
    simpa only [PowerSeries.HasGaussNorm, map_neg, norm_neg] using hg
  have hsub : (f - g).HasGaussNorm norm c := by
    simpa only [sub_eq_add_neg] using hasGaussNorm_add hc hf hneg
  have hcoeff := (PowerSeries.le_gaussNorm norm c (f - g) hsub n).trans_lt h
  rw [map_sub] at hcoeff
  have key {a b : R} (ha : ‖a - b‖ * c ^ n < ‖a‖ * c ^ n) : ‖a‖ = ‖b‖ :=
    IsUltrametricDist.norm_eq_of_norm_sub_lt_left
      (lt_of_mul_lt_mul_right ha (pow_nonneg hc n))
  constructor
  · intro hn
    have heq := key (hn ▸ hcoeff)
    rw [← heq, hn, hnorm]
  · intro hn
    have hcoeff' : ‖g.coeff n - f.coeff n‖ * c ^ n < ‖g.coeff n‖ * c ^ n := by
      simpa only [norm_sub_rev, hn, ← hnorm] using hcoeff
    rw [← key hcoeff', hn, hnorm]

/-- A perturbation strictly smaller in Gauss norm preserves distinguishedness in every degree. -/
theorem isDistinguished_iff_of_gaussNorm_sub_lt (hc : 0 ≤ c)
    (hf : f.HasGaussNorm norm c) (hg : g.HasGaussNorm norm c)
    (h : (f - g).gaussNorm norm c < f.gaussNorm norm c) :
    IsDistinguished c s f ↔ IsDistinguished c s g := by
  have heq := norm_coeff_mul_pow_eq_gaussNorm_iff_of_gaussNorm_sub_lt hc hf hg h
  constructor
  · intro hs
    refine ⟨(heq s).mp hs.norm_coeff_mul_pow_eq, fun m hm ↦ ?_⟩
    exact lt_of_le_of_ne (PowerSeries.le_gaussNorm norm c g hg m) fun hgm ↦
      (hs.norm_coeff_mul_pow_lt m hm).ne ((heq m).mpr hgm)
  · intro hs
    refine ⟨(heq s).mpr hs.norm_coeff_mul_pow_eq, fun m hm ↦ ?_⟩
    exact lt_of_le_of_ne (PowerSeries.le_gaussNorm norm c f hf m) fun hfm ↦
      (hs.norm_coeff_mul_pow_lt m hm).ne ((heq m).mp hfm)

/-- A perturbation strictly smaller in Gauss norm preserves the lowest dominant degree. -/
theorem isLowestDominant_iff_of_gaussNorm_sub_lt (hc : 0 ≤ c)
    (hf : f.HasGaussNorm norm c) (hg : g.HasGaussNorm norm c)
    (h : (f - g).gaussNorm norm c < f.gaussNorm norm c) :
    IsLowestDominant c s f ↔ IsLowestDominant c s g := by
  have hnorm := gaussNorm_eq_of_gaussNorm_sub_lt hc hf hg h
  have heq := norm_coeff_mul_pow_eq_gaussNorm_iff_of_gaussNorm_sub_lt hc hf hg h
  constructor
  · intro hs
    refine ⟨hnorm ▸ hs.gaussNorm_pos, (heq s).mp hs.norm_coeff_mul_pow_eq, fun m hm ↦ ?_⟩
    exact lt_of_le_of_ne (PowerSeries.le_gaussNorm norm c g hg m) fun hgm ↦
      (hs.norm_coeff_mul_pow_lt m hm).ne ((heq m).mpr hgm)
  · intro hs
    refine ⟨hnorm.symm ▸ hs.gaussNorm_pos, (heq s).mpr hs.norm_coeff_mul_pow_eq, fun m hm ↦ ?_⟩
    exact lt_of_le_of_ne (PowerSeries.le_gaussNorm norm c f hf m) fun hfm ↦
      (hs.norm_coeff_mul_pow_lt m hm).ne ((heq m).mp hfm)

end TauCeti.PowerSeries
