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
norm preserves its Gauss norm and every degree attaining that norm; such a series is necessarily
nonzero. Consequently the perturbation preserves both the distinguished degree and the lowest
dominant degree. These statements require only bounded weighted coefficients, so apply in
particular to restricted power series without any completeness assumption.

At any nonnegative radius, finite coefficient error bounds together with tail bounds on both
series at the same tolerance bound the Gauss norm of their difference.
-/

public section

namespace TauCeti.PowerSeries

open _root_.PowerSeries

section CoefficientBounds

variable {R : Type*} [SeminormedRing R] [IsUltrametricDist R]
  {f g : PowerSeries R} {s δ : ℝ} {N : ℕ}

/-- Finite coefficient error bounds and separate bounds on the two tails bound the Gauss
norm of the difference. All bounds use the same tolerance at a nonnegative radius. -/
theorem gaussNorm_sub_le_of_coeff_le_of_tail_le (hs : 0 ≤ s)
    (hcoeff : ∀ n < N, ‖f.coeff n - g.coeff n‖ * s ^ n ≤ δ)
    (hf : ∀ n, N ≤ n → ‖f.coeff n‖ * s ^ n ≤ δ)
    (hg : ∀ n, N ≤ n → ‖g.coeff n‖ * s ^ n ≤ δ) :
    (f - g).gaussNorm norm s ≤ δ := by
  rw [gaussNorm_eq]
  refine ciSup_le fun n => ?_
  by_cases hn : n < N
  · simpa only [map_sub] using hcoeff n hn
  · have h := norm_coeff_add_mul_pow_le_max f (-g) hs n
    rw [← sub_eq_add_neg] at h
    exact h.trans (max_le (hf n (Nat.le_of_not_gt hn))
      (by simpa using hg n (Nat.le_of_not_gt hn)))

end CoefficientBounds

variable {R : Type*} [SeminormedRing R] [IsUltrametricDist R]
  {c : ℝ} {f g : PowerSeries R} {s : ℕ}

omit [IsUltrametricDist R] in
/-- A series admitting a perturbation strictly smaller in Gauss norm is nonzero. -/
theorem ne_zero_of_gaussNorm_sub_lt (h : (f - g).gaussNorm norm c < f.gaussNorm norm c) :
    f ≠ 0 := by
  rintro rfl
  exact h.not_ge <| by
    rw [PowerSeries.gaussNorm_zero norm c norm_zero]
    exact PowerSeries.gaussNorm_nonneg norm c _ norm_nonneg

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
  have hfle := PowerSeries.gaussNorm_add_le_max norm c (f - g) g hc norm_nonneg
    IsUltrametricDist.isNonarchimedean_norm hsub hg
  rw [sub_add_cancel] at hfle
  have hgle := PowerSeries.gaussNorm_add_le_max norm c (g - f) f hc norm_nonneg
    IsUltrametricDist.isNonarchimedean_norm hrev hf
  rw [sub_add_cancel, gaussNorm_sub_comm g f c, max_eq_right h.le] at hgle
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

section NormedRing

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] {c : ℝ} {f g : PowerSeries R}

/-- If `f` is restricted at `c ≥ 0`, `g` has bounded weighted coefficients at `c`, and
`‖f - g‖_c < ‖f‖_c`, then `f` and `g` share a common distinguished degree and a common lowest
dominant degree at `c`. -/
theorem exists_isDistinguished_and_isLowestDominant_of_gaussNorm_sub_lt (hc : 0 ≤ c)
    (hf : f.IsRestricted c) (hg : g.HasGaussNorm norm c)
    (h : (f - g).gaussNorm norm c < f.gaussNorm norm c) :
    ∃ d l, IsDistinguished c d f ∧ IsDistinguished c d g ∧
      IsLowestDominant c l f ∧ IsLowestDominant c l g := by
  have hfh : f.HasGaussNorm norm c := hasGaussNorm_of_isRestricted hf
  have ⟨d, l, hd, hl⟩ : ∃ d l, IsDistinguished c d f ∧ IsLowestDominant c l f := by
    rcases hc.eq_or_lt with rfl | hcpos
    · have hpos : 0 < f.gaussNorm norm 0 :=
        (PowerSeries.gaussNorm_nonneg norm 0 (f - g) norm_nonneg).trans_lt h
      have h0 : f.gaussNorm norm 0 = ‖f.coeff 0‖ * (0 : ℝ) ^ 0 :=
        gaussNorm_eq_of_forall_le (s := 0) fun n ↦ by
          rcases eq_or_ne n 0 with rfl | hn
          · exact le_rfl
          · simp [zero_pow hn]
      have hd : IsDistinguished 0 0 f :=
        ⟨h0.symm, fun m hm ↦ by simpa [zero_pow hm.ne'] using hpos⟩
      exact ⟨0, 0, hd, hd.isLowestDominant_zero⟩
    · have hf0 := ne_zero_of_gaussNorm_sub_lt h
      obtain ⟨d, hd⟩ := exists_isDistinguished hcpos hf hf0
      obtain ⟨l, hl⟩ := exists_isLowestDominant hcpos hf hf0
      exact ⟨d, l, hd, hl⟩
  exact ⟨d, l, hd, (isDistinguished_iff_of_gaussNorm_sub_lt hc hfh hg h).mp hd,
    hl, (isLowestDominant_iff_of_gaussNorm_sub_lt hc hfh hg h).mp hl⟩

end NormedRing

end TauCeti.PowerSeries
