/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Perturbation.Basic

/-!
# Finite coefficient tests for uniform Gauss-small perturbations

For a nonzero series `f` restricted at `s` and `0 < r ≤ s`, finitely many coefficient
comparisons, together with a bound on the tail of a second series `g`, ensure
`‖f - g‖_t < ‖f‖_t` simultaneously for every `t ∈ [r, s]`. The finite comparisons and
the tail bound are all made at the single upper radius `s`. The cutoff and the positive
error tolerance depend only on `f`, `r`, and `s`. Positivity of the lower radius gives
a uniform positive tolerance. An explicit test also applies to any prescribed cutoff
and tolerance below the lower-radius Gauss norm, with tail bounds on both series
at `s`.

In particular, every sufficiently long polynomial truncation preserves the Gauss norm
and the complete set of active coefficient indices throughout the interval, including
its upper endpoint. The existing fixed-radius stability theorems also give preservation
of the first and last dominant indices. No completeness, discrete valuation, or
splitting assumption is needed.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

open Set Filter
open scoped Topology

namespace TauCeti.PowerSeries

open _root_.PowerSeries

variable {R : Type*} [SeminormedRing R] [IsUltrametricDist R]
  {f g : PowerSeries R} {r s δ : ℝ} {N : ℕ}

/-- An explicit finite coefficient-and-tail test at the upper radius gives a Gauss-small
perturbation throughout a closed interval of nonnegative radii. The tolerance need only
be strictly below the lower-radius Gauss norm. -/
theorem gaussNorm_sub_lt_of_coeff_le_of_tail_le (hr : 0 ≤ r)
    (hδ : δ < f.gaussNorm norm r)
    (hcoeff : ∀ n < N, ‖f.coeff n - g.coeff n‖ * s ^ n ≤ δ)
    (hftail : ∀ n, N ≤ n → ‖f.coeff n‖ * s ^ n ≤ δ)
    (hgtail : ∀ n, N ≤ n → ‖g.coeff n‖ * s ^ n ≤ δ) :
    ∀ t ∈ Icc r s, (f - g).gaussNorm norm t < f.gaussNorm norm t := by
  have hf := hasGaussNorm_of_tail_le hftail
  intro t ht
  have hterm (a : R) (n : ℕ) : ‖a‖ * t ^ n ≤ ‖a‖ * s ^ n :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hr.trans ht.1) ht.2 n) (norm_nonneg _)
  calc
    (f - g).gaussNorm norm t ≤ δ :=
      gaussNorm_sub_le_of_coeff_le_of_tail_le (hr.trans ht.1)
        (fun n hn => (hterm _ n).trans (hcoeff n hn))
        (fun n hn => (hterm _ n).trans (hftail n hn))
        (fun n hn => (hterm _ n).trans (hgtail n hn))
    _ < f.gaussNorm norm r := hδ
    _ ≤ f.gaussNorm norm t :=
      gaussNorm_le_gaussNorm_of_le norm_nonneg hr ht.1
        (hf.of_le norm_nonneg (hr.trans ht.1) ht.2)

/-- The finite coefficient-and-tail test preserves every active coefficient index uniformly
on the radius interval, without a restrictedness assumption on either series. -/
theorem norm_coeff_mul_pow_eq_gaussNorm_iff_of_coeff_le_of_tail_le (hr : 0 ≤ r)
    (hδ : δ < f.gaussNorm norm r)
    (hcoeff : ∀ n < N, ‖f.coeff n - g.coeff n‖ * s ^ n ≤ δ)
    (hftail : ∀ n, N ≤ n → ‖f.coeff n‖ * s ^ n ≤ δ)
    (hgtail : ∀ n, N ≤ n → ‖g.coeff n‖ * s ^ n ≤ δ) :
    ∀ t ∈ Icc r s, ∀ n : ℕ,
      ‖f.coeff n‖ * t ^ n = f.gaussNorm norm t ↔
        ‖g.coeff n‖ * t ^ n = g.gaussNorm norm t := by
  have hf := hasGaussNorm_of_tail_le hftail
  intro t ht n
  exact norm_coeff_mul_pow_eq_gaussNorm_iff_of_gaussNorm_sub_lt (hr.trans ht.1)
    (hf.of_le norm_nonneg (hr.trans ht.1) ht.2)
    ((hasGaussNorm_of_tail_le hgtail).of_le norm_nonneg (hr.trans ht.1) ht.2)
    (gaussNorm_sub_lt_of_coeff_le_of_tail_le hr hδ hcoeff hftail hgtail t ht) n

end TauCeti.PowerSeries

namespace PowerSeries.IsRestricted

open TauCeti.PowerSeries

variable {R : Type*} [NormedRing R] [IsUltrametricDist R]
  {f : PowerSeries R} {r s : ℝ}

/-- A finite coefficient test and one tail bound imply Gauss-small perturbation uniformly
on a closed interval of positive radii. The cutoff and tolerance can be chosen independently
of the perturbing series, and every larger cutoff works with the same tolerance.
No restrictedness hypothesis on that series is needed: a bound on its tail already gives
bounded weighted coefficients via `TauCeti.PowerSeries.hasGaussNorm_of_tail_le`. -/
theorem exists_nat_exists_pos_gaussNorm_sub_lt_of_coeff_le_of_tail_le
    (hf : f.IsRestricted s) (hf0 : f ≠ 0) (hr : 0 < r) :
    ∃ N : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ M : ℕ, N ≤ M → ∀ g : PowerSeries R,
      (∀ n < M, ‖f.coeff n - g.coeff n‖ * s ^ n ≤ δ) →
      (∀ n, M ≤ n → ‖g.coeff n‖ * s ^ n ≤ δ) →
      ∀ t ∈ Icc r s, (f - g).gaussNorm norm t < f.gaussNorm norm t := by
  by_cases hrs : r ≤ s
  · have hfs := hasGaussNorm_of_isRestricted hf
    have hfr := hfs.of_le norm_nonneg hr.le hrs
    have hpos := gaussNorm_pos hr hfr hf0
    let δ := f.gaussNorm norm r / 2
    have hδ : 0 < δ := half_pos hpos
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (((isRestricted_iff' s f).mp hf).eventually (gt_mem_nhds hδ))
    refine ⟨N, δ, hδ, fun M hM g hcoeff hg => ?_⟩
    exact gaussNorm_sub_lt_of_coeff_le_of_tail_le hr.le (half_lt_self hpos)
      hcoeff (fun n hn => (hN n (hM.trans hn)).le) hg
  · refine ⟨0, 1, zero_lt_one, ?_⟩
    intro M hM g hcoeff hg t ht
    exact (hrs (ht.1.trans ht.2)).elim

/-- Every sufficiently long polynomial truncation is a Gauss-small perturbation throughout
any closed interval of positive radii ending at a restricted radius. -/
theorem eventually_gaussNorm_sub_trunc_lt (hf : f.IsRestricted s) (hf0 : f ≠ 0)
    (hr : 0 < r) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc r s,
      (f - (f.trunc N : PowerSeries R)).gaussNorm norm t < f.gaussNorm norm t := by
  obtain ⟨N, δ, hδ, hN⟩ :=
    hf.exists_nat_exists_pos_gaussNorm_sub_lt_of_coeff_le_of_tail_le hf0 hr
  filter_upwards [eventually_ge_atTop N] with M hM
  apply hN M hM (f.trunc M)
  · intro n hn
    simpa [coeff_trunc, hn] using hδ.le
  · intro n hn
    simpa [coeff_trunc, not_lt.mpr hn] using hδ.le

/-- Sufficiently long polynomial truncations preserve the Gauss norm simultaneously
throughout a compact interval of positive radii. This includes the zero series. -/
theorem eventually_gaussNorm_trunc_eq (hf : f.IsRestricted s) (hr : 0 < r) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc r s,
      (f.trunc N : PowerSeries R).gaussNorm norm t = f.gaussNorm norm t := by
  obtain rfl | hf0 := eq_or_ne f 0
  · simp
  filter_upwards [hf.eventually_gaussNorm_sub_trunc_lt hf0 hr] with N hN t ht
  exact (gaussNorm_eq_of_gaussNorm_sub_lt (hr.le.trans ht.1)
    ((hasGaussNorm_of_isRestricted hf).of_le norm_nonneg (hr.le.trans ht.1) ht.2)
    (hasGaussNorm_of_isRestricted (isRestricted_polynomial (f.trunc N) (c := t)))
    (hN t ht)).symm

/-- Sufficiently long polynomial truncations have exactly the same active coefficient
indices as the series, simultaneously throughout a compact interval of positive radii.
This includes the zero series, for which every index is active. -/
theorem eventually_norm_coeff_trunc_mul_pow_eq_gaussNorm_iff (hf : f.IsRestricted s)
    (hr : 0 < r) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc r s, ∀ n : ℕ,
      ‖(f.trunc N).coeff n‖ * t ^ n = (f.trunc N : PowerSeries R).gaussNorm norm t ↔
        ‖f.coeff n‖ * t ^ n = f.gaussNorm norm t := by
  obtain rfl | hf0 := eq_or_ne f 0
  · simp [gaussNorm_zero norm _ (norm_zero : ‖(0 : R)‖ = 0)]
  filter_upwards [hf.eventually_gaussNorm_sub_trunc_lt hf0 hr] with N hN t ht n
  have hft := (hasGaussNorm_of_isRestricted hf).of_le norm_nonneg
    (hr.le.trans ht.1) ht.2
  simpa only [Polynomial.coeff_coe] using
    (norm_coeff_mul_pow_eq_gaussNorm_iff_of_gaussNorm_sub_lt
      (hr.le.trans ht.1) hft
      (hasGaussNorm_of_isRestricted (isRestricted_polynomial (f.trunc N) (c := t)))
      (hN t ht) n).symm

end PowerSeries.IsRestricted
