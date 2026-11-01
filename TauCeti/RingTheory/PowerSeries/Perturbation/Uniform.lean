/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Perturbation.Basic
import TauCeti.Analysis.Normed.Group.Ultra

/-!
# Finite coefficient tests for uniform Gauss-small perturbations

For a nonzero series `f` restricted at `s` and `0 < r ≤ s`, finitely many coefficient
comparisons, together with a bound on the tail of a second series `g`, ensure
`‖f - g‖_t < ‖f‖_t` simultaneously for every `t ∈ [r, s]`. The finite comparisons and
the tail bound are all made at the single upper radius `s`. The cutoff and the positive
error tolerance depend only on `f`, `r`, and `s`.

The lower radius is positive so that `f` has a positive Gauss norm there. Its Gauss norm
is no smaller at any radius in the interval. Restrictedness at the upper radius makes
the tail uniformly smaller than this lower bound. The ultrametric inequality then
controls the difference of the two tails without adding their error bounds.

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

section SeminormedRing

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
  rw [map_sub]
  by_cases hn : n < N
  · exact hcoeff n hn
  · calc
      ‖f.coeff n - g.coeff n‖ * s ^ n ≤ max ‖f.coeff n‖ ‖g.coeff n‖ * s ^ n :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_sub_le_max _ _) (pow_nonneg hs n)
      _ = max (‖f.coeff n‖ * s ^ n) (‖g.coeff n‖ * s ^ n) :=
        max_mul_of_nonneg _ _ (pow_nonneg hs n)
      _ ≤ δ := max_le (hf n (Nat.le_of_not_gt hn)) (hg n (Nat.le_of_not_gt hn))

end SeminormedRing

section NormedRing

variable {R : Type*} [NormedRing R] [IsUltrametricDist R]
  {f : PowerSeries R} {r s : ℝ}

/-- A finite coefficient test and one tail bound imply Gauss-small perturbation uniformly
on a closed interval of positive radii. The cutoff and tolerance can be chosen independently
of the perturbing series, and every larger cutoff works with the same tolerance.
No restrictedness hypothesis on that series is needed for the
inequality: the coefficient bounds already bound its weighted coefficients. -/
theorem exists_nat_pos_gaussNorm_sub_lt_of_coeff_le_of_tail_le
    (hf : f.IsRestricted s) (hf0 : f ≠ 0) (hr : 0 < r) (hrs : r ≤ s) :
    ∃ N : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ M : ℕ, N ≤ M → ∀ g : PowerSeries R,
      (∀ n < M, ‖f.coeff n - g.coeff n‖ * s ^ n ≤ δ) →
      (∀ n, M ≤ n → ‖g.coeff n‖ * s ^ n ≤ δ) →
      ∀ t ∈ Icc r s, (f - g).gaussNorm norm t < f.gaussNorm norm t := by
  have hfs := hasGaussNorm_of_isRestricted hf
  have hfr := hfs.of_le norm_nonneg hr.le hrs
  have hpos := gaussNorm_pos hr hfr hf0
  let δ := f.gaussNorm norm r / 2
  have hδ : 0 < δ := half_pos hpos
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (((isRestricted_iff' s f).mp hf).eventually (gt_mem_nhds hδ))
  refine ⟨N, δ, hδ, fun M hM g hcoeff hg t ht => ?_⟩
  have hterm (a : R) (n : ℕ) : ‖a‖ * t ^ n ≤ ‖a‖ * s ^ n :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hr.le.trans ht.1) ht.2 n) (norm_nonneg _)
  calc
    (f - g).gaussNorm norm t ≤ δ :=
      gaussNorm_sub_le_of_coeff_le_of_tail_le (hr.le.trans ht.1)
        (fun n hn => (hterm _ n).trans (hcoeff n hn))
        (fun n hn => (hterm _ n).trans (hN n (hM.trans hn)).le)
        (fun n hn => (hterm _ n).trans (hg n hn))
    _ < f.gaussNorm norm r := half_lt_self hpos
    _ ≤ f.gaussNorm norm t :=
      gaussNorm_le_gaussNorm_of_le norm_nonneg hr.le ht.1
        (hfs.of_le norm_nonneg (hr.le.trans ht.1) ht.2)

/-- Every sufficiently long polynomial truncation is a Gauss-small perturbation throughout
any closed interval of positive radii ending at a restricted radius. -/
theorem eventually_gaussNorm_sub_trunc_lt (hf : f.IsRestricted s) (hf0 : f ≠ 0)
    (hr : 0 < r) (hrs : r ≤ s) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc r s,
      (f - (f.trunc N : PowerSeries R)).gaussNorm norm t < f.gaussNorm norm t := by
  obtain ⟨N, δ, hδ, hN⟩ :=
    exists_nat_pos_gaussNorm_sub_lt_of_coeff_le_of_tail_le hf hf0 hr hrs
  filter_upwards [eventually_ge_atTop N] with M hM
  apply hN M hM (f.trunc M)
  · intro n hn
    simpa [coeff_trunc, hn] using hδ.le
  · intro n hn
    simpa [coeff_trunc, not_lt.mpr hn] using hδ.le

/-- Sufficiently long polynomial truncations have exactly the same active coefficient
indices as the series, simultaneously throughout a compact interval of positive radii. -/
theorem eventually_norm_coeff_trunc_mul_pow_eq_gaussNorm_iff (hf : f.IsRestricted s)
    (hf0 : f ≠ 0) (hr : 0 < r) (hrs : r ≤ s) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc r s, ∀ n : ℕ,
      ‖(f.trunc N).coeff n‖ * t ^ n = (f.trunc N : PowerSeries R).gaussNorm norm t ↔
        ‖f.coeff n‖ * t ^ n = f.gaussNorm norm t := by
  filter_upwards [eventually_gaussNorm_sub_trunc_lt hf hf0 hr hrs] with N hN t ht n
  have hft := (hasGaussNorm_of_isRestricted hf).of_le norm_nonneg
    (hr.le.trans ht.1) ht.2
  have htrunc := hasGaussNorm_of_isRestricted (isRestricted_polynomial (f.trunc N) (c := t))
  simpa only [Polynomial.coeff_coe] using
    (norm_coeff_mul_pow_eq_gaussNorm_iff_of_gaussNorm_sub_lt
      (hr.le.trans ht.1) hft htrunc (hN t ht) n).symm

end NormedRing

end TauCeti.PowerSeries
