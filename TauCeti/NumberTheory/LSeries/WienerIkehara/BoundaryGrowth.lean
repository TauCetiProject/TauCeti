/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.LSeries.Positivity
public import TauCeti.Analysis.Fourier.Decay
public import TauCeti.NumberTheory.LSeries.Summable
public import TauCeti.NumberTheory.LSeries.WienerIkehara.Asymptotic

/-!
# A growth bound for nonnegative coefficients, and the summability it supplies

The smoothed Wiener--Ikehara asymptotic
`TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop` still carries a summability hypothesis: the
Fourier-weighted series `∑ a n 𝓕 psi (log (n / x) / 2π) / n` has to converge on the boundary line
`Re s = 1`, where the coefficients are no longer damped by `n ^ (-(sigma - 1))`. This file removes
that hypothesis for nonnegative coefficients, which is the only case Wiener--Ikehara is about.

The input is a growth bound for the partial sums. Nonnegativity turns the boundary data into the
one-sided estimate `∑ ‖a n‖ / n ^ sigma ≤ B / (sigma - 1)` on `(1, 2]`, and inserting
`sigma = 1 + 1 / log t` into it bounds `∑_{n ≤ t} ‖a n‖` by a multiple of `t log t`. That is weaker
than the Chebyshev bound `O(t)` which Wiener--Ikehara ultimately proves, but it is available before
any Tauberian argument, and one logarithm to spare is all the summability needs: the Fourier
transform of a smooth compactly supported function decays faster than `|v| ^ (-3)`, so the factor
attached to `a n` is `O((log n) ^ (-3))`, and the Abel-summation bound
`TauCeti.LSeries.LSeriesSummable_mul_of_norm_le` converts `O(t log t)` partial sums into a
convergent series.

Only the values of the boundary remainder on the real segment `sigma ∈ (1, 2]` enter the growth
bound, so the results below are stated with the boundary data restricted to that segment; the final
asymptotic specializes the half-plane hypotheses it inherits from
`TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop_of_contDiff`.

## Main results

* `TauCeti.LSeries.tsum_norm_term_le_of_boundary`: nonnegative coefficients with a boundary
  remainder continuous on the segment `[1, 2]` have a convergent norm series with
  `∑ ‖term a sigma n‖ ≤ B / (sigma - 1)` on `(1, 2]`.
* `TauCeti.LSeries.isBigO_sum_Icc_norm_of_boundary`: the resulting `O(t log t)` bound for the
  partial sums.
* `TauCeti.LSeries.LSeriesSummable_mul_fourier_of_nonneg`: the Fourier weight is small enough for
  that bound to force summability at `s = 1`, at every scale `x > 0`.
* `TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop_of_nonneg`: **the smoothed Wiener--Ikehara
  asymptotic for nonnegative coefficients**, with no summability hypothesis left.

## References

* Layer 9.1 of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`, which asks for the growth
  bound to be derived from coefficient nonnegativity, the half-plane summability hypothesis, and
  the boundary data.
* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.
-/

public section

namespace TauCeti.LSeries

open Asymptotics Complex Filter FourierTransform MeasureTheory Real Set
open scoped ComplexOrder ContDiff Topology

variable {a : ℕ → ℂ} {A : ℂ} {G : ℂ → ℂ} {psi : ℝ → ℂ} {x : ℝ}

/-! ### The one-sided bound coming from the boundary data -/

/-- For nonnegative coefficients, a boundary remainder `G` continuous on the real segment `[1, 2]`
bounds the Dirichlet series on `(1, 2]` by `B / (sigma - 1)`: the remainder is bounded on the
compact segment, and the pole term contributes `‖A‖ / (sigma - 1)`.

No analytic continuation is used, only the values of `G` on that segment and the identity
`G = LSeries a - A / (s - 1)` on its interior. -/
theorem tsum_norm_term_le_of_boundary (ha : 0 ≤ a)
    (hG : ContinuousOn (fun sigma : ℝ ↦ G (sigma : ℂ)) (Icc 1 2))
    (hG' : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 →
      G (sigma : ℂ) = LSeries a (sigma : ℂ) - A / ((sigma : ℂ) - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 → LSeriesSummable a (sigma : ℂ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 →
      Summable (fun n : ℕ ↦ ‖_root_.LSeries.term a (sigma : ℂ) n‖) ∧
        ∑' n : ℕ, ‖_root_.LSeries.term a (sigma : ℂ) n‖ ≤ B / (sigma - 1) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hG
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 1 ⟨le_rfl, one_le_two⟩)
  refine ⟨M + ‖A‖, by positivity, fun sigma h1 h2 ↦
    ⟨summable_norm_term_of_nonneg ha (hsum sigma h1 h2), ?_⟩⟩
  have hsub : (sigma : ℂ) - 1 = ((sigma - 1 : ℝ) : ℂ) := by push_cast; ring
  have hnorm : ‖A / ((sigma : ℂ) - 1)‖ = ‖A‖ / (sigma - 1) := by
    rw [hsub, norm_div, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hnn : (0 : ℝ) ≤ ∑' n : ℕ, ‖_root_.LSeries.term a (sigma : ℂ) n‖ :=
    tsum_nonneg fun _ ↦ norm_nonneg _
  have hS : ((∑' n : ℕ, ‖_root_.LSeries.term a (sigma : ℂ) n‖ : ℝ) : ℂ) =
      G (sigma : ℂ) + A / ((sigma : ℂ) - 1) := by
    rw [← LSeries_eq_ofReal_tsum_norm_of_nonneg ha sigma, hG' sigma h1 h2]
    ring
  have hMdiv : M ≤ M / (sigma - 1) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < sigma - 1)]
    nlinarith
  have hkey : ∑' n : ℕ, ‖_root_.LSeries.term a (sigma : ℂ) n‖ ≤ M + ‖A‖ / (sigma - 1) := by
    calc ∑' n : ℕ, ‖_root_.LSeries.term a (sigma : ℂ) n‖
        = ‖((∑' n : ℕ, ‖_root_.LSeries.term a (sigma : ℂ) n‖ : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hnn]
      _ ≤ ‖G (sigma : ℂ)‖ + ‖A / ((sigma : ℂ) - 1)‖ := by rw [hS]; exact norm_add_le _ _
      _ ≤ M + ‖A‖ / (sigma - 1) := by
          rw [hnorm]
          gcongr
          exact hM sigma ⟨h1.le, h2⟩
  rw [add_div]
  linarith

/-! ### The partial-sum bound -/

/-- **A crude growth bound for the partial sums.** Nonnegative coefficients whose Dirichlet series
has a boundary remainder continuous on the segment `[1, 2]` satisfy
`∑_{1 ≤ n ≤ t} ‖a n‖ = O(t log t)`.

The proof inserts `sigma = 1 + 1 / log t` into `tsum_norm_term_le_of_boundary`: the truncation
`n ≤ t` costs a factor `t ^ sigma = e t`, and the bound `B / (sigma - 1)` is `B log t`. This is one
logarithm short of the Chebyshev bound `O(t)` that Wiener--Ikehara eventually delivers, but it
needs no Tauberian input. -/
theorem isBigO_sum_Icc_norm_of_boundary (ha : 0 ≤ a)
    (hG : ContinuousOn (fun sigma : ℝ ↦ G (sigma : ℂ)) (Icc 1 2))
    (hG' : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 →
      G (sigma : ℂ) = LSeries a (sigma : ℂ) - A / ((sigma : ℂ) - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 → LSeriesSummable a (sigma : ℂ)) :
    (fun t : ℝ ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖a k‖) =O[atTop] fun t : ℝ ↦ t * Real.log t := by
  obtain ⟨B, hB0, hB⟩ := tsum_norm_term_le_of_boundary ha hG hG' hsum
  refine .of_bound (Real.exp 1 * B) ?_
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with t ht
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (Real.exp_pos 1) ht
  have hlog1 : (1 : ℝ) ≤ Real.log t := (Real.le_log_iff_exp_le ht0).2 ht
  have hlogpos : (0 : ℝ) < Real.log t := by linarith
  set sigma : ℝ := 1 + 1 / Real.log t with hsig
  have h1 : 1 < sigma := by
    rw [hsig]
    have : (0 : ℝ) < 1 / Real.log t := by positivity
    linarith
  have h2 : sigma ≤ 2 := by
    rw [hsig]
    have : 1 / Real.log t ≤ 1 := by rw [div_le_one hlogpos]; exact hlog1
    linarith
  have hsig1 : sigma - 1 = 1 / Real.log t := by rw [hsig]; ring
  obtain ⟨hsummable, hbound⟩ := hB sigma h1 h2
  have hpow : t ^ sigma = Real.exp 1 * t := by
    rw [hsig, Real.rpow_add ht0, Real.rpow_one, Real.rpow_def_of_pos ht0, mul_one_div,
      div_self hlogpos.ne']
    ring
  have hfloor : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0.le
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _),
    Real.norm_of_nonneg (by positivity)]
  calc ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖a k‖
      ≤ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖_root_.LSeries.term a (sigma : ℂ) k‖ * t ^ sigma := by
        refine Finset.sum_le_sum fun k hk ↦ ?_
        obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
        have hk0 : k ≠ 0 := by omega
        have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
        have hknorm : ‖_root_.LSeries.term a (sigma : ℂ) k‖ = ‖a k‖ / (k : ℝ) ^ sigma := by
          rw [_root_.LSeries.term_of_ne_zero hk0, norm_div, ← Complex.ofReal_natCast,
            ← Complex.ofReal_cpow (Nat.cast_nonneg k), Complex.norm_real,
            Real.norm_of_nonneg (by positivity)]
        have hkt : (k : ℝ) ≤ t := le_trans (Nat.cast_le.2 hk2) hfloor
        rw [hknorm, div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) ^ sigma)]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg k) hkt (by linarith)) (norm_nonneg _)
    _ = (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖_root_.LSeries.term a (sigma : ℂ) k‖) * t ^ sigma :=
        (Finset.sum_mul ..).symm
    _ ≤ (∑' k : ℕ, ‖_root_.LSeries.term a (sigma : ℂ) k‖) * t ^ sigma := by
        have := hsummable.sum_le_tsum (Finset.Icc 1 ⌊t⌋₊) fun i _ ↦ norm_nonneg _
        have hrp : (0 : ℝ) ≤ t ^ sigma := by positivity
        exact mul_le_mul_of_nonneg_right this hrp
    _ ≤ B / (sigma - 1) * t ^ sigma := by
        have hrp : (0 : ℝ) ≤ t ^ sigma := by positivity
        exact mul_le_mul_of_nonneg_right hbound hrp
    _ = Real.exp 1 * B * (t * Real.log t) := by
        rw [hsig1, hpow]
        field_simp

/-! ### The Fourier weight -/

/-- **The Fourier-weighted series converges on the boundary line.** For nonnegative coefficients
with a boundary remainder continuous on the segment `[1, 2]` and a smooth compactly supported test
function, the series tested at scale `x > 0` is summable at `s = 1`. This discharges the standing
summability hypothesis of
`TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop_of_contDiff`. -/
theorem LSeriesSummable_mul_fourier_of_nonneg (ha : 0 ≤ a)
    (hG : ContinuousOn (fun sigma : ℝ ↦ G (sigma : ℂ)) (Icc 1 2))
    (hG' : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 →
      G (sigma : ℂ) = LSeries a (sigma : ℂ) - A / ((sigma : ℂ) - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 → LSeriesSummable a (sigma : ℂ))
    (hpsi : ContDiff ℝ ∞ psi) (hsupp : HasCompactSupport psi) (hx : 0 < x) :
    LSeriesSummable (fun n : ℕ ↦ a n * 𝓕 psi (1 / (2 * π) * Real.log (n / x))) 1 := by
  obtain ⟨C, hC0, hC⟩ := TauCeti.exists_norm_pow_mul_norm_fourier_le hpsi hsupp 3
  have hpi : (0 : ℝ) < π := Real.pi_pos
  refine LSeriesSummable_mul_of_norm_le (D := 8 * C * (4 * π) ^ 3)
    (isBigO_sum_Icc_norm_of_boundary ha hG hG' hsum) ?_
  filter_upwards [eventually_ge_atTop (max ⌈Real.exp 1⌉₊ ⌈x ^ 2⌉₊)] with n hn
  have hn1 : ⌈Real.exp 1⌉₊ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : ⌈x ^ 2⌉₊ ≤ n := le_trans (le_max_right _ _) hn
  have hne : Real.exp 1 ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (Nat.cast_le.2 hn1)
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (Real.exp_pos 1) hne
  have hL1 : (1 : ℝ) ≤ Real.log n := (Real.le_log_iff_exp_le hn0).2 hne
  have hx2 : x ^ 2 ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (Nat.cast_le.2 hn2)
  have hlogx : 2 * Real.log x ≤ Real.log n := by
    have h := Real.log_le_log (by positivity) hx2
    rwa [Real.log_pow] at h
  have hv : 1 / (2 * π) * Real.log ((n : ℝ) / x) = (Real.log n - Real.log x) / (2 * π) := by
    rw [Real.log_div hn0.ne' hx.ne']
    ring
  have hvge : Real.log n / (4 * π) ≤ 1 / (2 * π) * Real.log ((n : ℝ) / x) := by
    rw [hv, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hvnn : (0 : ℝ) ≤ 1 / (2 * π) * Real.log ((n : ℝ) / x) :=
    le_trans (by positivity) hvge
  have hcube : (Real.log n / (4 * π)) ^ 3 * ‖𝓕 psi (1 / (2 * π) * Real.log ((n : ℝ) / x))‖ ≤ C := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)) (hC _)
    rw [Real.norm_of_nonneg hvnn]
    exact pow_le_pow_left₀ (by positivity) hvge 3
  have hfrac : (Real.log n / (4 * π)) ^ 3 = Real.log n ^ 3 / (64 * π ^ 3) := by
    field_simp
    ring
  rw [hfrac, div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hcube
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (1 + Real.log n) ^ 3)]
  have hpow : (1 + Real.log n) ^ 3 ≤ 8 * Real.log n ^ 3 := by nlinarith [sq_nonneg (Real.log n - 1)]
  nlinarith [norm_nonneg (𝓕 psi (1 / (2 * π) * Real.log ((n : ℝ) / x))),
    mul_le_mul_of_nonneg_left hpow
      (norm_nonneg (𝓕 psi (1 / (2 * π) * Real.log ((n : ℝ) / x))))]

/-- **The smoothed Wiener--Ikehara asymptotic for nonnegative coefficients.** Testing the Dirichlet
series of a nonnegative coefficient system against a smooth compactly supported function on the
line `Re s = 1` gives the limit `2π A psi 0`, where `A` is the residue subtracted off by the
continuous boundary remainder `G`.

This is `TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop_of_contDiff` with its summability
hypothesis discharged: for nonnegative coefficients the boundary data itself forces the
Fourier-weighted series to converge at every large scale. The hypotheses are now exactly the
analytic input of Wiener--Ikehara. -/
theorem tendsto_tsum_term_mul_fourier_atTop_of_nonneg (ha : 0 ≤ a)
    (hG : ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → LSeriesSummable a sigma)
    (hpsi : ContDiff ℝ ∞ psi) (hsupp : HasCompactSupport psi) :
    Tendsto (fun x : ℝ ↦
        ∑' n : ℕ, _root_.LSeries.term a 1 n * 𝓕 psi (1 / (2 * π) * Real.log (n / x)))
      atTop (𝓝 (2 * (π : ℂ) * A * psi 0)) :=
  tendsto_tsum_term_mul_fourier_atTop_of_contDiff hG hG' hsum hpsi hsupp <| by
    have hGseg : ContinuousOn (fun sigma : ℝ ↦ G (sigma : ℂ)) (Icc 1 2) :=
      hG.comp Complex.continuous_ofReal.continuousOn fun r hr ↦ by simpa using hr.1
    have hG'seg : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 →
        G (sigma : ℂ) = LSeries a (sigma : ℂ) - A / ((sigma : ℂ) - 1) :=
      fun sigma h1 _ ↦ hG' sigma (by simpa using h1)
    have hsumseg : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 → LSeriesSummable a (sigma : ℂ) :=
      fun sigma h1 _ ↦ hsum sigma h1
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact LSeriesSummable_mul_fourier_of_nonneg ha hGseg hG'seg hsumseg hpsi hsupp hx

end TauCeti.LSeries
