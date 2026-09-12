/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.AbelSummation
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
attached to `a n` is `O((log n) ^ (-3))`, and Abel summation converts `O(t log t)` partial sums into
a convergent series.

## Main results

* `TauCeti.LSeries.tsum_norm_term_le_of_boundary`: nonnegative coefficients with a continuous
  boundary remainder satisfy `∑ ‖term a sigma n‖ ≤ B / (sigma - 1)` on `(1, 2]`.
* `TauCeti.LSeries.isBigO_sum_Icc_norm_of_boundary`: the resulting `O(t log t)` bound for the
  partial sums.
* `TauCeti.LSeries.summable_norm_div_mul_one_add_log_cube`: that bound makes
  `∑ ‖a n‖ / (n (1 + log n) ^ 3)` converge.
* `TauCeti.LSeries.LSeriesSummable_mul_of_norm_le`: hence any weighting of `a` by a factor of
  size `O((1 + log n) ^ (-3))` has a Dirichlet series converging at `s = 1`.
* `TauCeti.LSeries.LSeriesSummable_mul_fourier_of_nonneg`: the Fourier weight is such a factor, at
  every scale `x > 0`.
* `TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop_of_nonneg`: **the smoothed Wiener--Ikehara
  asymptotic for nonnegative coefficients**, with no summability hypothesis left.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.
-/

public section

namespace TauCeti.LSeries

open Asymptotics Complex Filter FourierTransform MeasureTheory Real Set
open scoped ComplexOrder ContDiff Topology

variable {a : ℕ → ℂ} {A : ℂ} {G : ℂ → ℂ} {psi : ℝ → ℂ} {t x : ℝ}

/-! ### The comparison weight

Abel summation is run against the real weight `(t (1 + log t) ^ 3)⁻¹`. Writing `1 + log t` rather
than `log t` keeps the weight positive and smooth at `t = 1`, where the Abel-summation interface
`summable_mul_of_bigO_atTop'` starts.
-/

/-- The weight `(t (1 + log t) ^ 3)⁻¹` against which the partial-sum bound is summed. -/
private noncomputable def decayWeight (t : ℝ) : ℝ := (t * (1 + Real.log t) ^ 3)⁻¹

/-- `1 + log t` is positive to the right of `exp (-1)`, so the comparison weight is positive on a
neighbourhood of `Ici 1`. -/
private lemma one_add_log_pos (ht : Real.exp (-1) < t) : 0 < 1 + Real.log t := by
  have h := Real.log_lt_log (Real.exp_pos _) ht
  rw [Real.log_exp] at h
  linarith

private lemma exp_neg_one_lt_one : Real.exp (-1) < 1 :=
  Real.exp_lt_one_iff.2 (by norm_num)

private lemma decayWeight_pos (ht : Real.exp (-1) < t) : 0 < decayWeight t := by
  have h := one_add_log_pos ht
  have ht0 : (0 : ℝ) < t := lt_trans (Real.exp_pos _) ht
  exact inv_pos.2 (by positivity)

private lemma hasDerivAt_decayWeight (ht : Real.exp (-1) < t) :
    HasDerivAt decayWeight
      (-(((1 + Real.log t) ^ 3 + 3 * (1 + Real.log t) ^ 2) /
        (t * (1 + Real.log t) ^ 3) ^ 2)) t := by
  have hlog := one_add_log_pos ht
  have ht0 : (0 : ℝ) < t := lt_trans (Real.exp_pos _) ht
  have ht0' : t ≠ 0 := ht0.ne'
  have hlog' : (1 : ℝ) + Real.log t ≠ 0 := hlog.ne'
  have h1 : HasDerivAt (fun u : ℝ ↦ 1 + Real.log u) t⁻¹ t :=
    (Real.hasDerivAt_log ht0').const_add 1
  refine ((hasDerivAt_id' (x := t)).fun_mul (h1.fun_pow 3) |>.inv
    (by positivity)).congr_deriv ?_
  push_cast
  field_simp

/-- On a neighbourhood of `Ici 1` the comparison weight is positive, so taking its norm changes
nothing. -/
private lemma norm_decayWeight_eventuallyEq (ht : 1 ≤ t) :
    (fun u : ℝ ↦ ‖decayWeight u‖) =ᶠ[𝓝 t] decayWeight := by
  have hmem : t ∈ Ioi (Real.exp (-1)) := lt_of_lt_of_le exp_neg_one_lt_one ht
  filter_upwards [isOpen_Ioi.mem_nhds hmem] with u hu
  exact Real.norm_of_nonneg (decayWeight_pos hu).le

private lemma differentiableAt_norm_decayWeight (ht : 1 ≤ t) :
    DifferentiableAt ℝ (fun u : ℝ ↦ ‖decayWeight u‖) t :=
  (norm_decayWeight_eventuallyEq ht).differentiableAt_iff.2
    (hasDerivAt_decayWeight (lt_of_lt_of_le exp_neg_one_lt_one ht)).differentiableAt

private lemma deriv_norm_decayWeight (ht : 1 ≤ t) :
    deriv (fun u : ℝ ↦ ‖decayWeight u‖) t =
      -(((1 + Real.log t) ^ 3 + 3 * (1 + Real.log t) ^ 2) /
        (t * (1 + Real.log t) ^ 3) ^ 2) := by
  rw [(norm_decayWeight_eventuallyEq ht).deriv_eq]
  exact (hasDerivAt_decayWeight (lt_of_lt_of_le exp_neg_one_lt_one ht)).deriv

private lemma locallyIntegrableOn_deriv_norm_decayWeight :
    LocallyIntegrableOn (deriv fun u : ℝ ↦ ‖decayWeight u‖) (Ici 1) := by
  refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ici
  have hne : ∀ u ∈ Ici (1 : ℝ), u ≠ 0 := fun u hu ↦ by
    have : (1 : ℝ) ≤ u := hu
    linarith
  have hlog : ∀ u ∈ Ici (1 : ℝ), 1 + Real.log u ≠ 0 := fun u hu ↦ by
    have : (1 : ℝ) ≤ u := hu
    exact (one_add_log_pos (lt_of_lt_of_le exp_neg_one_lt_one this)).ne'
  refine ContinuousOn.congr (f := fun u : ℝ ↦
    -(((1 + Real.log u) ^ 3 + 3 * (1 + Real.log u) ^ 2) / (u * (1 + Real.log u) ^ 3) ^ 2)) ?_
    fun u hu ↦ deriv_norm_decayWeight hu
  have hcont : ContinuousOn (fun u : ℝ ↦ 1 + Real.log u) (Ici 1) :=
    continuousOn_const.add (Real.continuousOn_log.comp continuousOn_id fun u hu ↦ hne u hu)
  refine (((hcont.pow 3).add ((hcont.pow 2).const_smul (3 : ℝ))).div
    ((continuousOn_id.mul (hcont.pow 3)).pow 2) fun u hu ↦ ?_).neg.congr fun u hu ↦ by
      simp [smul_eq_mul]
  exact pow_ne_zero 2 (mul_ne_zero (hne u hu) (pow_ne_zero 3 (hlog u hu)))

/-- The majorant `(t (1 + log t) ^ 2)⁻¹` produced by Abel summation is integrable at infinity: it
is the derivative of the bounded increasing function `-(1 + log t)⁻¹`. -/
private lemma integrableAtFilter_inv_mul_one_add_log_sq :
    IntegrableAtFilter (fun u : ℝ ↦ (u * (1 + Real.log u) ^ 2)⁻¹) atTop := by
  refine ⟨Ioi 1, Ioi_mem_atTop 1, ?_⟩
  have hderiv : ∀ u ∈ Ioi (1 : ℝ), HasDerivAt (fun v : ℝ ↦ -(1 + Real.log v)⁻¹)
      ((u * (1 + Real.log u) ^ 2)⁻¹) u := by
    intro u hu
    have hu1 : (1 : ℝ) < u := hu
    have hu0 : (0 : ℝ) < u := lt_trans one_pos hu1
    have hlog := one_add_log_pos (lt_trans exp_neg_one_lt_one hu1)
    refine (((Real.hasDerivAt_log hu0.ne').const_add 1).inv hlog.ne').neg.congr_deriv ?_
    field_simp
  refine integrableOn_Ioi_deriv_of_nonneg (l := 0) ?_ hderiv (fun u hu ↦ ?_) ?_
  · exact ((((Real.hasDerivAt_log one_ne_zero).const_add 1).inv
      (one_add_log_pos exp_neg_one_lt_one).ne').neg).continuousAt.continuousWithinAt
  · have hu1 : (1 : ℝ) < u := hu
    have hu0 : (0 : ℝ) < u := lt_trans one_pos hu1
    have hlog := one_add_log_pos (lt_trans exp_neg_one_lt_one hu1)
    positivity
  · have h : Tendsto (fun u : ℝ ↦ 1 + Real.log u) atTop atTop :=
      tendsto_atTop_add_const_left _ 1 Real.tendsto_log_atTop
    simpa using h.inv_tendsto_atTop.neg

/-! ### Nonnegative coefficients on the real axis -/

/-- At a real point, a nonnegative Dirichlet coefficient system has terms equal to their own
norms. -/
private lemma term_eq_ofReal_norm (ha : 0 ≤ a) (sigma : ℝ) (n : ℕ) :
    _root_.LSeries.term a (sigma : ℂ) n = (‖_root_.LSeries.term a (sigma : ℂ) n‖ : ℂ) := by
  have hnn : (0 : ℂ) ≤ _root_.LSeries.term a (sigma : ℂ) n := _root_.LSeries.term_nonneg (ha n) _
  have hre : _root_.LSeries.term a (sigma : ℂ) n =
      ((_root_.LSeries.term a (sigma : ℂ) n).re : ℂ) :=
    Complex.eq_re_of_ofReal_le (by rw [Complex.ofReal_zero]; exact hnn)
  rw [hre, Complex.norm_real,
    Real.norm_of_nonneg (by simpa using (Complex.le_def.mp hnn).1)]

private lemma summable_norm_term (ha : 0 ≤ a) {sigma : ℝ} (h : LSeriesSummable a sigma) :
    Summable fun n : ℕ ↦ ‖_root_.LSeries.term a (sigma : ℂ) n‖ := by
  rw [← Complex.summable_ofReal]
  exact h.congr fun n ↦ term_eq_ofReal_norm ha sigma n

private lemma LSeries_eq_ofReal_tsum_norm (ha : 0 ≤ a) (sigma : ℝ) :
    LSeries a (sigma : ℂ) = ((∑' n : ℕ, ‖_root_.LSeries.term a (sigma : ℂ) n‖ : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun n ↦ term_eq_ofReal_norm ha sigma n

/-! ### The one-sided bound coming from the boundary data -/

/-- For nonnegative coefficients, a continuous boundary remainder `G` bounds the Dirichlet series
on the real segment `(1, 2]` by `B / (sigma - 1)`: the remainder is bounded on the compact segment
`[1, 2]`, and the pole term contributes `‖A‖ / (sigma - 1)`.

No analytic continuation is used, only the values of `G` on that segment and the identity
`G = LSeries a - A / (s - 1)` to the right of it. -/
theorem tsum_norm_term_le_of_boundary (ha : 0 ≤ a) (hG : ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = LSeries a z - A / (z - 1)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 →
      ∑' n : ℕ, ‖_root_.LSeries.term a (sigma : ℂ) n‖ ≤ B / (sigma - 1) := by
  have hcompact : IsCompact ((fun r : ℝ ↦ (r : ℂ)) '' Icc 1 2) :=
    isCompact_Icc.image (by fun_prop)
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn <| hG.mono <| by
    rintro _ ⟨r, hr, rfl⟩
    simpa using hr.1
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM ((1 : ℝ) : ℂ) ⟨1, by norm_num, rfl⟩)
  refine ⟨M + ‖A‖, by positivity, fun sigma h1 h2 ↦ ?_⟩
  have hre : (1 : ℝ) < ((sigma : ℂ)).re := by simpa using h1
  have hsub : (sigma : ℂ) - 1 = ((sigma - 1 : ℝ) : ℂ) := by push_cast; ring
  have hnorm : ‖A / ((sigma : ℂ) - 1)‖ = ‖A‖ / (sigma - 1) := by
    rw [hsub, norm_div, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hnn : (0 : ℝ) ≤ ∑' n : ℕ, ‖_root_.LSeries.term a (sigma : ℂ) n‖ :=
    tsum_nonneg fun _ ↦ norm_nonneg _
  have hS : ((∑' n : ℕ, ‖_root_.LSeries.term a (sigma : ℂ) n‖ : ℝ) : ℂ) =
      G (sigma : ℂ) + A / ((sigma : ℂ) - 1) := by
    rw [← LSeries_eq_ofReal_tsum_norm ha sigma, hG' _ hre]
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
          exact hM _ ⟨sigma, ⟨h1.le, h2⟩, rfl⟩
  rw [add_div]
  linarith

/-! ### The partial-sum bound -/

/-- **A crude growth bound for the partial sums.** Nonnegative coefficients whose Dirichlet series
has a continuous boundary remainder satisfy `∑_{1 ≤ n ≤ t} ‖a n‖ = O(t log t)`.

The proof inserts `sigma = 1 + 1 / log t` into `tsum_norm_term_le_of_boundary`: the truncation
`n ≤ t` costs a factor `t ^ sigma = e t`, and the bound `B / (sigma - 1)` is `B log t`. This is one
logarithm short of the Chebyshev bound `O(t)` that Wiener--Ikehara eventually delivers, but it
needs no Tauberian input. -/
theorem isBigO_sum_Icc_norm_of_boundary (ha : 0 ≤ a) (hG : ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → LSeriesSummable a sigma) :
    (fun t : ℝ ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖a k‖) =O[atTop] fun t : ℝ ↦ t * Real.log t := by
  obtain ⟨B, hB0, hB⟩ := tsum_norm_term_le_of_boundary ha hG hG'
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
  have hsummable := summable_norm_term ha (hsum sigma h1)
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
        exact mul_le_mul_of_nonneg_right (hB sigma h1 h2) hrp
    _ = Real.exp 1 * B * (t * Real.log t) := by
        rw [hsig1, hpow]
        field_simp

/-! ### From the growth bound to summability -/

/-- The boundedness hypothesis of Abel summation: an `O(t log t)` partial sum times the comparison
weight is bounded, because `log t ≤ (1 + log t) ^ 3` for `t ≥ 1`. -/
private lemma decayWeight_mul_le {C S : ℝ} (ht : 1 ≤ t) (hC : 0 ≤ C)
    (hS : S ≤ C * t * Real.log t) : decayWeight t * S ≤ C := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hL : (0 : ℝ) ≤ Real.log t := Real.log_nonneg ht
  have hu : (0 : ℝ) < 1 + Real.log t := by linarith
  have hkey : (t * (1 + Real.log t) ^ 3)⁻¹ * (C * t * Real.log t) =
      C * (Real.log t / (1 + Real.log t) ^ 3) := by
    field_simp
  have hratio : Real.log t / (1 + Real.log t) ^ 3 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [pow_pos hu 3, pow_pos hu 2, sq_nonneg (Real.log t)]
  rw [decayWeight]
  calc (t * (1 + Real.log t) ^ 3)⁻¹ * S
      ≤ (t * (1 + Real.log t) ^ 3)⁻¹ * (C * t * Real.log t) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = C * (Real.log t / (1 + Real.log t) ^ 3) := hkey
    _ ≤ C := by nlinarith

/-- The majorant hypothesis of Abel summation: the derivative of the comparison weight times an
`O(t log t)` partial sum is `O((t (1 + log t) ^ 2)⁻¹)`, because
`log t (4 + log t) ≤ 4 (1 + log t) ^ 2`. -/
private lemma norm_deriv_decayWeight_mul_le {C S : ℝ} (ht : 1 ≤ t) (hC : 0 ≤ C) (hS0 : 0 ≤ S)
    (hS : S ≤ C * t * Real.log t) :
    ‖-(((1 + Real.log t) ^ 3 + 3 * (1 + Real.log t) ^ 2) /
        (t * (1 + Real.log t) ^ 3) ^ 2) * S‖ ≤
      4 * C * ‖(t * (1 + Real.log t) ^ 2)⁻¹‖ := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hL : (0 : ℝ) ≤ Real.log t := Real.log_nonneg ht
  have hu : (0 : ℝ) < 1 + Real.log t := by linarith
  have hX : (0 : ℝ) < (1 + Real.log t) ^ 3 + 3 * (1 + Real.log t) ^ 2 := by
    have h3 := pow_pos hu 3
    have h2 := pow_pos hu 2
    linarith
  have hY : (0 : ℝ) < (t * (1 + Real.log t) ^ 3) ^ 2 :=
    pow_pos (mul_pos ht0 (pow_pos hu 3)) 2
  have hden : (0 : ℝ) < t * (1 + Real.log t) ^ 4 := mul_pos ht0 (pow_pos hu 4)
  have hdiv : (0 : ℝ) ≤ ((1 + Real.log t) ^ 3 + 3 * (1 + Real.log t) ^ 2) /
      (t * (1 + Real.log t) ^ 3) ^ 2 := le_of_lt (div_pos hX hY)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hdiv,
    abs_of_nonneg hS0, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t * (1 + Real.log t) ^ 2)⁻¹)]
  have hkey : ((1 + Real.log t) ^ 3 + 3 * (1 + Real.log t) ^ 2) /
      (t * (1 + Real.log t) ^ 3) ^ 2 * (C * t * Real.log t) =
        C * Real.log t * (4 + Real.log t) / (t * (1 + Real.log t) ^ 4) := by
    field_simp
    ring
  have hgoal : 4 * C * (t * (1 + Real.log t) ^ 2)⁻¹ =
      4 * C * (1 + Real.log t) ^ 2 / (t * (1 + Real.log t) ^ 4) := by
    field_simp
  calc ((1 + Real.log t) ^ 3 + 3 * (1 + Real.log t) ^ 2) /
        (t * (1 + Real.log t) ^ 3) ^ 2 * S
      ≤ ((1 + Real.log t) ^ 3 + 3 * (1 + Real.log t) ^ 2) /
          (t * (1 + Real.log t) ^ 3) ^ 2 * (C * t * Real.log t) :=
        mul_le_mul_of_nonneg_left hS hdiv
    _ = C * Real.log t * (4 + Real.log t) / (t * (1 + Real.log t) ^ 4) := hkey
    _ ≤ 4 * C * (1 + Real.log t) ^ 2 / (t * (1 + Real.log t) ^ 4) := by
        gcongr ?_ / _
        nlinarith [mul_nonneg hC hL, mul_nonneg hC (mul_nonneg hL hL)]
    _ = 4 * C * (t * (1 + Real.log t) ^ 2)⁻¹ := hgoal.symm

/-- **Abel summation turns the growth bound into a convergent series.** An `O(t log t)` bound for
the partial sums of `‖a‖` makes `∑ ‖a n‖ / (n (1 + log n) ^ 3)` converge: the weight is the
derivative-integrable majorant `(t (1 + log t) ^ 2)⁻¹` after summation by parts. -/
theorem summable_norm_div_mul_one_add_log_cube
    (hcheb : (fun t : ℝ ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖a k‖) =O[atTop] fun t : ℝ ↦ t * Real.log t) :
    Summable fun n : ℕ ↦ ‖a n‖ / (n * (1 + Real.log n) ^ 3) := by
  obtain ⟨C, hC⟩ := hcheb.bound
  have hbound : ∀ᶠ u : ℝ in atTop,
      ∑ k ∈ Finset.Icc 1 ⌊u⌋₊, ‖a k‖ ≤ max C 0 * u * Real.log u := by
    filter_upwards [hC, eventually_ge_atTop (1 : ℝ)] with u hu hu1
    have h0 : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu1
    have hle : ∑ k ∈ Finset.Icc 1 ⌊u⌋₊, ‖a k‖ ≤ C * (u * Real.log u) := by
      rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _),
        Real.norm_of_nonneg (by positivity)] at hu
      exact hu
    nlinarith [le_max_left C 0, mul_nonneg (by linarith : (0 : ℝ) ≤ u) h0]
  have hbdd : (fun n : ℕ ↦ ‖decayWeight n‖ * ∑ k ∈ Finset.Icc 1 n, ‖‖a k‖‖) =O[atTop]
      fun _ : ℕ ↦ (1 : ℝ) := by
    refine .of_bound (max C 0) ?_
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually hbound,
      eventually_ge_atTop 1] with n hn hn1
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    rw [Nat.floor_natCast] at hn
    simp only [norm_norm, norm_one, mul_one]
    rw [Real.norm_of_nonneg (le_of_lt (decayWeight_pos
      (lt_of_lt_of_le exp_neg_one_lt_one hn1')))]
    rw [Real.norm_of_nonneg (mul_nonneg (le_of_lt (decayWeight_pos
      (lt_of_lt_of_le exp_neg_one_lt_one hn1'))) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _))]
    exact decayWeight_mul_le hn1' (le_max_right C 0) (by linarith [hn])
  have hg1 : (fun u : ℝ ↦ deriv (fun v : ℝ ↦ ‖decayWeight v‖) u *
      ∑ k ∈ Finset.Icc 1 ⌊u⌋₊, ‖‖a k‖‖) =O[atTop]
        fun u : ℝ ↦ (u * (1 + Real.log u) ^ 2)⁻¹ := by
    refine .of_bound (4 * max C 0) ?_
    filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with u hu hu1
    simp only [norm_norm]
    rw [deriv_norm_decayWeight hu1]
    exact norm_deriv_decayWeight_mul_le hu1 (le_max_right C 0)
      (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) hu
  have habel : Summable fun n : ℕ ↦ decayWeight n * ‖a n‖ :=
    summable_mul_of_bigO_atTop' (f := decayWeight) (fun n ↦ ‖a n‖)
      (fun u hu ↦ differentiableAt_norm_decayWeight hu)
      locallyIntegrableOn_deriv_norm_decayWeight hbdd hg1
      integrableAtFilter_inv_mul_one_add_log_sq
  refine habel.congr fun n ↦ ?_
  rw [decayWeight, inv_mul_eq_div]

/-- Weighting nonnegative coefficients with an `O((1 + log n) ^ (-3))` factor leaves a Dirichlet
series that converges at `s = 1`, as soon as the partial sums of `‖a‖` are `O(t log t)`. -/
theorem LSeriesSummable_mul_of_norm_le {W : ℕ → ℂ} {D : ℝ}
    (hcheb : (fun t : ℝ ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖a k‖) =O[atTop] fun t : ℝ ↦ t * Real.log t)
    (hW : ∀ᶠ n : ℕ in atTop, ‖W n‖ ≤ D / (1 + Real.log n) ^ 3) :
    LSeriesSummable (fun n ↦ a n * W n) 1 := by
  have hD : 0 ≤ D := by
    obtain ⟨n, hn, hn1⟩ := (hW.and (eventually_ge_atTop 1)).exists
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hu : (0 : ℝ) < 1 + Real.log n := by
      have := Real.log_nonneg hn1'
      linarith
    have h0 : (0 : ℝ) ≤ D / (1 + Real.log n) ^ 3 := le_trans (norm_nonneg _) hn
    rwa [le_div_iff₀ (pow_pos hu 3), zero_mul] at h0
  refine Summable.of_norm_bounded_eventually_nat
    (g := fun n : ℕ ↦ D * (‖a n‖ / (n * (1 + Real.log n) ^ 3)))
    ((summable_norm_div_mul_one_add_log_cube hcheb).mul_left D) ?_
  filter_upwards [hW, eventually_ge_atTop 1] with n hn hn1
  have hn0 : n ≠ 0 := by omega
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hu : (0 : ℝ) < 1 + Real.log n := by
    have := Real.log_nonneg hn1'
    linarith
  rw [_root_.LSeries.term_of_ne_zero hn0, Complex.cpow_one, norm_div, norm_mul,
    Complex.norm_natCast]
  calc ‖a n‖ * ‖W n‖ / (n : ℝ)
      ≤ ‖a n‖ * (D / (1 + Real.log n) ^ 3) / (n : ℝ) := by gcongr
    _ = D * (‖a n‖ / ((n : ℝ) * (1 + Real.log n) ^ 3)) := by
        have hn' : (n : ℝ) ≠ 0 := hnpos.ne'
        have hu' : (1 : ℝ) + Real.log n ≠ 0 := hu.ne'
        field_simp

/-! ### The Fourier weight -/

/-- The Fourier transform of a smooth compactly supported function decays faster than
`‖v‖ ^ (-3)`, because it is a Schwartz function. -/
private lemma exists_norm_fourier_le (hpsi : ContDiff ℝ ∞ psi) (hsupp : HasCompactSupport psi) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : ℝ, ‖v‖ ^ 3 * ‖𝓕 psi v‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := (𝓕 (hsupp.toSchwartzMap hpsi) : SchwartzMap ℝ ℂ).decay 3 0
  refine ⟨C, hC0, fun v ↦ ?_⟩
  have hcoe0 : ⇑(hsupp.toSchwartzMap hpsi) = psi := by
    ext u
    simp
  have hcoe : ((𝓕 (hsupp.toSchwartzMap hpsi) : SchwartzMap ℝ ℂ) : ℝ → ℂ) = 𝓕 psi := by
    rw [SchwartzMap.fourier_coe, hcoe0]
  have h := hC v
  rw [norm_iteratedFDeriv_zero, hcoe] at h
  exact h

/-- **The Fourier-weighted series converges on the boundary line.** For nonnegative coefficients
with a continuous boundary remainder and a smooth compactly supported test function, the series
tested at scale `x > 0` is summable at `s = 1`. This discharges the standing summability hypothesis
of `TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop_of_contDiff`. -/
theorem LSeriesSummable_mul_fourier_of_nonneg (ha : 0 ≤ a)
    (hG : ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → LSeriesSummable a sigma)
    (hpsi : ContDiff ℝ ∞ psi) (hsupp : HasCompactSupport psi) (hx : 0 < x) :
    LSeriesSummable (fun n : ℕ ↦ a n * 𝓕 psi (1 / (2 * π) * Real.log (n / x))) 1 := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_fourier_le hpsi hsupp
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
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact LSeriesSummable_mul_fourier_of_nonneg ha hG hG' hsum hpsi hsupp hx

end TauCeti.LSeries
