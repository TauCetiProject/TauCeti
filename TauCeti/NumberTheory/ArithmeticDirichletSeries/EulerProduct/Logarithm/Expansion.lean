/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Data
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.FormalLog
import Mathlib.Analysis.Complex.LocallyUniformLimit
import TauCeti.Analysis.Complex.BranchLogRoot

/-!
# The prime-power expansion of the logarithm of an ideal Euler product

For `D : TauCeti.EulerProductData K`, the local Euler factor at a height-one prime `P` is the
evaluation at `N(P) ^ (-s)` of the local power series `F_P(X) = ∑ e, D(P ^ e) X ^ e`, and
`TauCeti.EulerProductData.localLogSeries` is its formal logarithm. Evaluating that logarithm gives
the local prime-power sum

`ℓ_P(s) = ∑ e, [X ^ e] log F_P(X) · N(P) ^ (-e s)`,

which exponentiates to the local factor inside a zero-free disk
(`TauCeti.EulerProductData.exp_tsum_coeff_localLogSeries_eq_eulerFactor_of_zeroFree`). This file
sums these local logarithms over all primes.

`exp` determines `ℓ_P(s)` only modulo `2πi ℤ`, so summability over `P` does not follow from the
local identity alone. It comes from comparing with the principal logarithm: when the prime-power
tail of `D` at `P`, measured at `σ`, has norm sum less than `1`, the local power series maps the
whole disk of radius `N(P) ^ (-σ)` into the slit plane, and `ℓ_P(s)` is then exactly
`Complex.log` of the local factor for `Re(s) > σ`. Absolute convergence of the ideal-indexed series
at `σ` makes those tails summable over `P`, so this holds for all but finitely many primes,
uniformly on the half-plane. The principal logarithms of the local factors are summable. At
primes whose tail is at most `1 / 2`, the local logarithm is bounded by `3 / 2` times that tail;
the finitely many exceptional local logarithms are bounded on smaller half-planes by their
absolutely convergent norm sums. These bounds give convergence of `∑ P, ℓ_P(s)` and holomorphy.

The result is a holomorphic logarithm of the `L`-series on the whole half-plane `Re(s) > σ`, given
by an explicit prime-power series, not merely chosen on a simply connected region. Its derivative is
the logarithmic derivative of the `L`-series, whose own prime-power expansion is
`TauCeti.EulerProductData.hasSum_tsum_coeff_localLogDerivSeries_of_zeroFree`.

The summability theorem proves that the outer family of values expressed by the local `tsum`s is
summable; it does not assume that every inner series converges. The zero-free hypothesis in the
later statements supplies convergence of every inner series: for the finitely many primes with a
large tail, the local power series may vanish inside the disk, and then its formal logarithm need
not converge.

## Main results

* `TauCeti.EulerProductData.tsum_coeff_localLogSeries_eq_log_eulerFactor`: a local prime-power
  logarithm with a small tail converges to the principal logarithm of the local factor.
* `TauCeti.EulerProductData.differentiableOn_tsum_coeff_localLogSeries_of_zeroFree`: each local
  prime-power logarithm is holomorphic on the half-plane of its zero-free disk.
* `TauCeti.EulerProductData.summable_tsum_coeff_localLogSeries`: the outer family of values
  expressed by the local `tsum`s is summable over the primes.
* `TauCeti.EulerProductData.exp_tsum_tsum_coeff_localLogSeries_eq_LSeries_of_zeroFree`: their sum
  is a logarithm of the `L`-series of the norm coefficients.
* `TauCeti.EulerProductData.differentiableOn_tsum_tsum_coeff_localLogSeries_of_zeroFree` and
  `TauCeti.EulerProductData.deriv_tsum_tsum_coeff_localLogSeries_eq_logDeriv_LSeries_of_zeroFree`:
  the sum is holomorphic on the half-plane, with derivative the logarithmic derivative of the
  `L`-series.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
-/

public section

namespace TauCeti.EulerProductData

open Complex IsDedekindDomain Filter IdealArithmeticFunction
open scoped nonZeroDivisors NumberField

variable {K : Type*} [Field K] [NumberField K]

/-! ### One prime -/

/-- **A local prime-power logarithm with a small tail is the principal logarithm.** Suppose the
local series at `P` converges absolutely at the real point `σ`, and its prime-power tail there has
norm sum less than `1`. Then for `Re(s) > σ` the evaluated formal logarithm of the local factor is
`Complex.log` of the local factor, and the logarithm series converges. No zero-free hypothesis is
needed: the small tail keeps the local power series in the slit plane on the whole disk of radius
`N(P) ^ (-σ)`. -/
theorem tsum_coeff_localLogSeries_eq_log_eulerFactor (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) {σ : ℝ} {s : ℂ}
    (hσ : Summable fun e : ℕ ↦
      idealTerm K D.toIdealArithmeticFunction σ (P.primeIdealPow e))
    (hP : ∑' e : ℕ,
      ‖idealTerm K D.toIdealArithmeticFunction σ (P.primeIdealPow (e + 1))‖ < 1)
    (hs : σ < s.re) :
    (Summable fun e : ℕ ↦ PowerSeries.coeff e (D.localLogSeries P) *
        ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e) ∧
      ∑' e : ℕ, PowerSeries.coeff e (D.localLogSeries P) *
          ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e =
        Complex.log (D.eulerFactor P s) := by
  let q : ℂ := (Ideal.absNorm P.asIdeal : ℂ) ^ (-(σ : ℂ))
  let a : ℕ → ℂ := fun e ↦ PowerSeries.coeff e (D.localPowerSeries P)
  have hterm (e : ℕ) : ‖a e‖ * ‖q‖ ^ e =
      ‖idealTerm K D.toIdealArithmeticFunction σ (P.primeIdealPow e)‖ := by
    rw [idealTerm_primeIdealPow_eq_mul_cpow_neg, norm_mul, norm_pow]
    simp only [a, q, D.coeff_localPowerSeries]
  have hr : (‖q‖₊ : ENNReal) ≤ (FormalMultilinearSeries.ofScalars ℂ a).radius :=
    FormalMultilinearSeries.le_radius_of_summable _ <| by
      simpa [FormalMultilinearSeries.ofScalars_norm, hterm] using hσ.norm
  have ha0 : a 0 = 1 := by simp [a]
  -- On the disk of radius `‖q‖`, the local power series stays within distance `1` of `1`.
  have hslit (z : ℂ) (hz : ‖z‖ₑ < ‖q‖₊) :
      FormalMultilinearSeries.ofScalarsSum (E := ℂ) a z ∈ Complex.slitPlane := by
    have hzq : ‖z‖ ≤ ‖q‖ := by
      rw [enorm_eq_nnnorm, ENNReal.coe_lt_coe] at hz
      exact hz.le
    have hbound (e : ℕ) : ‖a e * z ^ e‖ ≤
        ‖idealTerm K D.toIdealArithmeticFunction σ (P.primeIdealPow e)‖ := by
      rw [← hterm, norm_mul, norm_pow]
      gcongr
    have hsz : Summable fun e : ℕ ↦ ‖a e * z ^ e‖ :=
      hσ.norm.of_nonneg_of_le (fun _ ↦ by positivity) hbound
    rw [FormalMultilinearSeries.ofScalars_sum_eq]
    simp_rw [smul_eq_mul]
    rw [hsz.of_norm.tsum_eq_zero_add, ha0, pow_zero, mul_one]
    apply Complex.mem_slitPlane_of_norm_lt_one
    have hsz' := (summable_nat_add_iff 1).mpr hsz
    calc ‖∑' e : ℕ, a (e + 1) * z ^ (e + 1)‖ ≤ ∑' e : ℕ, ‖a (e + 1) * z ^ (e + 1)‖ :=
          norm_tsum_le_tsum_norm hsz'
      _ ≤ ∑' e : ℕ,
          ‖idealTerm K D.toIdealArithmeticFunction σ (P.primeIdealPow (e + 1))‖ :=
          hsz'.tsum_le_tsum (fun e ↦ hbound (e + 1)) ((summable_nat_add_iff 1).mpr hσ.norm)
      _ < 1 := hP
  have hx : ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ₑ < ‖q‖₊ := by
    rw [enorm_eq_nnnorm, ENNReal.coe_lt_coe]
    exact P.norm_absNorm_cpow_neg_lt (by simpa using hs)
  have h := PowerSeries.hasSum_coeff_logOf_mul_pow_of_slitPlane (D.localPowerSeries P)
    (D.constantCoeff_localPowerSeries P) hr hslit hx
  constructor
  · simpa only [D.localLogSeries_def] using h.summable
  · rw [D.localLogSeries_def, h.tsum_eq]
    simp only [D.coeff_localPowerSeries, D.localPowerSeries_eval_eq_eulerFactor]

/-- **Each local prime-power logarithm is holomorphic.** If the local series at `P` converges
absolutely at the real point `σ` and the local power series has no zero in the disk of radius
`N(P) ^ (-σ)`, then the evaluated formal logarithm of the local factor is holomorphic in `s` on the
half-plane `Re(s) > σ`. -/
theorem differentiableOn_tsum_coeff_localLogSeries_of_zeroFree (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) {σ : ℝ}
    (hσ : LSeriesSummable (D.localArithmeticFactor P) (σ : ℂ))
    (hne : ∀ z : ℂ,
      ‖z‖ < ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-(σ : ℂ))‖ →
        FormalMultilinearSeries.ofScalarsSum (E := ℂ)
          (fun n ↦ PowerSeries.coeff n (D.localPowerSeries P)) z ≠ 0) :
    DifferentiableOn ℂ (fun s : ℂ ↦ ∑' e : ℕ, PowerSeries.coeff e (D.localLogSeries P) *
      ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e) {s : ℂ | σ < s.re} := by
  have hΛ := PowerSeries.differentiableOn_tsum_coeff_logOf_mul_pow_of_zeroFree
    (D.localPowerSeries P) (D.constantCoeff_localPowerSeries P)
    (D.norm_absNorm_cpow_neg_le_radius_localPowerSeries P hσ) fun z hz ↦ by
      apply hne z
      rw [enorm_eq_nnnorm, ENNReal.coe_lt_coe] at hz
      exact_mod_cast hz
  rw [D.localLogSeries_def]
  refine hΛ.comp (fun s _ ↦ ?_) fun s hs ↦ ?_
  · exact (differentiableAt_id.neg.const_cpow
      (Or.inl P.natCast_absNorm_ne_zero)).differentiableWithinAt
  · rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_coe]
    exact P.norm_absNorm_cpow_neg_lt (by simpa using hs)

/-! ### All primes -/

/-- The prime-power tails at `σ` are summable over the primes. -/
private theorem summable_tsum_norm_idealTerm_primeIdealPow_succ (D : EulerProductData K)
    {σ : ℝ} (hσ : Summable (idealTerm K D.toIdealArithmeticFunction σ)) :
    Summable fun P : HeightOneSpectrum (𝓞 K) ↦ ∑' e : ℕ,
      ‖idealTerm K D.toIdealArithmeticFunction σ (P.primeIdealPow (e + 1))‖ :=
  (summable_tsum_norm_idealPrimePowerOf hσ.norm).congr fun P ↦
    tsum_congr fun e ↦ congrArg _ (congrArg _ (Subtype.ext (by simp)))

/-- All but finitely many prime-power tails at `σ` have norm sum less than `1 / 2`. -/
private theorem eventually_tsum_norm_idealTerm_primeIdealPow_succ_lt (D : EulerProductData K)
    {σ : ℝ} (hσ : Summable (idealTerm K D.toIdealArithmeticFunction σ)) :
    ∀ᶠ P : HeightOneSpectrum (𝓞 K) in cofinite, ∑' e : ℕ,
      ‖idealTerm K D.toIdealArithmeticFunction σ (P.primeIdealPow (e + 1))‖ < 1 / 2 :=
  (D.summable_tsum_norm_idealTerm_primeIdealPow_succ hσ).tendsto_cofinite_zero.eventually
    (eventually_lt_nhds (by norm_num))

/-- For all but finitely many primes, the local prime-power logarithm is the principal logarithm
of the local factor, simultaneously at every point of the half-plane `Re(s) > σ`. -/
private theorem eventually_tsum_coeff_localLogSeries_eq_log_eulerFactor (D : EulerProductData K)
    {σ : ℝ} (hσ : Summable (idealTerm K D.toIdealArithmeticFunction σ)) :
    ∀ᶠ P : HeightOneSpectrum (𝓞 K) in cofinite, ∀ s : ℂ, σ < s.re →
      ∑' e : ℕ, PowerSeries.coeff e (D.localLogSeries P) *
          ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e =
        Complex.log (D.eulerFactor P s) :=
  (D.eventually_tsum_norm_idealTerm_primeIdealPow_succ_lt hσ).mono fun P hP s hs ↦
    (D.tsum_coeff_localLogSeries_eq_log_eulerFactor P
      (hσ.comp_injective P.primeIdealPow_injective) (hP.trans (by norm_num)) hs).2

/-- **The local prime-power logarithms are summable over the primes.** If the ideal-indexed series
converges absolutely at the real point `σ`, then for `Re(s) > σ` the local logarithm sums form a
summable family over the height-one primes. -/
theorem summable_tsum_coeff_localLogSeries (D : EulerProductData K) {σ : ℝ} {s : ℂ}
    (hσ : Summable (idealTerm K D.toIdealArithmeticFunction σ))
    (hs : σ < s.re) :
    Summable fun P : HeightOneSpectrum (𝓞 K) ↦ ∑' e : ℕ,
      PowerSeries.coeff e (D.localLogSeries P) *
        ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e :=
  (D.summable_log_eulerFactor
    (summable_idealTerm_of_re_le_re K (by simpa using hs.le) hσ)).congr_cofinite <|
    (D.eventually_tsum_coeff_localLogSeries_eq_log_eulerFactor hσ).mono
      fun _ hP ↦ (hP s hs).symm

/-- **The prime-power expansion of the logarithm.** Suppose the ideal-indexed series converges
absolutely at the real point `σ` and every local power series is zero-free on the disk of radius
`N(P) ^ (-σ)`. Then for `Re(s) > σ` the sum over all primes of the evaluated formal logarithms of
the local factors is a logarithm of the `L`-series of the norm coefficients. -/
theorem exp_tsum_tsum_coeff_localLogSeries_eq_LSeries_of_zeroFree (D : EulerProductData K)
    {σ : ℝ} {s : ℂ}
    (hσ : Summable (idealTerm K D.toIdealArithmeticFunction σ))
    (hne : ∀ (P : HeightOneSpectrum (𝓞 K)) (z : ℂ),
      ‖z‖ < ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-(σ : ℂ))‖ →
        FormalMultilinearSeries.ofScalarsSum (E := ℂ)
          (fun n ↦ PowerSeries.coeff n (D.localPowerSeries P)) z ≠ 0)
    (hs : σ < s.re) :
    Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), ∑' e : ℕ,
        PowerSeries.coeff e (D.localLogSeries P) *
          ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e) =
      LSeries (normCoeff K D.toIdealArithmeticFunction) s := by
  have hprod := (D.summable_tsum_coeff_localLogSeries hσ hs).hasSum.cexp
  refine hprod.unique ((D.hasProd_eulerFactor
    (summable_idealTerm_of_re_le_re K (by simpa using hs.le) hσ)).congr_fun fun P ↦ ?_)
  exact D.exp_tsum_coeff_localLogSeries_eq_eulerFactor_of_zeroFree P
    (D.LSeriesSummable_localArithmeticFactor hσ P) (hne P) hs

/-- A local prime-power logarithm whose tail at `σ` has norm sum at most `1 / 2` is bounded on
`Re(s) > σ` by `3 / 2` times that tail. -/
private theorem norm_tsum_coeff_localLogSeries_le_of_tsum_norm_le (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) {σ : ℝ} {s : ℂ}
    (hσ : Summable fun e : ℕ ↦
      idealTerm K D.toIdealArithmeticFunction σ (P.primeIdealPow e))
    (hP : ∑' e : ℕ,
      ‖idealTerm K D.toIdealArithmeticFunction σ (P.primeIdealPow (e + 1))‖ ≤ 1 / 2)
    (hs : σ < s.re) :
    ‖∑' e : ℕ, PowerSeries.coeff e (D.localLogSeries P) *
        ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e‖ ≤
      3 / 2 * ∑' e : ℕ,
        ‖idealTerm K D.toIdealArithmeticFunction σ (P.primeIdealPow (e + 1))‖ := by
  have hdev := D.norm_eulerFactor_sub_one_le_tsum_norm_of_re_le_re hσ (z := s)
    (by simpa using hs.le)
  rw [(D.tsum_coeff_localLogSeries_eq_log_eulerFactor P hσ
    (hP.trans_lt (by norm_num)) hs).2,
    ← add_sub_cancel 1 (D.eulerFactor P s)]
  exact (Complex.norm_log_one_add_half_le_self (hdev.trans hP)).trans (by gcongr)

/-- To the right of a real point `σ'` inside the zero-free half-plane, a local prime-power
logarithm is bounded by its absolutely convergent norm sum at `σ'`. -/
private theorem norm_tsum_coeff_localLogSeries_le_tsum_norm (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) {σ σ' : ℝ} {s : ℂ}
    (hσ : LSeriesSummable (D.localArithmeticFactor P) (σ : ℂ))
    (hne : ∀ z : ℂ,
      ‖z‖ < ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-(σ : ℂ))‖ →
        FormalMultilinearSeries.ofScalarsSum (E := ℂ)
          (fun n ↦ PowerSeries.coeff n (D.localPowerSeries P)) z ≠ 0)
    (hσσ' : σ < σ') (hs : σ' < s.re) :
    ‖∑' e : ℕ, PowerSeries.coeff e (D.localLogSeries P) *
        ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e‖ ≤
      ∑' e : ℕ, ‖PowerSeries.coeff e (D.localLogSeries P) *
        ((Ideal.absNorm P.asIdeal : ℂ) ^ (-(σ' : ℂ))) ^ e‖ := by
  have hsum' := D.summable_norm_coeff_localLogSeries_of_zeroFree P hσ hne (s := σ')
    (by simpa using hσσ')
  have hsum := D.summable_norm_coeff_localLogSeries_of_zeroFree P hσ hne (hσσ'.trans hs)
  have hxy := (P.norm_absNorm_cpow_neg_lt (s := σ') (by simpa using hs)).le
  refine (norm_tsum_le_tsum_norm hsum).trans (hsum.tsum_le_tsum (fun e ↦ ?_) hsum')
  rw [norm_mul, norm_mul, norm_pow, norm_pow]
  gcongr

/-- **The prime-power expansion of the logarithm is holomorphic.** Under the hypotheses of
`TauCeti.EulerProductData.exp_tsum_tsum_coeff_localLogSeries_eq_LSeries_of_zeroFree`, the sum over
all primes of the evaluated local formal logarithms is holomorphic on the half-plane `Re(s) > σ`. -/
theorem differentiableOn_tsum_tsum_coeff_localLogSeries_of_zeroFree (D : EulerProductData K) {σ : ℝ}
    (hσ : Summable (idealTerm K D.toIdealArithmeticFunction σ))
    (hne : ∀ (P : HeightOneSpectrum (𝓞 K)) (z : ℂ),
      ‖z‖ < ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-(σ : ℂ))‖ →
        FormalMultilinearSeries.ofScalarsSum (E := ℂ)
          (fun n ↦ PowerSeries.coeff n (D.localPowerSeries P)) z ≠ 0) :
    DifferentiableOn ℂ (fun s : ℂ ↦ ∑' P : HeightOneSpectrum (𝓞 K), ∑' e : ℕ,
      PowerSeries.coeff e (D.localLogSeries P) *
        ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e) {s : ℂ | σ < s.re} := by
  let ℓ : HeightOneSpectrum (𝓞 K) → ℂ → ℂ := fun P s ↦ ∑' e : ℕ,
    PowerSeries.coeff e (D.localLogSeries P) * ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e
  let T : HeightOneSpectrum (𝓞 K) → ℝ := fun P ↦ ∑' e : ℕ,
    ‖idealTerm K D.toIdealArithmeticFunction σ (P.primeIdealPow (e + 1))‖
  -- The primes whose tail is not small form a finite exceptional set.
  let E : Set (HeightOneSpectrum (𝓞 K)) := {P | ¬ T P < 1 / 2}
  have hE : E.Finite := D.eventually_tsum_norm_idealTerm_primeIdealPow_succ_lt hσ
  have hT : Summable T := D.summable_tsum_norm_idealTerm_primeIdealPow_succ hσ
  have hℓd (P : HeightOneSpectrum (𝓞 K)) : DifferentiableOn ℂ (ℓ P) {s : ℂ | σ < s.re} :=
    D.differentiableOn_tsum_coeff_localLogSeries_of_zeroFree P
      (D.LSeriesSummable_localArithmeticFactor hσ P) (hne P)
  -- Holomorphy is local, so it suffices to work on each smaller half-plane `Re(s) > σ'`.
  intro s₀ hs₀
  rw [Set.mem_ofPred_eq] at hs₀
  obtain ⟨σ', hσσ', hσ's₀⟩ := exists_between hs₀
  let V : Set ℂ := {s : ℂ | σ' < s.re}
  have hVo : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hVsub : V ⊆ {s : ℂ | σ < s.re} := fun s hs ↦ hσσ'.trans hs
  -- Off `E` the local logarithm is principal and bounded by `3 / 2` times the tail; on `E` it is
  -- bounded on `V` by its absolutely convergent value at the real point `σ'`.
  let u : HeightOneSpectrum (𝓞 K) → ℝ := fun P ↦
    E.indicator (fun P ↦ ∑' e : ℕ, ‖PowerSeries.coeff e (D.localLogSeries P) *
      ((Ideal.absNorm P.asIdeal : ℂ) ^ (-(σ' : ℂ))) ^ e‖) P + 3 / 2 * T P
  have hu : Summable u :=
    (summable_of_ne_finset_zero (s := hE.toFinset) fun P hP ↦
      Set.indicator_of_notMem (by simpa using hP) _).add (hT.mul_left _)
  have hbound (P : HeightOneSpectrum (𝓞 K)) (s : ℂ) (hs : s ∈ V) : ‖ℓ P s‖ ≤ u P := by
    by_cases hP : P ∈ E
    · simp only [u, Set.indicator_of_mem hP]
      exact (D.norm_tsum_coeff_localLogSeries_le_tsum_norm P
        (D.LSeriesSummable_localArithmeticFactor hσ P) (hne P) hσσ' hs).trans
        (le_add_of_nonneg_right (mul_nonneg (by norm_num) (tsum_nonneg fun _ ↦ norm_nonneg _)))
    · simp only [u, Set.indicator_of_notMem hP, zero_add]
      exact D.norm_tsum_coeff_localLogSeries_le_of_tsum_norm_le P
        (hσ.comp_injective P.primeIdealPow_injective) (not_not.mp hP).le (hσσ'.trans hs)
  have hdiff : DifferentiableOn ℂ (fun s ↦ ∑' P, ℓ P s) V :=
    differentiableOn_tsum_of_summable_norm hu (fun P ↦ (hℓd P).mono hVsub) hVo hbound
  exact (hdiff.differentiableAt (hVo.mem_nhds hσ's₀)).differentiableWithinAt

/-- **The derivative of the prime-power expansion of the logarithm.** Under the hypotheses of
`TauCeti.EulerProductData.exp_tsum_tsum_coeff_localLogSeries_eq_LSeries_of_zeroFree`, the
derivative of the sum over all primes of the evaluated local formal logarithms is the logarithmic
derivative of the `L`-series of the norm coefficients. -/
theorem deriv_tsum_tsum_coeff_localLogSeries_eq_logDeriv_LSeries_of_zeroFree
    (D : EulerProductData K) {σ : ℝ} {s : ℂ}
    (hσ : Summable (idealTerm K D.toIdealArithmeticFunction σ))
    (hne : ∀ (P : HeightOneSpectrum (𝓞 K)) (z : ℂ),
      ‖z‖ < ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-(σ : ℂ))‖ →
        FormalMultilinearSeries.ofScalarsSum (E := ℂ)
          (fun n ↦ PowerSeries.coeff n (D.localPowerSeries P)) z ≠ 0)
    (hs : σ < s.re) :
    deriv (fun s : ℂ ↦ ∑' P : HeightOneSpectrum (𝓞 K), ∑' e : ℕ,
        PowerSeries.coeff e (D.localLogSeries P) *
          ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e) s =
      logDeriv (LSeries (normCoeff K D.toIdealArithmeticFunction)) s :=
  TauCeti.deriv_eq_logDeriv_of_eqOn_exp_comp (isOpen_lt continuous_const Complex.continuous_re)
    (D.differentiableOn_tsum_tsum_coeff_localLogSeries_of_zeroFree hσ hne)
    (fun _ hz ↦ D.exp_tsum_tsum_coeff_localLogSeries_eq_LSeries_of_zeroFree hσ hne hz) hs

end TauCeti.EulerProductData
