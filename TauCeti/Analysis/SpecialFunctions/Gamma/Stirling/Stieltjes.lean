/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.Analysis.SpecialFunctions.Gamma.Log
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Asymptotics.Sum.EulerMaclaurin
import TauCeti.Analysis.Calculus.Deriv.Fract
import TauCeti.Analysis.Complex.SectorBounds
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Basic
import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Stieltjes representation and higher derivatives of the Stirling remainder

On the slit plane `ℂ ∖ (-∞, 0]`, the Stirling remainder of the normalized holomorphic logarithm of
Gamma is

`R(z) = logGamma z - ((z - 1/2) * Complex.log z - z + Real.log (2 * π) / 2)`.

Applying the second-order Euler–Maclaurin formula to `u ↦ Complex.log (z + u)` on `[0, N]` and
letting `N → ∞` yields Stieltjes' integral representation

`R(z) = ∫ t in Ioi 0, Q(t) / (z + t) ^ 2`,   `Q(t) = (Int.fract t - Int.fract t ^ 2) / 2`.

Every compact subset `K ⊆ slitPlane` admits a uniform lower bound `c_K * (1 + t) ≤ ‖z + t‖`, giving
a common integrable majorant for `Q(t) / (z + t) ^ (j + 2)` on `K`. Differentiating under the
integral sign then produces all iterated derivatives on the slit plane:

`iteratedDeriv j R z = (-1) ^ j * (j + 1)! * ∫ t in Ioi 0, Q(t) / (z + t) ^ (j + 2)`.

Combining `0 ≤ Q(t) ≤ 1 / 8` with the sharp half-angle geometric bound
`cos (arg z / 2) * (‖z‖ + t) ≤ ‖z + t‖` (valid throughout `slitPlane`, including `Re z < 0`) and
evaluating `∫ t in Ioi 0, ((‖z‖ + t) ^ (j + 2))⁻¹ = ((j + 1) * ‖z‖ ^ (j + 1))⁻¹` yields the exact
sector bound

`‖iteratedDeriv j R z‖ ≤ j! / (8 * cos (arg z / 2) ^ (j + 2) * ‖z‖ ^ (j + 1))`

for every `j : ℕ` and `z ∈ slitPlane`, together with the closed-sector form with `sin (δ / 2)` on
`|arg z| ≤ π - δ`. At `j = 1` this specializes to the sharp sectorial digamma bound
`‖ψ(z) - log z + 1 / (2 z)‖ ≤ 1 / (8 * cos (arg z / 2) ^ 3 * ‖z‖ ^ 2)`. On the positive real axis
`R(x) > 0` and `R'(x) < 0`, with `R(1) = 1 - log (2π) / 2` and `R'(1) = 1 / 2 - γ`.

## Main declarations

* `TauCeti.stirlingRemainder`: the Stirling remainder `R(z)` of `TauCeti.logGamma`.
* `TauCeti.stirlingRemainder_one`, `TauCeti.deriv_stirlingRemainder`,
  `TauCeti.deriv_stirlingRemainder_one`: normalization and first derivative `ψ(z) - log z + 1/(2z)`.
* `TauCeti.exists_integrableOn_stirlingRemainder_integrand_bound`,
  `TauCeti.integrableOn_stirlingRemainder_integrand`: compact domination and integrability of the
  Stieltjes integrands `Q(t) / (z + t) ^ (j + 2)`.
* `TauCeti.stirlingRemainder_eq_integral`: Stieltjes' integral identity on the slit plane.
* `TauCeti.hasDerivAt_integral_stirlingRemainder_integrand`,
  `TauCeti.iteratedDeriv_stirlingRemainder_eq_integral`: differentiation under the integral sign and
  exact integral formula for all iterated derivatives `R^{(j)}(z)`.
* `TauCeti.norm_iteratedDeriv_stirlingRemainder_le`,
  `TauCeti.norm_iteratedDeriv_stirlingRemainder_le_of_abs_arg_le`: sharp sector bounds for all
  `j : ℕ`.
* `TauCeti.norm_stirlingRemainder_le`, `TauCeti.digamma_sub_log_add_inv_two_mul_eq_integral`,
  `TauCeti.norm_digamma_sub_log_add_inv_two_mul_le`: specializations at `j = 0` and `j = 1`.
* `TauCeti.re_stirlingRemainder_ofReal_pos`, `TauCeti.re_deriv_stirlingRemainder_ofReal_neg`,
  `TauCeti.deriv_real_stirlingRemainder_neg`: positivity of `R` and strict decrease on `(0, ∞)`.

## References

* T. J. Stieltjes, *Sur le développement de `log Γ(a)`*, J. Math. Pures Appl. (4) 5 (1889),
  425–444.
* G. Nemes, *Error bounds and exponential improvements for the asymptotic expansions of the gamma
  function and its reciprocal*, Proc. Roy. Soc. Edinburgh Sect. A 145 (2015), 571–596, §2,
  eq. (2.5) and Lemma 2.1.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8.
* NIST *Digital Library of Mathematical Functions*, §5.11.
-/

public section

open Complex Real Filter Set Topology MeasureTheory
open scoped Nat

namespace TauCeti

/-! ### Definition and basic calculus of the Stirling remainder -/

/-- The Stirling remainder of the normalized holomorphic logarithm of Gamma on the slit plane:
`logGamma z - ((z - 1 / 2) * Complex.log z - z + Real.log (2 * π) / 2)`. -/
noncomputable def stirlingRemainder (z : ℂ) : ℂ :=
  logGamma z - ((z - 1 / 2) * Complex.log z - z + (Real.log (2 * π) / 2 : ℝ))

/-- Unfolding lemma for `stirlingRemainder`. -/
theorem stirlingRemainder_def (z : ℂ) :
    stirlingRemainder z =
      logGamma z - ((z - 1 / 2) * Complex.log z - z + (Real.log (2 * π) / 2 : ℝ)) :=
  (rfl)

/-- On the positive real axis, `stirlingRemainder` is the real Stirling remainder of
`Real.log (Real.Gamma x)`. -/
theorem stirlingRemainder_ofReal {x : ℝ} (hx : 0 < x) :
    stirlingRemainder x =
      ((Real.log (Real.Gamma x) - ((x - 1 / 2) * Real.log x - x + Real.log (2 * π) / 2) : ℝ) :
        ℂ) := by
  rw [stirlingRemainder_def, logGamma_ofReal hx, ← Complex.ofReal_log hx.le]
  push_cast
  ring

/-- At `z = 1`, the Stirling remainder equals `1 - log (2π) / 2`. -/
@[simp]
theorem stirlingRemainder_one :
    stirlingRemainder 1 = ((1 - Real.log (2 * π) / 2 : ℝ) : ℂ) := by
  rw [stirlingRemainder_def, logGamma_one, Complex.log_one]
  push_cast
  ring

/-- On the slit plane, `stirlingRemainder` has derivative `ψ(z) - log z + 1 / (2 z)`. -/
theorem hasDerivAt_stirlingRemainder {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt stirlingRemainder (Complex.digamma z - Complex.log z + (2 * z)⁻¹) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hL : HasDerivAt logGamma (Complex.digamma z) z := by
    rw [← deriv_logGamma hz]
    exact (differentiableOn_logGamma.differentiableAt
      (isOpen_slitPlane.mem_nhds hz)).hasDerivAt
  have hlog := Complex.hasDerivAt_log hz
  have h := hL.sub ((((hasDerivAt_id z).sub_const (1 / 2 : ℂ)).mul hlog).sub
    (hasDerivAt_id z) |>.add_const ((Real.log (2 * π) / 2 : ℝ) : ℂ))
  refine (h.congr_of_eventuallyEq
    (Eventually.of_forall fun w ↦ stirlingRemainder_def w)).congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- On the slit plane, `deriv stirlingRemainder z = ψ(z) - log z + 1 / (2 z)`. -/
theorem deriv_stirlingRemainder {z : ℂ} (hz : z ∈ slitPlane) :
    deriv stirlingRemainder z = Complex.digamma z - Complex.log z + (2 * z)⁻¹ :=
  (hasDerivAt_stirlingRemainder hz).deriv

/-- The Stirling remainder is holomorphic on the slit plane. -/
theorem differentiableOn_stirlingRemainder : DifferentiableOn ℂ stirlingRemainder slitPlane :=
  fun _ hz ↦ (hasDerivAt_stirlingRemainder hz).differentiableAt.differentiableWithinAt

/-- The Stirling remainder is analytic at every point of the slit plane. -/
theorem analyticOnNhd_stirlingRemainder : AnalyticOnNhd ℂ stirlingRemainder slitPlane :=
  differentiableOn_stirlingRemainder.analyticOnNhd isOpen_slitPlane

/-- At `z = 1`, the derivative of the Stirling remainder equals `1 / 2 - γ`. -/
@[simp]
theorem deriv_stirlingRemainder_one :
    deriv stirlingRemainder 1 = ((1 / 2 - Real.eulerMascheroniConstant : ℝ) : ℂ) := by
  rw [deriv_stirlingRemainder one_mem_slitPlane, Complex.digamma_one, Complex.log_one]
  push_cast
  ring

/-! ### Periodic Bernoulli kernel and compact domination -/

private theorem measurable_stirlingRemainder_integrand (w : ℂ) (j : ℕ) :
    Measurable fun t : ℝ ↦
      (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (w + (t : ℂ)) ^ (j + 2) := by
  have hQ : Continuous fun t : ℝ ↦ (Int.fract t - Int.fract t ^ 2) / 2 := by
    have heq : (fun t : ℝ ↦ (Int.fract t - Int.fract t ^ 2) / 2) =
        fun t : ℝ ↦ -(Int.fract t ^ 2 - Int.fract t) / 2 := by
      ext t; ring
    rw [heq]
    exact Int.continuous_fract_sq_sub_fract.neg.div_const 2
  exact (continuous_ofReal.comp hQ).measurable.div
    ((continuous_const.add continuous_ofReal).pow (j + 2)).measurable

private theorem norm_stirlingRemainder_integrand_le {z : ℂ} {c a t : ℝ} (hc : 0 < c) (ha : 0 < a)
    (ht : 0 ≤ t) (hden : c * (a + t) ≤ ‖z + (t : ℂ)‖) (m : ℕ) :
    ‖(((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + (t : ℂ)) ^ m‖ ≤
      (8 * c ^ m)⁻¹ * ((a + t) ^ m)⁻¹ := by
  have hQ0 : 0 ≤ (Int.fract t - Int.fract t ^ 2) / 2 := by
    have h0 := Int.fract_nonneg t
    have h1 := (Int.fract_lt_one t).le
    nlinarith
  have hQ8 : (Int.fract t - Int.fract t ^ 2) / 2 ≤ 1 / 8 := by
    linarith [(abs_le.mp (Int.abs_fract_sq_sub_fract_le t)).1]
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hQ0]
  have hpow : c ^ m * (a + t) ^ m ≤ ‖z + (t : ℂ)‖ ^ m := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hden m
  calc
    (Int.fract t - Int.fract t ^ 2) / 2 / ‖z + (t : ℂ)‖ ^ m
        ≤ (1 / 8) / (c ^ m * (a + t) ^ m) :=
      div_le_div₀ (by norm_num) hQ8 (by positivity) hpow
    _ = (8 * c ^ m)⁻¹ * ((a + t) ^ m)⁻¹ := by
      rw [one_div, div_eq_mul_inv, mul_inv, mul_inv, mul_assoc]

/-- On every compact subset `K` of the slit plane and for every `j : ℕ`, the Stieltjes integrands
`Q(t) / (z + t) ^ (j + 2)` admit a common integrable majorant on `(0, ∞)`. -/
theorem exists_integrableOn_stirlingRemainder_integrand_bound {K : Set ℂ} (hK : IsCompact K)
    (hKs : K ⊆ slitPlane) (j : ℕ) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧
      ∀ z ∈ K, ∀ t ∈ Ioi (0 : ℝ),
        ‖(((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + (t : ℂ)) ^ (j + 2)‖ ≤ g t := by
  obtain ⟨c, hc, hden⟩ := exists_pos_forall_mem_mul_one_add_le_norm_add hK hKs
  exact ⟨fun t : ℝ ↦ (8 * c ^ (j + 2))⁻¹ * ((1 + t) ^ (j + 2))⁻¹,
    (integrableOn_Ioi_inv_add_pow one_pos (Nat.succ_pos j)).const_mul _, fun z hz t ht ↦
      norm_stirlingRemainder_integrand_le hc one_pos ht.out.le (hden z hz t ht.out.le) (j + 2)⟩

/-- For every `z ∈ slitPlane` and `j : ℕ`, the Stieltjes integrand `Q(t) / (z + t) ^ (j + 2)` is
integrable on `(0, ∞)`. -/
theorem integrableOn_stirlingRemainder_integrand {z : ℂ} (hz : z ∈ slitPlane) (j : ℕ) :
    IntegrableOn
      (fun t : ℝ ↦ (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + (t : ℂ)) ^ (j + 2))
      (Ioi 0) := by
  obtain ⟨g, hg, hbound⟩ := exists_integrableOn_stirlingRemainder_integrand_bound
    isCompact_singleton (singleton_subset_iff.mpr hz) j
  refine hg.mono' (measurable_stirlingRemainder_integrand z j).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact hbound z rfl t ht

/-! ### Stieltjes integral identity via Euler–Maclaurin -/

private theorem sum_Icc_log_add_eq {z : ℂ} (hz : z ∈ slitPlane) (N : ℕ) :
    ∑ j ∈ Finset.Icc (0 : ℤ) (N : ℤ), Complex.log (z + ((j : ℝ) : ℂ)) =
      logGamma (z + N) - logGamma z + Complex.log (z + N) := by
  have hsumNat : ∑ j ∈ Finset.Icc (0 : ℤ) (N : ℤ), Complex.log (z + ((j : ℝ) : ℂ)) =
      ∑ k ∈ Finset.range (N + 1), Complex.log (z + (k : ℂ)) := by
    refine Finset.sum_nbij (fun j : ℤ ↦ j.toNat) ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_Icc] at hj
      rw [Finset.mem_range]
      omega
    · intro j₁ hj₁ j₂ hj₂ h
      simp only [Finset.mem_coe, Finset.mem_Icc] at hj₁ hj₂
      dsimp only at h
      omega
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_range] at hk
      refine ⟨(k : ℤ), Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), by simp⟩
    · intro j hj
      rw [Finset.mem_Icc] at hj
      have hj' : ((j.toNat : ℕ) : ℂ) = (j : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hj.1
      simp only [ofReal_intCast, hj']
  rw [hsumNat, Finset.sum_range_succ, logGamma_add_natCast hz N]
  ring

private theorem bernoulli_two_term_sub_integral_eq {z : ℂ} (hz : z ∈ slitPlane) (N : ℕ) :
    (bernoulli 2 / (2 : ℕ).factorial : ℝ) • ((z + (N : ℂ))⁻¹ - z⁻¹) -
      ((-1 : ℝ) ^ 2 / (2 : ℕ).factorial : ℝ) •
        ∫ x : ℝ in 0..(N : ℝ), bernoulliFun 2 (Int.fract x) • (-((z + (x : ℂ)) ^ 2)⁻¹) =
      -(∫ x : ℝ in 0..(N : ℝ),
        (((Int.fract x - Int.fract x ^ 2) / 2 : ℝ) : ℂ) / (z + (x : ℂ)) ^ 2) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have huIcc : ∀ u ∈ uIcc (0 : ℝ) (N : ℝ), z + (u : ℂ) ≠ 0 := fun u hu ↦ by
    rw [uIcc_of_le hN] at hu
    exact slitPlane_ne_zero (add_ofReal_mem_slitPlane hz hu.1)
  have hinv_int : IntervalIntegrable (fun x : ℝ ↦ ((z + (x : ℂ)) ^ 2)⁻¹) volume 0 (N : ℝ) :=
    (((continuousOn_const.add continuous_ofReal.continuousOn).pow 2).inv₀
      fun u hu ↦ pow_ne_zero _ (huIcc u hu)).intervalIntegrable
  have hint_sq : ∫ x : ℝ in 0..(N : ℝ), ((z + (x : ℂ)) ^ 2)⁻¹ = z⁻¹ - (z + (N : ℂ))⁻¹ := by
    simpa only [Nat.cast_one, pow_one, one_mul, ofReal_zero, add_zero, ofReal_natCast] using
      integral_inv_add_ofReal_pow (z := z) (a := 0) (b := (N : ℝ)) (n := 1) le_rfl huIcc
  have h1 : (bernoulli 2 / (2 : ℕ).factorial : ℝ) • ((z + (N : ℂ))⁻¹ - z⁻¹) =
      -(∫ x : ℝ in 0..(N : ℝ), (bernoulli 2 / 2 : ℝ) • ((z + (x : ℂ)) ^ 2)⁻¹) := by
    rw [intervalIntegral.integral_smul, hint_sq]
    simp [Complex.real_smul]
    ring
  have h2 : ((-1 : ℝ) ^ 2 / (2 : ℕ).factorial : ℝ) •
      ∫ x : ℝ in 0..(N : ℝ), bernoulliFun 2 (Int.fract x) • (-((z + (x : ℂ)) ^ 2)⁻¹) =
      -(∫ x : ℝ in 0..(N : ℝ),
        (bernoulliFun 2 (Int.fract x) / 2 : ℝ) • ((z + (x : ℂ)) ^ 2)⁻¹) := by
    rw [← intervalIntegral.integral_smul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x _ ↦ ?_
    simp [Complex.real_smul]
    ring
  rw [h1, h2, sub_neg_eq_add, add_comm, ← sub_eq_add_neg, ← neg_sub,
    ← intervalIntegral.integral_sub]
  · congr 1
    refine intervalIntegral.integral_congr fun x _ ↦ ?_
    rw [bernoulli_two, bernoulliFun_two]
    simp only [Complex.real_smul, div_eq_mul_inv]
    push_cast
    ring
  · exact hinv_int.smul (bernoulli 2 / 2 : ℝ)
  · refine ((hinv_int.bernoulliFun_fract_smul 2).smul (2 : ℝ)⁻¹).congr fun x _ ↦ ?_
    dsimp only [Pi.smul_apply]
    rw [smul_smul, div_eq_inv_mul]

private theorem stirlingRemainder_eq_add_intervalIntegral {z : ℂ} (hz : z ∈ slitPlane) (N : ℕ) :
    stirlingRemainder z = stirlingRemainder (z + N) +
      ∫ t : ℝ in 0..(N : ℝ),
        (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + (t : ℂ)) ^ 2 := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  let g : ℕ → ℝ → ℂ := fun i u ↦ match i with
    | 0 => Complex.log (z + (u : ℂ))
    | 1 => (z + (u : ℂ))⁻¹
    | 2 => -((z + (u : ℂ)) ^ 2)⁻¹
    | _ + 3 => 0
  have hcont : ∀ i < 2, ContinuousOn (g i) (Icc (0 : ℝ) N) := by
    intro i hi
    interval_cases i
    · intro u hu
      exact ((Complex.hasDerivAt_log (add_ofReal_mem_slitPlane hz hu.1)).continuousAt.comp
        (f := fun t : ℝ ↦ z + (t : ℂ))
        (continuousAt_const.add continuous_ofReal.continuousAt)).continuousWithinAt
    · exact (continuousOn_const.add continuous_ofReal.continuousOn).inv₀
        fun _ hu ↦ slitPlane_ne_zero (add_ofReal_mem_slitPlane hz hu.1)
  have hderiv : ∀ i < 2, ∀ x ∈ Ioo (0 : ℝ) N, HasDerivAt (g i) (g (i + 1) x) x := by
    intro i hi x hx
    have hmem := add_ofReal_mem_slitPlane hz hx.1.le
    interval_cases i
    · simpa [g] using ((Complex.hasDerivAt_log hmem).comp (x : ℂ)
        ((hasDerivAt_id (x : ℂ)).const_add z)).comp_ofReal
    · refine (((hasDerivAt_id (x : ℂ)).const_add z).inv
        (slitPlane_ne_zero hmem)).comp_ofReal.congr_deriv ?_
      simp [g]
      ring
  have huIcc : ∀ u ∈ uIcc (0 : ℝ) (N : ℝ), z + (u : ℂ) ∈ slitPlane := fun u hu ↦ by
    rw [uIcc_of_le hN] at hu
    exact add_ofReal_mem_slitPlane hz hu.1
  have hint2 : IntervalIntegrable (g 2) volume 0 (N : ℝ) :=
    (((continuousOn_const.add continuous_ofReal.continuousOn).pow 2).inv₀
      fun u hu ↦ pow_ne_zero _ (slitPlane_ne_zero (huIcc u hu))).neg.intervalIntegrable
  have hEM := sum_Icc_eq_eulerMaclaurin_of_hasDerivAt (g := g) (a := (0 : ℤ)) (n := (N : ℤ))
    (Int.natCast_nonneg N) (k := 2) (by norm_num) (by simpa using hcont) (by simpa using hderiv)
    (by simpa using hint2)
  simp only [Int.cast_zero, Int.cast_natCast, Finset.Icc_self, Finset.sum_singleton,
    Nat.reduceSub] at hEM
  dsimp only [g] at hEM
  simp only [ofReal_zero, add_zero, ofReal_natCast] at hEM
  rw [sum_Icc_log_add_eq hz N, integral_log_add_ofReal huIcc, add_sub_assoc,
    bernoulli_two_term_sub_integral_eq hz N] at hEM
  simp only [ofReal_zero, add_zero, ofReal_natCast, Complex.real_smul, ofReal_inv,
    ofReal_ofNat] at hEM
  rw [stirlingRemainder_def, stirlingRemainder_def]
  linear_combination -hEM

private theorem tendsto_stirlingRemainder_add_natCast (z : ℂ) :
    Tendsto (fun N : ℕ ↦ stirlingRemainder (z + N)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hupper : Tendsto (fun N : ℕ ↦ (2 : ℝ) / (z.re + (N : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_left atTop z.re tendsto_natCast_atTop_atTop)
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hupper
  filter_upwards [eventually_ge_atTop (⌈|z.re|⌉₊ + 1)] with N hN
  have hre : 1 ≤ (z + (N : ℂ)).re := by
    rw [add_re, natCast_re]
    have hN' : (⌈|z.re|⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast hN
    linarith [Nat.le_ceil |z.re|, neg_abs_le z.re]
  have hre_pos : 0 < (z + (N : ℂ)).re := by linarith
  have hne : z + (N : ℂ) ≠ 0 := fun h ↦ by simp [h] at hre_pos
  have harg : |(z + (N : ℂ)).arg| ≤ π - π / 2 := by
    have := abs_arg_le_pi_div_two_iff.mpr hre_pos.le
    linarith
  have hst := norm_logGamma_sub_stirling_le (s := z + (N : ℂ)) (δ := π / 2)
    (by positivity) (by linarith [pi_pos]) harg hne
  rw [← stirlingRemainder_def, Real.cos_pi_div_two] at hst
  norm_num at hst
  refine hst.trans ?_
  have hnorm : z.re + (N : ℝ) ≤ ‖z + (N : ℂ)‖ := by
    simpa [add_re, natCast_re] using Complex.re_le_norm (z + (N : ℂ))
  exact div_le_div_of_nonneg_left zero_le_two (by simpa [add_re, natCast_re] using hre_pos) hnorm

/-- **Stieltjes' integral identity**: for every `z` in the slit plane `ℂ ∖ (-∞, 0]`,
`stirlingRemainder z = ∫ t in Ioi 0, ((Int.fract t - Int.fract t ^ 2) / 2) / (z + t) ^ 2`. -/
theorem stirlingRemainder_eq_integral {z : ℂ} (hz : z ∈ slitPlane) :
    stirlingRemainder z =
      ∫ t in Ioi (0 : ℝ),
        (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + (t : ℂ)) ^ 2 := by
  have hint := intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_stirlingRemainder_integrand hz 0) tendsto_natCast_atTop_atTop
  have hsum : Tendsto
      (fun N : ℕ ↦ stirlingRemainder (z + N) +
        ∫ t : ℝ in 0..(N : ℝ),
          (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + (t : ℂ)) ^ 2)
      atTop
      (𝓝 (∫ t in Ioi (0 : ℝ),
        (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + (t : ℂ)) ^ 2)) := by
    simpa only [zero_add] using (tendsto_stirlingRemainder_add_natCast z).add hint
  refine tendsto_nhds_unique (l := atTop) (f := fun _ : ℕ ↦ stirlingRemainder z)
    tendsto_const_nhds ?_
  exact hsum.congr fun N ↦ (stirlingRemainder_eq_add_intervalIntegral hz N).symm

/-! ### Differentiation under the integral sign and iterated derivatives -/

private theorem hasDerivAt_stirlingRemainder_integrand {w : ℂ} {t : ℝ} (hne : w + (t : ℂ) ≠ 0)
    (j : ℕ) :
    HasDerivAt
      (fun u : ℂ ↦ (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (u + (t : ℂ)) ^ (j + 2))
      (-((j + 2 : ℕ) : ℂ) *
        ((((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (w + (t : ℂ)) ^ (j + 3))) w := by
  have hinv := ((((hasDerivAt_id w).add_const (t : ℂ)).pow (j + 2)).inv
    (pow_ne_zero _ hne)).const_mul (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ)
  refine (hinv.congr_of_eventuallyEq (Eventually.of_forall fun u ↦ ?_)).congr_deriv ?_
  · simp only [div_eq_mul_inv, Pi.inv_apply, Pi.pow_apply, id]
  · simp only [Pi.pow_apply, id, mul_one, Nat.succ_sub_one]
    have hpow_ne : (w + (t : ℂ)) ^ (j + 3) ≠ 0 := pow_ne_zero _ hne
    have hpow_eq : ((w + (t : ℂ)) ^ (j + 2)) ^ 2 =
        (w + (t : ℂ)) ^ (j + 1) * (w + (t : ℂ)) ^ (j + 3) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    rw [hpow_eq]
    field_simp [hne, hpow_ne]

/-- Differentiating the Stieltjes remainder integral under the integral sign: for every `z` in the
slit plane and `j : ℕ`, the derivative of `w ↦ ∫ t in Ioi 0, Q(t) / (w + t) ^ (j + 2)` at `z` is
`-(j + 2) * ∫ t in Ioi 0, Q(t) / (z + t) ^ (j + 3)`. -/
theorem hasDerivAt_integral_stirlingRemainder_integrand {z : ℂ} (hz : z ∈ slitPlane) (j : ℕ) :
    HasDerivAt
      (fun w : ℂ ↦ ∫ t in Ioi (0 : ℝ),
        (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (w + (t : ℂ)) ^ (j + 2))
      (-((j + 2 : ℕ) : ℂ) * ∫ t in Ioi (0 : ℝ),
        (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + (t : ℂ)) ^ (j + 3)) z := by
  obtain ⟨c, hc, hball⟩ := exists_pos_forall_mem_ball_mul_one_add_le_norm_add hz
  let Q : ℝ → ℂ := fun t ↦ (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ)
  let F : ℂ → ℝ → ℂ := fun w t ↦ Q t / (w + (t : ℂ)) ^ (j + 2)
  let F' : ℂ → ℝ → ℂ := fun w t ↦ -((j + 2 : ℕ) : ℂ) * (Q t / (w + (t : ℂ)) ^ (j + 3))
  have hF_meas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (F w) (volume.restrict (Ioi 0)) :=
    Eventually.of_forall fun w ↦ (measurable_stirlingRemainder_integrand w j).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable (F' z) (volume.restrict (Ioi 0)) :=
    (measurable_const.mul (measurable_stirlingRemainder_integrand z (j + 1))).aestronglyMeasurable
  have hbound_int : IntegrableOn
      (fun t : ℝ ↦ ((j + 2 : ℕ) : ℝ) * ((8 * c ^ (j + 3))⁻¹ * ((1 + t) ^ (j + 3))⁻¹)) (Ioi 0) :=
    ((integrableOn_Ioi_inv_add_pow one_pos (by omega : 1 ≤ j + 2)).const_mul _).const_mul _
  have hbound : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ w ∈ Metric.ball z c,
      ‖F' w t‖ ≤ ((j + 2 : ℕ) : ℝ) * ((8 * c ^ (j + 3))⁻¹ * ((1 + t) ^ (j + 3))⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    simp only [F', Q, norm_mul, norm_neg, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left
      (norm_stirlingRemainder_integrand_le hc one_pos ht.out.le (hball w hw ⟨t, ht.out.le⟩) (j + 3))
      (Nat.cast_nonneg _)
  have hdiff : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ w ∈ Metric.ball z c,
      HasDerivAt (F · t) (F' w t) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    have hden : c * (1 + t) ≤ ‖w + (t : ℂ)‖ := hball w hw ⟨t, ht.out.le⟩
    have hne : w + (t : ℂ) ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le (mul_pos hc (by linarith [ht.out])) hden)
    exact hasDerivAt_stirlingRemainder_integrand hne j
  have hkey := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z hc)
    hF_meas (integrableOn_stirlingRemainder_integrand hz j) hF'_meas hbound hbound_int hdiff).2
  simpa only [F, F', Q, MeasureTheory.integral_const_mul] using hkey

/-- Integral formula for every iterated derivative of the Stirling remainder on the slit plane:
for every `j : ℕ` and `z ∈ slitPlane`,
`iteratedDeriv j stirlingRemainder z =`
`(-1) ^ j * (j + 1)! * ∫ t in Ioi 0, Q(t) / (z + t) ^ (j + 2)`. -/
theorem iteratedDeriv_stirlingRemainder_eq_integral (j : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv j stirlingRemainder z =
      (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) *
        ∫ t in Ioi (0 : ℝ),
          (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + (t : ℂ)) ^ (j + 2) := by
  induction j generalizing z with
  | zero =>
    simpa only [iteratedDeriv_zero, pow_zero, zero_add, Nat.factorial_one, Nat.cast_one, mul_one,
      one_mul] using stirlingRemainder_eq_integral hz
  | succ j ih =>
    have heq : iteratedDeriv j stirlingRemainder =ᶠ[𝓝 z]
        fun w : ℂ ↦ (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) *
          ∫ t in Ioi (0 : ℝ),
            (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (w + (t : ℂ)) ^ (j + 2) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      exact ih hw
    rw [iteratedDeriv_succ, heq.deriv_eq,
      ((hasDerivAt_integral_stirlingRemainder_integrand hz j).const_mul _).deriv]
    rw [Nat.factorial_succ (j + 1), pow_succ]
    push_cast
    ring

/-- Stieltjes integral representation of the digamma remainder on the slit plane:
`ψ(z) - log z + 1 / (2 z) = -2 * ∫ t in Ioi 0, Q(t) / (z + t) ^ 3`. -/
theorem digamma_sub_log_add_inv_two_mul_eq_integral {z : ℂ} (hz : z ∈ slitPlane) :
    Complex.digamma z - Complex.log z + (2 * z)⁻¹ =
      -2 * ∫ t in Ioi (0 : ℝ),
        (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + (t : ℂ)) ^ 3 := by
  have h := iteratedDeriv_stirlingRemainder_eq_integral 1 hz
  rw [iteratedDeriv_one, deriv_stirlingRemainder hz] at h
  simpa using h

/-! ### Exact sector bounds -/

/-- **Sharp sector bound for the Stirling remainder and all its derivatives**: for every `j : ℕ`
and `z` in the slit plane `ℂ ∖ (-∞, 0]` (including `Re z < 0`),
`‖iteratedDeriv j stirlingRemainder z‖ ≤ j! / (8 * cos (arg z / 2) ^ (j + 2) * ‖z‖ ^ (j + 1))`. -/
theorem norm_iteratedDeriv_stirlingRemainder_le (j : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    ‖iteratedDeriv j stirlingRemainder z‖ ≤
      (j.factorial : ℝ) / (8 * Real.cos (z.arg / 2) ^ (j + 2) * ‖z‖ ^ (j + 1)) := by
  have hcos : 0 < Real.cos (z.arg / 2) := cos_arg_div_two_pos_of_mem_slitPlane hz
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr (slitPlane_ne_zero hz)
  rw [iteratedDeriv_stirlingRemainder_eq_integral j hz, norm_mul, norm_mul, norm_pow, norm_neg,
    norm_one, one_pow, one_mul, Complex.norm_natCast]
  have hdom : IntegrableOn
      (fun t : ℝ ↦ (8 * Real.cos (z.arg / 2) ^ (j + 2))⁻¹ * ((‖z‖ + t) ^ (j + 2))⁻¹) (Ioi 0) :=
    (integrableOn_Ioi_inv_add_pow hzn (Nat.succ_pos j)).const_mul _
  have hle : ‖∫ t in Ioi (0 : ℝ),
        (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + (t : ℂ)) ^ (j + 2)‖ ≤
      ∫ t in Ioi (0 : ℝ), (8 * Real.cos (z.arg / 2) ^ (j + 2))⁻¹ * ((‖z‖ + t) ^ (j + 2))⁻¹ := by
    refine norm_integral_le_of_norm_le hdom ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_stirlingRemainder_integrand_le hcos hzn ht.out.le
      (cos_arg_div_two_mul_norm_add_le_norm_add_ofReal z t) (j + 2)
  calc
    ((j + 1).factorial : ℝ) * ‖∫ t in Ioi (0 : ℝ),
          (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + (t : ℂ)) ^ (j + 2)‖
        ≤ ((j + 1).factorial : ℝ) *
          ∫ t in Ioi (0 : ℝ),
            (8 * Real.cos (z.arg / 2) ^ (j + 2))⁻¹ * ((‖z‖ + t) ^ (j + 2))⁻¹ := by
      gcongr
    _ = ((j + 1).factorial : ℝ) *
          ((8 * Real.cos (z.arg / 2) ^ (j + 2))⁻¹ * (((j + 1 : ℕ) : ℝ) * ‖z‖ ^ (j + 1))⁻¹) := by
      rw [MeasureTheory.integral_const_mul, integral_Ioi_inv_add_pow hzn (Nat.succ_pos j)]
    _ = (j.factorial : ℝ) / (8 * Real.cos (z.arg / 2) ^ (j + 2) * ‖z‖ ^ (j + 1)) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
      have hj1 : ((j + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)
      field_simp

/-- Uniform bound on a closed sector `|arg z| ≤ π - δ` (`0 < δ`, `z ≠ 0`) for every `j : ℕ`:
`‖iteratedDeriv j stirlingRemainder z‖ ≤ j! / (8 * sin (δ / 2) ^ (j + 2) * ‖z‖ ^ (j + 1))`. -/
theorem norm_iteratedDeriv_stirlingRemainder_le_of_abs_arg_le (j : ℕ) {z : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hz : |z.arg| ≤ π - δ) (hz0 : z ≠ 0) :
    ‖iteratedDeriv j stirlingRemainder z‖ ≤
      (j.factorial : ℝ) / (8 * Real.sin (δ / 2) ^ (j + 2) * ‖z‖ ^ (j + 1)) := by
  have hslit : z ∈ slitPlane := mem_slitPlane_of_abs_arg_le hδ hz hz0
  have hδπ : δ ≤ π := by linarith [abs_nonneg z.arg]
  have hsin_pos : 0 < Real.sin (δ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  have hcos : Real.sin (δ / 2) ≤ Real.cos (z.arg / 2) :=
    sin_div_two_le_cos_arg_div_two_of_abs_arg_le hδ.le hz
  refine (norm_iteratedDeriv_stirlingRemainder_le j hslit).trans ?_
  gcongr

/-- Sharp slit-plane bound for the Stirling remainder (`j = 0`):
`‖stirlingRemainder z‖ ≤ 1 / (8 * cos (arg z / 2) ^ 2 * ‖z‖)`. -/
theorem norm_stirlingRemainder_le {z : ℂ} (hz : z ∈ slitPlane) :
    ‖stirlingRemainder z‖ ≤ 1 / (8 * Real.cos (z.arg / 2) ^ 2 * ‖z‖) := by
  simpa using norm_iteratedDeriv_stirlingRemainder_le 0 hz

/-- **Sharp sectorial digamma bound** (`j = 1`): for every `z` in the slit plane `ℂ ∖ (-∞, 0]`,
`‖ψ(z) - log z + 1 / (2 z)‖ ≤ 1 / (8 * cos (arg z / 2) ^ 3 * ‖z‖ ^ 2)`. -/
theorem norm_digamma_sub_log_add_inv_two_mul_le {z : ℂ} (hz : z ∈ slitPlane) :
    ‖Complex.digamma z - Complex.log z + (2 * z)⁻¹‖ ≤
      1 / (8 * Real.cos (z.arg / 2) ^ 3 * ‖z‖ ^ 2) := by
  have h := norm_iteratedDeriv_stirlingRemainder_le 1 hz
  rw [iteratedDeriv_one, deriv_stirlingRemainder hz] at h
  simpa using h

/-! ### Positive real axis: reality, sign, and monotonicity -/

/-- On the positive real axis, every iterated derivative of `stirlingRemainder` is real and equals
`(-1) ^ j * (j + 1)! * ∫ t in Ioi 0, ((Int.fract t - Int.fract t ^ 2) / 2) / (x + t) ^ (j + 2)`. -/
theorem iteratedDeriv_stirlingRemainder_ofReal (j : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv j stirlingRemainder x =
      (((-1 : ℝ) ^ j * ((j + 1).factorial : ℝ) *
        ∫ t in Ioi (0 : ℝ),
          (Int.fract t - Int.fract t ^ 2) / 2 / (x + t) ^ (j + 2) : ℝ) : ℂ) := by
  rw [iteratedDeriv_stirlingRemainder_eq_integral j (ofReal_mem_slitPlane.mpr hx)]
  have hint : ∫ t in Ioi (0 : ℝ),
        (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / ((x : ℂ) + (t : ℂ)) ^ (j + 2) =
      ((∫ t in Ioi (0 : ℝ), (Int.fract t - Int.fract t ^ 2) / 2 / (x + t) ^ (j + 2) : ℝ) : ℂ) := by
    calc
      ∫ t in Ioi (0 : ℝ),
          (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / ((x : ℂ) + (t : ℂ)) ^ (j + 2)
        = ∫ t in Ioi (0 : ℝ),
            (((Int.fract t - Int.fract t ^ 2) / 2 / (x + t) ^ (j + 2) : ℝ) : ℂ) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
          push_cast
          rfl
      _ = ((∫ t in Ioi (0 : ℝ),
            (Int.fract t - Int.fract t ^ 2) / 2 / (x + t) ^ (j + 2) : ℝ) : ℂ) :=
        integral_ofReal (𝕜 := ℂ)
  rw [hint]
  push_cast
  rfl

/-- For every `x > 0` and `j : ℕ`, the real Stieltjes integral
`∫ t in Ioi 0, ((Int.fract t - Int.fract t ^ 2) / 2) / (x + t) ^ (j + 2)` is strictly positive. -/
theorem integral_stirlingRemainder_integrand_pos {x : ℝ} (hx : 0 < x) (j : ℕ) :
    0 < ∫ t in Ioi (0 : ℝ), (Int.fract t - Int.fract t ^ 2) / 2 / (x + t) ^ (j + 2) := by
  let f : ℝ → ℝ := fun t ↦ (Int.fract t - Int.fract t ^ 2) / 2 / (x + t) ^ (j + 2)
  have hf_int : IntegrableOn f (Ioi 0) := by
    have h := (integrableOn_stirlingRemainder_integrand (ofReal_mem_slitPlane.mpr hx) j).re
    refine h.congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
    dsimp only [f]
    rw [RCLike.re_to_complex, ← ofReal_add, ← ofReal_pow, ← ofReal_div, ofReal_re]
  have hf_nonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have h0 := Int.fract_nonneg t
    have h1 := (Int.fract_lt_one t).le
    exact div_nonneg (by nlinarith) (pow_nonneg (by linarith [ht.out]) _)
  rw [setIntegral_pos_iff_support_of_nonneg_ae hf_nonneg hf_int]
  have hsub : Ioo (1 / 4 : ℝ) (3 / 4) ⊆ Function.support f ∩ Ioi 0 := by
    intro t ht
    refine ⟨?_, Set.mem_Ioi.mpr (by linarith [ht.1])⟩
    have hfl : Int.fract t = t := Int.fract_eq_self.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hpos : 0 < f t := by
      dsimp only [f]
      rw [hfl]
      exact div_pos (by nlinarith [ht.1, ht.2]) (pow_pos (by linarith [ht.1]) _)
    exact hpos.ne'
  have hmeas : (0 : ENNReal) < volume (Ioo (1 / 4 : ℝ) (3 / 4)) := by
    rw [Real.volume_Ioo]
    norm_num
  exact hmeas.trans_le (measure_mono hsub)

/-- On the positive real axis, the Stirling remainder is strictly positive. -/
theorem re_stirlingRemainder_ofReal_pos {x : ℝ} (hx : 0 < x) :
    0 < (stirlingRemainder x).re := by
  have h := iteratedDeriv_stirlingRemainder_ofReal 0 hx
  rw [iteratedDeriv_zero] at h
  rw [h, ofReal_re]
  simpa using integral_stirlingRemainder_integrand_pos hx 0

/-- On the positive real axis, the derivative of the Stirling remainder is strictly negative. -/
theorem re_deriv_stirlingRemainder_ofReal_neg {x : ℝ} (hx : 0 < x) :
    (deriv stirlingRemainder x).re < 0 := by
  have h := iteratedDeriv_stirlingRemainder_ofReal 1 hx
  rw [iteratedDeriv_one] at h
  rw [h, ofReal_re]
  have hpos := integral_stirlingRemainder_integrand_pos hx 1
  norm_num
  linarith

/-- On `(0, ∞)`, the real Stirling remainder
`u ↦ Real.log (Real.Gamma u) - ((u - 1 / 2) * Real.log u - u + Real.log (2 * π) / 2)` has strictly
negative derivative. -/
theorem deriv_real_stirlingRemainder_neg {x : ℝ} (hx : 0 < x) :
    deriv (fun u : ℝ ↦ Real.log (Real.Gamma u) -
      ((u - 1 / 2) * Real.log u - u + Real.log (2 * π) / 2)) x < 0 := by
  have hd : HasDerivAt (fun u : ℝ ↦ (stirlingRemainder u).re) (deriv stirlingRemainder x).re x := by
    have hc : HasDerivAt (fun u : ℝ ↦ stirlingRemainder (u : ℂ)) (deriv stirlingRemainder x) x := by
      rw [deriv_stirlingRemainder (ofReal_mem_slitPlane.mpr hx)]
      exact (hasDerivAt_stirlingRemainder (ofReal_mem_slitPlane.mpr hx)).comp_ofReal
    simpa [Function.comp_def] using Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hc
  have heq : (fun u : ℝ ↦ Real.log (Real.Gamma u) -
        ((u - 1 / 2) * Real.log u - u + Real.log (2 * π) / 2)) =ᶠ[𝓝 x]
      fun u : ℝ ↦ (stirlingRemainder u).re := by
    filter_upwards [Ioi_mem_nhds hx] with u hu
    rw [stirlingRemainder_ofReal hu, ofReal_re]
  rw [heq.deriv_eq, hd.deriv]
  exact re_deriv_stirlingRemainder_ofReal_neg hx

end TauCeti
