/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.Calculus.IteratedFDeriv.Reciprocal
import TauCeti.Analysis.Fourier.FourierCharDeriv
import TauCeti.Analysis.InnerProductSpace.Calculus

/-!
# Non-stationary phase

An oscillatory integral `∫ φ(x) 𝐞(Φ(x)) dx` with a smooth compactly supported amplitude decays
faster than every power of the size of the phase, as long as the phase has no critical point on the
support of the amplitude: integrating by parts against `𝐞(Φ)`, each time dividing by a derivative
of the phase, gains one power of its size. This file proves three forms of this principle.

## Quadratic phases on the line

For a smooth amplitude `g` supported in `[-R, R]`, consider the oscillatory integral

`∫ exp(2πi (t r - s r²)) g(r) dr`.

Its phase has derivative `2π (t - 2 s r)`. When `4 R |s| ≤ |t|`, on the support of `g` this
derivative satisfies `|t - 2 s r| ≥ |t| / 2`, so it stays away from zero as soon as moreover
`t ≠ 0`. In this non-stationary regime, `t ≠ 0` and `4 R |s| ≤ |t|`, the integral decays faster
than every power of `|t|`, uniformly in `s`:

`‖∫ exp(2πi (t r - s r²)) g(r) dr‖ ≤ C_N |t|^(-N)` for `t ≠ 0` and `4 R |s| ≤ |t|`.

(`TauCeti.exists_norm_integral_cexp_mul_le_of_mul_abs_le`, which only needs `g` to be `C^N` for
the rate `|t|^(-N)`). The proof integrates by parts `N`
times against `exp(2πi (t r - s r²))`, each time dividing by the phase derivative. Since that
derivative is affine in `r`, every amplitude produced on the way is a sum of terms
`h(r) s^j / (t - 2 s r)^k` with `h` a derivative of `g` and `j ≤ k`, and such a term is
`O(|t|^(j - k))` on the support. Inducting over this class of amplitudes, rather than over
explicit formulas, keeps the bookkeeping to one integration by parts.

This is the decay that makes the low-frequency part of the subordination of the half-wave
propagator to the Schrödinger propagator negligible.

## Phases with a large directional derivative

On a finite-dimensional real normed space, let `Φᵢ` be a family of smooth real phases, `wᵢ`
directions with `‖wᵢ‖ ≤ 1` and `τᵢ > 0` such that `|DΦᵢ(x) wᵢ| ≥ τᵢ` on the support of `φ`, while
every derivative of `Φᵢ` of positive order is `O(τᵢ)` there. Then

`‖∫ φ(x) 𝐞(Φᵢ(x)) dx‖ ≤ C_N τᵢ^(-N)`, uniformly in `i`

(`TauCeti.exists_norm_integral_mul_fourierChar_le`). The proof integrates by parts `N` times in
the direction `wᵢ` only: the amplitudes `u₀ = φ`, `uₖ₊₁ = D((DΦᵢ · wᵢ)⁻¹ uₖ) wᵢ`, where `uₖ` has
derivatives of size `O(τᵢ⁻ᵏ)`, by the Leibniz rule and the bounds `O(τᵢ⁻¹)` for the derivatives
of the reciprocal `(DΦᵢ · wᵢ)⁻¹` (`TauCeti.exists_norm_iteratedFDeriv_inv_le_div`).

## Changes of variables in a Fourier integral

On a finite-dimensional real inner product space, a change of variables `f` in a Fourier integral
produces the phases `⟪f x, ζ⟫ - ⟪x, ξ⟫`, with gradient `(Df(x))† ζ - ξ`. If `(Df(x))†` stays within
`c / 2` of a linear map `B` on the support of `φ`, then on the frequencies with
`c (‖ξ‖ + ‖ζ‖) ≤ ‖B ζ - ξ‖` the derivative of the phase in the direction of `B ζ - ξ` is at least
`c (‖ξ‖ + ‖ζ‖) / 2`, and the oscillatory integral decays faster than every power of `‖ξ‖ + ‖ζ‖`
(`TauCeti.exists_norm_integral_mul_fourierChar_inner_sub_le`). This is the estimate behind the
invariance of the wave front set under changes of variables.

## Main declarations

* `TauCeti.exists_norm_integral_cexp_mul_le_of_mul_abs_le`: decay at the rate `|t|^(-N)` of the
  oscillatory integral with phase `t r - s r²` and a `C^N` amplitude, in the non-stationary regime
  `t ≠ 0`, `4 R |s| ≤ |t|`.
* `TauCeti.exists_norm_integral_mul_fourierChar_le`: decay at the rate `τᵢ^(-N)`, uniformly in
  `i`, for a family of phases whose derivatives in directions `wᵢ` have size at least `τᵢ`.
* `TauCeti.exists_norm_integral_mul_fourierChar_inner_sub_le`: rapid decay in `‖ξ‖ + ‖ζ‖` of the
  oscillatory integrals with phases `⟪f x, ζ⟫ - ⟪x, ξ⟫`, away from their stationary frequencies.

## References

* E. M. Stein, *Harmonic Analysis: Real-Variable Methods, Orthogonality, and Oscillatory
  Integrals*, Chapter VIII, §1.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 7.7.1.
-/

public section

noncomputable section

open MeasureTheory Set Filter Complex Real
open scoped Topology ContDiff FourierTransform RealInnerProductSpace InnerProduct

namespace TauCeti

namespace NonstationaryPhase

/-- The oscillating factor `exp(2πi (t r - s r²))`. -/
private def phase (t s r : ℝ) : ℂ :=
  cexp (((2 * π * (t * r - s * r ^ 2) : ℝ) : ℂ) * I)

/-- The coefficient `s^j / (t - 2 s r)^k` produced by `k` divisions by the phase derivative. -/
private def coeff (t s : ℝ) (j k : ℕ) (r : ℝ) : ℝ :=
  s ^ j / (t - 2 * s * r) ^ k

private theorem norm_phase (t s r : ℝ) : ‖phase t s r‖ = 1 :=
  norm_exp_ofReal_mul_I _

private theorem continuous_phase (t s : ℝ) : Continuous (phase t s) := by
  unfold phase
  fun_prop

private theorem hasDerivAt_phase (t s r : ℝ) :
    HasDerivAt (phase t s) (phase t s r * (((2 * π * (t - 2 * s * r)) : ℝ) * I)) r := by
  have h : HasDerivAt (fun r : ℝ ↦ 2 * π * (t * r - s * r ^ 2)) (2 * π * (t - 2 * s * r)) r := by
    refine ((((hasDerivAt_id' r).const_mul t).sub
      ((hasDerivAt_pow 2 r).const_mul s)).const_mul (2 * π)).congr_deriv ?_
    simp only [mul_one, Nat.cast_ofNat]
    ring
  exact (h.ofReal_comp.mul_const I).cexp

variable {t s R : ℝ}

/-- On `[-R, R]` the phase derivative stays away from zero in the non-stationary regime. -/
private theorem half_abs_le_abs_sub (hts : 4 * R * |s| ≤ |t|) {r : ℝ} (hr : r ∈ Icc (-R) R) :
    |t| / 2 ≤ |t - 2 * s * r| := by
  have hr' : |r| ≤ R := abs_le.2 hr
  have h2 : |2 * s * r| ≤ |t| / 2 := by
    rw [abs_mul, abs_mul, abs_two]
    nlinarith [abs_nonneg s, abs_nonneg r]
  have := abs_sub_abs_le_abs_sub t (2 * s * r)
  linarith

private theorem abs_le_of_mul_abs_le (hR : 0 < R) (hts : 4 * R * |s| ≤ |t|) :
    |s| ≤ |t| / (4 * R) := by
  rw [le_div_iff₀ (by positivity)]
  linarith

private theorem continuousAt_coeff (j k : ℕ) {r : ℝ} (hr : t - 2 * s * r ≠ 0) :
    ContinuousAt (coeff t s j k) r := by
  unfold coeff
  exact continuousAt_const.div (by fun_prop) (pow_ne_zero _ hr)

private theorem hasDerivAt_coeff (j k : ℕ) {r : ℝ} (hr : t - 2 * s * r ≠ 0) :
    HasDerivAt (coeff t s j k) (2 * (k : ℝ) * coeff t s (j + 1) (k + 1) r) r := by
  have hP : HasDerivAt (fun r : ℝ ↦ t - 2 * s * r) (-(2 * s)) r := by
    simpa using ((hasDerivAt_id r).const_mul (2 * s)).const_sub t
  have hPk : HasDerivAt (fun r : ℝ ↦ (t - 2 * s * r) ^ k)
      (k * (t - 2 * s * r) ^ (k - 1) * -(2 * s)) r := hP.pow k
  have := (hasDerivAt_const r (s ^ j)).fun_div hPk (pow_ne_zero k hr)
  refine this.congr_deriv ?_
  rcases k with _ | k
  · simp
  · simp only [coeff, Nat.add_sub_cancel]
    field_simp
    push_cast
    ring

/-- An amplitude `h s^j / (t - 2 s r)^k` with `h` continuous and supported in `[-R, R]` is
continuous in the non-stationary regime: off the support of `h` it vanishes locally. -/
private theorem continuous_mul_coeff {h : ℝ → ℂ} (hh : Continuous h)
    (hhR : tsupport h ⊆ Icc (-R) R) (ht : t ≠ 0) (hts : 4 * R * |s| ≤ |t|) (j k : ℕ) :
    Continuous fun r ↦ phase t s r * (h r * coeff t s j k r) := by
  refine continuous_iff_continuousAt.2 fun r ↦ ?_
  by_cases hr : r ∈ tsupport h
  · have hP : t - 2 * s * r ≠ 0 := by
      have := half_abs_le_abs_sub hts (hhR hr)
      intro h0
      rw [h0, abs_zero] at this
      have : 0 < |t| := abs_pos.2 ht
      linarith
    exact (continuous_phase t s).continuousAt.mul
      (hh.continuousAt.mul (continuous_ofReal.continuousAt.comp (continuousAt_coeff j k hP)))
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hr] with x hx
    simp [hx]

private theorem integrable_mul_coeff {h : ℝ → ℂ} (hh : Continuous h)
    (hhR : tsupport h ⊆ Icc (-R) R) (ht : t ≠ 0) (hts : 4 * R * |s| ≤ |t|) (j k : ℕ) :
    Integrable fun r ↦ phase t s r * (h r * coeff t s j k r) := by
  refine (continuous_mul_coeff hh hhR ht hts j k).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun r hr ↦ ?_
  have : h r = 0 := image_eq_zero_of_notMem_tsupport fun h' ↦ hr (hhR h')
  simp [this]

/-- The trivial bound: on the support, `|s^j / (t - 2 s r)^k| ≤ (4R)^(-j) 2^k |t|^(j - k)`. -/
private theorem norm_integral_mul_coeff_le {h : ℝ → ℂ} (hh : Continuous h) (hR : 0 < R)
    (hhR : tsupport h ⊆ Icc (-R) R) (ht : t ≠ 0) (hts : 4 * R * |s| ≤ |t|) {j k : ℕ}
    (hjk : j ≤ k) :
    ‖∫ r, phase t s r * (h r * coeff t s j k r)‖ ≤
      (∫ r, ‖h r‖) * (((4 * R) ^ j)⁻¹ * 2 ^ k * (|t| ^ (k - j))⁻¹) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjk
  rw [Nat.add_sub_cancel_left]
  have hhi : Integrable h := hh.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -R) (b := R))
      ((subset_tsupport h).trans hhR))
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (hhi.norm.mul_const _) (Eventually.of_forall fun r ↦ ?_)
  rw [norm_mul, norm_phase, one_mul, norm_mul, norm_real, Real.norm_eq_abs]
  by_cases hr : r ∈ tsupport h
  · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hP := half_abs_le_abs_sub hts (hhR hr)
    have hs := abs_le_of_mul_abs_le hR hts
    have hPpos : 0 < |t - 2 * s * r| := lt_of_lt_of_le (by positivity) hP
    rw [coeff, abs_div, abs_pow, abs_pow, div_le_iff₀ (pow_pos hPpos _)]
    calc |s| ^ j ≤ (|t| / (4 * R)) ^ j := pow_le_pow_left₀ (abs_nonneg s) hs j
      _ = ((4 * R) ^ j)⁻¹ * 2 ^ (j + m) * (|t| ^ m)⁻¹ * (|t| / 2) ^ (j + m) := by
          rw [div_pow, div_pow, pow_add, pow_add]
          field_simp
      _ ≤ ((4 * R) ^ j)⁻¹ * 2 ^ (j + m) * (|t| ^ m)⁻¹ * |t - 2 * s * r| ^ (j + m) := by
          gcongr
  · rw [image_eq_zero_of_notMem_tsupport hr, norm_zero, zero_mul, zero_mul]

/-- One integration by parts: the integral against `s^j / (t - 2 s r)^k` is `-(2πi)⁻¹` times the
integrals against `s^j / (t - 2 s r)^(k+1)` with `g'` and against `s^(j+1) / (t - 2 s r)^(k+2)`
with `2 (k + 1) g`. -/
private theorem integral_mul_coeff_eq {g : ℝ → ℂ} (hg : ContDiff ℝ 1 g)
    (hgR : tsupport g ⊆ Icc (-R) R) (ht : t ≠ 0) (hts : 4 * R * |s| ≤ |t|) (j k : ℕ) :
    ∫ r, phase t s r * (g r * coeff t s j k r) =
      -((2 * π : ℂ) * I)⁻¹ * ((∫ r, phase t s r * (deriv g r * coeff t s j (k + 1) r)) +
        (2 * ((k : ℝ) + 1) : ℝ) * ∫ r, phase t s r * (g r * coeff t s (j + 1) (k + 2) r)) := by
  have hP : ∀ r ∈ tsupport g, t - 2 * s * r ≠ 0 := fun r hr h0 ↦ by
    have := half_abs_le_abs_sub hts (hgR hr)
    rw [h0, abs_zero] at this
    linarith [abs_pos.2 ht]
  have hgc : Continuous g := hg.continuous
  have hg'c : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hg'R : tsupport (deriv g) ⊆ Icc (-R) R := (tsupport_deriv_subset).trans hgR
  set v : ℝ → ℂ := fun r ↦ g r * coeff t s j (k + 1) r
  set v' : ℝ → ℂ := fun r ↦ deriv g r * coeff t s j (k + 1) r +
    (2 * ((k : ℝ) + 1) : ℝ) * (g r * coeff t s (j + 1) (k + 2) r)
  set u' : ℝ → ℂ := fun r ↦ phase t s r * (((2 * π * (t - 2 * s * r)) : ℝ) * I)
  have hv : ∀ r, HasDerivAt v (v' r) r := fun r ↦ by
    by_cases hr : r ∈ tsupport g
    · have h1 := (hg.differentiable one_ne_zero r).hasDerivAt
      have h2 := (hasDerivAt_coeff j (k + 1) (hP r hr)).ofReal_comp
      convert h1.mul h2 using 1
      simp only [v', Nat.cast_add, Nat.cast_one]
      push_cast
      ring
    · have h0 : v' r = 0 := by
        simp [v', image_eq_zero_of_notMem_tsupport hr, deriv_of_notMem_tsupport hr]
      rw [h0]
      refine (hasDerivAt_const r (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hr] with x hx
      simp [v, hx]
  -- `phase * g * coeff k` is `(2πi)⁻¹ u' * v`, pointwise.
  have hpt : ∀ r, phase t s r * (g r * coeff t s j k r) = ((2 * π : ℂ) * I)⁻¹ * (u' r * v r) :=
    fun r ↦ by
      by_cases hr : r ∈ tsupport g
      · have hPc : (t : ℂ) - 2 * s * r ≠ 0 := by exact_mod_cast hP r hr
        simp only [u', v, coeff]
        push_cast
        field_simp
        ring
      · simp [v, image_eq_zero_of_notMem_tsupport hr]
  have hint1 := integrable_mul_coeff hg'c hg'R ht hts j (k + 1)
  have hint2 := integrable_mul_coeff hgc hgR ht hts (j + 1) (k + 2)
  have huv' : Integrable fun r ↦ phase t s r * v' r := by
    simp only [v', mul_add, mul_left_comm (phase t s _) ((_ : ℝ) : ℂ)]
    exact hint1.add (hint2.const_mul _)
  have huv : Integrable fun r ↦ phase t s r * v r := integrable_mul_coeff hgc hgR ht hts j _
  have hu'v : Integrable fun r ↦ u' r * v r := by
    have := (integrable_mul_coeff hgc hgR ht hts j k).const_mul ((2 * π : ℂ) * I)
    refine this.congr (Eventually.of_forall fun r ↦ ?_)
    dsimp only
    rw [hpt r, ← mul_assoc, mul_inv_cancel₀ (by simp [pi_ne_zero]), one_mul]
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (u := phase t s) (u' := u')
    (fun r _ ↦ hasDerivAt_phase t s r) (fun r _ ↦ hv r) huv' hu'v huv
  have h2 : ∫ r, u' r * v r = -∫ r, phase t s r * v' r := by rw [hibp, neg_neg]
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul, h2, mul_neg, ← neg_mul]
  congr 1
  simp only [v', mul_add, mul_left_comm (phase t s _) ((_ : ℝ) : ℂ)]
  rw [integral_add hint1 (hint2.const_mul _), integral_const_mul]

/-- The induction behind non-stationary phase: the integral against `s^j / (t - 2 s r)^k`, `j ≤ k`,
is `O(|t|^(-(N + k - j)))` for every `N`. -/
private theorem exists_norm_integral_mul_coeff_le (hR : 0 < R) (N : ℕ) :
    ∀ (g : ℝ → ℂ), ContDiff ℝ N g → tsupport g ⊆ Icc (-R) R → ∀ j k : ℕ, j ≤ k →
      ∃ C, ∀ t s : ℝ, t ≠ 0 → 4 * R * |s| ≤ |t| →
        ‖∫ r, phase t s r * (g r * coeff t s j k r)‖ ≤ C * (|t| ^ (N + (k - j)))⁻¹ := by
  induction N with
  | zero =>
    intro g hg hgR j k hjk
    refine ⟨(∫ r, ‖g r‖) * (((4 * R) ^ j)⁻¹ * 2 ^ k), fun t s ht hts ↦ ?_⟩
    rw [zero_add]
    exact (norm_integral_mul_coeff_le hg.continuous hR hgR ht hts hjk).trans_eq (by ring)
  | succ N ih =>
    intro g hg hgR j k hjk
    have hg' : ContDiff ℝ (N + 1) g := by exact_mod_cast hg
    obtain ⟨C₁, hC₁⟩ := ih (deriv g) (contDiff_succ_iff_deriv.1 hg').2.2
      ((tsupport_deriv_subset).trans hgR) j (k + 1) (by omega)
    obtain ⟨C₂, hC₂⟩ := ih g (hg.of_le (by exact_mod_cast N.le_succ)) hgR (j + 1) (k + 2)
      (by omega)
    refine ⟨(2 * π)⁻¹ * (C₁ + 2 * ((k : ℝ) + 1) * C₂), fun t s ht hts ↦ ?_⟩
    have he₁ : N + (k + 1 - j) = N + 1 + (k - j) := by omega
    have he₂ : N + (k + 2 - (j + 1)) = N + 1 + (k - j) := by omega
    have h₁ := hC₁ t s ht hts
    have h₂ := hC₂ t s ht hts
    rw [he₁] at h₁
    rw [he₂] at h₂
    have key : ‖-((2 * π : ℂ) * I)⁻¹‖ = (2 * π)⁻¹ := by
      simp [abs_of_pos pi_pos]
    rw [integral_mul_coeff_eq (hg.of_le (by exact_mod_cast Nat.le_add_left 1 N)) hgR ht hts j k,
      norm_mul, key, mul_assoc]
    gcongr
    calc _ ≤ ‖∫ r, phase t s r * (deriv g r * coeff t s j (k + 1) r)‖ +
          ‖((2 * ((k : ℝ) + 1) : ℝ) : ℂ)‖ *
            ‖∫ r, phase t s r * (g r * coeff t s (j + 1) (k + 2) r)‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ C₁ * (|t| ^ (N + 1 + (k - j)))⁻¹ +
          2 * ((k : ℝ) + 1) * (C₂ * (|t| ^ (N + 1 + (k - j)))⁻¹) := by
          rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
          gcongr
      _ = _ := by ring

end NonstationaryPhase

open NonstationaryPhase in
/-- **Non-stationary phase for quadratic phases.** Let `g` be `N` times continuously
differentiable and supported in `[-R, R]`, `R > 0`. There is `C ≥ 0` such that, whenever `t ≠ 0`
and `4 R |s| ≤ |t|`,

`‖∫ exp(2πi (t r - s r²)) g(r) dr‖ ≤ C |t|^(-N)`.

On the support of `g` the phase derivative `2π (t - 2 s r)` has size at least `π |t|`. -/
theorem exists_norm_integral_cexp_mul_le_of_mul_abs_le {g : ℝ → ℂ} {N : ℕ} (hg : ContDiff ℝ N g)
    {R : ℝ} (hR : 0 < R) (hgR : tsupport g ⊆ Icc (-R) R) :
    ∃ C, 0 ≤ C ∧ ∀ t s : ℝ, t ≠ 0 → 4 * R * |s| ≤ |t| →
      ‖∫ r, cexp (((2 * π * (t * r - s * r ^ 2) : ℝ) : ℂ) * I) * g r‖ ≤ C * (|t| ^ N)⁻¹ := by
  obtain ⟨C, hC⟩ := exists_norm_integral_mul_coeff_le hR N g hg hgR 0 0 le_rfl
  have hC' : ∀ t s : ℝ, t ≠ 0 → 4 * R * |s| ≤ |t| →
      ‖∫ r, cexp (((2 * π * (t * r - s * r ^ 2) : ℝ) : ℂ) * I) * g r‖ ≤ C * (|t| ^ N)⁻¹ :=
    fun t s ht hts ↦ by simpa [coeff, phase] using hC t s ht hts
  exact ⟨C, by simpa using (norm_nonneg _).trans (hC' 1 0 one_ne_zero (by simp)), hC'⟩

section Directional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace NonstationaryPhase

/-- The reciprocal of the derivative of the phase in the direction `w`, times an amplitude `u`
supported where that derivative does not vanish, is smooth. -/
private theorem contDiff_inv_fderiv_apply_mul {u : E → ℂ} (hu : ContDiff ℝ ∞ u) {Φ : E → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) {w : E} (ha : ∀ x ∈ tsupport u, fderiv ℝ Φ x w ≠ 0) :
    ContDiff ℝ ∞ fun z ↦ ((fderiv ℝ Φ z w : ℝ) : ℂ)⁻¹ * u z := by
  have hac := hΦ.ofReal_fderiv_apply (m := ∞) (by simp) w
  exact (ContinuousLinearMap.mul ℝ ℂ).contDiff_of_tsupport_subset_right
    (hac.contDiffOn.inv fun z hz ↦ hz) hu.contDiffOn
    (isOpen_ne_fun hac.continuous continuous_const) fun x hx ↦ by simpa using ha x hx

/-- The amplitudes produced by integrating `k` times by parts in the direction `w` against the
phase `𝐞 (Φ x)`, starting from `φ`. -/
private noncomputable def amplitude (Φ : E → ℝ) (w : E) (φ : E → ℂ) : ℕ → E → ℂ
  | 0 => φ
  | k + 1 => fun x ↦ fderiv ℝ (fun z ↦ ((fderiv ℝ Φ z w : ℝ) : ℂ)⁻¹ * amplitude Φ w φ k z) x w

private theorem contDiff_amplitude {φ : E → ℂ} (hφ : ContDiff ℝ ∞ φ) {Φ : E → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) {w : E} (ha : ∀ x ∈ tsupport φ, fderiv ℝ Φ x w ≠ 0) (k : ℕ) :
    ContDiff ℝ ∞ (amplitude Φ w φ k) ∧ tsupport (amplitude Φ w φ k) ⊆ tsupport φ := by
  induction k with
  | zero => exact ⟨hφ, subset_rfl⟩
  | succ k ih =>
    have hf := contDiff_inv_fderiv_apply_mul ih.1 hΦ fun x hx ↦ ha x (ih.2 hx)
    refine ⟨(hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const, ?_⟩
    refine (tsupport_comp_subset (g := fun L : E →L[ℝ] ℂ ↦ L w) (by simp) _).trans ?_
    exact (tsupport_fderiv_subset ℝ).trans ((tsupport_mul_subset_right).trans ih.2)

variable {ι : Type*} {φ : E → ℂ} {Φ : ι → E → ℝ} {w : ι → E} {τ : ι → ℝ}

/-- Uniform bounds on the derivatives of the reciprocal of the phase derivative `DΦᵢ(x) wᵢ`: if it
has size at least `τᵢ` on `K` and the derivatives of `Φᵢ` of positive order are `O(τᵢ)` on `K`, then
the derivatives of its reciprocal are `O(τᵢ⁻¹)` on `K`. -/
private theorem exists_norm_iteratedFDeriv_inv_fderiv_apply_le {K : Set E}
    (hΦ : ∀ i, ContDiff ℝ ∞ (Φ i)) (hw : ∀ i, ‖w i‖ ≤ 1) (hτ : ∀ i, 0 < τ i)
    (hlow : ∀ i, ∀ x ∈ K, τ i ≤ |fderiv ℝ (Φ i) x (w i)|)
    (hhigh : ∀ k : ℕ, ∃ C, ∀ i, ∀ x ∈ K, ‖iteratedFDeriv ℝ (k + 1) (Φ i) x‖ ≤ C * τ i) (n : ℕ) :
    ∃ Q, 0 ≤ Q ∧ ∀ i, ∀ j ≤ n, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (fun z ↦ ((fderiv ℝ (Φ i) z (w i) : ℝ) : ℂ)⁻¹) x‖ ≤ Q / τ i := by
  choose C hC using hhigh
  set A := ∑ j ∈ Finset.range (n + 1), |C j|
  obtain ⟨Q, hQ0, hQ⟩ := exists_norm_iteratedFDeriv_inv_le_div (E := E) (𝕜 := ℂ) n A one_pos
  refine ⟨Q, hQ0, fun i j hj x hx ↦ hQ _ (τ i) x (hτ i) ?_ (fun j' hj' ↦ ?_) ?_ j hj⟩
  · exact ((hΦ i).ofReal_fderiv_apply (m := ∞) (by simp) (w i)).of_le (by exact_mod_cast le_top)
  · have hCτ : 0 ≤ C j' * τ i := (norm_nonneg _).trans (hC j' i x hx)
    calc _ ≤ ‖iteratedFDeriv ℝ (j' + 1) (Φ i) x‖ * ‖w i‖ :=
          (hΦ i).norm_iteratedFDeriv_ofReal_fderiv_apply_le (by exact_mod_cast le_top) _ x
      _ ≤ C j' * τ i * 1 := mul_le_mul (hC j' i x hx) (hw i) (norm_nonneg _) hCτ
      _ ≤ |C j'| * τ i := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right (le_abs_self _) (hτ i).le
      _ ≤ A * τ i := by
          refine mul_le_mul_of_nonneg_right ?_ (hτ i).le
          exact Finset.single_le_sum (f := fun j ↦ |C j|) (fun _ _ ↦ abs_nonneg _)
              (Finset.mem_range.2 (Nat.lt_succ_of_le hj'))
  · rw [one_mul, norm_real, Real.norm_eq_abs]
    exact hlow i x hx

/-- The phase derivative does not vanish where it is bounded below by a positive `τᵢ`. -/
private theorem fderiv_apply_ne_zero_of_le_abs (hτ : ∀ i, 0 < τ i)
    (hlow : ∀ i, ∀ x ∈ tsupport φ, τ i ≤ |fderiv ℝ (Φ i) x (w i)|) (i : ι) :
    ∀ x ∈ tsupport φ, fderiv ℝ (Φ i) x (w i) ≠ 0 := fun x hx h ↦ by
  have h' := hlow i x hx
  rw [h, abs_zero] at h'
  exact (hτ i).not_ge h'

/-- Uniform bounds on the amplitudes: the derivatives of the `k`-th amplitude are `O(τᵢ⁻ᵏ)`. -/
private theorem exists_norm_iteratedFDeriv_amplitude_le (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ)
    (hΦ : ∀ i, ContDiff ℝ ∞ (Φ i)) (hw : ∀ i, ‖w i‖ ≤ 1) (hτ : ∀ i, 0 < τ i)
    (hlow : ∀ i, ∀ x ∈ tsupport φ, τ i ≤ |fderiv ℝ (Φ i) x (w i)|)
    (hhigh : ∀ k : ℕ, ∃ C, ∀ i, ∀ x ∈ tsupport φ,
      ‖iteratedFDeriv ℝ (k + 1) (Φ i) x‖ ≤ C * τ i) (k n : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ i, ∀ j ≤ n, ∀ y,
      ‖iteratedFDeriv ℝ j (amplitude (Φ i) (w i) φ k) y‖ ≤ C / τ i ^ k := by
  induction k generalizing n with
  | zero =>
    obtain ⟨C, hC0, hC⟩ :=
      hφc.exists_bound_iteratedFDeriv_of_contDiff
        (hφ.of_le (m := (n : WithTop ℕ∞)) (by exact_mod_cast le_top))
    exact ⟨C, hC0, fun i j hj y ↦ by simpa [amplitude] using hC j hj y⟩
  | succ k ih =>
    obtain ⟨C, hC0, hC⟩ := ih (n + 1)
    obtain ⟨Q, hQ0, hQ⟩ :=
      exists_norm_iteratedFDeriv_inv_fderiv_apply_le hΦ hw hτ hlow hhigh (n + 1)
    refine ⟨2 ^ (n + 1) * Q * C, by positivity, fun i j hj y ↦ ?_⟩
    have ha := fderiv_apply_ne_zero_of_le_abs hτ hlow i
    obtain ⟨hk, hks⟩ := contDiff_amplitude hφ (hΦ i) ha k
    have hac := (hΦ i).ofReal_fderiv_apply (m := ∞) (by simp) (w i)
    have hs : IsOpen {z | ((fderiv ℝ (Φ i) z (w i) : ℝ) : ℂ) ≠ 0} :=
      isOpen_ne_fun hac.continuous continuous_const
    have hm : minSmoothness ℝ (j + 1) ≤ (∞ : WithTop ℕ∞) := by simp
    have hτi := hτ i
    calc ‖iteratedFDeriv ℝ j (amplitude (Φ i) (w i) φ (k + 1)) y‖
        ≤ ‖iteratedFDeriv ℝ (j + 1) (fun z ↦ ((fderiv ℝ (Φ i) z (w i) : ℝ) : ℂ)⁻¹ *
            amplitude (Φ i) (w i) φ k z) y‖ * ‖w i‖ :=
          ContDiff.norm_iteratedFDeriv_fderiv_apply_le
            (contDiff_inv_fderiv_apply_mul hk (hΦ i) fun x hx ↦ ha x (hks hx)) hm (w i) y
      _ ≤ 2 ^ (j + 1) * (Q / τ i) * (C / τ i ^ k) * 1 := by
          refine mul_le_mul ?_ (hw i) (norm_nonneg _) (by positivity)
          exact norm_iteratedFDeriv_mul_le_of_tsupport_subset hs (fun x hx ↦ by simpa using ha x hx)
            (hac.contDiffOn.inv fun z hz ↦ hz) hk hks (by exact_mod_cast le_top) (by positivity)
            (fun i' hi' x hx ↦ hQ i i' (by omega) x hx) (fun i' hi' x ↦ hC i i' (by omega) x) y
      _ = 2 ^ (j + 1) * Q * C / τ i ^ (k + 1) := by
          field_simp
          ring
      _ ≤ 2 ^ (n + 1) * Q * C / τ i ^ (k + 1) := by
          gcongr
          exact one_le_two

end NonstationaryPhase

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure]

namespace NonstationaryPhase

/-- **One integration by parts in a direction `w`.** If the derivative `DΦ(x) w` of the phase does
not vanish on the support of the amplitude `u`, then
`∫ u 𝐞(Φ) = -(2πi)⁻¹ ∫ D((DΦ · w)⁻¹ u) w 𝐞(Φ)`. -/
private theorem integral_mul_fourierChar_eq {u : E → ℂ} (hu : ContDiff ℝ ∞ u)
    (huc : HasCompactSupport u) {Φ : E → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {w : E}
    (ha : ∀ x ∈ tsupport u, fderiv ℝ Φ x w ≠ 0) :
    ∫ x, u x * 𝐞 (Φ x) ∂μ =
      -(2 * π * I)⁻¹ * ∫ x, fderiv ℝ (fun z ↦ ((fderiv ℝ Φ z w : ℝ) : ℂ)⁻¹ * u z) x w *
        𝐞 (Φ x) ∂μ := by
  set a : E → ℂ := fun z ↦ ((fderiv ℝ Φ z w : ℝ) : ℂ)
  set f : E → ℂ := fun z ↦ (a z)⁻¹ * u z
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hf : ContDiff ℝ ∞ f := contDiff_inv_fderiv_apply_mul hu hΦ ha
  have hfs : tsupport f ⊆ tsupport u :=
    tsupport_mul_subset_right (f := fun z ↦ (a z)⁻¹) (g := u)
  have hfc : HasCompactSupport f := IsCompact.of_isClosed_subset huc (isClosed_tsupport f) hfs
  have hcont : Continuous fun y ↦ (𝐞 (Φ y) : ℂ) := by fun_prop
  -- On the support of `u`, `f * D(𝐞 Φ) w = 2πi u 𝐞(Φ)`.
  have hkey (x : E) : f x * fderiv ℝ (fun y ↦ (𝐞 (Φ y) : ℂ)) x w =
      2 * π * I * (u x * 𝐞 (Φ x)) := by
    rw [fderiv_fourierChar_comp_apply (hΦd x)]
    by_cases hx : x ∈ tsupport u
    · have hax : a x ≠ 0 := by simpa [a] using ha x hx
      simp only [f]
      field_simp
      simp [a, mul_comm]
    · simp [f, image_eq_zero_of_notMem_tsupport hx]
  have hsupp : Function.support (fun x ↦ fderiv ℝ f x w * 𝐞 (Φ x)) ⊆ tsupport f := fun x hx ↦ by
    by_contra h
    simp [fderiv_of_notMem_tsupport ℝ h] at hx
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ) (f := f)
    (g := fun y ↦ (𝐞 (Φ y) : ℂ)) (v := w)
    ((((hf.continuous_fderiv (by simp)).clm_apply continuous_const).mul hcont)
      |>.integrable_of_hasCompactSupport (hfc.mono' hsupp))
    (by
      simp_rw [hkey]
      exact (continuous_const.mul (hu.continuous.mul hcont)).integrable_of_hasCompactSupport
        huc.mul_right.mul_left)
    (((hf.continuous).mul hcont).integrable_of_hasCompactSupport hfc.mul_right)
    (fun x _ ↦ hf.differentiable (by simp) x)
    (fun x _ ↦ (hΦd x).hasFDerivAt.fourierChar.differentiableAt)
  simp_rw [hkey, integral_const_mul] at hibp
  have hc : (2 * π * I : ℂ) ≠ 0 := by simp [pi_ne_zero]
  rw [neg_mul, ← mul_neg, ← hibp, inv_mul_cancel_left₀ hc]

/-- Integrating `k` times by parts: `∫ φ 𝐞(Φ) = (-(2πi)⁻¹)ᵏ ∫ uₖ 𝐞(Φ)` for the `k`-th amplitude
`uₖ`, as long as `DΦ(x) w` does not vanish on the support of `φ`. -/
private theorem integral_mul_fourierChar_eq_pow_mul {φ : E → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) {Φ : E → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {w : E}
    (ha : ∀ x ∈ tsupport φ, fderiv ℝ Φ x w ≠ 0) (k : ℕ) :
    ∫ x, φ x * 𝐞 (Φ x) ∂μ =
      (-(2 * π * I)⁻¹) ^ k * ∫ x, amplitude Φ w φ k x * 𝐞 (Φ x) ∂μ := by
  induction k with
  | zero => simp [amplitude]
  | succ k ih =>
    obtain ⟨hk, hks⟩ := contDiff_amplitude hφ hΦ ha k
    rw [ih, integral_mul_fourierChar_eq hk
      (IsCompact.of_isClosed_subset hφc (isClosed_tsupport _) hks) hΦ fun x hx ↦ ha x (hks hx),
      pow_succ, mul_assoc ((-(2 * π * I)⁻¹) ^ k)]
    simp only [amplitude]

end NonstationaryPhase

open NonstationaryPhase in
/-- **Non-stationary phase.** Let `φ` be a smooth compactly supported amplitude on a
finite-dimensional real normed space, and let `Φᵢ` be a family of smooth real phases, `wᵢ`
directions with `‖wᵢ‖ ≤ 1` and `τᵢ > 0` scales such that on the support of `φ` the derivative of
`Φᵢ` in the direction `wᵢ` has size at least `τᵢ`, `|DΦᵢ(x) wᵢ| ≥ τᵢ`, while every derivative of
`Φᵢ` of positive order is `O(τᵢ)`, uniformly in `i`. Then the oscillatory integrals decay faster
than every power of `τᵢ`, uniformly in `i`:

`‖∫ φ(x) 𝐞(Φᵢ(x)) dx‖ ≤ C_N τᵢ^(-N)`.

Only derivatives in the single direction `wᵢ` are integrated by parts, so no lower bound on the
full gradient is needed beyond its component along `wᵢ`. -/
theorem exists_norm_integral_mul_fourierChar_le {ι : Type*} {φ : E → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) {Φ : ι → E → ℝ} (hΦ : ∀ i, ContDiff ℝ ∞ (Φ i)) {w : ι → E}
    (hw : ∀ i, ‖w i‖ ≤ 1) {τ : ι → ℝ} (hτ : ∀ i, 0 < τ i)
    (hlow : ∀ i, ∀ x ∈ tsupport φ, τ i ≤ |fderiv ℝ (Φ i) x (w i)|)
    (hhigh : ∀ k : ℕ, ∃ C, ∀ i, ∀ x ∈ tsupport φ, ‖iteratedFDeriv ℝ (k + 1) (Φ i) x‖ ≤ C * τ i)
    (N : ℕ) : ∃ C, ∀ i, ‖∫ x, φ x * 𝐞 (Φ i x) ∂μ‖ ≤ C / τ i ^ N := by
  obtain ⟨C, -, hC⟩ := exists_norm_iteratedFDeriv_amplitude_le hφ hφc hΦ hw hτ hlow hhigh N 0
  refine ⟨(2 * π)⁻¹ ^ N * (C * μ.real (tsupport φ)), fun i ↦ ?_⟩
  have ha := fderiv_apply_ne_zero_of_le_abs hτ hlow i
  obtain ⟨-, hNs⟩ := contDiff_amplitude hφ (hΦ i) ha N
  -- The `N`-th amplitude is `O(τᵢ⁻ᴺ)` and vanishes off the support of `φ`.
  have hint : ‖∫ x, amplitude (Φ i) (w i) φ N x * 𝐞 (Φ i x) ∂μ‖ ≤
      C / τ i ^ N * μ.real (tsupport φ) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hNs h), zero_mul]]
    refine norm_setIntegral_le_of_norm_le_const hφc.measure_lt_top fun x _ ↦ ?_
    rw [norm_mul, Circle.norm_coe, mul_one]
    simpa using hC i 0 le_rfl x
  have h2π : ‖-(2 * π * I : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
    simp [abs_of_pos pi_pos]
  rw [integral_mul_fourierChar_eq_pow_mul hφ hφc (hΦ i) ha N, norm_mul, norm_pow, h2π]
  calc (2 * π)⁻¹ ^ N * ‖∫ x, amplitude (Φ i) (w i) φ N x * 𝐞 (Φ i x) ∂μ‖
      ≤ (2 * π)⁻¹ ^ N * (C / τ i ^ N * μ.real (tsupport φ)) := by gcongr
    _ = (2 * π)⁻¹ ^ N * (C * μ.real (tsupport φ)) / τ i ^ N := by ring

end Directional

section ChangeOfVariables

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

namespace NonstationaryPhase

/-- Where `(Df(x))†` is within `c / 2` of `B` and `c (‖ξ‖ + ‖ζ‖) ≤ ‖B ζ - ξ‖`, the derivative of
the phase in the direction of `B ζ - ξ` is at least `c / 2 (‖ξ‖ + ‖ζ‖)`. -/
private theorem le_inner_adjoint_sub {A : E →L[ℝ] F} {B : F →L[ℝ] E} {c : ℝ}
    (hAB : ‖A† - B‖ ≤ c / 2) {ξ : E} {ζ : F} (hξζ : c * (‖ξ‖ + ‖ζ‖) ≤ ‖B ζ - ξ‖) :
    c / 2 * (‖ξ‖ + ‖ζ‖) ≤ ⟪‖B ζ - ξ‖⁻¹ • (B ζ - ξ), (A†) ζ - ξ⟫ := by
  set d := ‖B ζ - ξ‖ with hd_def
  have hsplit : (A†) ζ - ξ = (B ζ - ξ) + (A† - B) ζ := by
    simp only [sub_apply]
    abel
  have h1 : ⟪d⁻¹ • (B ζ - ξ), B ζ - ξ⟫ = d := by
    rcases eq_or_ne d 0 with hd | hd
    · simp [hd, norm_eq_zero.1 hd]
    · rw [real_inner_smul_left, real_inner_self_eq_norm_sq, ← hd_def]
      field_simp
  have h2 : -(c / 2 * ‖ζ‖) ≤ ⟪d⁻¹ • (B ζ - ξ), (A† - B) ζ⟫ := by
    have hw : ‖d⁻¹ • (B ζ - ξ)‖ ≤ 1 := by
      rw [norm_smul, norm_inv, norm_norm]
      exact inv_mul_le_one
    refine neg_le_of_abs_le ((abs_real_inner_le_norm _ _).trans ?_)
    calc ‖d⁻¹ • (B ζ - ξ)‖ * ‖(A† - B) ζ‖ ≤ 1 * (c / 2 * ‖ζ‖) :=
          mul_le_mul hw (((A† - B).le_opNorm ζ).trans (by gcongr)) (norm_nonneg _) zero_le_one
      _ = c / 2 * ‖ζ‖ := one_mul _
  have hc : 0 ≤ c := by linarith [(norm_nonneg _).trans hAB]
  rw [hsplit, inner_add_right, h1]
  nlinarith [mul_nonneg hc (norm_nonneg ξ)]

end NonstationaryPhase

variable [MeasurableSpace E] [BorelSpace E]

namespace NonstationaryPhase

/-- The non-stationary phase estimate for the phases `⟪f x, ζ⟫ - ⟪x, ξ⟫` on the frequencies with
`c (‖ξ‖ + ‖ζ‖) ≤ ‖B ζ - ξ‖` and `1 ≤ ‖ξ‖ + ‖ζ‖`, integrating by parts in the direction of
`B ζ - ξ`. -/
private theorem exists_norm_integral_mul_fourierChar_inner_sub_le_div {f : E → F}
    (hf : ContDiff ℝ ∞ f) {φ : E → ℂ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    {B : F →L[ℝ] E} {c : ℝ} (hc : 0 < c)
    (hfB : ∀ x ∈ tsupport φ, ‖(fderiv ℝ f x)† - B‖ ≤ c / 2) (N : ℕ) :
    ∃ C, ∀ (ξ : E) (ζ : F), c * (‖ξ‖ + ‖ζ‖) ≤ ‖B ζ - ξ‖ → 1 ≤ ‖ξ‖ + ‖ζ‖ →
      ‖∫ x, φ x * 𝐞 (⟪f x, ζ⟫ - ⟪x, ξ⟫)‖ ≤ C / (c / 2 * (‖ξ‖ + ‖ζ‖)) ^ N := by
  set S := {p : E × F // c * (‖p.1‖ + ‖p.2‖) ≤ ‖B p.2 - p.1‖ ∧ 1 ≤ ‖p.1‖ + ‖p.2‖}
  have hsum (p : S) : 0 < ‖p.1.1‖ + ‖p.1.2‖ := one_pos.trans_le p.2.2
  have hf' : Differentiable ℝ f := hf.differentiable (by simp)
  have hM (k : ℕ) : ∃ M, 0 ≤ M ∧ ∀ x ∈ tsupport φ, ‖iteratedFDeriv ℝ (k + 1) f x‖ ≤ M := by
    obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuousOn
      (hf.continuous_iteratedFDeriv (m := k + 1) (by exact_mod_cast le_top)).continuousOn
    exact ⟨max M 0, le_max_right _ _, fun x hx ↦ (hM x hx).trans (le_max_left _ _)⟩
  choose M hM0 hM using hM
  obtain ⟨C₁, hC₁⟩ := exists_norm_integral_mul_fourierChar_le (μ := (volume : Measure E)) hφ hφc
    (Φ := fun (p : S) y ↦ ⟪f y, p.1.2⟫ - ⟪y, p.1.1⟫)
    (fun p ↦ (hf.inner ℝ contDiff_const).sub (contDiff_id.inner ℝ contDiff_const))
    (w := fun p ↦ ‖B p.1.2 - p.1.1‖⁻¹ • (B p.1.2 - p.1.1))
    (fun p ↦ by rw [norm_smul, norm_inv, norm_norm]; exact inv_mul_le_one)
    (τ := fun p ↦ c / 2 * (‖p.1.1‖ + ‖p.1.2‖)) (fun p ↦ by have := hsum p; positivity)
    (fun p x hx ↦ by
      rw [fderiv_inner_sub_inner_apply (hf' x)]
      exact (le_inner_adjoint_sub (hfB x hx) p.2.1).trans (le_abs_self _))
    (fun k ↦ ⟨2 / c * (M k + 1), fun p x hx ↦ by
      refine (norm_iteratedFDeriv_succ_inner_sub_inner_le
        (hf.contDiffAt.of_le (by exact_mod_cast le_top)) _ _).trans ?_
      have h := hM k x hx
      have := hM0 k
      rw [show 2 / c * (M k + 1) * (c / 2 * (‖p.1.1‖ + ‖p.1.2‖)) =
        (M k + 1) * (‖p.1.1‖ + ‖p.1.2‖) by field_simp]
      nlinarith [norm_nonneg p.1.1, norm_nonneg p.1.2, norm_nonneg (iteratedFDeriv ℝ (k + 1) f x)]⟩)
    N
  exact ⟨C₁, fun ξ ζ hξζ h1 ↦ hC₁ ⟨(ξ, ζ), hξζ, h1⟩⟩

end NonstationaryPhase

open NonstationaryPhase in
/-- **Non-stationary phase for changes of variables in a Fourier integral.** Let `f` be smooth, `φ`
a smooth compactly supported amplitude, and `B` a linear map within `c / 2` of the transposes
`(Df(x))†` of the derivatives of `f` on the support of `φ`, for some `c > 0`. Then the oscillatory
integral with phase `⟪f x, ζ⟫ - ⟪x, ξ⟫` decays faster than every power of `‖ξ‖ + ‖ζ‖` on the
frequencies `(ξ, ζ)` with `c (‖ξ‖ + ‖ζ‖) ≤ ‖B ζ - ξ‖`, where its gradient `(Df(x))† ζ - ξ` stays
away from zero:

`‖∫ φ(x) 𝐞(⟪f x, ζ⟫ - ⟪x, ξ⟫) dx‖ ≤ C_N (1 + ‖ξ‖ + ‖ζ‖)^(-N)`. -/
theorem exists_norm_integral_mul_fourierChar_inner_sub_le {f : E → F} (hf : ContDiff ℝ ∞ f)
    {φ : E → ℂ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) {B : F →L[ℝ] E} {c : ℝ}
    (hc : 0 < c) (hfB : ∀ x ∈ tsupport φ, ‖(fderiv ℝ f x)† - B‖ ≤ c / 2) (N : ℕ) :
    ∃ C, ∀ (ξ : E) (ζ : F), c * (‖ξ‖ + ‖ζ‖) ≤ ‖B ζ - ξ‖ →
      ‖∫ x, φ x * 𝐞 (⟪f x, ζ⟫ - ⟪x, ξ⟫)‖ ≤ C / (1 + ‖ξ‖ + ‖ζ‖) ^ N := by
  obtain ⟨C₁, hC₁⟩ := exists_norm_integral_mul_fourierChar_inner_sub_le_div hf hφ hφc hc hfB N
  refine ⟨max (C₁ * (4 / c) ^ N) ((∫ x, ‖φ x‖) * 2 ^ N), fun ξ ζ hξζ ↦ ?_⟩
  rw [le_div_iff₀ (by positivity)]
  by_cases h1 : 1 ≤ ‖ξ‖ + ‖ζ‖
  · -- Away from the origin, `1 + ‖ξ‖ + ‖ζ‖ ≤ 2 (‖ξ‖ + ‖ζ‖)`.
    have h := hC₁ ξ ζ hξζ h1
    have hτ : 0 < c / 2 * (‖ξ‖ + ‖ζ‖) := by positivity
    have hle : (1 + ‖ξ‖ + ‖ζ‖) ^ N ≤ (4 / c) ^ N * (c / 2 * (‖ξ‖ + ‖ζ‖)) ^ N := by
      rw [← mul_pow]
      gcongr
      have h2 : 4 / c * (c / 2 * (‖ξ‖ + ‖ζ‖)) = 2 * (‖ξ‖ + ‖ζ‖) := by
        field_simp
        ring
      rw [h2]
      linarith
    calc ‖∫ x, φ x * 𝐞 (⟪f x, ζ⟫ - ⟪x, ξ⟫)‖ * (1 + ‖ξ‖ + ‖ζ‖) ^ N
        ≤ C₁ / (c / 2 * (‖ξ‖ + ‖ζ‖)) ^ N * ((4 / c) ^ N * (c / 2 * (‖ξ‖ + ‖ζ‖)) ^ N) :=
          mul_le_mul h hle (by positivity) ((norm_nonneg _).trans h)
      _ = C₁ * (4 / c) ^ N := by
          rw [mul_left_comm, div_mul_cancel₀ _ (pow_ne_zero N hτ.ne'), mul_comm]
      _ ≤ _ := le_max_left _ _
  · -- Near the origin, `‖∫ φ 𝐞(…)‖ ≤ ∫ ‖φ‖` and `1 + ‖ξ‖ + ‖ζ‖ ≤ 2`.
    have htriv : ‖∫ x, φ x * 𝐞 (⟪f x, ζ⟫ - ⟪x, ξ⟫)‖ ≤ ∫ x, ‖φ x‖ :=
      (norm_integral_le_integral_norm _).trans_eq (by simp)
    calc ‖∫ x, φ x * 𝐞 (⟪f x, ζ⟫ - ⟪x, ξ⟫)‖ * (1 + ‖ξ‖ + ‖ζ‖) ^ N
        ≤ (∫ x, ‖φ x‖) * 2 ^ N := by
          gcongr
          linarith
      _ ≤ _ := le_max_right _ _

end ChangeOfVariables

end TauCeti
