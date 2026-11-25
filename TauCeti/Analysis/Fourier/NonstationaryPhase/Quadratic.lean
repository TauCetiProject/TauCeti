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
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Non-stationary phase for quadratic phases on the line

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

## Main declarations

* `TauCeti.exists_norm_integral_cexp_mul_le_of_mul_abs_le`: decay at the rate `|t|^(-N)` of the
  oscillatory integral with phase `t r - s r²` and a `C^N` amplitude, in the non-stationary regime
  `t ≠ 0`, `4 R |s| ≤ |t|`.

## References

* E. M. Stein, *Harmonic Analysis: Real-Variable Methods, Orthogonality, and Oscillatory
  Integrals*, Chapter VIII, §1.
-/

public section

noncomputable section

open MeasureTheory Set Filter Complex Real
open scoped Topology ContDiff

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

end TauCeti
