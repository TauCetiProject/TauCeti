/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.JacobianOneDim
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Order.Monotone.Basic
import TauCeti.Topology.Order.Interval

/-!
# Bleistein's change of variables for coalescing critical points

For Laplace-type integrals
`I(α, x) = ∫ t in (0, k), exp (-x * p(α, t)) • t ^ (λ - 1) • q(α, t) dt`
with `λ > 0` and an interior or endpoint minimum `t = α` of `p(α, ·)` that may coalesce with the
algebraic singularity at `t = 0`, separate expansions for `α > 0`, `α = 0`, and `α < 0` fail to be
uniform in `α` near `0`. Bleistein's method replaces `t` by a coordinate `w = bleisteinW (p α) α t`
in which the phase becomes the exact quadratic `w ^ 2 / 2 - a(α) * w + p(α, 0)` while `t = 0` stays
mapped to `w = 0` and `t = α` maps to `w = a(α) = bleisteinA (p α) α`.

This file defines `bleisteinA`, `bleisteinW`, and the transformed amplitude `bleisteinAmplitude`
(valued in any type with an `ℝ`-action for its algebraic API, and in a real normed space `E` for
integration). At `w = 0`, the removable `0 / 0` singularity of `t(w) / w` is resolved by
`(deriv (bleisteinW p α) 0)⁻¹`: under the open-domain, `C¹`-coordinate, strict-monotonicity,
positive-derivative, and amplitude-continuity hypotheses of
`TauCeti.continuousOn_bleisteinAmplitude_of_zero_mem`, `bleisteinAmplitude` is continuous across
`w = 0` and `w = bleisteinA p α` for all `α` (`α < 0`, `α = 0`, and `α > 0`), as well as on
positive domains (`TauCeti.continuousOn_bleisteinAmplitude`,
`TauCeti.continuousOn_bleisteinAmplitude_of_injOn`). The file establishes the exact quadratic phase
identity, continuity, strict monotonicity, and `C¹` regularity of `bleisteinW` across `t = α`,
characterizations of the upper integration limit `κ(α) = lim_{t → k} w(α, t)` (with an explicit
bounded-phase counterexample showing that `k = ∞` alone does not force `κ = ∞`), and the
one-dimensional change-of-variables formulas for both integrability and the Bochner integral.

## Main definitions

* `TauCeti.bleisteinA`: the transformed critical point
  `sgn(α) * √(2 * (p 0 - p α))` (DLMF 2.3.26).
* `TauCeti.bleisteinW`: Bleistein's coordinate
  `bleisteinA p α + sgn(t - α) * √(2 * (p t - p α))` (DLMF 2.3.25).
* `TauCeti.bleisteinAmplitude`: the transformed amplitude of DLMF 2.3.30, desingularized at
  `w = 0` by `(deriv (bleisteinW p α) 0)⁻¹`.

## Main results

* `TauCeti.bleistein_phase_eq`: `bleisteinW p α t ^ 2 / 2 - bleisteinA p α * bleisteinW p α t + p 0
  = p t` whenever `p α ≤ p 0` and `p α ≤ p t`.
* `TauCeti.continuousWithinAt_bleisteinW`, `TauCeti.strictMonoOn_bleisteinW`, and
  `TauCeti.contDiffOn_bleisteinW`: `bleisteinW p α` is continuous wherever `p` is continuous,
  strictly increasing under strict monotonicity away from `α`, and `C¹` across `t = α` for `C¹`
  phases with a strict minimum at `α` and `0 < deriv (deriv p) α`, with derivative
  `√(deriv (deriv p) α)` at `t = α` (`TauCeti.hasDerivAt_bleisteinW_self`) and derivative
  `(deriv p t) / (w - a)` away from `α` (`TauCeti.deriv_bleisteinW_of_ne`, DLMF 2.3.28).
* `TauCeti.deriv_bleisteinW_pos`, `TauCeti.deriv_bleisteinW_pos_of_differentiableOn`: positivity
  of `w'` when `α` is the only critical point of `p`.
* `TauCeti.bleisteinAmplitude_congr_set`, `TauCeti.bleisteinAmplitude_bleisteinA`,
  `TauCeti.bleisteinAmplitude_self`, `TauCeti.bleisteinAmplitude_self_zero`,
  `TauCeti.bleisteinAmplitude_bleisteinA_ne_zero`, and `TauCeti.bleisteinAmplitude_self_ne_zero`:
  domain invariance, evaluation, and nonvanishing of `bleisteinAmplitude` at `w = bleisteinA p α`
  across `α < 0`, `α = 0`, and `α > 0`.
* `TauCeti.hasStrictDerivAt_invFunOn_bleisteinW`,
  `TauCeti.bleisteinAmplitude_eq_mul_deriv_invFunOn_smul`, `TauCeti.bleisteinAmplitude_eq_dslope`,
  `TauCeti.continuousOn_bleisteinAmplitude_of_zero_mem`,
  `TauCeti.continuousOn_bleisteinAmplitude`, and `TauCeti.continuousOn_bleisteinAmplitude_of_injOn`:
  strict differentiability of the inverse coordinate, the DLMF 2.3.30 and `dslope` forms of the
  transformed amplitude, and its continuity across `w = 0` and on positive domains.
* `TauCeti.integrableOn_bleistein_iff_of_deriv_pos`, `TauCeti.exp_smul_integral_bleistein_eq`,
  `TauCeti.integral_bleistein_eq_of_deriv_pos`, `TauCeti.integrableOn_bleistein_iff`, and
  `TauCeti.integral_bleistein_eq`: equivalence of integrability and equality of the original and
  transformed integrals (DLMF 2.3.24, 2.3.29), together with interval specializations on `(0, k)`
  and `(0, ∞)`.

## References

* NIST *Digital Library of Mathematical Functions*, §2.3(v), formulas 2.3.24–2.3.30,
  <https://dlmf.nist.gov/2.3#v>.
* N. Bleistein, *Uniform asymptotic expansions of integrals with stationary point near algebraic
  singularity*, Comm. Pure Appl. Math. 19 (1966), 353–370.
* N. Bleistein and R. A. Handelsman, *Asymptotic Expansions of Integrals*, Holt, Rinehart and
  Winston, 1975; reprinted Dover, 1986. Chapter 9, §9.4.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 9, §9.
* R. Wong, *Asymptotic Approximations of Integrals*, Academic Press, 1989; reprinted SIAM, 2001.
  Chapter 7, §2.
-/

public section

open Filter Function MeasureTheory Set
open scoped Topology ContDiff

namespace TauCeti

/-! ### Coordinate definitions and algebraic identities -/

/-- The transformed critical point `a(α) = sgn(α) * √(2 * (p 0 - p α))` of Bleistein's change of
variables (DLMF 2.3.26), with `sgn 0 = 0`. -/
noncomputable def bleisteinA (p : ℝ → ℝ) (α : ℝ) : ℝ :=
  SignType.sign α * Real.sqrt (2 * (p 0 - p α))

/-- Unfolding `TauCeti.bleisteinA`. -/
theorem bleisteinA_def (p : ℝ → ℝ) (α : ℝ) :
    bleisteinA p α = SignType.sign α * Real.sqrt (2 * (p 0 - p α)) :=
  (rfl)

/-- Bleistein's coordinate `w(α, t) = a(α) + sgn(t - α) * √(2 * (p t - p α))` turning `p t` into
the quadratic `w ^ 2 / 2 - a(α) * w + p 0` while keeping `w(α, 0) = 0` (DLMF 2.3.25). -/
noncomputable def bleisteinW (p : ℝ → ℝ) (α t : ℝ) : ℝ :=
  bleisteinA p α + SignType.sign (t - α) * Real.sqrt (2 * (p t - p α))

/-- Unfolding `TauCeti.bleisteinW`. -/
theorem bleisteinW_def (p : ℝ → ℝ) (α t : ℝ) :
    bleisteinW p α t = bleisteinA p α + SignType.sign (t - α) * Real.sqrt (2 * (p t - p α)) :=
  (rfl)

/-- At `α = 0`, the transformed critical point `bleisteinA p 0` vanishes. -/
@[simp]
theorem bleisteinA_zero (p : ℝ → ℝ) : bleisteinA p 0 = 0 := by
  simp [bleisteinA]

/-- Bleistein's coordinate fixes the origin: `bleisteinW p α 0 = 0` for every `α` (DLMF 2.3.27). -/
@[simp]
theorem bleisteinW_zero (p : ℝ → ℝ) (α : ℝ) : bleisteinW p α 0 = 0 := by
  rcases lt_trichotomy α 0 with hα | rfl | hα
  · simp [bleisteinW, bleisteinA, sign_neg hα, sign_pos (neg_pos.mpr hα)]
  · simp [bleisteinW]
  · simp [bleisteinW, bleisteinA, sign_pos hα, sign_neg (neg_lt_zero.mpr hα)]

/-- Bleistein's coordinate maps `t = α` to `bleisteinA p α` (DLMF 2.3.27). -/
@[simp]
theorem bleisteinW_self (p : ℝ → ℝ) (α : ℝ) : bleisteinW p α α = bleisteinA p α := by
  simp [bleisteinW]

/-- Magnitude `|bleisteinA p α| = √(2 * (p 0 - p α))` for every `α` (DLMF 2.3.26). -/
@[simp]
theorem abs_bleisteinA (p : ℝ → ℝ) (α : ℝ) :
    |bleisteinA p α| = Real.sqrt (2 * (p 0 - p α)) := by
  rcases lt_trichotomy α 0 with hα | rfl | hα
  · simp [bleisteinA, sign_neg hα, abs_of_nonneg (Real.sqrt_nonneg _)]
  · simp [bleisteinA]
  · simp [bleisteinA, sign_pos hα, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- Formula for `bleisteinA p α` when `0 < α`. -/
theorem bleisteinA_of_pos {p : ℝ → ℝ} {α : ℝ} (hα : 0 < α) :
    bleisteinA p α = Real.sqrt (2 * (p 0 - p α)) := by
  rw [bleisteinA, sign_pos hα, SignType.coe_one, one_mul]

/-- Formula for `bleisteinA p α` when `α < 0`. -/
theorem bleisteinA_of_neg {p : ℝ → ℝ} {α : ℝ} (hα : α < 0) :
    bleisteinA p α = -Real.sqrt (2 * (p 0 - p α)) := by
  rw [bleisteinA, sign_neg hα, SignType.coe_neg_one, neg_one_mul]

/-- When `0 < α` and `p α < p 0`, `bleisteinA p α` is strictly positive. -/
theorem bleisteinA_pos {p : ℝ → ℝ} {α : ℝ} (hα : 0 < α) (hp : p α < p 0) :
    0 < bleisteinA p α := by
  rw [bleisteinA, sign_pos hα, SignType.coe_one, one_mul]
  exact Real.sqrt_pos.mpr (by linarith)

/-- When `α < 0` and `p α < p 0`, `bleisteinA p α` is strictly negative. -/
theorem bleisteinA_neg {p : ℝ → ℝ} {α : ℝ} (hα : α < 0) (hp : p α < p 0) :
    bleisteinA p α < 0 := by
  rw [bleisteinA, sign_neg hα, SignType.coe_neg_one, neg_one_mul, neg_lt_zero]
  exact Real.sqrt_pos.mpr (by linarith)

/-- When `p α < p 0`, `bleisteinA p α` is nonzero. -/
theorem bleisteinA_ne_zero {p : ℝ → ℝ} {α : ℝ} (hp : p α < p 0) :
    bleisteinA p α ≠ 0 :=
  abs_pos.mp <| by rw [abs_bleisteinA]; exact Real.sqrt_pos.mpr (by linarith)

/-- When `p α < p 0`, `bleisteinA p α` has the same sign as `α` (DLMF 2.3.26). -/
theorem sign_bleisteinA {p : ℝ → ℝ} {α : ℝ} (hp : p α < p 0) :
    SignType.sign (bleisteinA p α) = SignType.sign α := by
  rcases lt_trichotomy α 0 with hα | rfl | hα
  · rw [sign_neg (bleisteinA_neg hα hp), sign_neg hα]
  · simp
  · rw [sign_pos (bleisteinA_pos hα hp), sign_pos hα]

/-- Displacement of `bleisteinW p α t` from the transformed critical point `bleisteinA p α`. -/
theorem bleisteinW_sub_bleisteinA (p : ℝ → ℝ) (α t : ℝ) :
    bleisteinW p α t - bleisteinA p α =
      SignType.sign (t - α) * Real.sqrt (2 * (p t - p α)) :=
  add_sub_cancel_left _ _

/-- Displacement `bleisteinW p α t - bleisteinA p α = √(2 * (p t - p α))` when `α < t`. -/
theorem bleisteinW_sub_bleisteinA_of_gt {p : ℝ → ℝ} {α t : ℝ} (ht : α < t) :
    bleisteinW p α t - bleisteinA p α = Real.sqrt (2 * (p t - p α)) := by
  rw [bleisteinW_sub_bleisteinA, sign_pos (sub_pos.mpr ht), SignType.coe_one, one_mul]

/-- Displacement `bleisteinW p α t - bleisteinA p α = -√(2 * (p t - p α))` when `t < α`. -/
theorem bleisteinW_sub_bleisteinA_of_lt {p : ℝ → ℝ} {α t : ℝ} (ht : t < α) :
    bleisteinW p α t - bleisteinA p α = -Real.sqrt (2 * (p t - p α)) := by
  rw [bleisteinW_sub_bleisteinA, sign_neg (sub_neg.mpr ht), SignType.coe_neg_one, neg_one_mul]

/-- Square of `bleisteinA p α` when `p α ≤ p 0` (DLMF 2.3.26). -/
theorem sq_bleisteinA {p : ℝ → ℝ} {α : ℝ} (h0 : p α ≤ p 0) :
    bleisteinA p α ^ 2 = 2 * (p 0 - p α) := by
  rcases lt_trichotomy α 0 with hα | rfl | hα
  · rw [bleisteinA, sign_neg hα, SignType.coe_neg_one, neg_one_mul, neg_sq,
      Real.sq_sqrt (by linarith)]
  · simp
  · rw [bleisteinA, sign_pos hα, SignType.coe_one, one_mul, Real.sq_sqrt (by linarith)]

/-- Squared displacement `(bleisteinW p α t - bleisteinA p α) ^ 2 = 2 * (p t - p α)` when
`p α ≤ p t` (DLMF 2.3.25). -/
theorem sq_bleisteinW_sub_bleisteinA {p : ℝ → ℝ} {α t : ℝ} (ht : p α ≤ p t) :
    (bleisteinW p α t - bleisteinA p α) ^ 2 = 2 * (p t - p α) := by
  rw [bleisteinW_sub_bleisteinA]
  rcases lt_trichotomy (t - α) 0 with h | h | h
  · rw [sign_neg h, SignType.coe_neg_one, neg_one_mul, neg_sq, Real.sq_sqrt (by linarith)]
  · rw [sub_eq_zero.mp h]
    simp
  · rw [sign_pos h, SignType.coe_one, one_mul, Real.sq_sqrt (by linarith)]

/-- Quadratic phase identity of Bleistein's change of variables (DLMF 2.3.25). -/
theorem bleistein_phase_eq {p : ℝ → ℝ} {α t : ℝ} (h0 : p α ≤ p 0) (ht : p α ≤ p t) :
    bleisteinW p α t ^ 2 / 2 - bleisteinA p α * bleisteinW p α t + p 0 = p t := by
  have h1 := sq_bleisteinA h0
  have h2 := sq_bleisteinW_sub_bleisteinA ht
  have hsq : (bleisteinW p α t - bleisteinA p α) ^ 2 =
      bleisteinW p α t ^ 2 - 2 * (bleisteinA p α * bleisteinW p α t) + bleisteinA p α ^ 2 := by
    ring
  linarith [h1, h2, hsq]

/-- Subtracted form `w ^ 2 / 2 - a * w = p t - p 0` of Bleistein's phase identity (DLMF 2.3.25). -/
theorem bleistein_phase_sub_eq {p : ℝ → ℝ} {α t : ℝ} (h0 : p α ≤ p 0) (ht : p α ≤ p t) :
    bleisteinW p α t ^ 2 / 2 - bleisteinA p α * bleisteinW p α t = p t - p 0 := by
  linarith [bleistein_phase_eq h0 ht]

/-- Whenever `p α < p t`, `bleisteinW p α t` is distinct from `bleisteinA p α`. -/
theorem bleisteinW_sub_bleisteinA_ne_zero {p : ℝ → ℝ} {α t : ℝ} (ht : p α < p t) :
    bleisteinW p α t - bleisteinA p α ≠ 0 := by
  intro h
  have hsq : (bleisteinW p α t - bleisteinA p α) ^ 2 = 0 := by rw [h, sq, mul_zero]
  linarith [sq_bleisteinW_sub_bleisteinA ht.le]

/-! ### Continuity and strict monotonicity -/

/-- Bleistein's coordinate `bleisteinW p α` is continuous within `s` at `t` whenever `p` is. -/
theorem continuousWithinAt_bleisteinW {p : ℝ → ℝ} {s : Set ℝ} {t : ℝ}
    (hp : ContinuousWithinAt p s t) (α : ℝ) :
    ContinuousWithinAt (bleisteinW p α) s t := by
  rcases eq_or_ne t α with rfl | hne
  · rw [ContinuousWithinAt, bleisteinW_self]
    have h0 : Tendsto (fun u => (SignType.sign (u - t) : ℝ) * Real.sqrt (2 * (p u - p t)))
        (𝓝[s] t) (𝓝 0) := by
      refine squeeze_zero_norm (a := fun u => Real.sqrt (2 * (p u - p t))) (fun u => ?_) ?_
      · rw [norm_mul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        have hs : ‖(SignType.sign (u - t) : ℝ)‖ ≤ 1 := by
          rcases lt_trichotomy (u - t) 0 with h | h | h
          · simp [sign_neg h]
          · simp [h]
          · simp [sign_pos h]
        exact mul_le_of_le_one_left (Real.sqrt_nonneg _) hs
      · have hp0 : Tendsto (fun u => 2 * (p u - p t)) (𝓝[s] t) (𝓝 0) := by
          simpa using (hp.tendsto.sub_const (p t)).const_mul 2
        have hsq := (Real.continuous_sqrt.tendsto 0).comp hp0
        rwa [Real.sqrt_zero] at hsq
    have hsum := (tendsto_const_nhds (x := bleisteinA p t)).add h0
    rwa [add_zero] at hsum
  · let c : ℝ := SignType.sign (t - α)
    have hs_ev : ∀ᶠ u in 𝓝 t, (SignType.sign (u - α) : ℝ) = c := by
      rcases hne.lt_or_gt with hlt | hgt
      · filter_upwards [Iio_mem_nhds hlt] with u hu
        simp [c, sign_neg (sub_neg.mpr hu), sign_neg (sub_neg.mpr hlt)]
      · filter_upwards [Ioi_mem_nhds hgt] with u hu
        simp [c, sign_pos (sub_pos.mpr hu), sign_pos (sub_pos.mpr hgt)]
    have hc_ev : (fun u => bleisteinA p α + c * Real.sqrt (2 * (p u - p α))) =ᶠ[𝓝[s] t]
        bleisteinW p α :=
      (eventually_nhdsWithin_of_eventually_nhds hs_ev).mono fun u hu => by rw [bleisteinW, hu]
    have hsqrt : ContinuousWithinAt (fun u => Real.sqrt (2 * (p u - p α))) s t :=
      Real.continuous_sqrt.continuousAt.comp_continuousWithinAt
        ((hp.sub continuousWithinAt_const).const_mul 2)
    exact (continuousWithinAt_const.add (hsqrt.const_mul c)).congr_of_eventuallyEq
      hc_ev.symm (by simp [bleisteinW, c])

/-- Bleistein's coordinate `bleisteinW p α` is continuous on any set `s` where `p` is
continuous. -/
theorem continuousOn_bleisteinW {p : ℝ → ℝ} {s : Set ℝ} (hp : ContinuousOn p s) (α : ℝ) :
    ContinuousOn (bleisteinW p α) s :=
  fun t ht => continuousWithinAt_bleisteinW (hp t ht) α

/-- Bleistein's coordinate `bleisteinW p α` is strictly increasing on `I` whenever `p` is strictly
decreasing on `I ∩ (-∞, α]` and strictly increasing on `I ∩ [α, ∞)`. -/
theorem strictMonoOn_bleisteinW {p : ℝ → ℝ} {I : Set ℝ} {α : ℝ} (hα : α ∈ I)
    (hanti : StrictAntiOn p (I ∩ Iic α)) (hmono : StrictMonoOn p (I ∩ Ici α)) :
    StrictMonoOn (bleisteinW p α) I := by
  intro t₁ ht₁ t₂ ht₂ hlt
  simp only [bleisteinW, add_lt_add_iff_left]
  have neg_val : ∀ u < α,
      SignType.sign (u - α) * Real.sqrt (2 * (p u - p α)) = -Real.sqrt (2 * (p u - p α)) :=
    fun u hu => by rw [sign_neg (sub_neg.mpr hu), SignType.coe_neg_one, neg_one_mul]
  have pos_val : ∀ u, α < u →
      SignType.sign (u - α) * Real.sqrt (2 * (p u - p α)) = Real.sqrt (2 * (p u - p α)) :=
    fun u hu => by rw [sign_pos (sub_pos.mpr hu), SignType.coe_one, one_mul]
  rcases lt_trichotomy t₁ α with h₁ | rfl | h₁
  · rw [neg_val t₁ h₁]
    have hp₁ : 0 < 2 * (p t₁ - p α) := by linarith [hanti ⟨ht₁, h₁.le⟩ ⟨hα, le_rfl⟩ h₁]
    rcases lt_trichotomy t₂ α with h₂ | rfl | h₂
    · rw [neg_val t₂ h₂, neg_lt_neg_iff]
      have hp₂ : 0 < 2 * (p t₂ - p α) := by linarith [hanti ⟨ht₂, h₂.le⟩ ⟨hα, le_rfl⟩ h₂]
      have h12 : p t₂ < p t₁ := hanti ⟨ht₁, h₁.le⟩ ⟨ht₂, h₂.le⟩ hlt
      exact Real.sqrt_lt_sqrt hp₂.le (by linarith)
    · rw [sub_self, sign_zero, SignType.coe_zero, zero_mul, neg_lt_zero]
      exact Real.sqrt_pos.mpr hp₁
    · rw [pos_val t₂ h₂]
      have hp₂ : 0 < 2 * (p t₂ - p α) := by linarith [hmono ⟨hα, le_rfl⟩ ⟨ht₂, h₂.le⟩ h₂]
      linarith [Real.sqrt_pos.mpr hp₁, Real.sqrt_pos.mpr hp₂]
  · rw [sub_self, sign_zero, SignType.coe_zero, zero_mul, pos_val t₂ hlt]
    exact Real.sqrt_pos.mpr (by linarith [hmono ⟨hα, le_rfl⟩ ⟨ht₂, hlt.le⟩ hlt])
  · have h₂ : α < t₂ := h₁.trans hlt
    rw [pos_val t₁ h₁, pos_val t₂ h₂]
    have hp₁ : 0 < 2 * (p t₁ - p α) := by linarith [hmono ⟨hα, le_rfl⟩ ⟨ht₁, h₁.le⟩ h₁]
    have h12 : p t₁ < p t₂ := hmono ⟨ht₁, h₁.le⟩ ⟨ht₂, h₂.le⟩ hlt
    exact Real.sqrt_lt_sqrt hp₁.le (by linarith)

/-- Positivity of `bleisteinW p α t` for `0 < t` under the monotonicity hypotheses of
`TauCeti.strictMonoOn_bleisteinW` when `0 ∈ I`. -/
theorem bleisteinW_pos {p : ℝ → ℝ} {I : Set ℝ} {α t : ℝ} (hα : α ∈ I) (h0 : 0 ∈ I)
    (hanti : StrictAntiOn p (I ∩ Iic α)) (hmono : StrictMonoOn p (I ∩ Ici α)) (ht : t ∈ I)
    (ht0 : 0 < t) :
    0 < bleisteinW p α t := by
  simpa [bleisteinW_zero] using strictMonoOn_bleisteinW hα hanti hmono h0 ht ht0

/-! ### Differentiability, `C¹` smoothness across the critical point, and positivity of `w'` -/

/-- Away from the critical point `t = α` (where `p α < p t`), `bleisteinW p α` is differentiable
whenever `p` is, with derivative `p' / (bleisteinW p α t - bleisteinA p α)` (DLMF 2.3.28). -/
theorem hasDerivAt_bleisteinW_of_ne {p : ℝ → ℝ} {α t p' : ℝ} (hpt : p α < p t)
    (hp : HasDerivAt p p' t) :
    HasDerivAt (bleisteinW p α) (p' / (bleisteinW p α t - bleisteinA p α)) t := by
  have hne : t ≠ α := by
    rintro rfl
    exact lt_irrefl _ hpt
  have hpos : 0 < 2 * (p t - p α) := by linarith
  have hsqrt : HasDerivAt (fun u => Real.sqrt (2 * (p u - p α)))
      (2 * p' / (2 * Real.sqrt (2 * (p t - p α)))) t :=
    ((hp.sub_const (p α)).const_mul 2).sqrt hpos.ne'
  let s : ℝ := SignType.sign (t - α)
  have hs_ev : ∀ᶠ u in 𝓝 t, (SignType.sign (u - α) : ℝ) = s := by
    rcases hne.lt_or_gt with hlt | hgt
    · filter_upwards [Iio_mem_nhds hlt] with u hu
      simp [s, sign_neg (sub_neg.mpr hu), sign_neg (sub_neg.mpr hlt)]
    · filter_upwards [Ioi_mem_nhds hgt] with u hu
      simp [s, sign_pos (sub_pos.mpr hu), sign_pos (sub_pos.mpr hgt)]
  have hbase : HasDerivAt (fun u => bleisteinA p α + s * Real.sqrt (2 * (p u - p α)))
      (s * (2 * p' / (2 * Real.sqrt (2 * (p t - p α))))) t :=
    (hsqrt.const_mul s).const_add (bleisteinA p α)
  have heq : (fun u => bleisteinA p α + s * Real.sqrt (2 * (p u - p α))) =ᶠ[𝓝 t] bleisteinW p α :=
    hs_ev.mono fun u hu => by simp [bleisteinW, hu]
  refine (hbase.congr_of_eventuallyEq heq.symm).congr_deriv ?_
  have hs_sq : s * s = 1 := by
    rcases hne.lt_or_gt with hlt | hgt
    · simp [s, sign_neg (sub_neg.mpr hlt)]
    · simp [s, sign_pos (sub_pos.mpr hgt)]
  have hr_ne : Real.sqrt (2 * (p t - p α)) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hs_ne : s ≠ 0 := fun hs0 => by simp [hs0] at hs_sq
  rw [bleisteinW_sub_bleisteinA]
  calc s * (2 * p' / (2 * Real.sqrt (2 * (p t - p α))))
      = (s * s) * p' / (s * Real.sqrt (2 * (p t - p α))) := by field_simp [hs_ne, hr_ne]
    _ = p' / (s * Real.sqrt (2 * (p t - p α))) := by rw [hs_sq, one_mul]

/-- Value of `deriv (bleisteinW p α) t` away from `t = α` where `p α < p t` (DLMF 2.3.28). Both
sides vanish when `p` is not differentiable at `t`. -/
theorem deriv_bleisteinW_of_ne {p : ℝ → ℝ} {α t : ℝ} (hpt : p α < p t) :
    deriv (bleisteinW p α) t = deriv p t / (bleisteinW p α t - bleisteinA p α) := by
  by_cases hd : DifferentiableAt ℝ p t
  · exact (hasDerivAt_bleisteinW_of_ne hpt hd.hasDerivAt).deriv
  · rw [deriv_zero_of_not_differentiableAt hd, zero_div]
    refine deriv_zero_of_not_differentiableAt fun hw => hd ?_
    have hev : ∀ᶠ u in 𝓝 t, bleisteinW p α u - bleisteinA p α ≠ 0 :=
      (hw.continuousAt.sub continuousAt_const).eventually_ne
        (bleisteinW_sub_bleisteinA_ne_zero hpt)
    have hp_eq :
        (fun u => (bleisteinW p α u - bleisteinA p α) ^ 2 / 2 + p α) =ᶠ[𝓝 t] p := by
      filter_upwards [hev] with u hu
      have hpu : p α ≤ p u := by
        by_contra! hlt
        apply hu
        rw [bleisteinW_sub_bleisteinA, Real.sqrt_eq_zero_of_nonpos (by linarith), mul_zero]
      linarith [sq_bleisteinW_sub_bleisteinA hpu]
    exact (((hw.sub (differentiableAt_const _)).pow 2).div_const 2 |>.add
      (differentiableAt_const _)).congr_of_eventuallyEq hp_eq.symm

/-- Strict positivity of `deriv (bleisteinW p α) t` away from `t = α` when `p α < p t` and
`deriv p t` has the sign of `t - α`. -/
theorem deriv_bleisteinW_pos_of_lt {p : ℝ → ℝ} {α t : ℝ}
    (hpt : p α < p t) (hsign : 0 < (t - α) * deriv p t) :
    0 < deriv (bleisteinW p α) t := by
  rw [deriv_bleisteinW_of_ne hpt]
  have hsqrt : 0 < Real.sqrt (2 * (p t - p α)) := Real.sqrt_pos.mpr (by linarith)
  rcases (ne_of_apply_ne p hpt.ne').lt_or_gt with hlt | hgt
  · rw [bleisteinW_sub_bleisteinA_of_lt hlt]
    exact div_pos_of_neg_of_neg (neg_of_mul_pos_right hsign (sub_neg.mpr hlt).le)
      (neg_neg_of_pos hsqrt)
  · rw [bleisteinW_sub_bleisteinA_of_gt hgt]
    exact div_pos (pos_of_mul_pos_right hsign (sub_pos.mpr hgt).le) hsqrt

/-- At the critical point `t = α`, `bleisteinW p α` is differentiable with derivative `√(p'')`
whenever `deriv p α = 0` and `HasDerivAt (deriv p) p'' α`. -/
theorem hasDerivAt_bleisteinW_self {p : ℝ → ℝ} {α p'' : ℝ}
    (hp_diff : ∀ᶠ t in 𝓝 α, DifferentiableAt ℝ p t) (hpα : deriv p α = 0)
    (hp'' : HasDerivAt (deriv p) p'' α) :
    HasDerivAt (bleisteinW p α) (Real.sqrt p'') α := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hlim : Tendsto (fun t => 2 * (p t - p α) / (t - α) ^ 2) (𝓝[≠] α) (𝓝 p'') := by
    have hp_cont : ContinuousAt p α := (hp_diff.self_of_nhds).continuousAt
    have hf' : ∀ᶠ t in 𝓝[≠] α, HasDerivAt (fun u => 2 * (p u - p α)) (2 * deriv p t) t :=
      (eventually_nhdsWithin_of_eventually_nhds hp_diff).mono fun t ht =>
        (ht.hasDerivAt.sub_const (p α)).const_mul 2
    have hg' : ∀ᶠ t in 𝓝[≠] α, HasDerivAt (fun u => (u - α) ^ 2) (2 * (t - α)) t :=
      Eventually.of_forall fun t =>
        (((hasDerivAt_id t).sub_const α).fun_pow 2).congr_deriv (by simp [id])
    have hg_ne : ∀ᶠ t in 𝓝[≠] α, 2 * (t - α) ≠ 0 :=
      eventually_mem_nhdsWithin.mono fun t ht =>
        mul_ne_zero two_ne_zero (sub_ne_zero.mpr (mem_compl_singleton_iff.mp ht))
    have hfa : Tendsto (fun u => 2 * (p u - p α)) (𝓝[≠] α) (𝓝 0) := by
      have h0 : Tendsto (fun u => 2 * (p u - p α)) (𝓝 α) (𝓝 (2 * (p α - p α))) :=
        ((hp_cont.sub continuousAt_const).const_mul 2).tendsto
      simpa using h0.mono_left nhdsWithin_le_nhds
    have hga : Tendsto (fun u => (u - α) ^ 2) (𝓝[≠] α) (𝓝 0) := by
      have h0 : Tendsto (fun u => (u - α) ^ 2) (𝓝 α) (𝓝 ((α - α) ^ 2)) :=
        ((continuousAt_id.sub continuousAt_const).pow 2).tendsto
      simpa using h0.mono_left nhdsWithin_le_nhds
    have hdiv : Tendsto (fun t => 2 * deriv p t / (2 * (t - α))) (𝓝[≠] α) (𝓝 p'') := by
      refine (hasDerivAt_iff_tendsto_slope.mp hp'').congr' ?_
      filter_upwards [eventually_mem_nhdsWithin] with t ht
      have hne : t - α ≠ 0 := sub_ne_zero.mpr (mem_compl_singleton_iff.mp ht)
      rw [slope_def_field, hpα, sub_zero]
      field_simp [hne]
    exact HasDerivAt.lhopital_zero_nhdsNE hf' hg' hg_ne hfa hga hdiv
  have hsqrt_lim : Tendsto (fun t => Real.sqrt (2 * (p t - p α) / (t - α) ^ 2))
      (𝓝[≠] α) (𝓝 (Real.sqrt p'')) :=
    (Real.continuous_sqrt.continuousAt).tendsto.comp hlim
  refine hsqrt_lim.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  have hne : t - α ≠ 0 := sub_ne_zero.mpr (mem_compl_singleton_iff.mp ht)
  rw [slope_def_field, bleisteinW_self, bleisteinW_sub_bleisteinA,
    Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq_eq_abs]
  have habs_ne : |t - α| ≠ 0 := abs_ne_zero.mpr hne
  field_simp [habs_ne, hne]
  linear_combination -Real.sqrt (2 * (p t - p α)) * sign_mul_abs (t - α)

/-- Value of `deriv (bleisteinW p α) α` at a critical point `α` of `p`. -/
theorem deriv_bleisteinW_self {p : ℝ → ℝ} {α p'' : ℝ}
    (hp_diff : ∀ᶠ t in 𝓝 α, DifferentiableAt ℝ p t) (hpα : deriv p α = 0)
    (hp'' : HasDerivAt (deriv p) p'' α) :
    deriv (bleisteinW p α) α = Real.sqrt p'' :=
  (hasDerivAt_bleisteinW_self hp_diff hpα hp'').deriv

/-- Strict positivity of `deriv (bleisteinW p α)` at a nondegenerate critical point `t = α`. -/
theorem deriv_bleisteinW_self_pos {p : ℝ → ℝ} {α p'' : ℝ}
    (hp_diff : ∀ᶠ t in 𝓝 α, DifferentiableAt ℝ p t) (hpα : deriv p α = 0)
    (hp'' : HasDerivAt (deriv p) p'' α) (hp''_pos : 0 < p'') :
    0 < deriv (bleisteinW p α) α := by
  rw [deriv_bleisteinW_self hp_diff hpα hp'']
  exact Real.sqrt_pos.mpr hp''_pos

/-- Continuity of `deriv (bleisteinW p α)` at a nondegenerate critical point `t = α`. -/
theorem continuousAt_deriv_bleisteinW_self {p : ℝ → ℝ} {α p'' : ℝ}
    (hp_diff : ∀ᶠ t in 𝓝 α, DifferentiableAt ℝ p t) (hpα : deriv p α = 0)
    (hp'' : HasDerivAt (deriv p) p'' α) (hp''_pos : 0 < p'') :
    ContinuousAt (deriv (bleisteinW p α)) α := by
  rw [continuousAt_iff_punctured_nhds, deriv_bleisteinW_self hp_diff hpα hp'']
  have hslope1 : Tendsto (fun t => deriv p t / (t - α)) (𝓝[≠] α) (𝓝 p'') := by
    simpa [slope_fun_def_field, hpα] using hasDerivAt_iff_tendsto_slope.mp hp''
  have hslope2 : Tendsto (fun t => (bleisteinW p α t - bleisteinW p α α) / (t - α))
      (𝓝[≠] α) (𝓝 (Real.sqrt p'')) := by
    have h := hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_bleisteinW_self hp_diff hpα hp'')
    rwa [slope_fun_def_field] at h
  have hsqrt_pos : 0 < Real.sqrt p'' := Real.sqrt_pos.mpr hp''_pos
  have hquot : Tendsto (fun t => (deriv p t / (t - α)) /
      ((bleisteinW p α t - bleisteinW p α α) / (t - α))) (𝓝[≠] α) (𝓝 (Real.sqrt p'')) := by
    rw [← Real.div_sqrt (x := p'')]
    exact hslope1.div hslope2 hsqrt_pos.ne'
  refine hquot.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hslope2.eventually (lt_mem_nhds hsqrt_pos)] with
    t (ht : t ≠ α) hpos
  have hsub : t - α ≠ 0 := sub_ne_zero.mpr ht
  have hw_ne : bleisteinW p α t - bleisteinA p α ≠ 0 := fun h => by
    rw [bleisteinW_self, h, zero_div] at hpos
    exact lt_irrefl 0 hpos
  have hpt : p α < p t := by
    contrapose! hw_ne
    rw [bleisteinW_sub_bleisteinA, Real.sqrt_eq_zero_of_nonpos (by linarith), mul_zero]
  rw [deriv_bleisteinW_of_ne hpt, bleisteinW_self, div_div_div_cancel_right₀ hsub]

/-- Bleistein's coordinate `bleisteinW p α` is `C¹` across the critical point `t = α` on an open
set `I` when `p` is `C¹` on `I`, attains its strict minimum on `I` at `α`, and satisfies
`0 < deriv (deriv p) α`. -/
theorem contDiffOn_bleisteinW {p : ℝ → ℝ} {I : Set ℝ} {α : ℝ} (hI : IsOpen I) (hα : α ∈ I)
    (hp : ContDiffOn ℝ 1 p I) (hmin : ∀ t ∈ I, t ≠ α → p α < p t)
    (hp''_pos : 0 < deriv (deriv p) α) :
    ContDiffOn ℝ 1 (bleisteinW p α) I := by
  have hdiff : ∀ t ∈ I, DifferentiableAt ℝ p t :=
    fun t ht => (hp.differentiableOn one_ne_zero).differentiableAt (hI.mem_nhds ht)
  have hp'_cont : ContinuousOn (deriv p) I := hp.continuousOn_deriv_of_isOpen hI le_rfl
  have hdiff_nhds : ∀ᶠ t in 𝓝 α, DifferentiableAt ℝ p t :=
    Filter.Eventually.mono (hI.mem_nhds hα) hdiff
  have hpα : deriv p α = 0 :=
    ((isMinOn_iff.mpr fun t ht => (eq_or_ne t α).elim (fun h => h ▸ le_rfl)
      (fun hne => (hmin t ht hne).le)).isLocalMin (hI.mem_nhds hα)).deriv_eq_zero
  have hp''_at : HasDerivAt (deriv p) (deriv (deriv p) α) α :=
    (differentiableAt_of_deriv_ne_zero hp''_pos.ne').hasDerivAt
  rw [contDiffOn_one_iff_derivWithin hI.uniqueDiffOn]
  refine ⟨fun t ht => ?_, ContinuousOn.congr ?_ fun _ hx => derivWithin_of_isOpen hI hx⟩
  · rcases eq_or_ne t α with rfl | hne
    · exact (hasDerivAt_bleisteinW_self hdiff_nhds hpα hp''_at).differentiableAt
        |>.differentiableWithinAt
    · exact (hasDerivAt_bleisteinW_of_ne (hmin t ht hne)
        (hdiff t ht).hasDerivAt).differentiableAt.differentiableWithinAt
  · intro t ht
    rcases eq_or_ne t α with rfl | hne
    · exact (continuousAt_deriv_bleisteinW_self hdiff_nhds hpα hp''_at
        hp''_pos).continuousWithinAt
    · have hw_cont : ContinuousAt (bleisteinW p α) t :=
        (continuousOn_bleisteinW hp.continuousOn α).continuousAt (hI.mem_nhds ht)
      have hquot : ContinuousAt (fun u => deriv p u / (bleisteinW p α u - bleisteinA p α)) t :=
        (hp'_cont.continuousAt (hI.mem_nhds ht)).div (hw_cont.sub continuousAt_const)
          (bleisteinW_sub_bleisteinA_ne_zero (hmin t ht hne))
      refine (hquot.congr ?_).continuousWithinAt
      filter_upwards [hI.mem_nhds ht, isOpen_ne.mem_nhds hne] with u hu hune
      exact (deriv_bleisteinW_of_ne (hmin u hu hune)).symm

/-- Strict differentiability of `bleisteinW p α` at every point of an open set `I` under the
hypotheses of `TauCeti.contDiffOn_bleisteinW`. -/
theorem hasStrictDerivAt_bleisteinW {p : ℝ → ℝ} {I : Set ℝ} {α t : ℝ}
    (hI : IsOpen I) (hα : α ∈ I) (hp : ContDiffOn ℝ 1 p I)
    (hmin : ∀ u ∈ I, u ≠ α → p α < p u) (hp''_pos : 0 < deriv (deriv p) α) (ht : t ∈ I) :
    HasStrictDerivAt (bleisteinW p α) (deriv (bleisteinW p α) t) t :=
  ((contDiffOn_bleisteinW hI hα hp hmin hp''_pos).contDiffAt
    (hI.mem_nhds ht)).hasStrictDerivAt_deriv one_ne_zero

/-- When `α` is the unique critical point of `p` on an open order-connected set `I`,
`deriv (bleisteinW p α)` is strictly positive everywhere on `I`. -/
theorem deriv_bleisteinW_pos {p : ℝ → ℝ} {I : Set ℝ} {α t : ℝ}
    (hI : IsOpen I) (hord : OrdConnected I) (hα : α ∈ I) (hp : ContDiffOn ℝ 2 p I)
    (hpα : deriv p α = 0) (hp''_pos : 0 < deriv (deriv p) α)
    (hp' : ∀ u ∈ I, u ≠ α → deriv p u ≠ 0) (ht : t ∈ I) :
    0 < deriv (bleisteinW p α) t := by
  have hp'_cont : ContinuousOn (deriv p) I := hp.continuousOn_deriv_of_isOpen hI (by decide)
  have hanti := strictAntiOn_Iic_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hmono := strictMonoOn_Ici_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hp_diff : ∀ u ∈ I, DifferentiableAt ℝ p u := fun u hu =>
    (hp.contDiffAt (hI.mem_nhds hu)).differentiableAt (by decide)
  rcases lt_trichotomy t α with hlt | rfl | hgt
  · have hpt : p α < p t := hanti ⟨ht, hlt.le⟩ ⟨hα, le_rfl⟩ hlt
    have hsign := sign_deriv_eq_sign_sub hord hα hp'_cont hpα hp''_pos hp' ht
    rw [sign_neg (sub_neg.mpr hlt), sign_eq_neg_one_iff] at hsign
    rw [deriv_bleisteinW_of_ne hpt, bleisteinW_sub_bleisteinA,
      sign_neg (sub_neg.mpr hlt), SignType.coe_neg_one, neg_one_mul]
    exact div_pos_of_neg_of_neg hsign (neg_lt_zero.mpr (Real.sqrt_pos.mpr (by linarith)))
  · have hp''_at : HasDerivAt (deriv p) (deriv (deriv p) t) t :=
      (((hp.deriv_of_isOpen hI (by decide)).contDiffAt (hI.mem_nhds hα)).differentiableAt
        one_ne_zero).hasDerivAt
    exact deriv_bleisteinW_self_pos (Filter.eventually_of_mem (hI.mem_nhds hα) hp_diff)
      hpα hp''_at hp''_pos
  · have hpt : p α < p t := hmono ⟨hα, le_rfl⟩ ⟨ht, hgt.le⟩ hgt
    have hsign := sign_deriv_eq_sign_sub hord hα hp'_cont hpα hp''_pos hp' ht
    rw [sign_pos (sub_pos.mpr hgt), sign_eq_one_iff] at hsign
    rw [deriv_bleisteinW_of_ne hpt, bleisteinW_sub_bleisteinA,
      sign_pos (sub_pos.mpr hgt), SignType.coe_one, one_mul]
    exact div_pos hsign (Real.sqrt_pos.mpr (by linarith))

/-- Strict positivity of `deriv (bleisteinW p α)` at `t ∈ I` when `p` is differentiable on an open
set `I ∋ α`, strictly decreasing on `I ∩ (-∞, α]`, strictly increasing on `I ∩ [α, ∞)`, satisfies
`0 < deriv (deriv p) α`, and has no stationary point at `t` other than `α`. -/
theorem deriv_bleisteinW_pos_of_differentiableOn {p : ℝ → ℝ} {I : Set ℝ} {α t : ℝ}
    (hI : IsOpen I) (hα : α ∈ I) (hp : DifferentiableOn ℝ p I)
    (hanti : StrictAntiOn p (I ∩ Iic α)) (hmono : StrictMonoOn p (I ∩ Ici α))
    (hp''_pos : 0 < deriv (deriv p) α) (ht : t ∈ I) (hreg : t ≠ α → deriv p t ≠ 0) :
    0 < deriv (bleisteinW p α) t := by
  rcases eq_or_ne t α with rfl | hne
  · have hdiff_nhds : ∀ᶠ u in 𝓝 t, DifferentiableAt ℝ p u :=
      Filter.Eventually.mono (hI.mem_nhds hα) fun _ hu => hp.differentiableAt (hI.mem_nhds hu)
    have hpα : deriv p t = 0 :=
      ((isMinOn_iff.mpr fun _ hu =>
        le_of_antitoneOn_monotoneOn hα hanti.antitoneOn hmono.monotoneOn hu).isLocalMin
        (hI.mem_nhds hα)).deriv_eq_zero
    exact deriv_bleisteinW_self_pos hdiff_nhds hpα
      (differentiableAt_of_deriv_ne_zero hp''_pos.ne').hasDerivAt hp''_pos
  · have hsign : 0 < (t - α) * deriv p t := by
      rcases hne.lt_or_gt with hlt | hgt
      · have hle : deriv p t ≤ 0 := by
          rw [← derivWithin_of_isOpen (hI.inter isOpen_Iio) ⟨ht, hlt⟩]
          exact (hanti.antitoneOn.mono (inter_subset_inter_right I Iio_subset_Iic_self))
            |>.derivWithin_nonpos
        exact mul_pos_of_neg_of_neg (sub_neg.mpr hlt) (lt_of_le_of_ne hle (hreg hne))
      · have hge : 0 ≤ deriv p t := by
          rw [← derivWithin_of_isOpen (hI.inter isOpen_Ioi) ⟨ht, hgt⟩]
          exact (hmono.monotoneOn.mono (inter_subset_inter_right I Ioi_subset_Ici_self))
            |>.derivWithin_nonneg
        exact mul_pos (sub_pos.mpr hgt) (lt_of_le_of_ne' hge (hreg hne))
    exact deriv_bleisteinW_pos_of_lt
      (lt_of_strictAntiOn_strictMonoOn hα hanti hmono ht hne) hsign

/-! ### Upper integration limit `κ` and interval images -/

/-- Right-hand limit `bleisteinW p α t → 0` as `t → 0⁺` when `p` is right-continuous at `0`. -/
theorem tendsto_bleisteinW_nhdsGT_zero {p : ℝ → ℝ} (α : ℝ)
    (hp : ContinuousWithinAt p (Ioi 0) 0) :
    Tendsto (bleisteinW p α) (𝓝[>] 0) (𝓝 0) := by
  simpa only [ContinuousWithinAt, bleisteinW_zero] using continuousWithinAt_bleisteinW hp α

/-- If `p t → +∞` along a filter `l` on which eventually `α < t`, then `bleisteinW p α t → +∞`. -/
theorem tendsto_bleisteinW_atTop_of_tendsto_atTop {p : ℝ → ℝ} {α : ℝ} {l : Filter ℝ}
    (hα : ∀ᶠ t in l, α < t) (hp : Tendsto p l atTop) :
    Tendsto (bleisteinW p α) l atTop := by
  have hsqrt : Tendsto (fun t => bleisteinA p α + Real.sqrt (2 * (p t - p α))) l atTop :=
    tendsto_const_nhds.add_atTop <|
      Real.tendsto_sqrt_atTop.comp ((hp.atTop_add tendsto_const_nhds).const_mul_atTop two_pos)
  refine hsqrt.congr' ?_
  filter_upwards [hα] with t ht
  rw [bleisteinW, sign_pos (sub_pos.mpr ht), SignType.coe_one, one_mul]

/-- Along any filter `l` eventually to the right of `α` on which `p` tends to a finite limit `pb`,
`bleisteinW p α` tends to `bleisteinA p α + √(2 * (pb - p α))`. -/
theorem tendsto_bleisteinW_nhds_of_tendsto_nhds {p : ℝ → ℝ} {α pb : ℝ} {l : Filter ℝ}
    (hα : ∀ᶠ t in l, α < t) (hp : Tendsto p l (𝓝 pb)) :
    Tendsto (bleisteinW p α) l (𝓝 (bleisteinA p α + Real.sqrt (2 * (pb - p α)))) := by
  have hsqrt : Tendsto (fun t => bleisteinA p α + Real.sqrt (2 * (p t - p α))) l
      (𝓝 (bleisteinA p α + Real.sqrt (2 * (pb - p α)))) :=
    tendsto_const_nhds.add <|
      (Real.continuous_sqrt.tendsto _).comp ((hp.sub_const (p α)).const_mul 2)
  refine hsqrt.congr' ?_
  filter_upwards [hα] with t ht
  rw [bleisteinW, sign_pos (sub_pos.mpr ht), SignType.coe_one, one_mul]

/-- If `p` is continuous on an open order-connected set `I ⊇ [0, k)` containing `α` and
`p t → +∞` as `t → k⁻`, then `bleisteinW p α t → +∞` as `t → k⁻`. -/
theorem tendsto_bleisteinW_nhdsLT_atTop {p : ℝ → ℝ} {I : Set ℝ} {α k : ℝ}
    (hk : 0 < k) (hI : IsOpen I) (hord : OrdConnected I) (hsub : Ico 0 k ⊆ I) (hα : α ∈ I)
    (hp : ContinuousOn p I) (hlim : Tendsto p (𝓝[<] k) atTop) :
    Tendsto (bleisteinW p α) (𝓝[<] k) atTop := by
  have hαk : α < k := by
    by_contra hge
    have hkI : k ∈ I := hord.out (hsub ⟨le_rfl, hk⟩) hα ⟨hk.le, not_lt.mp hge⟩
    have hp_cont : Tendsto p (𝓝[<] k) (𝓝 (p k)) :=
      ((hp k hkI).continuousAt (hI.mem_nhds hkI)).tendsto.mono_left nhdsWithin_le_nhds
    exact not_tendsto_nhds_of_tendsto_atTop hlim (p k) hp_cont
  exact tendsto_bleisteinW_atTop_of_tendsto_atTop
    (eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds hαk)) hlim

/-- If `p` is strictly decreasing on `I ∩ (-∞, α]` for a set `I ⊇ [0, k)` and `p t → +∞` as
`t → k⁻`, then `bleisteinW p α t → +∞` as `t → k⁻`. -/
theorem tendsto_bleisteinW_nhdsLT_atTop_of_strictAntiOn {p : ℝ → ℝ} {I : Set ℝ} {α k : ℝ}
    (hk : 0 < k) (hsub : Ico 0 k ⊆ I) (hanti : StrictAntiOn p (I ∩ Iic α))
    (hlim : Tendsto p (𝓝[<] k) atTop) :
    Tendsto (bleisteinW p α) (𝓝[<] k) atTop := by
  have hαk : α < k := by
    by_contra! hle
    have hev : ∀ᶠ t in 𝓝[<] k, t ∈ Ioo 0 k ∧ p 0 < p t :=
      Filter.inter_mem (Ioo_mem_nhdsLT hk) (hlim.eventually_gt_atTop (p 0))
    obtain ⟨t, ht, hpt⟩ := hev.exists
    have hlt : p t < p 0 := hanti ⟨hsub ⟨le_rfl, hk⟩, hk.le.trans hle⟩
      ⟨hsub ⟨ht.1.le, ht.2⟩, ht.2.le.trans hle⟩ ht.1
    exact hlt.not_gt hpt
  exact tendsto_bleisteinW_atTop_of_tendsto_atTop
    (Filter.mem_of_superset (Ioo_mem_nhdsLT hαk) fun _ h => h.1) hlim

/-- Image of `(0, k)` under `bleisteinW p α` when `bleisteinW p α` approaches a finite limit `κ`
as `t → k⁻`. -/
theorem image_bleisteinW_Ioo_of_tendsto_nhds {p : ℝ → ℝ} {I : Set ℝ} {α k κ : ℝ}
    (hk : 0 < k) (hsub : Ico 0 k ⊆ I) (hα : α ∈ I) (hp : ContinuousOn p (Ico 0 k))
    (hanti : StrictAntiOn p (I ∩ Iic α)) (hmono : StrictMonoOn p (I ∩ Ici α))
    (hκ : Tendsto (bleisteinW p α) (𝓝[<] k) (𝓝 κ)) :
    bleisteinW p α '' Ioo 0 k = Ioo 0 κ := by
  simpa [bleisteinW_zero] using (continuousOn_bleisteinW hp α).image_Ioo_of_strictMonoOn_of_tendsto
    hk ((strictMonoOn_bleisteinW hα hanti hmono).mono hsub) hκ

/-- Image of `(0, k)` under `bleisteinW p α` when `bleisteinW p α → +∞` as `t → k⁻` (`κ = ∞`). -/
theorem image_bleisteinW_Ioo_of_tendsto_atTop {p : ℝ → ℝ} {I : Set ℝ} {α k : ℝ}
    (hk : 0 < k) (hsub : Ico 0 k ⊆ I) (hα : α ∈ I) (hp : ContinuousOn p (Ico 0 k))
    (hanti : StrictAntiOn p (I ∩ Iic α)) (hmono : StrictMonoOn p (I ∩ Ici α))
    (hκ : Tendsto (bleisteinW p α) (𝓝[<] k) atTop) :
    bleisteinW p α '' Ioo 0 k = Ioi 0 := by
  simpa [bleisteinW_zero] using
    (continuousOn_bleisteinW hp α).image_Ioo_of_strictMonoOn_of_tendsto_atTop
      hk ((strictMonoOn_bleisteinW hα hanti hmono).mono hsub) hκ

/-- Image of `(0, ∞)` under `bleisteinW p α` when `bleisteinW p α` approaches a finite limit `κ`
at `+∞`. -/
theorem image_bleisteinW_Ioi_of_tendsto_nhds {p : ℝ → ℝ} {I : Set ℝ} {α κ : ℝ}
    (hsub : Ici 0 ⊆ I) (hα : α ∈ I) (hp : ContinuousOn p (Ici 0))
    (hanti : StrictAntiOn p (I ∩ Iic α)) (hmono : StrictMonoOn p (I ∩ Ici α))
    (hκ : Tendsto (bleisteinW p α) atTop (𝓝 κ)) :
    bleisteinW p α '' Ioi 0 = Ioo 0 κ := by
  simpa [bleisteinW_zero] using (continuousOn_bleisteinW hp α).image_Ioi_of_strictMonoOn_of_tendsto
    ((strictMonoOn_bleisteinW hα hanti hmono).mono hsub) hκ

/-- Image of `(0, ∞)` under `bleisteinW p α` when `bleisteinW p α → +∞` at `+∞` (`κ = ∞`). -/
theorem image_bleisteinW_Ioi_of_tendsto_atTop {p : ℝ → ℝ} {I : Set ℝ} {α : ℝ}
    (hsub : Ici 0 ⊆ I) (hα : α ∈ I) (hp : ContinuousOn p (Ici 0))
    (hanti : StrictAntiOn p (I ∩ Iic α)) (hmono : StrictMonoOn p (I ∩ Ici α))
    (hκ : Tendsto (bleisteinW p α) atTop atTop) :
    bleisteinW p α '' Ioi 0 = Ioi 0 := by
  have hw_cont : ContinuousOn (bleisteinW p α) (Ici 0) := continuousOn_bleisteinW hp α
  have hw_mono : StrictMonoOn (bleisteinW p α) (Ici 0) :=
    (strictMonoOn_bleisteinW hα hanti hmono).mono hsub
  simpa [bleisteinW_zero] using hw_cont.image_Ioi_of_strictMonoOn hw_mono hκ

/-- Having upper integration limit `k = ∞` on the `t`-side does not by itself force `κ = ∞` on the
`w`-side: for the smooth bounded phase `p t = t ^ 2 / (1 + t ^ 2)` at `α = 0`, `bleisteinW p 0`
maps `(0, ∞)` onto the bounded interval `(0, √2)`. -/
theorem image_bleisteinW_sq_div_one_add_sq_Ioi :
    bleisteinW (fun t : ℝ => t ^ 2 / (1 + t ^ 2)) 0 '' Ioi 0 = Ioo 0 (Real.sqrt 2) := by
  let p : ℝ → ℝ := fun t => t ^ 2 / (1 + t ^ 2)
  have hderiv : ∀ t : ℝ, HasDerivAt p (2 * t / (1 + t ^ 2) ^ 2) t := fun t => by
    have hd : HasDerivAt (fun u : ℝ => 1 + u ^ 2) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t).const_add 1
    exact ((hasDerivAt_pow 2 t).div hd (by positivity)).congr_deriv (by ring)
  have hp_cont : Continuous p := continuous_iff_continuousAt.mpr fun t =>
    (hderiv t).differentiableAt.continuousAt
  have hanti : StrictAntiOn p (Ici 0 ∩ Iic 0) :=
    fun _ hx _ hy hlt => (hlt.not_ge (hy.2.trans hx.1)).elim
  have hmono : StrictMonoOn p (Ici 0 ∩ Ici 0) := by
    rw [inter_self]
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) hp_cont.continuousOn fun t ht => ?_
    have ht_pos : 0 < t := by rwa [interior_Ici] at ht
    rw [(hderiv t).deriv]
    positivity
  have hlim_p : Tendsto p atTop (𝓝 1) := by
    have h1 : Tendsto (fun t : ℝ => (1 : ℝ) / ((t ^ 2)⁻¹ + 1)) atTop (𝓝 ((1 : ℝ) / (0 + 1))) :=
      tendsto_const_nhds.div
        ((tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by decide : 2 ≠ 0))).add
          tendsto_const_nhds)
        (by positivity)
    rw [zero_add, div_one] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hsq : t ^ 2 ≠ 0 := pow_ne_zero 2 ht.ne'
    simp only [p]
    field_simp [hsq]
  have hlim_w : Tendsto (bleisteinW p 0) atTop (𝓝 (Real.sqrt 2)) := by
    simpa [p] using tendsto_bleisteinW_nhds_of_tendsto_nhds (eventually_gt_atTop 0) hlim_p
  exact image_bleisteinW_Ioi_of_tendsto_nhds Subset.rfl (le_rfl : (0 : ℝ) ∈ Ici 0)
    hp_cont.continuousOn hanti hmono hlim_w

/-! ### Inverse coordinate, transformed amplitude, and change of variables -/

/-- Transformed amplitude `f(α, w) = ((t / w) ^ (λ - 1) / deriv (bleisteinW p α) t) • q t`
evaluated at `t = invFunOn (bleisteinW p α) s w` (DLMF 2.3.30), with the removable `0 / 0`
singularity of `t / w` at `w = 0` resolved by `(deriv (bleisteinW p α) 0)⁻¹` and the Jacobian
factor written via `deriv (bleisteinW p α) t` to avoid the `0 / 0` indeterminacy of
`(w - a) / deriv p t` at `t = α`. Under the open-domain, `C¹`-coordinate, strict-monotonicity,
positive-derivative, and amplitude-continuity hypotheses of
`TauCeti.continuousOn_bleisteinAmplitude_of_zero_mem`, this extension is continuous across `w = 0`
and `w = bleisteinA p α`. -/
noncomputable def bleisteinAmplitude {E : Type*} [SMul ℝ E]
    (p : ℝ → ℝ) (q : ℝ → E) (lam α : ℝ) (s : Set ℝ) (w : ℝ) : E :=
  let t := invFunOn (bleisteinW p α) s w
  ((if w = 0 then (deriv (bleisteinW p α) 0)⁻¹ else t / w) ^ (lam - 1) /
      deriv (bleisteinW p α) t) •
    q t

section AmplitudeAlgebra

variable {E : Type*} [SMul ℝ E]

/-- Unfolding `TauCeti.bleisteinAmplitude`. -/
theorem bleisteinAmplitude_def (p : ℝ → ℝ) (q : ℝ → E) (lam α : ℝ) (s : Set ℝ) (w : ℝ) :
    bleisteinAmplitude p q lam α s w =
      (((if w = 0 then (deriv (bleisteinW p α) 0)⁻¹
          else invFunOn (bleisteinW p α) s w / w) ^ (lam - 1)) /
        deriv (bleisteinW p α) (invFunOn (bleisteinW p α) s w)) •
      q (invFunOn (bleisteinW p α) s w) :=
  (rfl)

/-- For `w ≠ 0` (in particular on `(0, ∞)`), `bleisteinAmplitude` simplifies to
`((t / w) ^ (lam - 1) / deriv (bleisteinW p α) t) • q t`. -/
theorem bleisteinAmplitude_of_ne_zero (p : ℝ → ℝ) (q : ℝ → E) (lam α : ℝ) (s : Set ℝ)
    {w : ℝ} (hw : w ≠ 0) :
    bleisteinAmplitude p q lam α s w =
      (((invFunOn (bleisteinW p α) s w / w) ^ (lam - 1)) /
        deriv (bleisteinW p α) (invFunOn (bleisteinW p α) s w)) •
      q (invFunOn (bleisteinW p α) s w) := by
  simp [bleisteinAmplitude, hw]

/-- Value of `bleisteinAmplitude` at the endpoint `w = 0`. -/
theorem bleisteinAmplitude_zero (p : ℝ → ℝ) (q : ℝ → E) (lam α : ℝ) (s : Set ℝ) :
    bleisteinAmplitude p q lam α s 0 =
      (((deriv (bleisteinW p α) 0)⁻¹ ^ (lam - 1)) /
        deriv (bleisteinW p α) (invFunOn (bleisteinW p α) s 0)) •
      q (invFunOn (bleisteinW p α) s 0) := by
  simp [bleisteinAmplitude]

/-- Value of `bleisteinAmplitude` at `w = 0` when `0 ∈ s` and `bleisteinW p α` is injective on
`s`. -/
theorem bleisteinAmplitude_zero_of_injOn {p : ℝ → ℝ} {q : ℝ → E} {lam α : ℝ} {s : Set ℝ}
    (hinj : InjOn (bleisteinW p α) s) (h0 : 0 ∈ s) :
    bleisteinAmplitude p q lam α s 0 =
      (((deriv (bleisteinW p α) 0)⁻¹ ^ (lam - 1)) / deriv (bleisteinW p α) 0) • q 0 := by
  have hinv : invFunOn (bleisteinW p α) s 0 = 0 := by
    simpa [bleisteinW_zero] using hinj.leftInvOn_invFunOn h0
  rw [bleisteinAmplitude_zero, hinv]

/-- `bleisteinAmplitude` is invariant under enlarging the ambient inversion domain: if `s₁ ⊆ s₂`
and `bleisteinW p α` is injective on `s₂`, the two amplitudes coincide on `bleisteinW p α '' s₁`. -/
theorem bleisteinAmplitude_congr_set {p : ℝ → ℝ} {q : ℝ → E} {lam α : ℝ} {s₁ s₂ : Set ℝ}
    (hsub : s₁ ⊆ s₂) (hinj : InjOn (bleisteinW p α) s₂)
    {w : ℝ} (hw : w ∈ bleisteinW p α '' s₁) :
    bleisteinAmplitude p q lam α s₁ w = bleisteinAmplitude p q lam α s₂ w := by
  rcases hw with ⟨t, ht₁, rfl⟩
  have h₁ : invFunOn (bleisteinW p α) s₁ (bleisteinW p α t) = t :=
    (hinj.mono hsub).leftInvOn_invFunOn ht₁
  have h₂ : invFunOn (bleisteinW p α) s₂ (bleisteinW p α t) = t :=
    hinj.leftInvOn_invFunOn (hsub ht₁)
  simp only [bleisteinAmplitude_def, h₁, h₂]

/-- Evaluating `bleisteinAmplitude` at `bleisteinW p α t` for `t ∈ s` with
`bleisteinW p α t ≠ 0` recovers the original point `t` whenever `bleisteinW p α` is injective on
`s`. -/
theorem bleisteinAmplitude_bleisteinW {p : ℝ → ℝ} {q : ℝ → E} {lam α t : ℝ} {s : Set ℝ}
    (hinj : InjOn (bleisteinW p α) s) (ht : t ∈ s) (hw : bleisteinW p α t ≠ 0) :
    bleisteinAmplitude p q lam α s (bleisteinW p α t) =
      ((t / bleisteinW p α t) ^ (lam - 1) / deriv (bleisteinW p α) t) • q t := by
  rw [bleisteinAmplitude_of_ne_zero p q lam α s hw, hinj.leftInvOn_invFunOn ht]

/-- Explicit formula of DLMF 2.3.30 away from `t = α` and `w = 0`:
`f(α, w) = ((t / w) ^ (lam - 1) * (w - a) / deriv p t) • q t`. -/
theorem bleisteinAmplitude_bleisteinW_of_ne {p : ℝ → ℝ} {q : ℝ → E} {lam α t : ℝ} {s : Set ℝ}
    (hinj : InjOn (bleisteinW p α) s) (ht : t ∈ s) (hw : bleisteinW p α t ≠ 0)
    (hpt : p α < p t) :
    bleisteinAmplitude p q lam α s (bleisteinW p α t) =
      ((t / bleisteinW p α t) ^ (lam - 1) *
        (bleisteinW p α t - bleisteinA p α) / deriv p t) • q t := by
  rw [bleisteinAmplitude_bleisteinW hinj ht hw, deriv_bleisteinW_of_ne hpt, div_div_eq_mul_div]

/-- Evaluation of `bleisteinAmplitude` at the transformed critical point `w = bleisteinA p α` for
any `α ∈ s` (including `α = 0`, where `bleisteinA p 0 = 0`). -/
theorem bleisteinAmplitude_bleisteinA {p : ℝ → ℝ} {q : ℝ → E} {lam α : ℝ} {s : Set ℝ}
    (hinj : InjOn (bleisteinW p α) s) (hα : α ∈ s) :
    bleisteinAmplitude p q lam α s (bleisteinA p α) =
      (((if bleisteinA p α = 0 then (deriv (bleisteinW p α) 0)⁻¹
          else α / bleisteinA p α) ^ (lam - 1)) /
        deriv (bleisteinW p α) α) • q α := by
  have hinv : invFunOn (bleisteinW p α) s (bleisteinA p α) = α := by
    simpa [bleisteinW_self] using hinj.leftInvOn_invFunOn hα
  rw [bleisteinAmplitude_def, hinv]

/-- Value of `bleisteinAmplitude` at the transformed critical point `w = bleisteinA p α` when
`α ∈ s` and `bleisteinA p α ≠ 0` (DLMF 2.3.32). -/
theorem bleisteinAmplitude_self {p : ℝ → ℝ} {q : ℝ → E} {I s : Set ℝ} {lam α : ℝ}
    (hI : IsOpen I) (hord : OrdConnected I) (hαs : α ∈ s) (hs : s ⊆ I)
    (ha : bleisteinA p α ≠ 0) (hp : ContDiffOn ℝ 2 p I) (hpα : deriv p α = 0)
    (hp''_pos : 0 < deriv (deriv p) α) (hp' : ∀ u ∈ I, u ≠ α → deriv p u ≠ 0) :
    bleisteinAmplitude p q lam α s (bleisteinA p α) =
      ((α / bleisteinA p α) ^ (lam - 1) / Real.sqrt (deriv (deriv p) α)) • q α := by
  have hα : α ∈ I := hs hαs
  have hp'_cont : ContinuousOn (deriv p) I := hp.continuousOn_deriv_of_isOpen hI (by decide)
  have hanti := strictAntiOn_Iic_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hmono := strictMonoOn_Ici_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hinj : InjOn (bleisteinW p α) s := ((strictMonoOn_bleisteinW hα hanti hmono).mono hs).injOn
  have hp_diff : ∀ u ∈ I, DifferentiableAt ℝ p u := fun u hu =>
    (hp.contDiffAt (hI.mem_nhds hu)).differentiableAt (by decide)
  have hp''_at : HasDerivAt (deriv p) (deriv (deriv p) α) α :=
    (((hp.deriv_of_isOpen hI (by decide)).contDiffAt (hI.mem_nhds hα)).differentiableAt
      one_ne_zero).hasDerivAt
  rw [bleisteinAmplitude_bleisteinA hinj hαs,
    deriv_bleisteinW_self (Filter.eventually_of_mem (hI.mem_nhds hα) hp_diff) hpα hp''_at]
  simp [ha]

/-- Value of `bleisteinAmplitude` at coalescence `α = 0` (`bleisteinA p 0 = 0`):
`f(0, 0) = ((√(p'' 0))⁻¹ ^ (lam - 1) / √(p'' 0)) • q 0`. -/
theorem bleisteinAmplitude_self_zero {p : ℝ → ℝ} {q : ℝ → E} {s : Set ℝ} {lam : ℝ}
    (hinj : InjOn (bleisteinW p 0) s) (h0s : 0 ∈ s)
    (hp_diff : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ p t) (hp0 : deriv p 0 = 0)
    (hp'' : HasDerivAt (deriv p) (deriv (deriv p) 0) 0) :
    bleisteinAmplitude p q lam 0 s 0 =
      (((Real.sqrt (deriv (deriv p) 0))⁻¹ ^ (lam - 1)) /
        Real.sqrt (deriv (deriv p) 0)) • q 0 := by
  rw [bleisteinAmplitude_zero_of_injOn hinj h0s, deriv_bleisteinW_self hp_diff hp0 hp'']

/-- DLMF 2.3.30 form of the transformed amplitude in terms of the inverse derivative `dt / dw` for
`w ≠ 0`: `f(α, w) = ((t(w) / w) ^ (λ - 1) * t'(w)) • q(t(w))`. -/
theorem bleisteinAmplitude_eq_mul_deriv_invFunOn_smul {p : ℝ → ℝ} {q : ℝ → E} {s : Set ℝ}
    {lam α w w' : ℝ} (hw0 : w ≠ 0) (hw_mem : w ∈ bleisteinW p α '' s)
    (hs : s ∈ 𝓝 (invFunOn (bleisteinW p α) s w))
    (hw : HasStrictDerivAt (bleisteinW p α) w' (invFunOn (bleisteinW p α) s w))
    (hinj : InjOn (bleisteinW p α) s) (hd : w' ≠ 0) :
    bleisteinAmplitude p q lam α s w =
      ((invFunOn (bleisteinW p α) s w / w) ^ (lam - 1) *
        deriv (invFunOn (bleisteinW p α) s) w) • q (invFunOn (bleisteinW p α) s w) := by
  rw [bleisteinAmplitude_of_ne_zero p q lam α s hw0, hw.deriv_invFunOn hw_mem hd hs hinj,
    div_eq_mul_inv]

/-- On a neighbourhood `s` of `0 ∈ s` on which `bleisteinW p α` is injective with a nonzero
strict derivative at `0`, the desingularized ratio in `bleisteinAmplitude` is
`dslope (invFunOn (bleisteinW p α) s) 0`. -/
theorem bleisteinAmplitude_eq_dslope {p : ℝ → ℝ} {q : ℝ → E} {s : Set ℝ} {lam α w : ℝ}
    (h0 : 0 ∈ s) (hs : s ∈ 𝓝 (0 : ℝ)) (hinj : InjOn (bleisteinW p α) s)
    (hw0 : HasStrictDerivAt (bleisteinW p α) (deriv (bleisteinW p α) 0) 0)
    (hd0 : deriv (bleisteinW p α) 0 ≠ 0) :
    bleisteinAmplitude p q lam α s w =
      (((dslope (invFunOn (bleisteinW p α) s) 0 w) ^ (lam - 1)) /
        deriv (bleisteinW p α) (invFunOn (bleisteinW p α) s w)) •
      q (invFunOn (bleisteinW p α) s w) := by
  have hd := hw0.dslope_invFunOn_eq hd0 h0 hs hinj (bleisteinW_zero p α) w
  simp only [sub_zero] at hd
  rw [bleisteinAmplitude_def, ← hd]

end AmplitudeAlgebra

/-- `bleisteinAmplitude` vanishes when the amplitude `q` is identically zero. -/
@[simp]
theorem bleisteinAmplitude_zero_fun {E : Type*} [Zero E] [SMulZeroClass ℝ E]
    (p : ℝ → ℝ) (lam α : ℝ) (s : Set ℝ) (w : ℝ) :
    bleisteinAmplitude p (0 : ℝ → E) lam α s w = 0 := by
  simp [bleisteinAmplitude]

/-- Additivity of `bleisteinAmplitude` in the amplitude `q`. -/
theorem bleisteinAmplitude_add {E : Type*} [AddZeroClass E] [DistribSMul ℝ E]
    (p : ℝ → ℝ) (q₁ q₂ : ℝ → E) (lam α : ℝ) (s : Set ℝ) (w : ℝ) :
    bleisteinAmplitude p (q₁ + q₂) lam α s w =
      bleisteinAmplitude p q₁ lam α s w + bleisteinAmplitude p q₂ lam α s w := by
  simp [bleisteinAmplitude, smul_add]

/-- Homogeneity of `bleisteinAmplitude` in the amplitude `q`. -/
theorem bleisteinAmplitude_smul {𝕜 E : Type*} [SMul ℝ E] [SMul 𝕜 E] [SMulCommClass ℝ 𝕜 E]
    (p : ℝ → ℝ) (c : 𝕜) (q : ℝ → E) (lam α : ℝ) (s : Set ℝ) (w : ℝ) :
    bleisteinAmplitude p (c • q) lam α s w = c • bleisteinAmplitude p q lam α s w := by
  simp [bleisteinAmplitude, smul_comm]

/-- Nonvanishing of `bleisteinAmplitude` at the transformed critical point `w = bleisteinA p α`
whenever `q α ≠ 0`, uniformly across `α < 0`, `α = 0`, and `α > 0`. -/
theorem bleisteinAmplitude_bleisteinA_ne_zero {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {p : ℝ → ℝ} {q : ℝ → E} {lam α : ℝ} {U s : Set ℝ}
    (h0U : 0 ∈ U) (hαs : α ∈ s) (hsU : s ⊆ U) (hmono : StrictMonoOn (bleisteinW p α) U)
    (hw'α : 0 < deriv (bleisteinW p α) α) (hqα : q α ≠ 0) :
    bleisteinAmplitude p q lam α s (bleisteinA p α) ≠ 0 := by
  rw [bleisteinAmplitude_bleisteinA (hmono.injOn.mono hsU) hαs]
  have hαU : α ∈ U := hsU hαs
  have hpos : 0 < (if bleisteinA p α = 0 then (deriv (bleisteinW p α) 0)⁻¹
      else α / bleisteinA p α) := by
    split_ifs with ha
    · have hα0 : α = 0 :=
        hmono.injOn hαU h0U (by rw [bleisteinW_self, bleisteinW_zero, ha])
      exact inv_pos.mpr (hα0 ▸ hw'α)
    · have hα0 : α ≠ 0 := by rintro rfl; exact ha (bleisteinA_zero p)
      rcases hα0.lt_or_gt with hlt | hgt
      · exact div_pos_of_neg_of_neg hlt
          (by simpa [bleisteinW_self, bleisteinW_zero] using hmono hαU h0U hlt)
      · exact div_pos hgt
          (by simpa [bleisteinW_self, bleisteinW_zero] using hmono h0U hαU hgt)
  exact smul_ne_zero (div_pos (Real.rpow_pos_of_pos hpos _) hw'α).ne' hqα

/-- When `α ∈ s`, `s ⊆ I`, `0 ∈ I`, and `q α ≠ 0`, the transformed amplitude is nonzero at
`w = bleisteinA p α` for all `α` (`α < 0`, `α = 0`, and `α > 0`). -/
theorem bleisteinAmplitude_self_ne_zero {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {p : ℝ → ℝ} {q : ℝ → E} {I s : Set ℝ} {lam α : ℝ}
    (hI : IsOpen I) (hord : OrdConnected I) (h0I : 0 ∈ I) (hαs : α ∈ s)
    (hs : s ⊆ I) (hp : ContDiffOn ℝ 2 p I) (hpα : deriv p α = 0)
    (hp''_pos : 0 < deriv (deriv p) α) (hp' : ∀ u ∈ I, u ≠ α → deriv p u ≠ 0) (hqα : q α ≠ 0) :
    bleisteinAmplitude p q lam α s (bleisteinA p α) ≠ 0 := by
  have hα : α ∈ I := hs hαs
  have hp'_cont : ContinuousOn (deriv p) I := hp.continuousOn_deriv_of_isOpen hI (by decide)
  have hanti := strictAntiOn_Iic_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hmono := strictMonoOn_Ici_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  exact bleisteinAmplitude_bleisteinA_ne_zero h0I hαs hs (strictMonoOn_bleisteinW hα hanti hmono)
    (deriv_bleisteinW_pos hI hord hα hp hpα hp''_pos hp' hα) hqα

/-- On an open subset `s ⊆ I`, the inverse map `invFunOn (bleisteinW p α) s` has strict derivative
`(deriv (bleisteinW p α) t)⁻¹` at every `w ∈ bleisteinW p α '' s`. -/
theorem hasStrictDerivAt_invFunOn_bleisteinW {p : ℝ → ℝ} {I s : Set ℝ} {α w : ℝ}
    (hI : IsOpen I) (hord : OrdConnected I) (hs_open : IsOpen s) (hs : s ⊆ I) (hα : α ∈ I)
    (hp : ContDiffOn ℝ 2 p I) (hpα : deriv p α = 0) (hp''_pos : 0 < deriv (deriv p) α)
    (hp' : ∀ u ∈ I, u ≠ α → deriv p u ≠ 0) (hw : w ∈ bleisteinW p α '' s) :
    HasStrictDerivAt (invFunOn (bleisteinW p α) s)
      (deriv (bleisteinW p α) (invFunOn (bleisteinW p α) s w))⁻¹ w := by
  have hp'_cont : ContinuousOn (deriv p) I := hp.continuousOn_deriv_of_isOpen hI (by decide)
  have hanti := strictAntiOn_Iic_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hmono := strictMonoOn_Ici_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hinj : InjOn (bleisteinW p α) s := ((strictMonoOn_bleisteinW hα hanti hmono).mono hs).injOn
  let t := invFunOn (bleisteinW p α) s w
  have hts : t ∈ s := Function.invFunOn_mem hw
  have hstrict : HasStrictDerivAt (bleisteinW p α) (deriv (bleisteinW p α) t) t :=
    hasStrictDerivAt_bleisteinW hI hα (hp.of_le one_le_two)
      (fun u hu hne => lt_of_strictAntiOn_strictMonoOn hα hanti hmono hu hne) hp''_pos (hs hts)
  have hpos : 0 < deriv (bleisteinW p α) t :=
    deriv_bleisteinW_pos hI hord hα hp hpα hp''_pos hp' (hs hts)
  simpa only [t, Function.invFunOn_eq hw] using
    hstrict.invFunOn hpos.ne' (hs_open.mem_nhds hts) hinj

/-- Continuity of `bleisteinAmplitude p q lam α U` on `bleisteinW p α '' s` for any subset
`s ⊆ U` of an open domain `U` containing `0` (covering `w = 0` when `0 ∈ s`, and
`w = bleisteinA p α` whenever `α ∈ s`, including `α ≤ 0`). -/
theorem continuousOn_bleisteinAmplitude_of_zero_mem {E : Type*} [TopologicalSpace E] [SMul ℝ E]
    [ContinuousSMul ℝ E] {p : ℝ → ℝ} {q : ℝ → E} {lam α : ℝ} {U s : Set ℝ}
    (hsU : s ⊆ U) (hU : IsOpen U) (h0 : 0 ∈ U) (hw : ContDiffOn ℝ 1 (bleisteinW p α) U)
    (hmono : StrictMonoOn (bleisteinW p α) U)
    (hw' : ∀ t ∈ U, 0 < deriv (bleisteinW p α) t) (hq : ContinuousOn q s) :
    ContinuousOn (bleisteinAmplitude p q lam α U) (bleisteinW p α '' s) := by
  have hinj : InjOn (bleisteinW p α) U := hmono.injOn
  have hw'_ne : ∀ t ∈ U, deriv (bleisteinW p α) t ≠ 0 := fun t ht => (hw' t ht).ne'
  have hU0 : U ∈ 𝓝 (0 : ℝ) := hU.mem_nhds h0
  have hstrict0 : HasStrictDerivAt (bleisteinW p α) (deriv (bleisteinW p α) 0) 0 :=
    (hw.contDiffAt hU0).hasStrictDerivAt_deriv one_ne_zero
  have hdslope_cont : ContinuousOn (dslope (invFunOn (bleisteinW p α) U) 0)
      (bleisteinW p α '' U) :=
    bleisteinW_zero p α ▸ hw.continuousOn_dslope_invFunOn one_ne_zero hU h0 hinj hw'_ne
  have hrpow : ContinuousOn
      (fun w => dslope (invFunOn (bleisteinW p α) U) 0 w ^ (lam - 1))
      (bleisteinW p α '' U) :=
    hdslope_cont.rpow_const fun _ hw_mem => Or.inl
      (bleisteinW_zero p α ▸ hmono.dslope_invFunOn_pos h0 hw_mem hU0 hstrict0 (hw' 0 h0)).ne'
  have hmapsU : MapsTo (invFunOn (bleisteinW p α) U) (bleisteinW p α '' U) U :=
    fun _ hw_mem => invFunOn_mem hw_mem
  have hmaps : MapsTo (invFunOn (bleisteinW p α) U) (bleisteinW p α '' s) s := by
    rintro _ ⟨t, ht, rfl⟩; rwa [hinj.leftInvOn_invFunOn (hsU ht)]
  have hinv_cont : ContinuousOn (invFunOn (bleisteinW p α) U) (bleisteinW p α '' U) :=
    (hw.invFunOn one_ne_zero hU hinj hw'_ne).continuousOn
  have hscalar : ContinuousOn
      (fun w => (dslope (invFunOn (bleisteinW p α) U) 0 w ^ (lam - 1)) /
        deriv (bleisteinW p α) (invFunOn (bleisteinW p α) U w))
      (bleisteinW p α '' U) :=
    hrpow.div ((hw.continuousOn_deriv_of_isOpen hU le_rfl).comp hinv_cont hmapsU)
      fun _ hw_mem => hw'_ne _ (hmapsU hw_mem)
  have hsub : bleisteinW p α '' s ⊆ bleisteinW p α '' U := image_mono hsU
  exact ((hscalar.mono hsub).smul (hq.comp (hinv_cont.mono hsub) hmaps)).congr fun w _ =>
    bleisteinAmplitude_eq_dslope h0 hU0 hinj hstrict0 (hw'_ne 0 h0)

/-- Continuity of `bleisteinAmplitude p q lam α s` on `bleisteinW p α '' s` for an open set
`s ⊆ (0, ∞)` on which `bleisteinW p α` is `C¹`, injective, and positive with nonvanishing
derivative, when `q` is continuous on `s`. -/
theorem continuousOn_bleisteinAmplitude_of_injOn {E : Type*} [TopologicalSpace E] [SMul ℝ E]
    [ContinuousSMul ℝ E] {p : ℝ → ℝ} {q : ℝ → E} {s : Set ℝ}
    {lam α : ℝ} (hs : IsOpen s) (hs0 : s ⊆ Ioi 0) (hw : ContDiffOn ℝ 1 (bleisteinW p α) s)
    (hinj : InjOn (bleisteinW p α) s) (hw_pos : ∀ t ∈ s, 0 < bleisteinW p α t)
    (hd : ∀ t ∈ s, deriv (bleisteinW p α) t ≠ 0) (hq : ContinuousOn q s) :
    ContinuousOn (bleisteinAmplitude p q lam α s) (bleisteinW p α '' s) := by
  have hinv_cont : ContinuousOn (invFunOn (bleisteinW p α) s) (bleisteinW p α '' s) :=
    (hw.invFunOn one_ne_zero hs hinj hd).continuousOn
  have hmaps : MapsTo (invFunOn (bleisteinW p α) s) (bleisteinW p α '' s) s :=
    fun _ hw_mem => invFunOn_mem hw_mem
  have hw_deriv_cont : ContinuousOn (deriv (bleisteinW p α)) s :=
    hw.continuousOn_deriv_of_isOpen hs le_rfl
  have hrat : ContinuousOn (fun w => (invFunOn (bleisteinW p α) s w / w) ^ (lam - 1))
      (bleisteinW p α '' s) := by
    refine ContinuousOn.rpow_const (hinv_cont.div continuousOn_id ?_) ?_
    · rintro _ ⟨t, ht, rfl⟩
      exact (hw_pos t ht).ne'
    · rintro _ ⟨t, ht, rfl⟩
      exact Or.inl (div_pos (hs0 (hmaps ⟨t, ht, rfl⟩)) (hw_pos t ht)).ne'
  have hden : ContinuousOn (fun w => deriv (bleisteinW p α) (invFunOn (bleisteinW p α) s w))
      (bleisteinW p α '' s) :=
    hw_deriv_cont.comp hinv_cont hmaps
  have hcoef : ContinuousOn (fun w => (invFunOn (bleisteinW p α) s w / w) ^ (lam - 1) /
      deriv (bleisteinW p α) (invFunOn (bleisteinW p α) s w)) (bleisteinW p α '' s) :=
    hrat.div hden fun _ hw_mem => hd _ (hmaps hw_mem)
  refine (hcoef.smul (hq.comp hinv_cont hmaps)).congr ?_
  rintro _ ⟨t, ht, rfl⟩
  exact bleisteinAmplitude_of_ne_zero p q lam α s (hw_pos t ht).ne'

/-- Continuity of `bleisteinAmplitude` on `bleisteinW p α '' s` for an open domain
`s ⊆ I ∩ (0, ∞)` when `q` is continuous on `s`. -/
theorem continuousOn_bleisteinAmplitude {E : Type*} [TopologicalSpace E] [SMul ℝ E]
    [ContinuousSMul ℝ E] {p : ℝ → ℝ} {q : ℝ → E} {I s : Set ℝ} {lam α : ℝ}
    (hI : IsOpen I) (hord : OrdConnected I) (h0I : 0 ∈ I) (hs_open : IsOpen s)
    (hs : s ⊆ I ∩ Ioi 0) (hα : α ∈ I) (hp : ContDiffOn ℝ 2 p I) (hpα : deriv p α = 0)
    (hp''_pos : 0 < deriv (deriv p) α) (hp' : ∀ u ∈ I, u ≠ α → deriv p u ≠ 0)
    (hq : ContinuousOn q s) :
    ContinuousOn (bleisteinAmplitude p q lam α s) (bleisteinW p α '' s) := by
  have hsI : s ⊆ I := fun u hu => (hs hu).1
  have hp'_cont : ContinuousOn (deriv p) I := hp.continuousOn_deriv_of_isOpen hI (by decide)
  have hanti := strictAntiOn_Iic_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hmono := strictMonoOn_Ici_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  exact continuousOn_bleisteinAmplitude_of_injOn hs_open (fun u hu => (hs hu).2)
    ((contDiffOn_bleisteinW hI hα (hp.of_le one_le_two)
      (fun u hu hne => lt_of_strictAntiOn_strictMonoOn hα hanti hmono hu hne) hp''_pos).mono hsI)
    ((strictMonoOn_bleisteinW hα hanti hmono).injOn.mono hsI)
    (fun t ht => bleisteinW_pos hα h0I hanti hmono (hsI ht) (hs ht).2)
    (fun t ht => (deriv_bleisteinW_pos hI hord hα hp hpα hp''_pos hp' (hsI ht)).ne') hq

/-! ### Change of variables under pointwise hypotheses on the coordinate -/

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pointwise Jacobian cancellation between the transformed integrand at `w = bleisteinW p α t`
and the original integrand at `t`. -/
private theorem abs_deriv_smul_bleistein_integrand {p : ℝ → ℝ} {q : ℝ → E} {s : Set ℝ}
    {lam α x t : ℝ} (ht : t ∈ s) (ht0 : 0 < t) (h0 : p α ≤ p 0) (hmin : p α ≤ p t)
    (hw_pos : 0 < bleisteinW p α t) (hinj : InjOn (bleisteinW p α) s)
    (hdpos : 0 < deriv (bleisteinW p α) t) :
    |deriv (bleisteinW p α) t| •
        ((Real.exp (-x * (bleisteinW p α t ^ 2 / 2 - bleisteinA p α * bleisteinW p α t)) *
          bleisteinW p α t ^ (lam - 1)) • bleisteinAmplitude p q lam α s (bleisteinW p α t)) =
      Real.exp (x * p 0) • ((Real.exp (-x * p t) * t ^ (lam - 1)) • q t) := by
  have hrpow : bleisteinW p α t ^ (lam - 1) * (t / bleisteinW p α t) ^ (lam - 1) =
      t ^ (lam - 1) := by
    rw [← Real.mul_rpow hw_pos.le (div_nonneg ht0.le hw_pos.le), mul_div_cancel₀ _ hw_pos.ne']
  have hexp : Real.exp (-x * (bleisteinW p α t ^ 2 / 2 - bleisteinA p α * bleisteinW p α t)) =
      Real.exp (x * p 0) * Real.exp (-x * p t) := by
    rw [bleistein_phase_sub_eq h0 hmin, ← Real.exp_add]
    congr 1
    ring
  rw [bleisteinAmplitude_bleisteinW hinj ht hw_pos.ne', abs_of_pos hdpos, smul_smul, smul_smul,
    smul_smul, hexp]
  congr 1
  calc deriv (bleisteinW p α) t *
        (Real.exp (x * p 0) * Real.exp (-x * p t) * bleisteinW p α t ^ (lam - 1)) *
        ((t / bleisteinW p α t) ^ (lam - 1) / deriv (bleisteinW p α) t)
      = Real.exp (x * p 0) * Real.exp (-x * p t) *
          (bleisteinW p α t ^ (lam - 1) * (t / bleisteinW p α t) ^ (lam - 1)) *
          (deriv (bleisteinW p α) t / deriv (bleisteinW p α) t) := by ring
    _ = Real.exp (x * p 0) * (Real.exp (-x * p t) * t ^ (lam - 1)) := by
          rw [hrpow, div_self hdpos.ne', mul_one, mul_assoc]

/-- Equivalence of integrability of the original Laplace-type integral (DLMF 2.3.24) on a
measurable set `s ⊆ (0, ∞)` and of Bleistein's transformed integral (DLMF 2.3.29) on
`bleisteinW p α '' s`, assuming only that `p α` bounds `p` from below on `s ∪ {0}` and that
`bleisteinW p α` is positive, injective, and has positive derivative on `s`. -/
theorem integrableOn_bleistein_iff_of_deriv_pos {p : ℝ → ℝ} {q : ℝ → E} {s : Set ℝ}
    {lam α x : ℝ} (hs : MeasurableSet s) (hs0 : s ⊆ Ioi 0) (h0 : p α ≤ p 0)
    (hmin : ∀ t ∈ s, p α ≤ p t) (hw_pos : ∀ t ∈ s, 0 < bleisteinW p α t)
    (hinj : InjOn (bleisteinW p α) s) (hdpos : ∀ t ∈ s, 0 < deriv (bleisteinW p α) t) :
    IntegrableOn (fun w =>
      (Real.exp (-x * (w ^ 2 / 2 - bleisteinA p α * w)) * w ^ (lam - 1)) •
        bleisteinAmplitude p q lam α s w) (bleisteinW p α '' s) ↔
      IntegrableOn (fun t => (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) s := by
  have hderiv : ∀ t ∈ s, HasDerivWithinAt (bleisteinW p α) (deriv (bleisteinW p α) t) s t :=
    fun t ht => (differentiableAt_of_deriv_ne_zero (hdpos t ht).ne').hasDerivAt.hasDerivWithinAt
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul hs hderiv hinj,
    integrableOn_congr_fun (fun t ht => abs_deriv_smul_bleistein_integrand ht (hs0 ht) h0
      (hmin t ht) (hw_pos t ht) hinj (hdpos t ht)) hs]
  exact integrable_smul_iff (Real.exp_ne_zero (x * p 0)) _

/-- Bleistein's change of variables (DLMF 2.3.24, 2.3.29–2.3.30) scaled by `exp (x * p 0)`, under
the pointwise hypotheses of `TauCeti.integrableOn_bleistein_iff_of_deriv_pos`. -/
theorem exp_smul_integral_bleistein_eq {p : ℝ → ℝ} {q : ℝ → E} {s : Set ℝ} {lam α x : ℝ}
    (hs : MeasurableSet s) (hs0 : s ⊆ Ioi 0) (h0 : p α ≤ p 0)
    (hmin : ∀ t ∈ s, p α ≤ p t) (hw_pos : ∀ t ∈ s, 0 < bleisteinW p α t)
    (hinj : InjOn (bleisteinW p α) s) (hdpos : ∀ t ∈ s, 0 < deriv (bleisteinW p α) t) :
    Real.exp (x * p 0) • (∫ t in s, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) =
      ∫ w in bleisteinW p α '' s,
        (Real.exp (-x * (w ^ 2 / 2 - bleisteinA p α * w)) * w ^ (lam - 1)) •
          bleisteinAmplitude p q lam α s w := by
  have hderiv : ∀ t ∈ s, HasDerivWithinAt (bleisteinW p α) (deriv (bleisteinW p α) t) s t :=
    fun t ht => (differentiableAt_of_deriv_ne_zero (hdpos t ht).ne').hasDerivAt.hasDerivWithinAt
  rw [integral_image_eq_integral_abs_deriv_smul hs hderiv hinj,
    setIntegral_congr_fun hs (fun t ht => abs_deriv_smul_bleistein_integrand ht (hs0 ht) h0
      (hmin t ht) (hw_pos t ht) hinj (hdpos t ht)),
    integral_smul]

/-- Unscaled form of `TauCeti.exp_smul_integral_bleistein_eq` (DLMF 2.3.29). -/
theorem integral_bleistein_eq_of_deriv_pos {p : ℝ → ℝ} {q : ℝ → E} {s : Set ℝ} {lam α x : ℝ}
    (hs : MeasurableSet s) (hs0 : s ⊆ Ioi 0) (h0 : p α ≤ p 0)
    (hmin : ∀ t ∈ s, p α ≤ p t) (hw_pos : ∀ t ∈ s, 0 < bleisteinW p α t)
    (hinj : InjOn (bleisteinW p α) s) (hdpos : ∀ t ∈ s, 0 < deriv (bleisteinW p α) t) :
    ∫ t in s, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t =
      Real.exp (-x * p 0) • ∫ w in bleisteinW p α '' s,
        (Real.exp (-x * (w ^ 2 / 2 - bleisteinA p α * w)) * w ^ (lam - 1)) •
          bleisteinAmplitude p q lam α s w := by
  rw [← exp_smul_integral_bleistein_eq hs hs0 h0 hmin hw_pos hinj hdpos, smul_smul,
    ← Real.exp_add, (by ring : -x * p 0 + x * p 0 = 0), Real.exp_zero, one_smul]

/-! ### Change of variables for a unique nondegenerate critical point -/

/-- Equivalence of integrability between the original Laplace-type integral (DLMF 2.3.24) on a
measurable set `s ⊆ I ∩ (0, ∞)` and the Bleistein-transformed integral (DLMF 2.3.29) on
`bleisteinW p α '' s`, when `deriv p` vanishes only at `α`. -/
theorem integrableOn_bleistein_iff {p : ℝ → ℝ} {q : ℝ → E} {I s : Set ℝ} {lam α x : ℝ}
    (hI : IsOpen I) (hord : OrdConnected I) (h0I : 0 ∈ I) (hs_meas : MeasurableSet s)
    (hs : s ⊆ I ∩ Ioi 0) (hα : α ∈ I) (hp : ContDiffOn ℝ 2 p I) (hpα : deriv p α = 0)
    (hp''_pos : 0 < deriv (deriv p) α) (hp' : ∀ u ∈ I, u ≠ α → deriv p u ≠ 0) :
    IntegrableOn (fun w =>
      (Real.exp (-x * (w ^ 2 / 2 - bleisteinA p α * w)) * w ^ (lam - 1)) •
        bleisteinAmplitude p q lam α s w) (bleisteinW p α '' s) ↔
      IntegrableOn (fun t => (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) s := by
  have hp'_cont : ContinuousOn (deriv p) I := hp.continuousOn_deriv_of_isOpen hI (by decide)
  have hanti := strictAntiOn_Iic_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hmono := strictMonoOn_Ici_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hle : ∀ u ∈ I, p α ≤ p u :=
    fun u hu => le_of_antitoneOn_monotoneOn hα hanti.antitoneOn hmono.monotoneOn hu
  exact integrableOn_bleistein_iff_of_deriv_pos hs_meas (fun u hu => (hs hu).2) (hle 0 h0I)
    (fun t ht => hle t (hs ht).1)
    (fun t ht => bleisteinW_pos hα h0I hanti hmono (hs ht).1 (hs ht).2)
    ((strictMonoOn_bleisteinW hα hanti hmono).injOn.mono fun u hu => (hs hu).1)
    (fun t ht => deriv_bleisteinW_pos hI hord hα hp hpα hp''_pos hp' (hs ht).1)

/-- Bleistein's change-of-variables formula (DLMF 2.3.24, 2.3.29–2.3.30) on a measurable set
`s ⊆ I ∩ (0, ∞)` when `α` is the unique critical point of `p` on `I`. -/
theorem integral_bleistein_eq {p : ℝ → ℝ} {q : ℝ → E} {I s : Set ℝ} {lam α x : ℝ}
    (hI : IsOpen I) (hord : OrdConnected I) (h0I : 0 ∈ I) (hs_meas : MeasurableSet s)
    (hs : s ⊆ I ∩ Ioi 0) (hα : α ∈ I) (hp : ContDiffOn ℝ 2 p I) (hpα : deriv p α = 0)
    (hp''_pos : 0 < deriv (deriv p) α) (hp' : ∀ u ∈ I, u ≠ α → deriv p u ≠ 0) :
    ∫ t in s, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t =
      Real.exp (-x * p 0) • ∫ w in bleisteinW p α '' s,
        (Real.exp (-x * (w ^ 2 / 2 - bleisteinA p α * w)) * w ^ (lam - 1)) •
          bleisteinAmplitude p q lam α s w := by
  have hp'_cont : ContinuousOn (deriv p) I := hp.continuousOn_deriv_of_isOpen hI (by decide)
  have hanti := strictAntiOn_Iic_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hmono := strictMonoOn_Ici_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hle : ∀ u ∈ I, p α ≤ p u :=
    fun u hu => le_of_antitoneOn_monotoneOn hα hanti.antitoneOn hmono.monotoneOn hu
  exact integral_bleistein_eq_of_deriv_pos hs_meas (fun u hu => (hs hu).2) (hle 0 h0I)
    (fun t ht => hle t (hs ht).1)
    (fun t ht => bleisteinW_pos hα h0I hanti hmono (hs ht).1 (hs ht).2)
    ((strictMonoOn_bleisteinW hα hanti hmono).injOn.mono fun u hu => (hs hu).1)
    (fun t ht => deriv_bleisteinW_pos hI hord hα hp hpα hp''_pos hp' (hs ht).1)

/-- Bleistein's change of variables on a finite interval `(0, k)` with finite upper limit
`κ = lim_{t → k⁻} bleisteinW p α t` (DLMF 2.3.29). -/
theorem integral_bleistein_Ioo_eq_of_tendsto_nhds {p : ℝ → ℝ} {q : ℝ → E} {I : Set ℝ}
    {lam α k κ x : ℝ} (hk : 0 < k) (hI : IsOpen I) (hord : OrdConnected I) (hsub : Ico 0 k ⊆ I)
    (hα : α ∈ I) (hp : ContDiffOn ℝ 2 p I) (hpα : deriv p α = 0)
    (hp''_pos : 0 < deriv (deriv p) α) (hp' : ∀ u ∈ I, u ≠ α → deriv p u ≠ 0)
    (hκ : Tendsto (bleisteinW p α) (𝓝[<] k) (𝓝 κ)) :
    ∫ t in Ioo 0 k, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t =
      Real.exp (-x * p 0) • ∫ w in Ioo 0 κ,
        (Real.exp (-x * (w ^ 2 / 2 - bleisteinA p α * w)) * w ^ (lam - 1)) •
          bleisteinAmplitude p q lam α (Ioo 0 k) w := by
  have hp'_cont : ContinuousOn (deriv p) I := hp.continuousOn_deriv_of_isOpen hI (by decide)
  have hanti := strictAntiOn_Iic_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hmono := strictMonoOn_Ici_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  rw [integral_bleistein_eq hI hord (hsub ⟨le_rfl, hk⟩) measurableSet_Ioo
    (fun u hu => ⟨hsub ⟨hu.1.le, hu.2⟩, hu.1⟩) hα hp hpα hp''_pos hp',
    image_bleisteinW_Ioo_of_tendsto_nhds hk hsub hα (hp.continuousOn.mono hsub) hanti hmono hκ]

/-- Bleistein's change of variables on `(0, k)` when `bleisteinW p α t → +∞` as `t → k⁻`
(`κ = ∞`, DLMF 2.3.29). -/
theorem integral_bleistein_Ioo_eq_of_tendsto_atTop {p : ℝ → ℝ} {q : ℝ → E} {I : Set ℝ}
    {lam α k x : ℝ} (hk : 0 < k) (hI : IsOpen I) (hord : OrdConnected I) (hsub : Ico 0 k ⊆ I)
    (hα : α ∈ I) (hp : ContDiffOn ℝ 2 p I) (hpα : deriv p α = 0)
    (hp''_pos : 0 < deriv (deriv p) α) (hp' : ∀ u ∈ I, u ≠ α → deriv p u ≠ 0)
    (hκ : Tendsto (bleisteinW p α) (𝓝[<] k) atTop) :
    ∫ t in Ioo 0 k, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t =
      Real.exp (-x * p 0) • ∫ w in Ioi 0,
        (Real.exp (-x * (w ^ 2 / 2 - bleisteinA p α * w)) * w ^ (lam - 1)) •
          bleisteinAmplitude p q lam α (Ioo 0 k) w := by
  have hp'_cont : ContinuousOn (deriv p) I := hp.continuousOn_deriv_of_isOpen hI (by decide)
  have hanti := strictAntiOn_Iic_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hmono := strictMonoOn_Ici_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  rw [integral_bleistein_eq hI hord (hsub ⟨le_rfl, hk⟩) measurableSet_Ioo
    (fun u hu => ⟨hsub ⟨hu.1.le, hu.2⟩, hu.1⟩) hα hp hpα hp''_pos hp',
    image_bleisteinW_Ioo_of_tendsto_atTop hk hsub hα (hp.continuousOn.mono hsub) hanti hmono hκ]

/-- Bleistein's change of variables on `(0, ∞)` with finite upper limit
`κ = lim_{t → +∞} bleisteinW p α t` (DLMF 2.3.29). -/
theorem integral_bleistein_Ioi_eq_of_tendsto_nhds {p : ℝ → ℝ} {q : ℝ → E} {I : Set ℝ}
    {lam α κ x : ℝ} (hI : IsOpen I) (hord : OrdConnected I) (hsub : Ici 0 ⊆ I) (hα : α ∈ I)
    (hp : ContDiffOn ℝ 2 p I) (hpα : deriv p α = 0) (hp''_pos : 0 < deriv (deriv p) α)
    (hp' : ∀ u ∈ I, u ≠ α → deriv p u ≠ 0) (hκ : Tendsto (bleisteinW p α) atTop (𝓝 κ)) :
    ∫ t in Ioi 0, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t =
      Real.exp (-x * p 0) • ∫ w in Ioo 0 κ,
        (Real.exp (-x * (w ^ 2 / 2 - bleisteinA p α * w)) * w ^ (lam - 1)) •
          bleisteinAmplitude p q lam α (Ioi 0) w := by
  have hp'_cont : ContinuousOn (deriv p) I := hp.continuousOn_deriv_of_isOpen hI (by decide)
  have hanti := strictAntiOn_Iic_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hmono := strictMonoOn_Ici_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  rw [integral_bleistein_eq hI hord (hsub le_rfl) measurableSet_Ioi
    (fun u hu => ⟨hsub hu.le, hu⟩) hα hp hpα hp''_pos hp',
    image_bleisteinW_Ioi_of_tendsto_nhds hsub hα (hp.continuousOn.mono hsub) hanti hmono hκ]

/-- Bleistein's change of variables on `(0, ∞)` when `bleisteinW p α t → +∞` at `+∞`
(`κ = ∞`, DLMF 2.3.29). -/
theorem integral_bleistein_Ioi_eq_of_tendsto_atTop {p : ℝ → ℝ} {q : ℝ → E} {I : Set ℝ}
    {lam α x : ℝ} (hI : IsOpen I) (hord : OrdConnected I) (hsub : Ici 0 ⊆ I) (hα : α ∈ I)
    (hp : ContDiffOn ℝ 2 p I) (hpα : deriv p α = 0) (hp''_pos : 0 < deriv (deriv p) α)
    (hp' : ∀ u ∈ I, u ≠ α → deriv p u ≠ 0) (hκ : Tendsto (bleisteinW p α) atTop atTop) :
    ∫ t in Ioi 0, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t =
      Real.exp (-x * p 0) • ∫ w in Ioi 0,
        (Real.exp (-x * (w ^ 2 / 2 - bleisteinA p α * w)) * w ^ (lam - 1)) •
          bleisteinAmplitude p q lam α (Ioi 0) w := by
  have hp'_cont : ContinuousOn (deriv p) I := hp.continuousOn_deriv_of_isOpen hI (by decide)
  have hanti := strictAntiOn_Iic_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hmono := strictMonoOn_Ici_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  rw [integral_bleistein_eq hI hord (hsub le_rfl) measurableSet_Ioi
    (fun u hu => ⟨hsub hu.le, hu⟩) hα hp hpα hp''_pos hp',
    image_bleisteinW_Ioi_of_tendsto_atTop hsub hα (hp.continuousOn.mono hsub) hanti hmono hκ]

end Integral

end TauCeti
