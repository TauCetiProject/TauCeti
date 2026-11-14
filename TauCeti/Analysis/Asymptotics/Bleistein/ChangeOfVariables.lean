/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.Calculus.DerivativeTest

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
taking values in a real normed space `E` (including `ℝ` and `ℂ`). It establishes the exact quadratic
phase identity, continuity and strict monotonicity of `bleisteinW`, `C¹` regularity across the
critical point `t = α`, strict differentiability of the inverse map, continuity of the transformed
amplitude, characterizations of the upper integration limit `κ(α) = lim_{t → k} w(α, t)` (together
with an explicit bounded-phase example on `(0, ∞)` showing that `k = ∞` alone does not force
`κ = ∞`), and the one-dimensional change-of-variables formulas for both integrability and the
Bochner integral.

## Main definitions

* `TauCeti.bleisteinA`: the transformed critical point
  `sgn(α) * √(2 * (p 0 - p α))` (DLMF 2.3.26).
* `TauCeti.bleisteinW`: Bleistein's coordinate
  `bleisteinA p α + sgn(t - α) * √(2 * (p t - p α))` (DLMF 2.3.25).
* `TauCeti.bleisteinAmplitude`: the transformed amplitude
  `((t / w) ^ (λ - 1) / deriv (bleisteinW p α) t) • q t` at `t = invFunOn (bleisteinW p α) s w`
  (DLMF 2.3.30).

## Main results

* `TauCeti.bleistein_phase_eq`: `bleisteinW p α t ^ 2 / 2 - bleisteinA p α * bleisteinW p α t + p 0
  = p t` whenever `p α ≤ p 0` and `p α ≤ p t`.
* `TauCeti.continuousOn_bleisteinW`, `TauCeti.strictMonoOn_bleisteinW`, and
  `TauCeti.contDiffOn_bleisteinW`: `bleisteinW p α` is continuous wherever `p` is continuous,
  strictly increasing under strict monotonicity away from `α`, and `C¹` across `t = α` for `C²`
  phases, with positive derivative `√(deriv (deriv p) α)` at `t = α`
  (`TauCeti.hasDerivAt_bleisteinW_self`) and derivative `(deriv p t) / (w - a)` away from `α`
  (`TauCeti.hasDerivAt_bleisteinW_of_ne`, DLMF 2.3.28).
* `TauCeti.hasStrictDerivAt_invFunOn_bleisteinW` and `TauCeti.continuousOn_bleisteinAmplitude`:
  strict differentiability of the inverse coordinate and continuity of the transformed amplitude
  when `deriv p` vanishes only at `α`.
* `TauCeti.integrableOn_bleistein_iff` and `TauCeti.integral_bleistein_eq`: equivalence of
  integrability and equality of the original and transformed integrals (DLMF 2.3.24, 2.3.29),
  together with interval specializations on `(0, k)` and `(0, ∞)`.

## References

* NIST *Digital Library of Mathematical Functions*, §2.3(v), formulas 2.3.24–2.3.30,
  <https://dlmf.nist.gov/2.3#v>.
* N. Bleistein, *Uniform asymptotic expansions of integrals with stationary point near algebraic
  singularity*, Comm. Pure Appl. Math. 19 (1966), 353–370.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 9, §9.
-/

public section

open Filter Function MeasureTheory Set
open scoped Topology

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

/-- When `α ≠ 0` and `p α < p 0`, `bleisteinA p α` is nonzero. -/
theorem bleisteinA_ne_zero {p : ℝ → ℝ} {α : ℝ} (hα : α ≠ 0) (hp : p α < p 0) :
    bleisteinA p α ≠ 0 :=
  hα.lt_or_gt.elim (fun h => (bleisteinA_neg h hp).ne) fun h => (bleisteinA_pos h hp).ne'

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

/-- Bleistein's coordinate `bleisteinW p α` is continuous on any set `s` where `p` is
continuous. -/
theorem continuousOn_bleisteinW {p : ℝ → ℝ} {s : Set ℝ} (hp : ContinuousOn p s) (α : ℝ) :
    ContinuousOn (bleisteinW p α) s := by
  intro t ht
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
          simpa using ((hp t ht).tendsto.sub_const (p t)).const_mul 2
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
        (((hp t ht).sub continuousWithinAt_const).const_mul 2)
    exact (continuousWithinAt_const.add (hsqrt.const_mul c)).congr_of_eventuallyEq
      hc_ev.symm (by simp [bleisteinW, c])

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

/-! ### Differentiability, `C¹` smoothness across the critical point, and positivity of `w'` -/

/-- Away from the critical point `t = α`, `bleisteinW p α` is differentiable whenever `p` is,
with derivative `p' / (bleisteinW p α t - bleisteinA p α)` (DLMF 2.3.28). -/
theorem hasDerivAt_bleisteinW_of_ne {p : ℝ → ℝ} {α t p' : ℝ} (hne : t ≠ α) (hpt : p α < p t)
    (hp : HasDerivAt p p' t) :
    HasDerivAt (bleisteinW p α) (p' / (bleisteinW p α t - bleisteinA p α)) t := by
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

/-- Value of `deriv (bleisteinW p α) t` away from `t = α` (DLMF 2.3.28). -/
theorem deriv_bleisteinW_of_ne {p : ℝ → ℝ} {α t : ℝ} (hne : t ≠ α) (hpt : p α < p t)
    (hp : DifferentiableAt ℝ p t) :
    deriv (bleisteinW p α) t = deriv p t / (bleisteinW p α t - bleisteinA p α) :=
  (hasDerivAt_bleisteinW_of_ne hne hpt hp.hasDerivAt).deriv

/-- At the critical point `t = α`, `bleisteinW p α` is differentiable with positive derivative
`√(p'')` whenever `deriv p α = 0` and `HasDerivAt (deriv p) p'' α` with `0 < p''`. -/
theorem hasDerivAt_bleisteinW_self {p : ℝ → ℝ} {α p'' : ℝ}
    (hp_diff : ∀ᶠ t in 𝓝 α, DifferentiableAt ℝ p t) (hpα : deriv p α = 0)
    (hp'' : HasDerivAt (deriv p) p'' α) (hp''_pos : 0 < p'') :
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
  filter_upwards [eventually_mem_nhdsWithin, hlim.eventually (eventually_gt_nhds hp''_pos)]
    with t ht hpos
  have hne : t - α ≠ 0 := sub_ne_zero.mpr (mem_compl_singleton_iff.mp ht)
  have hnum_nonneg : 0 ≤ 2 * (p t - p α) :=
    le_of_lt ((div_pos_iff_of_pos_right (sq_pos_of_ne_zero hne)).mp hpos)
  rw [slope_def_field, bleisteinW_self, bleisteinW_sub_bleisteinA,
    Real.sqrt_div hnum_nonneg, Real.sqrt_sq_eq_abs]
  have habs_ne : |t - α| ≠ 0 := abs_ne_zero.mpr hne
  field_simp [habs_ne, hne]
  linear_combination -Real.sqrt (2 * (p t - p α)) * sign_mul_abs (t - α)

/-- Value of `deriv (bleisteinW p α) α` at a nondegenerate minimum `α` of `p`. -/
theorem deriv_bleisteinW_self {p : ℝ → ℝ} {α p'' : ℝ}
    (hp_diff : ∀ᶠ t in 𝓝 α, DifferentiableAt ℝ p t) (hpα : deriv p α = 0)
    (hp'' : HasDerivAt (deriv p) p'' α) (hp''_pos : 0 < p'') :
    deriv (bleisteinW p α) α = Real.sqrt p'' :=
  (hasDerivAt_bleisteinW_self hp_diff hpα hp'' hp''_pos).deriv

/-- Bleistein's coordinate `bleisteinW p α` is `C¹` across the critical point `t = α` on an open
set `I` when `p` is `C²` on `I` with `deriv p α = 0`, `0 < deriv (deriv p) α`, and strict
monotonicity away from `α`. -/
theorem contDiffOn_bleisteinW {p : ℝ → ℝ} {I : Set ℝ} {α : ℝ} (hI : IsOpen I) (hα : α ∈ I)
    (hp : ContDiffOn ℝ 2 p I) (hpα : deriv p α = 0) (hp''_pos : 0 < deriv (deriv p) α)
    (hanti : StrictAntiOn p (I ∩ Iic α)) (hmono : StrictMonoOn p (I ∩ Ici α)) :
    ContDiffOn ℝ 1 (bleisteinW p α) I := by
  have hlt_of_ne : ∀ u ∈ I, u ≠ α → p α < p u := fun u hu hne =>
    hne.lt_or_gt.elim (fun h => hanti ⟨hu, h.le⟩ ⟨hα, le_rfl⟩ h)
      fun h => hmono ⟨hα, le_rfl⟩ ⟨hu, h.le⟩ h
  have hp_diff : ∀ t ∈ I, DifferentiableAt ℝ p t := fun t ht =>
    (hp.contDiffAt (hI.mem_nhds ht)).differentiableAt (by decide)
  have hp'_cd : ContDiffOn ℝ 1 (deriv p) I := hp.deriv_of_isOpen hI (by decide)
  have hp''_at : HasDerivAt (deriv p) (deriv (deriv p) α) α :=
    ((hp'_cd.contDiffAt (hI.mem_nhds hα)).differentiableAt one_ne_zero).hasDerivAt
  have hw_self : HasDerivAt (bleisteinW p α) (Real.sqrt (deriv (deriv p) α)) α :=
    hasDerivAt_bleisteinW_self (Filter.eventually_of_mem (hI.mem_nhds hα) hp_diff)
      hpα hp''_at hp''_pos
  have hw_diff : DifferentiableOn ℝ (bleisteinW p α) I := fun t ht => by
    rcases eq_or_ne α t with rfl | hne
    · exact hw_self.differentiableAt.differentiableWithinAt
    · exact (hasDerivAt_bleisteinW_of_ne hne.symm (hlt_of_ne t ht hne.symm)
        (hp_diff t ht).hasDerivAt).differentiableAt.differentiableWithinAt
  have h1 : (1 : WithTop ℕ∞) = (0 : WithTop ℕ∞) + 1 := rfl
  rw [h1, contDiffOn_succ_iff_deriv_of_isOpen hI]
  refine ⟨hw_diff, by simp, contDiffOn_zero.mpr fun t ht => ContinuousAt.continuousWithinAt ?_⟩
  rcases eq_or_ne α t with rfl | hne_at
  · rw [continuousAt_iff_punctured_nhds, hw_self.deriv]
    have hnum : Tendsto (fun u => (u - α)⁻¹ * (deriv p u - deriv p α))
        (𝓝[≠] α) (𝓝 (deriv (deriv p) α)) :=
      hasDerivAt_iff_tendsto_slope.mp hp''_at
    have hden : Tendsto (fun u => (u - α)⁻¹ * (bleisteinW p α u - bleisteinW p α α))
        (𝓝[≠] α) (𝓝 (Real.sqrt (deriv (deriv p) α))) :=
      hasDerivAt_iff_tendsto_slope.mp hw_self
    have hquot := hnum.div hden (Real.sqrt_pos.mpr hp''_pos).ne'
    rw [Real.div_sqrt] at hquot
    refine hquot.congr' ?_
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (hI.mem_nhds hα),
        eventually_mem_nhdsWithin] with u huI hu_ne
    have hne' : u ≠ α := mem_compl_singleton_iff.mp hu_ne
    have hpu : p α < p u := hlt_of_ne u huI hne'
    have hw_ne := bleisteinW_sub_bleisteinA_ne_zero hpu
    have hsub_ne : u - α ≠ 0 := sub_ne_zero.mpr hne'
    rw [Pi.div_apply, deriv_bleisteinW_of_ne hne' hpu (hp_diff u huI), hpα, sub_zero,
      bleisteinW_self]
    field_simp [hsub_ne, hw_ne]
  · have hne : t ≠ α := hne_at.symm
    have hpt : p α < p t := hlt_of_ne t ht hne
    have hw_cont : ContinuousAt (bleisteinW p α) t :=
      (continuousOn_bleisteinW hp.continuousOn α).continuousAt (hI.mem_nhds ht)
    have hp'_cont : ContinuousAt (deriv p) t :=
      (hp'_cd.continuousOn t ht).continuousAt (hI.mem_nhds ht)
    have hquot : ContinuousAt (fun u => deriv p u / (bleisteinW p α u - bleisteinA p α)) t :=
      hp'_cont.div (hw_cont.sub continuousAt_const) (bleisteinW_sub_bleisteinA_ne_zero hpt)
    refine hquot.congr (Filter.eventually_of_mem
      (inter_mem (hI.mem_nhds ht) (isOpen_ne.mem_nhds hne)) fun u ⟨huI, hu_ne⟩ => ?_)
    exact (deriv_bleisteinW_of_ne hu_ne (hlt_of_ne u huI hu_ne) (hp_diff u huI)).symm

/-- Strict differentiability of `bleisteinW p α` at every point of an open set `I` under the
hypotheses of `TauCeti.contDiffOn_bleisteinW`. -/
theorem hasStrictDerivAt_bleisteinW {p : ℝ → ℝ} {I : Set ℝ} {α t : ℝ}
    (hI : IsOpen I) (hα : α ∈ I) (hp : ContDiffOn ℝ 2 p I) (hpα : deriv p α = 0)
    (hp''_pos : 0 < deriv (deriv p) α) (hanti : StrictAntiOn p (I ∩ Iic α))
    (hmono : StrictMonoOn p (I ∩ Ici α)) (ht : t ∈ I) :
    HasStrictDerivAt (bleisteinW p α) (deriv (bleisteinW p α) t) t :=
  ((contDiffOn_bleisteinW hI hα hp hpα hp''_pos hanti hmono).contDiffAt
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
    rw [deriv_bleisteinW_of_ne hlt.ne hpt (hp_diff t ht), bleisteinW_sub_bleisteinA,
      sign_neg (sub_neg.mpr hlt), SignType.coe_neg_one, neg_one_mul]
    exact div_pos_of_neg_of_neg hsign (neg_lt_zero.mpr (Real.sqrt_pos.mpr (by linarith)))
  · have hp''_at : HasDerivAt (deriv p) (deriv (deriv p) t) t :=
      (((hp.deriv_of_isOpen hI (by decide)).contDiffAt (hI.mem_nhds hα)).differentiableAt
        one_ne_zero).hasDerivAt
    rw [deriv_bleisteinW_self (Filter.eventually_of_mem (hI.mem_nhds hα) hp_diff)
      hpα hp''_at hp''_pos]
    exact Real.sqrt_pos.mpr hp''_pos
  · have hpt : p α < p t := hmono ⟨hα, le_rfl⟩ ⟨ht, hgt.le⟩ hgt
    have hsign := sign_deriv_eq_sign_sub hord hα hp'_cont hpα hp''_pos hp' ht
    rw [sign_pos (sub_pos.mpr hgt), sign_eq_one_iff] at hsign
    rw [deriv_bleisteinW_of_ne hgt.ne' hpt (hp_diff t ht), bleisteinW_sub_bleisteinA,
      sign_pos (sub_pos.mpr hgt), SignType.coe_one, one_mul]
    exact div_pos hsign (Real.sqrt_pos.mpr (by linarith))

/-! ### Upper integration limit `κ` and interval images -/

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

/-- Image of `(0, k)` under `bleisteinW p α` when `bleisteinW p α` approaches a finite limit `κ`
as `t → k⁻`. -/
theorem image_bleisteinW_Ioo_of_tendsto_nhds {p : ℝ → ℝ} {I : Set ℝ} {α k κ : ℝ}
    (hk : 0 < k) (hsub : Ico 0 k ⊆ I) (hα : α ∈ I) (hp : ContinuousOn p (Ico 0 k))
    (hanti : StrictAntiOn p (I ∩ Iic α)) (hmono : StrictMonoOn p (I ∩ Ici α))
    (hκ : Tendsto (bleisteinW p α) (𝓝[<] k) (𝓝 κ)) :
    bleisteinW p α '' Ioo 0 k = Ioo 0 κ := by
  have hw_cont : ContinuousOn (bleisteinW p α) (Ico 0 k) := continuousOn_bleisteinW hp α
  have hw_mono : StrictMonoOn (bleisteinW p α) I := strictMonoOn_bleisteinW hα hanti hmono
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨t, ht, rfl⟩
    have htI : t ∈ I := hsub ⟨ht.1.le, ht.2⟩
    refine ⟨by simpa [bleisteinW_zero] using hw_mono (hsub ⟨le_rfl, hk⟩) htI ht.1, ?_⟩
    obtain ⟨t', htt', ht'k⟩ := exists_between ht.2
    have ht'I : t' ∈ I := hsub ⟨(ht.1.trans htt').le, ht'k⟩
    refine (hw_mono htI ht'I htt').trans_le (ge_of_tendsto hκ ?_)
    filter_upwards [Ioo_mem_nhdsLT ht'k] with u hu
    exact (hw_mono ht'I (hsub ⟨(ht.1.trans (htt'.trans hu.1)).le, hu.2⟩) hu.1).le
  · have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Ico 0 k] 0 :=
      nhdsWithin_le_iff.mpr (mem_of_superset (Ioo_mem_nhdsGT hk) Ioo_subset_Ico_self)
    have ht₁ : Tendsto (bleisteinW p α) (𝓝[>] 0) (𝓝 0) := by
      simpa [bleisteinW_zero] using (hw_cont 0 ⟨le_rfl, hk⟩).mono_left hle
    exact isPreconnected_Ioo.intermediate_value_Ioo
      (le_principal_iff.mpr (Ioo_mem_nhdsGT hk)) (le_principal_iff.mpr (Ioo_mem_nhdsLT hk))
      (hw_cont.mono Ioo_subset_Ico_self) ht₁ hκ

/-- Image of `(0, k)` under `bleisteinW p α` when `bleisteinW p α → +∞` as `t → k⁻` (`κ = ∞`). -/
theorem image_bleisteinW_Ioo_of_tendsto_atTop {p : ℝ → ℝ} {I : Set ℝ} {α k : ℝ}
    (hk : 0 < k) (hsub : Ico 0 k ⊆ I) (hα : α ∈ I) (hp : ContinuousOn p (Ico 0 k))
    (hanti : StrictAntiOn p (I ∩ Iic α)) (hmono : StrictMonoOn p (I ∩ Ici α))
    (hκ : Tendsto (bleisteinW p α) (𝓝[<] k) atTop) :
    bleisteinW p α '' Ioo 0 k = Ioi 0 := by
  have hw_cont : ContinuousOn (bleisteinW p α) (Ico 0 k) := continuousOn_bleisteinW hp α
  have hw_mono : StrictMonoOn (bleisteinW p α) I := strictMonoOn_bleisteinW hα hanti hmono
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨t, ht, rfl⟩
    simpa [bleisteinW_zero] using hw_mono (hsub ⟨le_rfl, hk⟩) (hsub ⟨ht.1.le, ht.2⟩) ht.1
  · have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Ico 0 k] 0 :=
      nhdsWithin_le_iff.mpr (mem_of_superset (Ioo_mem_nhdsGT hk) Ioo_subset_Ico_self)
    have ht₁ : Tendsto (bleisteinW p α) (𝓝[>] 0) (𝓝 0) := by
      simpa [bleisteinW_zero] using (hw_cont 0 ⟨le_rfl, hk⟩).mono_left hle
    exact isPreconnected_Ioo.intermediate_value_Ioi
      (le_principal_iff.mpr (Ioo_mem_nhdsGT hk)) (le_principal_iff.mpr (Ioo_mem_nhdsLT hk))
      (hw_cont.mono Ioo_subset_Ico_self) ht₁ hκ

/-- Image of `(0, ∞)` under `bleisteinW p α` when `bleisteinW p α` approaches a finite limit `κ`
at `+∞`. -/
theorem image_bleisteinW_Ioi_of_tendsto_nhds {p : ℝ → ℝ} {I : Set ℝ} {α κ : ℝ}
    (hsub : Ici 0 ⊆ I) (hα : α ∈ I) (hp : ContinuousOn p (Ici 0))
    (hanti : StrictAntiOn p (I ∩ Iic α)) (hmono : StrictMonoOn p (I ∩ Ici α))
    (hκ : Tendsto (bleisteinW p α) atTop (𝓝 κ)) :
    bleisteinW p α '' Ioi 0 = Ioo 0 κ := by
  have hw_cont : ContinuousOn (bleisteinW p α) (Ici 0) := continuousOn_bleisteinW hp α
  have hw_mono : StrictMonoOn (bleisteinW p α) I := strictMonoOn_bleisteinW hα hanti hmono
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨t, ht : 0 < t, rfl⟩
    have ht1 : (0 : ℝ) ≤ t + 1 := by linarith
    refine ⟨by simpa [bleisteinW_zero] using hw_mono (hsub le_rfl) (hsub ht.le) ht, ?_⟩
    have hlt : bleisteinW p α t < bleisteinW p α (t + 1) :=
      hw_mono (hsub ht.le) (hsub ht1) (by linarith)
    refine hlt.trans_le (ge_of_tendsto hκ ?_)
    filter_upwards [eventually_ge_atTop (t + 1)] with u hu
    exact hw_mono.monotoneOn (hsub ht1) (hsub (ht1.trans hu)) hu
  · have ht₁ : Tendsto (bleisteinW p α) (𝓝[>] 0) (𝓝 0) := by
      simpa [bleisteinW_zero] using
        (hw_cont 0 le_rfl).mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
    exact isPreconnected_Ioi.intermediate_value_Ioo
      (le_principal_iff.mpr self_mem_nhdsWithin) (le_principal_iff.mpr (Ioi_mem_atTop 0))
      (hw_cont.mono Ioi_subset_Ici_self) ht₁ hκ

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
    have hsub : Tendsto (fun t => Real.sqrt (2 * (p t - 0))) atTop
        (𝓝 (Real.sqrt (2 * (1 - 0)))) :=
      (Real.continuous_sqrt.tendsto _).comp ((hlim_p.sub_const 0).const_mul 2)
    rw [sub_zero, mul_one] at hsub
    refine hsub.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp [bleisteinW, p, sign_pos ht]
  exact image_bleisteinW_Ioi_of_tendsto_nhds Subset.rfl (le_rfl : (0 : ℝ) ∈ Ici 0)
    hp_cont.continuousOn hanti hmono hlim_w

/-! ### Inverse coordinate, transformed amplitude, and change of variables -/

section Amplitude

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Transformed amplitude `f(α, w) = ((t / w) ^ (λ - 1) / deriv (bleisteinW p α) t) • q t`
evaluated at `t = invFunOn (bleisteinW p α) s w` (DLMF 2.3.30). Writing the Jacobian factor via
`deriv (bleisteinW p α) t` avoids the `0 / 0` indeterminacy of `(w - a) / deriv p t` at `t = α`. -/
noncomputable def bleisteinAmplitude (p : ℝ → ℝ) (q : ℝ → E) (lam α : ℝ) (s : Set ℝ) (w : ℝ) :
    E :=
  let t := invFunOn (bleisteinW p α) s w
  ((t / w) ^ (lam - 1) / deriv (bleisteinW p α) t) • q t

/-- Unfolding `TauCeti.bleisteinAmplitude`. -/
theorem bleisteinAmplitude_def (p : ℝ → ℝ) (q : ℝ → E) (lam α : ℝ) (s : Set ℝ) (w : ℝ) :
    bleisteinAmplitude p q lam α s w =
      ((invFunOn (bleisteinW p α) s w / w) ^ (lam - 1) /
        deriv (bleisteinW p α) (invFunOn (bleisteinW p α) s w)) •
        q (invFunOn (bleisteinW p α) s w) :=
  (rfl)

/-- Evaluating `bleisteinAmplitude` at `bleisteinW p α t` for `t ∈ s` recovers the original point
`t` whenever `bleisteinW p α` is injective on `s`. -/
theorem bleisteinAmplitude_bleisteinW {p : ℝ → ℝ} {q : ℝ → E} {lam α t : ℝ} {s : Set ℝ}
    (hinj : InjOn (bleisteinW p α) s) (ht : t ∈ s) :
    bleisteinAmplitude p q lam α s (bleisteinW p α t) =
      ((t / bleisteinW p α t) ^ (lam - 1) / deriv (bleisteinW p α) t) • q t := by
  rw [bleisteinAmplitude_def, hinj.leftInvOn_invFunOn ht]

/-- Value of `bleisteinAmplitude` at the transformed critical point `w = bleisteinA p α` when
`α ∈ s`. -/
theorem bleisteinAmplitude_self {p : ℝ → ℝ} {q : ℝ → E} {I s : Set ℝ} {lam α : ℝ}
    (hI : IsOpen I) (hord : OrdConnected I) (hαs : α ∈ s) (hs : s ⊆ I)
    (hp : ContDiffOn ℝ 2 p I) (hpα : deriv p α = 0) (hp''_pos : 0 < deriv (deriv p) α)
    (hp' : ∀ u ∈ I, u ≠ α → deriv p u ≠ 0) :
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
  rw [← bleisteinW_self p α, bleisteinAmplitude_bleisteinW hinj hαs, bleisteinW_self,
    deriv_bleisteinW_self (Filter.eventually_of_mem (hI.mem_nhds hα) hp_diff) hpα hp''_at hp''_pos]

/-- When `0 < α`, `α ∈ s`, `0 ∈ I`, and `q α ≠ 0`, the transformed amplitude is nonzero at
`w = bleisteinA p α`. -/
theorem bleisteinAmplitude_self_ne_zero {p : ℝ → ℝ} {q : ℝ → E} {I s : Set ℝ} {lam α : ℝ}
    (hI : IsOpen I) (hord : OrdConnected I) (h0I : 0 ∈ I) (hα_pos : 0 < α) (hαs : α ∈ s)
    (hs : s ⊆ I) (hp : ContDiffOn ℝ 2 p I) (hpα : deriv p α = 0)
    (hp''_pos : 0 < deriv (deriv p) α) (hp' : ∀ u ∈ I, u ≠ α → deriv p u ≠ 0) (hqα : q α ≠ 0) :
    bleisteinAmplitude p q lam α s (bleisteinA p α) ≠ 0 := by
  rw [bleisteinAmplitude_self hI hord hαs hs hp hpα hp''_pos hp']
  have hα : α ∈ I := hs hαs
  have hp'_cont : ContinuousOn (deriv p) I := hp.continuousOn_deriv_of_isOpen hI (by decide)
  have hanti := strictAntiOn_Iic_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hp0 : p α < p 0 := hanti ⟨h0I, hα_pos.le⟩ ⟨hα, le_rfl⟩ hα_pos
  have ha_pos : 0 < bleisteinA p α := bleisteinA_pos hα_pos hp0
  have hcoef_pos : 0 < (α / bleisteinA p α) ^ (lam - 1) / Real.sqrt (deriv (deriv p) α) :=
    div_pos (Real.rpow_pos_of_pos (div_pos hα_pos ha_pos) _) (Real.sqrt_pos.mpr hp''_pos)
  exact smul_ne_zero hcoef_pos.ne' hqα

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
  have htw : bleisteinW p α t = w := Function.invFunOn_eq hw
  have hstrict : HasStrictDerivAt (bleisteinW p α) (deriv (bleisteinW p α) t) t :=
    hasStrictDerivAt_bleisteinW hI hα hp hpα hp''_pos hanti hmono (hs hts)
  have hpos : 0 < deriv (bleisteinW p α) t :=
    deriv_bleisteinW_pos hI hord hα hp hpα hp''_pos hp' (hs hts)
  have hleft : ∀ᶠ u in 𝓝 t, invFunOn (bleisteinW p α) s (bleisteinW p α u) = u :=
    Filter.eventually_of_mem (hs_open.mem_nhds hts) fun u hu => hinj.leftInvOn_invFunOn hu
  simpa [t, htw] using hstrict.to_local_left_inverse hpos.ne' hleft

/-- Continuity of `bleisteinAmplitude` on `bleisteinW p α '' s` for an open domain
`s ⊆ I ∩ (0, ∞)` when `q` is continuous on `s`. -/
theorem continuousOn_bleisteinAmplitude {p : ℝ → ℝ} {q : ℝ → E} {I s : Set ℝ} {lam α : ℝ}
    (hI : IsOpen I) (hord : OrdConnected I) (h0I : 0 ∈ I) (hs_open : IsOpen s)
    (hs : s ⊆ I ∩ Ioi 0) (hα : α ∈ I) (hp : ContDiffOn ℝ 2 p I) (hpα : deriv p α = 0)
    (hp''_pos : 0 < deriv (deriv p) α) (hp' : ∀ u ∈ I, u ≠ α → deriv p u ≠ 0)
    (hq : ContinuousOn q s) :
    ContinuousOn (bleisteinAmplitude p q lam α s) (bleisteinW p α '' s) := by
  have hsI : s ⊆ I := fun u hu => (hs hu).1
  have hp'_cont : ContinuousOn (deriv p) I := hp.continuousOn_deriv_of_isOpen hI (by decide)
  have hanti := strictAntiOn_Iic_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hmono := strictMonoOn_Ici_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hw_mono := strictMonoOn_bleisteinW hα hanti hmono
  have hw_cd := contDiffOn_bleisteinW hI hα hp hpα hp''_pos hanti hmono
  have hw'_cont : ContinuousOn (deriv (bleisteinW p α)) I :=
    hw_cd.continuousOn_deriv_of_isOpen hI le_rfl
  have hinv_cont : ContinuousOn (invFunOn (bleisteinW p α) s) (bleisteinW p α '' s) := fun w hw =>
    (hasStrictDerivAt_invFunOn_bleisteinW hI hord hs_open hsI hα hp hpα hp''_pos hp' hw)
      |>.hasDerivAt.differentiableAt.continuousAt.continuousWithinAt
  have hmaps : MapsTo (invFunOn (bleisteinW p α) s) (bleisteinW p α '' s) s :=
    fun _ hw => Function.invFunOn_mem hw
  have hmapsI : MapsTo (invFunOn (bleisteinW p α) s) (bleisteinW p α '' s) I :=
    fun _ hw => hsI (Function.invFunOn_mem hw)
  have hw_pos_on : ∀ w ∈ bleisteinW p α '' s, 0 < w := by
    rintro _ ⟨t, ht, rfl⟩
    simpa [bleisteinW_zero] using hw_mono h0I (hsI ht) (hs ht).2
  have hratio_cont : ContinuousOn (fun w => invFunOn (bleisteinW p α) s w / w)
      (bleisteinW p α '' s) :=
    hinv_cont.div continuousOn_id fun w hw => (hw_pos_on w hw).ne'
  have hrpow_cont : ContinuousOn (fun w => (invFunOn (bleisteinW p α) s w / w) ^ (lam - 1))
      (bleisteinW p α '' s) :=
    ContinuousOn.rpow_const hratio_cont fun w hw =>
      Or.inl (div_pos (hs (hmaps hw)).2 (hw_pos_on w hw)).ne'
  have hcoef_cont : ContinuousOn (fun w =>
      (invFunOn (bleisteinW p α) s w / w) ^ (lam - 1) /
        deriv (bleisteinW p α) (invFunOn (bleisteinW p α) s w)) (bleisteinW p α '' s) :=
    hrpow_cont.div (hw'_cont.comp hinv_cont hmapsI) fun w hw =>
      (deriv_bleisteinW_pos hI hord hα hp hpα hp''_pos hp' (hmapsI hw)).ne'
  exact hcoef_cont.smul (hq.comp hinv_cont hmaps)

/-- Pointwise Jacobian identity relating the transformed integrand pulled back along
`bleisteinW p α` to the original integrand on `s ⊆ I ∩ (0, ∞)`. -/
private theorem bleistein_pullback_eq {p : ℝ → ℝ} {q : ℝ → E} {I s : Set ℝ} {lam α x t : ℝ}
    (hI : IsOpen I) (hord : OrdConnected I) (h0I : 0 ∈ I) (hs : s ⊆ I ∩ Ioi 0) (hα : α ∈ I)
    (hp : ContDiffOn ℝ 2 p I) (hpα : deriv p α = 0) (hp''_pos : 0 < deriv (deriv p) α)
    (hp' : ∀ u ∈ I, u ≠ α → deriv p u ≠ 0) (ht : t ∈ s) :
    deriv (bleisteinW p α) t •
        ((Real.exp (-x * (bleisteinW p α t ^ 2 / 2 - bleisteinA p α * bleisteinW p α t)) *
          bleisteinW p α t ^ (lam - 1)) •
          bleisteinAmplitude p q lam α s (bleisteinW p α t)) =
      Real.exp (x * p 0) • ((Real.exp (-x * p t) * t ^ (lam - 1)) • q t) := by
  have htI : t ∈ I := (hs ht).1
  have ht_pos : 0 < t := (hs ht).2
  have hp'_cont : ContinuousOn (deriv p) I := hp.continuousOn_deriv_of_isOpen hI (by decide)
  have hanti := strictAntiOn_Iic_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hmono := strictMonoOn_Ici_of_deriv_ne_zero hord hα hp.continuousOn hp'_cont hpα hp''_pos hp'
  have hle : ∀ u ∈ I, p α ≤ p u := fun u hu => by
    rcases lt_trichotomy u α with h | rfl | h
    · exact (hanti ⟨hu, h.le⟩ ⟨hα, le_rfl⟩ h).le
    · exact le_rfl
    · exact (hmono ⟨hα, le_rfl⟩ ⟨hu, h.le⟩ h).le
  have hw_mono := strictMonoOn_bleisteinW hα hanti hmono
  have hinj : InjOn (bleisteinW p α) s := (hw_mono.mono fun u hu => (hs hu).1).injOn
  have hw_pos : 0 < bleisteinW p α t := by
    simpa [bleisteinW_zero] using hw_mono h0I htI ht_pos
  have hw'_ne : deriv (bleisteinW p α) t ≠ 0 :=
    (deriv_bleisteinW_pos hI hord hα hp hpα hp''_pos hp' htI).ne'
  have hphase := bleistein_phase_sub_eq (hle 0 h0I) (hle t htI)
  rw [bleisteinAmplitude_bleisteinW hinj ht, hphase, smul_smul, smul_smul, smul_smul]
  congr 1
  have hrpow : bleisteinW p α t ^ (lam - 1) * (t / bleisteinW p α t) ^ (lam - 1) =
      t ^ (lam - 1) := by
    rw [← Real.mul_rpow hw_pos.le (div_nonneg ht_pos.le hw_pos.le),
      mul_div_cancel₀ _ hw_pos.ne']
  have hexp : Real.exp (-x * (p t - p 0)) = Real.exp (x * p 0) * Real.exp (-x * p t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp, ← hrpow]
  field_simp [hw'_ne]

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
  have hw_cd := contDiffOn_bleisteinW hI hα hp hpα hp''_pos hanti hmono
  have hw_deriv : ∀ t ∈ s, HasDerivWithinAt (bleisteinW p α) (deriv (bleisteinW p α) t) s t :=
    fun t ht => ((hw_cd.contDiffAt (hI.mem_nhds (hs ht).1)).differentiableAt
      one_ne_zero).hasDerivAt.hasDerivWithinAt
  have hw_mono : MonotoneOn (bleisteinW p α) s :=
    (strictMonoOn_bleisteinW hα hanti hmono).monotoneOn.mono fun u hu => (hs hu).1
  rw [integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn hs_meas hw_deriv hw_mono,
    integrableOn_congr_fun
      (fun t ht => bleistein_pullback_eq hI hord h0I hs hα hp hpα hp''_pos hp' ht) hs_meas]
  constructor
  · intro hint
    refine IntegrableOn.congr_fun (hint.smul (Real.exp (-x * p 0))) (fun t _ => ?_) hs_meas
    have hzero : -x * p 0 + x * p 0 = 0 := by ring
    rw [Pi.smul_apply, smul_smul, ← Real.exp_add, hzero, Real.exp_zero, one_smul]
  · exact fun hint => hint.smul (Real.exp (x * p 0))

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
  have hw_cd := contDiffOn_bleisteinW hI hα hp hpα hp''_pos hanti hmono
  have hw_deriv : ∀ t ∈ s, HasDerivWithinAt (bleisteinW p α) (deriv (bleisteinW p α) t) s t :=
    fun t ht => ((hw_cd.contDiffAt (hI.mem_nhds (hs ht).1)).differentiableAt
      one_ne_zero).hasDerivAt.hasDerivWithinAt
  have hw_mono : MonotoneOn (bleisteinW p α) s :=
    (strictMonoOn_bleisteinW hα hanti hmono).monotoneOn.mono fun u hu => (hs hu).1
  rw [integral_image_eq_integral_deriv_smul_of_monotoneOn hs_meas hw_deriv hw_mono,
    setIntegral_congr_fun hs_meas
      (fun t ht => bleistein_pullback_eq hI hord h0I hs hα hp hpα hp''_pos hp' ht)]
  have hzero : -x * p 0 + x * p 0 = 0 := by ring
  rw [integral_smul, smul_smul, ← Real.exp_add, hzero, Real.exp_zero, one_smul]

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

end Amplitude

end TauCeti
