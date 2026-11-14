/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Basic.Real.Sign
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Topology.Order.IntermediateValue

/-!
# Bleistein's change of variables for a saddle point coalescing with an endpoint

Consider a Laplace-type integral
`I(α, x) = ∫ t in s, exp (-x * g t) * t ^ (λ - 1) • q t`
over `s = (0, k)` or `s = (0, ∞)`, where the phase `g` (depending on an auxiliary parameter `α`)
has a simple minimum at `t = α` that may coalesce with the algebraic branch point at `t = 0`.
Standard Laplace's method and Watson's lemma lose uniformity as `α → 0` because the quadratic
saddle at `t = α` collides with the endpoint singularity `t ^ (λ - 1)` at `t = 0`.

Bleistein's canonical transformation maps `t` to a new variable `w = bleisteinCoord g α t` defined
by matching both critical points simultaneously: `w = 0` corresponds to the endpoint `t = 0` and
`w = a` (`a = bleisteinCenter g α`) corresponds to the saddle point `t = α`, so that the phase
becomes the exact quadratic polynomial

  `g t = w ^ 2 / 2 - a * w + g 0`

(DLMF 2.3.25). Explicitly, with `Real.sign 0 = 0`,

* `bleisteinCenter g α = Real.sign α * √(2 * (g 0 - g α))`,
* `bleisteinCoord g α t = bleisteinCenter g α + Real.sign (t - α) * √(2 * (g t - g α))`.

When `g` is strictly decreasing to the left of `α` and strictly increasing to the right of `α`,
`bleisteinCoord g α` is strictly increasing. If in addition `g` has vanishing first derivative and
positive second derivative at `α` and is `C²` on an open set `U` containing `α`, the apparent
square-root singularity at `t = α` cancels and `bleisteinCoord g α` is `C¹` on `U` with positive
derivative `√(g''(α))` at `α` and `g'(t) / (w - a)` away from `α` (DLMF 2.3.28). Changing
variables transforms `I(α, x)` into the canonical integral (DLMF 2.3.29–2.3.30)

  `exp (-x * g 0) • ∫ w in bleisteinCoord g α '' s,
      (exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (λ - 1)) • bleisteinAmplitude λ g q s α w`.

## Main definitions

* `TauCeti.bleisteinCenter`: the canonical saddle location
  `a(α) = Real.sign α * √(2 * (g 0 - g α))`.
* `TauCeti.bleisteinCoord`: Bleistein's canonical coordinate
  `w(α, t) = bleisteinCenter g α + Real.sign (t - α) * √(2 * (g t - g α))`.
* `TauCeti.bleisteinInv`: the inverse coordinate `t(w)` on a domain `s`.
* `TauCeti.bleisteinAmplitude`: the transformed amplitude
  `((t / w) ^ (λ - 1) / deriv (bleisteinCoord g α) t) • q t` with `t = bleisteinInv g s α w`
  (DLMF 2.3.30), valued in any real normed space `E`.

## Main results

* `TauCeti.abs_bleisteinCenter`: `|bleisteinCenter g α| = √(2 * (g 0 - g α))` (DLMF 2.3.26).
* `TauCeti.bleisteinCoord_zero`, `TauCeti.bleisteinCoord_self`: `w(α, 0) = 0` and
  `w(α, α) = a(α)`.
* `TauCeti.half_sq_bleisteinCoord_sub_mul`: `w ^ 2 / 2 - a * w + g 0 = g t` (DLMF 2.3.25).
* `TauCeti.strictMonoOn_bleisteinCoord`: `bleisteinCoord g α` is strictly increasing when `g` is
  strictly decreasing up to `α` and strictly increasing from `α` onward.
* `TauCeti.hasDerivAt_bleisteinCoord_of_ne`, `TauCeti.deriv_bleisteinCoord_of_ne`:
  `dw / dt = g'(t) / (w - a)` for `t ≠ α` (DLMF 2.3.28).
* `TauCeti.hasDerivAt_bleisteinCoord_self`, `TauCeti.deriv_bleisteinCoord_self_pos`,
  `TauCeti.contDiffOn_bleisteinCoord`: `dw / dt = √(g''(α)) > 0` at `t = α`, and
  `bleisteinCoord g α` is `C¹` on an open set `U` when `g` is `C²` on `U`.
* `TauCeti.hasStrictDerivAt_bleisteinInv`, `TauCeti.contDiffOn_bleisteinInv`:
  local inverse differentiability and `C¹` regularity of `bleisteinInv`.
* `TauCeti.image_bleisteinCoord_Ioo_of_tendsto`,
  `TauCeti.image_bleisteinCoord_Ioo_of_tendsto_atTop`,
  `TauCeti.image_bleisteinCoord_Ioi_of_tendsto`,
  `TauCeti.image_bleisteinCoord_Ioi_of_tendsto_atTop`: identification of the transformed range
  `(0, κ)` or `(0, ∞)`, including `κ = ∞` when `g(t) → ∞`.
* `TauCeti.integrableOn_bleistein_iff`, `TauCeti.exp_mul_integral_bleistein_eq`: equivalence of
  integrability and equality of the original and transformed integrals (DLMF 2.3.24, 2.3.29).

## References

* N. Bleistein, Uniform asymptotic expansions of integrals with stationary point near algebraic
  singularity, *Comm. Pure Appl. Math.* 19 (1966), 353–370.
* N. Bleistein and R. A. Handelsman, *Asymptotic Expansions of Integrals*, Holt, Rinehart and
  Winston, 1975; reprinted Dover, 1986. Chapter 9, §4.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted
  A K Peters, 1997. Chapter 9, §6.
* R. Wong, *Asymptotic Approximations of Integrals*, Academic Press, 1989; reprinted SIAM, 2001.
  Chapter 7, §2.
* NIST *Digital Library of Mathematical Functions*, §2.3(v), formulas 2.3.24–2.3.30,
  <https://dlmf.nist.gov/2.3#v>.
-/

public section

open Filter MeasureTheory Set
open scoped Topology ContDiff

namespace TauCeti

/-! ### Canonical coordinate and algebraic identities -/

/-- The canonical saddle-point coordinate `a(α) = sgn(α) √(2 (g 0 - g α))` in Bleistein's change
of variables, with `Real.sign 0 = 0`, chosen so that `bleisteinCoord g α 0 = 0`. -/
noncomputable def bleisteinCenter (g : ℝ → ℝ) (α : ℝ) : ℝ :=
  Real.sign α * Real.sqrt (2 * (g 0 - g α))

/-- Bleistein's canonical coordinate
`w(α, t) = bleisteinCenter g α + sgn(t - α) √(2 (g t - g α))`, mapping `t = 0` to `0` and
`t = α` to `bleisteinCenter g α`. -/
noncomputable def bleisteinCoord (g : ℝ → ℝ) (α t : ℝ) : ℝ :=
  bleisteinCenter g α + Real.sign (t - α) * Real.sqrt (2 * (g t - g α))

/-- The inverse coordinate `t(w)` of `bleisteinCoord g α` on a domain `s`. -/
noncomputable def bleisteinInv (g : ℝ → ℝ) (s : Set ℝ) (α w : ℝ) : ℝ :=
  Function.invFunOn (bleisteinCoord g α) s w

/-- The transformed amplitude `f(α, w) = ((t / w) ^ (λ - 1) / w'(t)) • q(t)` of DLMF 2.3.30,
where `t = bleisteinInv g s α w`, taking values in a real normed space `E`. -/
noncomputable def bleisteinAmplitude {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (lam : ℝ) (g : ℝ → ℝ) (q : ℝ → E) (s : Set ℝ) (α w : ℝ) : E :=
  ((bleisteinInv g s α w / w) ^ (lam - 1) /
    deriv (bleisteinCoord g α) (bleisteinInv g s α w)) • q (bleisteinInv g s α w)

/-- Explicit formula for `bleisteinCenter`. -/
theorem bleisteinCenter_def (g : ℝ → ℝ) (α : ℝ) :
    bleisteinCenter g α = Real.sign α * Real.sqrt (2 * (g 0 - g α)) := by rfl

/-- Explicit formula for `bleisteinCoord`. -/
theorem bleisteinCoord_def (g : ℝ → ℝ) (α t : ℝ) :
    bleisteinCoord g α t =
      bleisteinCenter g α + Real.sign (t - α) * Real.sqrt (2 * (g t - g α)) := by rfl

/-- Explicit formula for `bleisteinInv`. -/
theorem bleisteinInv_def (g : ℝ → ℝ) (s : Set ℝ) (α w : ℝ) :
    bleisteinInv g s α w = Function.invFunOn (bleisteinCoord g α) s w := by rfl

/-- Explicit formula for `bleisteinAmplitude`. -/
theorem bleisteinAmplitude_def {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (lam : ℝ) (g : ℝ → ℝ) (q : ℝ → E) (s : Set ℝ) (α w : ℝ) :
    bleisteinAmplitude lam g q s α w =
      ((bleisteinInv g s α w / w) ^ (lam - 1) /
        deriv (bleisteinCoord g α) (bleisteinInv g s α w)) • q (bleisteinInv g s α w) := by rfl

/-- At `α = 0`, the canonical saddle point `bleisteinCenter g 0` vanishes. -/
@[simp]
theorem bleisteinCenter_zero (g : ℝ → ℝ) : bleisteinCenter g 0 = 0 := by
  simp [bleisteinCenter]

/-- Formula for `bleisteinCenter g α` when `α > 0`. -/
theorem bleisteinCenter_of_pos {g : ℝ → ℝ} {α : ℝ} (hα : 0 < α) :
    bleisteinCenter g α = Real.sqrt (2 * (g 0 - g α)) := by
  simp [bleisteinCenter, Real.sign_of_pos hα]

/-- Formula for `bleisteinCenter g α` when `α < 0`. -/
theorem bleisteinCenter_of_neg {g : ℝ → ℝ} {α : ℝ} (hα : α < 0) :
    bleisteinCenter g α = -Real.sqrt (2 * (g 0 - g α)) := by
  simp [bleisteinCenter, Real.sign_of_neg hα]

/-- Magnitude of the canonical saddle coordinate (DLMF 2.3.26):
`|a(α)| = √(2 (g 0 - g α))`. -/
@[simp]
theorem abs_bleisteinCenter (g : ℝ → ℝ) (α : ℝ) :
    |bleisteinCenter g α| = Real.sqrt (2 * (g 0 - g α)) := by
  rcases eq_or_ne α 0 with rfl | hα
  · simp [bleisteinCenter]
  · have hs : |Real.sign α| = 1 := by
      rcases Real.sign_apply_eq_of_ne_zero α hα with h | h <;> simp [h]
    rw [bleisteinCenter, abs_mul, hs, one_mul, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- Square of `bleisteinCenter g α` when `g α ≤ g 0`. -/
theorem sq_bleisteinCenter {g : ℝ → ℝ} {α : ℝ} (h0 : g α ≤ g 0) :
    bleisteinCenter g α ^ 2 = 2 * (g 0 - g α) := by
  rw [← sq_abs, abs_bleisteinCenter, Real.sq_sqrt (by linarith)]

/-- Bleistein's coordinate maps `t = 0` to `w = 0`. -/
@[simp]
theorem bleisteinCoord_zero (g : ℝ → ℝ) (α : ℝ) : bleisteinCoord g α 0 = 0 := by
  rw [bleisteinCoord, bleisteinCenter, zero_sub, Real.sign_neg]
  ring

/-- Bleistein's coordinate maps the saddle point `t = α` to `bleisteinCenter g α`. -/
@[simp]
theorem bleisteinCoord_self (g : ℝ → ℝ) (α : ℝ) :
    bleisteinCoord g α α = bleisteinCenter g α := by
  simp [bleisteinCoord]

/-- Formula for `bleisteinCoord g α t - bleisteinCenter g α` when `t > α`. -/
theorem bleisteinCoord_sub_bleisteinCenter_of_gt {g : ℝ → ℝ} {α t : ℝ} (ht : α < t) :
    bleisteinCoord g α t - bleisteinCenter g α = Real.sqrt (2 * (g t - g α)) := by
  rw [bleisteinCoord, add_sub_cancel_left, Real.sign_of_pos (sub_pos.mpr ht), one_mul]

/-- Formula for `bleisteinCoord g α t - bleisteinCenter g α` when `t < α`. -/
theorem bleisteinCoord_sub_bleisteinCenter_of_lt {g : ℝ → ℝ} {α t : ℝ} (ht : t < α) :
    bleisteinCoord g α t - bleisteinCenter g α = -Real.sqrt (2 * (g t - g α)) := by
  rw [bleisteinCoord, add_sub_cancel_left, Real.sign_of_neg (sub_neg.mpr ht), neg_one_mul]

/-- Square of the displacement from the canonical saddle:
`(w - a) ^ 2 = 2 * (g t - g α)` whenever `g α ≤ g t`. -/
theorem sq_bleisteinCoord_sub_bleisteinCenter {g : ℝ → ℝ} {α t : ℝ} (ht : g α ≤ g t) :
    (bleisteinCoord g α t - bleisteinCenter g α) ^ 2 = 2 * (g t - g α) := by
  rcases eq_or_ne t α with rfl | hne
  · simp
  · have hs : Real.sign (t - α) ^ 2 = 1 := by
      rcases Real.sign_apply_eq_of_ne_zero _ (sub_ne_zero.mpr hne) with h | h <;> simp [h]
    rw [bleisteinCoord, add_sub_cancel_left, mul_pow, hs, one_mul, Real.sq_sqrt (by linarith)]

/-- Subtracted quadratic phase identity: `w ^ 2 / 2 - a * w = g t - g 0`. -/
theorem half_sq_bleisteinCoord_sub_mul_eq_sub {g : ℝ → ℝ} {α t : ℝ}
    (h0 : g α ≤ g 0) (ht : g α ≤ g t) :
    bleisteinCoord g α t ^ 2 / 2 - bleisteinCenter g α * bleisteinCoord g α t = g t - g 0 := by
  have h1 := sq_bleisteinCenter h0
  have h2 := sq_bleisteinCoord_sub_bleisteinCenter ht
  linarith

/-- Fundamental quadratic phase identity of Bleistein's change of variables (DLMF 2.3.25):
`w ^ 2 / 2 - a * w + g 0 = g t`. -/
theorem half_sq_bleisteinCoord_sub_mul {g : ℝ → ℝ} {α t : ℝ}
    (h0 : g α ≤ g 0) (ht : g α ≤ g t) :
    bleisteinCoord g α t ^ 2 / 2 - bleisteinCenter g α * bleisteinCoord g α t + g 0 = g t := by
  linarith [half_sq_bleisteinCoord_sub_mul_eq_sub h0 ht]

/-! ### Monotonicity and continuity -/

/-- Bleistein's coordinate `bleisteinCoord g α` is strictly increasing on `U` whenever `α ∈ U`,
`g` is strictly decreasing on `U ∩ (-∞, α]`, and `g` is strictly increasing on `U ∩ [α, ∞)`. -/
theorem strictMonoOn_bleisteinCoord {g : ℝ → ℝ} {U : Set ℝ} {α : ℝ}
    (hα : α ∈ U) (hanti : StrictAntiOn g (U ∩ Iic α)) (hmono : StrictMonoOn g (U ∩ Ici α)) :
    StrictMonoOn (bleisteinCoord g α) U := by
  intro t₁ ht₁ t₂ ht₂ h12
  suffices h : Real.sign (t₁ - α) * Real.sqrt (2 * (g t₁ - g α)) <
      Real.sign (t₂ - α) * Real.sqrt (2 * (g t₂ - g α)) by
    exact add_lt_add_right h (bleisteinCenter g α)
  have hgt : ∀ t ∈ U, t ≠ α → g α < g t := fun t ht hne ↦
    hne.lt_or_gt.elim (fun h ↦ hanti ⟨ht, h.le⟩ ⟨hα, le_rfl⟩ h)
      (fun h ↦ hmono ⟨hα, le_rfl⟩ ⟨ht, h.le⟩ h)
  have hpos : ∀ t ∈ U, t ≠ α → 0 < Real.sqrt (2 * (g t - g α)) := fun t ht hne ↦
    Real.sqrt_pos.mpr (by linarith [hgt t ht hne])
  rcases lt_trichotomy t₁ α with h₁ | rfl | h₁
  · rw [Real.sign_of_neg (sub_neg.mpr h₁), neg_one_mul]
    rcases lt_trichotomy t₂ α with h₂ | rfl | h₂
    · rw [Real.sign_of_neg (sub_neg.mpr h₂), neg_one_mul, neg_lt_neg_iff]
      have hg2 : g α < g t₂ := hgt t₂ ht₂ h₂.ne
      have hg12 : g t₂ < g t₁ := hanti ⟨ht₁, h₁.le⟩ ⟨ht₂, h₂.le⟩ h12
      exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
    · simpa using hpos t₁ ht₁ h₁.ne
    · rw [Real.sign_of_pos (sub_pos.mpr h₂), one_mul]
      exact (neg_neg_of_pos (hpos t₁ ht₁ h₁.ne)).trans (hpos t₂ ht₂ h₂.ne')
  · rw [sub_self, Real.sign_zero, zero_mul, Real.sign_of_pos (sub_pos.mpr h12), one_mul]
    exact hpos t₂ ht₂ h12.ne'
  · have h₂ : α < t₂ := h₁.trans h12
    rw [Real.sign_of_pos (sub_pos.mpr h₁), Real.sign_of_pos (sub_pos.mpr h₂), one_mul, one_mul]
    have hg1 : g α < g t₁ := hgt t₁ ht₁ h₁.ne'
    have hg12 : g t₁ < g t₂ := hmono ⟨ht₁, h₁.le⟩ ⟨ht₂, h₂.le⟩ h12
    exact Real.sqrt_lt_sqrt (by linarith) (by linarith)

/-- Positivity of `bleisteinCoord g α t` for `t > 0` under the monotonicity hypotheses on `g`. -/
theorem bleisteinCoord_pos {g : ℝ → ℝ} {U : Set ℝ} {α t : ℝ}
    (hα : α ∈ U) (h0 : 0 ∈ U) (hanti : StrictAntiOn g (U ∩ Iic α))
    (hmono : StrictMonoOn g (U ∩ Ici α)) (ht : t ∈ U) (ht0 : 0 < t) :
    0 < bleisteinCoord g α t := by
  simpa [bleisteinCoord_zero] using strictMonoOn_bleisteinCoord hα hanti hmono h0 ht ht0

/-- Continuity of `bleisteinCoord g α` on any set `U` where `g` is continuous. -/
theorem continuousOn_bleisteinCoord {g : ℝ → ℝ} {U : Set ℝ} (hg : ContinuousOn g U) (α : ℝ) :
    ContinuousOn (bleisteinCoord g α) U := by
  intro t ht
  have hrad : ContinuousWithinAt (fun u ↦ Real.sqrt (2 * (g u - g α))) U t :=
    Real.continuous_sqrt.continuousAt.comp_continuousWithinAt
      (continuousWithinAt_const.mul ((hg t ht).sub continuousWithinAt_const))
  rcases lt_trichotomy t α with hlt | rfl | hgt
  · refine ((continuousWithinAt_const (b := bleisteinCenter g α)).sub hrad).congr_of_eventuallyEq
      ?_ (by rw [bleisteinCoord, Real.sign_of_neg (sub_neg.mpr hlt), Pi.sub_apply]; ring)
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hlt)] with u (hu : u < α)
    rw [bleisteinCoord, Real.sign_of_neg (sub_neg.mpr hu), Pi.sub_apply]
    ring
  · rw [ContinuousWithinAt, bleisteinCoord_self]
    have h0 : Tendsto (fun u ↦ Real.sqrt (2 * (g u - g t))) (𝓝[U] t) (𝓝 0) := by
      simpa using hrad.tendsto
    have hdisp : Tendsto (fun u ↦ Real.sign (u - t) * Real.sqrt (2 * (g u - g t)))
        (𝓝[U] t) (𝓝 0) := by
      refine squeeze_zero_norm ?_ h0
      intro u
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      have hs : |Real.sign (u - t)| ≤ 1 := by
        rcases Real.sign_apply_eq (u - t) with h | h | h <;> simp [h]
      exact mul_le_of_le_one_left (Real.sqrt_nonneg _) hs
    have hsum : Tendsto (fun u ↦ bleisteinCenter g t +
        Real.sign (u - t) * Real.sqrt (2 * (g u - g t))) (𝓝[U] t) (𝓝 (bleisteinCenter g t)) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := bleisteinCenter g t)).add hdisp
    exact hsum.congr fun _ ↦ rfl
  · refine ((continuousWithinAt_const (b := bleisteinCenter g α)).add hrad).congr_of_eventuallyEq
      ?_ (by rw [bleisteinCoord, Real.sign_of_pos (sub_pos.mpr hgt), Pi.add_apply]; ring)
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hgt)] with u (hu : α < u)
    rw [bleisteinCoord, Real.sign_of_pos (sub_pos.mpr hu), Pi.add_apply]
    ring

/-! ### Derivatives and `C¹` regularity -/

/-- Derivative of `bleisteinCoord g α` away from the saddle point `t = α` (DLMF 2.3.28):
`w'(t) = g'(t) / (w(t) - a(α))`. -/
theorem hasDerivAt_bleisteinCoord_of_ne {g : ℝ → ℝ} {α t g' : ℝ}
    (hne : t ≠ α) (hgt : g α < g t) (hd : HasDerivAt g g' t) :
    HasDerivAt (bleisteinCoord g α) (g' / (bleisteinCoord g α t - bleisteinCenter g α)) t := by
  have hrad : HasDerivAt (fun u ↦ Real.sqrt (2 * (g u - g α)))
      (g' / Real.sqrt (2 * (g t - g α))) t := by
    have h := ((hd.sub_const (g α)).const_mul 2).sqrt (by linarith)
    rwa [mul_div_mul_left _ _ (two_ne_zero : (2 : ℝ) ≠ 0)] at h
  rcases hne.lt_or_gt with hlt | hgt'
  · rw [bleisteinCoord_sub_bleisteinCenter_of_lt hlt, div_neg]
    refine (hrad.neg.const_add (bleisteinCenter g α)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hlt] with u (hu : u < α)
    rw [bleisteinCoord, Real.sign_of_neg (sub_neg.mpr hu), neg_one_mul, Pi.neg_apply]
  · rw [bleisteinCoord_sub_bleisteinCenter_of_gt hgt']
    refine (hrad.const_add (bleisteinCenter g α)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hgt'] with u (hu : α < u)
    rw [bleisteinCoord, Real.sign_of_pos (sub_pos.mpr hu), one_mul]

/-- `deriv` form of `hasDerivAt_bleisteinCoord_of_ne` (DLMF 2.3.28). -/
theorem deriv_bleisteinCoord_of_ne {g : ℝ → ℝ} {α t : ℝ}
    (hne : t ≠ α) (hgt : g α < g t) (hd : DifferentiableAt ℝ g t) :
    deriv (bleisteinCoord g α) t =
      deriv g t / (bleisteinCoord g α t - bleisteinCenter g α) :=
  (hasDerivAt_bleisteinCoord_of_ne hne hgt hd.hasDerivAt).deriv

/-- Strict positivity of `deriv (bleisteinCoord g α) t` away from `t = α` when `g'` has the sign
of `t - α`. -/
theorem deriv_bleisteinCoord_pos_of_ne {g : ℝ → ℝ} {α t : ℝ}
    (hne : t ≠ α) (hgt : g α < g t) (hd : DifferentiableAt ℝ g t)
    (hsign : 0 < (t - α) * deriv g t) :
    0 < deriv (bleisteinCoord g α) t := by
  rw [deriv_bleisteinCoord_of_ne hne hgt hd]
  have hsqrt : 0 < Real.sqrt (2 * (g t - g α)) := Real.sqrt_pos.mpr (by linarith)
  rcases hne.lt_or_gt with hlt | hgt'
  · rw [bleisteinCoord_sub_bleisteinCenter_of_lt hlt]
    exact div_pos_of_neg_of_neg (neg_of_mul_pos_right hsign (sub_neg.mpr hlt).le)
      (neg_neg_of_pos hsqrt)
  · rw [bleisteinCoord_sub_bleisteinCenter_of_gt hgt']
    exact div_pos (pos_of_mul_pos_right hsign (sub_pos.mpr hgt').le) hsqrt

/-- Difference quotient of `bleisteinCoord g α` at `t = α` expressed as a single square root. -/
private theorem slope_bleisteinCoord_self {g : ℝ → ℝ} {α t : ℝ} (hne : t ≠ α) :
    (bleisteinCoord g α t - bleisteinCoord g α α) / (t - α) =
      Real.sqrt (2 * (g t - g α) / (t - α) ^ 2) := by
  have hdiv : Real.sign (t - α) / (t - α) = |t - α|⁻¹ := by
    rcases (sub_ne_zero.mpr hne).lt_or_gt with h | h
    · rw [Real.sign_of_neg h, abs_of_neg h, inv_neg, neg_div, one_div]
    · rw [Real.sign_of_pos h, abs_of_pos h, one_div]
  rw [bleisteinCoord_self, bleisteinCoord, add_sub_cancel_left, mul_div_right_comm,
    hdiv, inv_mul_eq_div, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- At the critical point `t = α`, `bleisteinCoord g α` is differentiable with derivative `√g''`
whenever `deriv g α = 0` and `HasDerivAt (deriv g) g'' α`. -/
theorem hasDerivAt_bleisteinCoord_self {g : ℝ → ℝ} {α g'' : ℝ}
    (hdiff : ∀ᶠ t in 𝓝 α, DifferentiableAt ℝ g t)
    (hd1 : deriv g α = 0) (hd2 : HasDerivAt (deriv g) g'' α) :
    HasDerivAt (bleisteinCoord g α) (Real.sqrt g'') α := by
  have hg_cont : ContinuousAt g α := (hdiff.self_of_nhds).continuousAt
  have hslope : Tendsto (fun t ↦ deriv g t / (t - α)) (𝓝[≠] α) (𝓝 g'') := by
    simpa [slope_fun_def_field, hd1] using hasDerivAt_iff_tendsto_slope.mp hd2
  have hsq : Tendsto (fun t ↦ 2 * (g t - g α) / (t - α) ^ 2) (𝓝[≠] α) (𝓝 g'') := by
    refine HasDerivAt.lhopital_zero_nhdsNE
      (f' := fun t ↦ 2 * deriv g t) (g' := fun t ↦ 2 * (t - α)) ?_ ?_ ?_ ?_ ?_ ?_
    · exact Filter.Eventually.mono (nhdsWithin_le_nhds hdiff) fun t ht ↦
        (ht.hasDerivAt.sub_const (g α)).const_mul 2
    · exact Eventually.of_forall fun t ↦ by
        convert (hasDerivAt_pow 2 (t - α)).comp t ((hasDerivAt_id t).sub_const α) using 1 <;>
          simp [Function.comp_def]
    · filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ α)
      exact mul_ne_zero two_ne_zero (sub_ne_zero.mpr ht)
    · exact tendsto_nhdsWithin_of_tendsto_nhds
        (by simpa using ((hg_cont.sub (continuousAt_const (y := g α))).const_mul 2).tendsto)
    · exact tendsto_nhdsWithin_of_tendsto_nhds
        (by simpa using ((tendsto_id.sub_const α).pow 2 :
          Tendsto (fun t ↦ (t - α) ^ 2) (𝓝 α) (𝓝 ((α - α) ^ 2))))
    · refine hslope.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t _
      exact (mul_div_mul_left _ _ two_ne_zero).symm
  rw [hasDerivAt_iff_tendsto_slope]
  refine (Real.continuous_sqrt.continuousAt.tendsto.comp hsq).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ α)
  rw [Function.comp_apply, slope_def_field, slope_bleisteinCoord_self ht]

/-- `deriv` form of `hasDerivAt_bleisteinCoord_self`. -/
theorem deriv_bleisteinCoord_self {g : ℝ → ℝ} {α g'' : ℝ}
    (hdiff : ∀ᶠ t in 𝓝 α, DifferentiableAt ℝ g t)
    (hd1 : deriv g α = 0) (hd2 : HasDerivAt (deriv g) g'' α) :
    deriv (bleisteinCoord g α) α = Real.sqrt g'' :=
  (hasDerivAt_bleisteinCoord_self hdiff hd1 hd2).deriv

/-- Strict positivity of `deriv (bleisteinCoord g α)` at the saddle point `t = α` when
`deriv g α = 0` and `g'' > 0`. -/
theorem deriv_bleisteinCoord_self_pos {g : ℝ → ℝ} {α g'' : ℝ}
    (hdiff : ∀ᶠ t in 𝓝 α, DifferentiableAt ℝ g t)
    (hd1 : deriv g α = 0) (hd2 : HasDerivAt (deriv g) g'' α) (hg'' : 0 < g'') :
    0 < deriv (bleisteinCoord g α) α := by
  rw [deriv_bleisteinCoord_self hdiff hd1 hd2]
  exact Real.sqrt_pos.mpr hg''

/-- Continuity of `deriv (bleisteinCoord g α)` at `t = α` when `deriv g α = 0` and `g'' > 0`. -/
theorem continuousAt_deriv_bleisteinCoord_self {g : ℝ → ℝ} {α g'' : ℝ}
    (hdiff : ∀ᶠ t in 𝓝 α, DifferentiableAt ℝ g t)
    (hd1 : deriv g α = 0) (hd2 : HasDerivAt (deriv g) g'' α) (hg'' : 0 < g'') :
    ContinuousAt (deriv (bleisteinCoord g α)) α := by
  rw [continuousAt_iff_punctured_nhds, deriv_bleisteinCoord_self hdiff hd1 hd2]
  have hslope1 : Tendsto (fun t ↦ deriv g t / (t - α)) (𝓝[≠] α) (𝓝 g'') := by
    simpa [slope_fun_def_field, hd1] using hasDerivAt_iff_tendsto_slope.mp hd2
  have hslope2 : Tendsto (fun t ↦ (bleisteinCoord g α t - bleisteinCoord g α α) / (t - α))
      (𝓝[≠] α) (𝓝 (Real.sqrt g'')) := by
    have h := hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_bleisteinCoord_self hdiff hd1 hd2)
    rwa [slope_fun_def_field] at h
  have hsqrt_pos : 0 < Real.sqrt g'' := Real.sqrt_pos.mpr hg''
  have hquot : Tendsto (fun t ↦ (deriv g t / (t - α)) /
      ((bleisteinCoord g α t - bleisteinCoord g α α) / (t - α)))
      (𝓝[≠] α) (𝓝 (Real.sqrt g'')) := by
    convert hslope1.div hslope2 hsqrt_pos.ne' using 2
    rw [eq_div_iff hsqrt_pos.ne', Real.mul_self_sqrt hg''.le]
  refine hquot.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hdiff,
    hslope2.eventually (lt_mem_nhds hsqrt_pos)] with t (ht : t ≠ α) htd hpos
  have hsub : t - α ≠ 0 := sub_ne_zero.mpr ht
  have hw_ne : bleisteinCoord g α t - bleisteinCenter g α ≠ 0 := fun h ↦ by
    rw [bleisteinCoord_self, h, zero_div] at hpos
    exact lt_irrefl 0 hpos
  rw [bleisteinCoord, add_sub_cancel_left] at hw_ne
  have hgt : g α < g t := by
    contrapose! hw_ne
    rw [Real.sqrt_eq_zero_of_nonpos (by linarith), mul_zero]
  rw [deriv_bleisteinCoord_of_ne ht hgt htd, bleisteinCoord_self, div_div_div_cancel_right₀ hsub]

/-- If `g` is `C²` on an open set `U` containing `α`, is strictly decreasing up to `α` and strictly
increasing beyond `α`, and satisfies `deriv g α = 0` and `0 < deriv (deriv g) α`, then
`bleisteinCoord g α` is `C¹` on `U`. -/
theorem contDiffOn_bleisteinCoord {g : ℝ → ℝ} {U : Set ℝ} {α : ℝ}
    (hU : IsOpen U) (hα : α ∈ U) (hg : ContDiffOn ℝ 2 g U)
    (hanti : StrictAntiOn g (U ∩ Iic α)) (hmono : StrictMonoOn g (U ∩ Ici α))
    (hd1 : deriv g α = 0) (hd2 : 0 < deriv (deriv g) α) :
    ContDiffOn ℝ 1 (bleisteinCoord g α) U := by
  have hg1 := (contDiffOn_succ_iff_deriv_of_isOpen (n := 1) hU).mp hg
  have hg2 := (contDiffOn_succ_iff_deriv_of_isOpen (n := 0) hU).mp hg1.2.2
  have hdiff_nhds : ∀ᶠ u in 𝓝 α, DifferentiableAt ℝ g u :=
    Filter.Eventually.mono (hU.mem_nhds hα) fun u hu ↦ hg1.1.differentiableAt (hU.mem_nhds hu)
  have hd2_at : HasDerivAt (deriv g) (deriv (deriv g) α) α :=
    (hg2.1.differentiableAt (hU.mem_nhds hα)).hasDerivAt
  have hgt : ∀ u ∈ U, u ≠ α → g α < g u := fun u hu hne ↦
    hne.lt_or_gt.elim (fun h ↦ hanti ⟨hu, h.le⟩ ⟨hα, le_rfl⟩ h)
      (fun h ↦ hmono ⟨hα, le_rfl⟩ ⟨hu, h.le⟩ h)
  rw [contDiffOn_one_iff_derivWithin hU.uniqueDiffOn]
  refine ⟨fun t ht ↦ ?_, ContinuousOn.congr ?_ fun _ hx ↦ derivWithin_of_isOpen hU hx⟩
  · rcases eq_or_ne t α with rfl | hne
    · exact (hasDerivAt_bleisteinCoord_self hdiff_nhds hd1 hd2_at).differentiableAt
        |>.differentiableWithinAt
    · exact (hasDerivAt_bleisteinCoord_of_ne hne (hgt t ht hne)
        (hg1.1.differentiableAt (hU.mem_nhds ht)).hasDerivAt).differentiableAt
        |>.differentiableWithinAt
  · intro t ht
    rcases eq_or_ne t α with rfl | hne
    · exact (continuousAt_deriv_bleisteinCoord_self hdiff_nhds hd1 hd2_at hd2).continuousWithinAt
    · have hw_cont : ContinuousAt (bleisteinCoord g α) t :=
        (continuousOn_bleisteinCoord hg.continuousOn α).continuousAt (hU.mem_nhds ht)
      have hgd_cont : ContinuousAt (deriv g) t :=
        hg1.2.2.continuousOn.continuousAt (hU.mem_nhds ht)
      have hw_ne : bleisteinCoord g α t - bleisteinCenter g α ≠ 0 := sub_ne_zero.mpr fun h ↦ by
        rw [← bleisteinCoord_self] at h
        exact hne ((strictMonoOn_bleisteinCoord hα hanti hmono).injOn ht hα h)
      have hquot : ContinuousAt
          (fun u ↦ deriv g u / (bleisteinCoord g α u - bleisteinCenter g α)) t :=
        hgd_cont.div (hw_cont.sub continuousAt_const) hw_ne
      refine (hquot.congr ?_).continuousWithinAt
      filter_upwards [hU.mem_nhds ht, isOpen_ne.mem_nhds hne] with u hu hune
      exact (deriv_bleisteinCoord_of_ne hune (hgt u hu hune)
        (hg1.1.differentiableAt (hU.mem_nhds hu))).symm

/-- Strict positivity of `deriv (bleisteinCoord g α)` at a point `t ∈ U` whenever `g` has no
stationary point at `t` other than `α` (`t ≠ α → deriv g t ≠ 0`). -/
theorem deriv_bleisteinCoord_pos {g : ℝ → ℝ} {U : Set ℝ} {α t : ℝ}
    (hU : IsOpen U) (hα : α ∈ U) (hg : ContDiffOn ℝ 2 g U)
    (hanti : StrictAntiOn g (U ∩ Iic α)) (hmono : StrictMonoOn g (U ∩ Ici α))
    (hd1 : deriv g α = 0) (hd2 : 0 < deriv (deriv g) α)
    (ht : t ∈ U) (hreg : t ≠ α → deriv g t ≠ 0) :
    0 < deriv (bleisteinCoord g α) t := by
  have hg1 := (contDiffOn_succ_iff_deriv_of_isOpen (n := 1) hU).mp hg
  have hg2 := (contDiffOn_succ_iff_deriv_of_isOpen (n := 0) hU).mp hg1.2.2
  rcases eq_or_ne t α with rfl | hne
  · exact deriv_bleisteinCoord_self_pos
      (Filter.Eventually.mono (hU.mem_nhds hα) fun u hu ↦ hg1.1.differentiableAt (hU.mem_nhds hu))
      hd1 (hg2.1.differentiableAt (hU.mem_nhds hα)).hasDerivAt hd2
  · have hsign : 0 < (t - α) * deriv g t := by
      rcases hne.lt_or_gt with hlt | hgt
      · have hle : deriv g t ≤ 0 := by
          rw [← derivWithin_of_isOpen (hU.inter isOpen_Iio) ⟨ht, hlt⟩]
          exact (hanti.antitoneOn.mono (inter_subset_inter_right U Iio_subset_Iic_self))
            |>.derivWithin_nonpos
        exact mul_pos_of_neg_of_neg (sub_neg.mpr hlt) (lt_of_le_of_ne hle (hreg hne))
      · have hge : 0 ≤ deriv g t := by
          rw [← derivWithin_of_isOpen (hU.inter isOpen_Ioi) ⟨ht, hgt⟩]
          exact (hmono.monotoneOn.mono (inter_subset_inter_right U Ioi_subset_Ici_self))
            |>.derivWithin_nonneg
        exact mul_pos (sub_pos.mpr hgt) (lt_of_le_of_ne' hge (hreg hne))
    have hgt : g α < g t := hne.lt_or_gt.elim (fun h ↦ hanti ⟨ht, h.le⟩ ⟨hα, le_rfl⟩ h)
      (fun h ↦ hmono ⟨hα, le_rfl⟩ ⟨ht, h.le⟩ h)
    exact deriv_bleisteinCoord_pos_of_ne hne hgt (hg1.1.differentiableAt (hU.mem_nhds ht)) hsign

/-! ### Range of the canonical coordinate -/

/-- If `g t → ∞` along a filter `l` concentrated strictly to the right of `α`, then
`bleisteinCoord g α t → ∞` along `l`. -/
theorem tendsto_bleisteinCoord_atTop {g : ℝ → ℝ} {α : ℝ} {l : Filter ℝ}
    (hα : ∀ᶠ t in l, α < t) (hg : Tendsto g l atTop) :
    Tendsto (bleisteinCoord g α) l atTop := by
  have hlin : Tendsto (fun t ↦ 2 * (g t - g α)) l atTop :=
    (hg.atTop_add tendsto_const_nhds).const_mul_atTop zero_lt_two
  have hsqrt : Tendsto (fun t ↦ bleisteinCenter g α + Real.sqrt (2 * (g t - g α))) l atTop :=
    tendsto_const_nhds.add_atTop (Real.tendsto_sqrt_atTop.comp hlin)
  refine hsqrt.congr' ?_
  filter_upwards [hα] with t ht
  simp [bleisteinCoord, Real.sign_of_pos (sub_pos.mpr ht)]

/-- Image of a finite interval `(0, k)` under `bleisteinCoord g α` when `w(t) → κ` as `t → k⁻`. -/
theorem image_bleisteinCoord_Ioo_of_tendsto {g : ℝ → ℝ} {U : Set ℝ} {α k κ : ℝ}
    (hk : 0 < k) (hα : α ∈ U) (hI : Ico 0 k ⊆ U) (hg : ContinuousOn g U)
    (hanti : StrictAntiOn g (U ∩ Iic α)) (hmono : StrictMonoOn g (U ∩ Ici α))
    (hκ : Tendsto (bleisteinCoord g α) (𝓝[<] k) (𝓝 κ)) :
    bleisteinCoord g α '' Ioo 0 k = Ioo 0 κ := by
  have hsm := strictMonoOn_bleisteinCoord hα hanti hmono
  have hcont := (continuousOn_bleisteinCoord hg α).mono (Ioo_subset_Ico_self.trans hI)
  have h0_lim : Tendsto (bleisteinCoord g α) (𝓝[>] 0) (𝓝 0) := by
    have hc0 := (continuousOn_bleisteinCoord hg α 0 (hI (left_mem_Ico.mpr hk))).mono
      (Ioo_subset_Ico_self.trans hI)
    rwa [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsGT hk, bleisteinCoord_zero] at hc0
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨t, ht, rfl⟩
    refine ⟨bleisteinCoord_pos hα (hI (left_mem_Ico.mpr hk)) hanti hmono
      (hI (Ioo_subset_Ico_self ht)) ht.1, ?_⟩
    have htm : t < (t + k) / 2 := by linarith [ht.2]
    have hmk : (t + k) / 2 < k := by linarith [ht.2]
    have hmU : (t + k) / 2 ∈ U := hI ⟨by linarith [ht.1, ht.2], hmk⟩
    have : NeBot (𝓝[<] k) := nhdsLT_neBot k
    refine (hsm (hI (Ioo_subset_Ico_self ht)) hmU htm).trans_le (ge_of_tendsto hκ ?_)
    filter_upwards [Ioo_mem_nhdsLT hmk] with u hu
    exact (hsm hmU (hI ⟨by linarith [ht.1, hu.1], hu.2⟩) hu.1).le
  · exact isPreconnected_Ioo.intermediate_value_Ioo
      (le_principal_iff.mpr (Ioo_mem_nhdsGT hk))
      (le_principal_iff.mpr (Ioo_mem_nhdsLT hk)) hcont h0_lim hκ

/-- Image of a finite interval `(0, k)` under `bleisteinCoord g α` when `g(t) → ∞` as `t → k⁻`
(so `κ = ∞` in DLMF 2.3.29). -/
theorem image_bleisteinCoord_Ioo_of_tendsto_atTop {g : ℝ → ℝ} {U : Set ℝ} {α k : ℝ}
    (hk : 0 < k) (hα : α ∈ U) (hI : Ico 0 k ⊆ U) (hg : ContinuousOn g U)
    (hanti : StrictAntiOn g (U ∩ Iic α)) (hmono : StrictMonoOn g (U ∩ Ici α))
    (htop : Tendsto g (𝓝[<] k) atTop) :
    bleisteinCoord g α '' Ioo 0 k = Ioi 0 := by
  have hαk : α < k := by
    by_contra! hle
    have : NeBot (𝓝[<] k) := nhdsLT_neBot k
    have hev : ∀ᶠ t in 𝓝[<] k, t ∈ Ioo 0 k ∧ g 0 < g t :=
      Filter.inter_mem (Ioo_mem_nhdsLT hk) (htop.eventually_gt_atTop (g 0))
    obtain ⟨t, ht, hgt⟩ := hev.exists
    have hlt : g t < g 0 := hanti ⟨hI (left_mem_Ico.mpr hk), hk.le.trans hle⟩
      ⟨hI (Ioo_subset_Ico_self ht), ht.2.le.trans hle⟩ ht.1
    exact hlt.not_gt hgt
  have hw_top : Tendsto (bleisteinCoord g α) (𝓝[<] k) atTop :=
    tendsto_bleisteinCoord_atTop
      (Filter.mem_of_superset (Ioo_mem_nhdsLT hαk) fun _ h ↦ h.1) htop
  have hcont := (continuousOn_bleisteinCoord hg α).mono (Ioo_subset_Ico_self.trans hI)
  have h0_lim : Tendsto (bleisteinCoord g α) (𝓝[>] 0) (𝓝 0) := by
    have hc0 := (continuousOn_bleisteinCoord hg α 0 (hI (left_mem_Ico.mpr hk))).mono
      (Ioo_subset_Ico_self.trans hI)
    rwa [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsGT hk, bleisteinCoord_zero] at hc0
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨t, ht, rfl⟩
    exact bleisteinCoord_pos hα (hI (left_mem_Ico.mpr hk)) hanti hmono
      (hI (Ioo_subset_Ico_self ht)) ht.1
  · exact isPreconnected_Ioo.intermediate_value_Ioi
      (le_principal_iff.mpr (Ioo_mem_nhdsGT hk))
      (le_principal_iff.mpr (Ioo_mem_nhdsLT hk)) hcont h0_lim hw_top

/-- Image of `(0, ∞)` under `bleisteinCoord g α` when `w(t) → κ` as `t → ∞` (finite `κ` with
`k = ∞`). -/
theorem image_bleisteinCoord_Ioi_of_tendsto {g : ℝ → ℝ} {U : Set ℝ} {α κ : ℝ}
    (hα : α ∈ U) (hI : Ici 0 ⊆ U) (hg : ContinuousOn g U)
    (hanti : StrictAntiOn g (U ∩ Iic α)) (hmono : StrictMonoOn g (U ∩ Ici α))
    (hκ : Tendsto (bleisteinCoord g α) atTop (𝓝 κ)) :
    bleisteinCoord g α '' Ioi 0 = Ioo 0 κ := by
  have hsm := strictMonoOn_bleisteinCoord hα hanti hmono
  have hcont := (continuousOn_bleisteinCoord hg α).mono (Ioi_subset_Ici_self.trans hI)
  have h0_lim : Tendsto (bleisteinCoord g α) (𝓝[>] 0) (𝓝 0) := by
    have hc0 := (continuousOn_bleisteinCoord hg α 0 (hI self_mem_Ici)).mono
      (Ioi_subset_Ici_self.trans hI)
    rwa [ContinuousWithinAt, bleisteinCoord_zero] at hc0
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨t, ht : 0 < t, rfl⟩
    refine ⟨bleisteinCoord_pos hα (hI self_mem_Ici) hanti hmono (hI ht.le) ht, ?_⟩
    have ht1 : t < t + 1 := lt_add_one t
    have h1U : t + 1 ∈ U := hI (by linarith : (0 : ℝ) ≤ t + 1)
    refine (hsm (hI ht.le) h1U ht1).trans_le (ge_of_tendsto hκ ?_)
    filter_upwards [Ioi_mem_atTop (t + 1)] with u (hu : t + 1 < u)
    exact (hsm h1U (hI (by linarith : (0 : ℝ) ≤ u)) hu).le
  · exact isPreconnected_Ioi.intermediate_value_Ioo
      (le_principal_iff.mpr self_mem_nhdsWithin)
      (le_principal_iff.mpr (Ioi_mem_atTop 0)) hcont h0_lim hκ

/-- Image of `(0, ∞)` under `bleisteinCoord g α` when `g(t) → ∞` as `t → ∞` (`κ = ∞` in
DLMF 2.3.29). -/
theorem image_bleisteinCoord_Ioi_of_tendsto_atTop {g : ℝ → ℝ} {U : Set ℝ} {α : ℝ}
    (hα : α ∈ U) (hI : Ici 0 ⊆ U) (hg : ContinuousOn g U)
    (hanti : StrictAntiOn g (U ∩ Iic α)) (hmono : StrictMonoOn g (U ∩ Ici α))
    (htop : Tendsto g atTop atTop) :
    bleisteinCoord g α '' Ioi 0 = Ioi 0 := by
  have hw_cont := (continuousOn_bleisteinCoord hg α).mono hI
  have hw_mono := (strictMonoOn_bleisteinCoord hα hanti hmono).mono hI
  have hw_top := tendsto_bleisteinCoord_atTop (Ioi_mem_atTop α) htop
  simpa [bleisteinCoord_zero] using hw_cont.image_Ioi_of_strictMonoOn hw_mono hw_top

/-! ### Inverse coordinate and transformed integral -/

/-- `bleisteinInv g s α` is a left inverse to `bleisteinCoord g α` on `s` whenever
`bleisteinCoord g α` is injective on `s`. -/
theorem leftInvOn_bleisteinInv {g : ℝ → ℝ} {s : Set ℝ} {α : ℝ}
    (hinj : InjOn (bleisteinCoord g α) s) :
    LeftInvOn (bleisteinInv g s α) (bleisteinCoord g α) s :=
  hinj.leftInvOn_invFunOn

/-- `bleisteinInv g s α` is a right inverse to `bleisteinCoord g α` on `bleisteinCoord g α '' s`. -/
theorem rightInvOn_bleisteinInv (g : ℝ → ℝ) (s : Set ℝ) (α : ℝ) :
    RightInvOn (bleisteinInv g s α) (bleisteinCoord g α) (bleisteinCoord g α '' s) :=
  fun _ hw ↦ Function.invFunOn_eq hw

/-- `bleisteinInv g s α` maps `bleisteinCoord g α '' s` into `s`. -/
theorem mapsTo_bleisteinInv (g : ℝ → ℝ) (s : Set ℝ) (α : ℝ) :
    MapsTo (bleisteinInv g s α) (bleisteinCoord g α '' s) s :=
  fun _ hw ↦ Function.invFunOn_mem hw

/-- Strict differentiability of the inverse coordinate `bleisteinInv g s α` at `w(t)` for `t` in an
open subset `s ⊆ U`, with derivative `(w'(t))⁻¹`. -/
theorem hasStrictDerivAt_bleisteinInv {g : ℝ → ℝ} {U s : Set ℝ} {α t : ℝ}
    (hU : IsOpen U) (hs : IsOpen s) (hsU : s ⊆ U)
    (hw : ContDiffOn ℝ 1 (bleisteinCoord g α) U) (hinj : InjOn (bleisteinCoord g α) s)
    (ht : t ∈ s) (hd : deriv (bleisteinCoord g α) t ≠ 0) :
    HasStrictDerivAt (bleisteinInv g s α) (deriv (bleisteinCoord g α) t)⁻¹
      (bleisteinCoord g α t) :=
  ((hw.contDiffAt (hU.mem_nhds (hsU ht))).hasStrictDerivAt_deriv one_ne_zero).to_local_left_inverse
    hd (Filter.Eventually.mono (hs.mem_nhds ht) fun _ hu ↦ leftInvOn_bleisteinInv hinj hu)

/-- Openness of the image `bleisteinCoord g α '' s` for an open subset `s ⊆ U` on which
`deriv (bleisteinCoord g α)` never vanishes. -/
theorem isOpen_image_bleisteinCoord {g : ℝ → ℝ} {U s : Set ℝ} {α : ℝ}
    (hU : IsOpen U) (hs : IsOpen s) (hsU : s ⊆ U)
    (hw : ContDiffOn ℝ 1 (bleisteinCoord g α) U)
    (hd : ∀ t ∈ s, deriv (bleisteinCoord g α) t ≠ 0) :
    IsOpen (bleisteinCoord g α '' s) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨t, ht, rfl⟩
  have hsd := (hw.contDiffAt (hU.mem_nhds (hsU ht))).hasStrictDerivAt_deriv one_ne_zero
  rw [← hsd.map_nhds_eq (hd t ht)]
  exact image_mem_map (hs.mem_nhds ht)

/-- `C¹` regularity of `bleisteinInv g s α` on `bleisteinCoord g α '' s` for an open set `s ⊆ U`. -/
theorem contDiffOn_bleisteinInv {g : ℝ → ℝ} {U s : Set ℝ} {α : ℝ}
    (hU : IsOpen U) (hs : IsOpen s) (hsU : s ⊆ U)
    (hw : ContDiffOn ℝ 1 (bleisteinCoord g α) U) (hinj : InjOn (bleisteinCoord g α) s)
    (hd : ∀ t ∈ s, deriv (bleisteinCoord g α) t ≠ 0) :
    ContDiffOn ℝ 1 (bleisteinInv g s α) (bleisteinCoord g α '' s) := by
  have himg : IsOpen (bleisteinCoord g α '' s) := isOpen_image_bleisteinCoord hU hs hsU hw hd
  have hw_deriv_cont : ContinuousOn (deriv (bleisteinCoord g α)) U :=
    hw.continuousOn_deriv_of_isOpen hU le_rfl
  rw [contDiffOn_one_iff_derivWithin himg.uniqueDiffOn]
  have hinv_diff : ∀ t ∈ s, HasDerivAt (bleisteinInv g s α)
      (deriv (bleisteinCoord g α) t)⁻¹ (bleisteinCoord g α t) := fun t ht ↦
    (hasStrictDerivAt_bleisteinInv hU hs hsU hw hinj ht (hd t ht)).hasDerivAt
  have hinv_cont : ContinuousOn (bleisteinInv g s α) (bleisteinCoord g α '' s) := by
    rintro _ ⟨t, ht, rfl⟩
    exact (hinv_diff t ht).continuousAt.continuousWithinAt
  refine ⟨?_, ContinuousOn.congr ?_ fun _ hx ↦ derivWithin_of_isOpen himg hx⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact (hinv_diff t ht).differentiableAt.differentiableWithinAt
  · refine ContinuousOn.congr (f := fun w ↦ (deriv (bleisteinCoord g α) (bleisteinInv g s α w))⁻¹)
      ?_ ?_
    · refine ContinuousOn.inv₀ ?_ ?_
      · exact hw_deriv_cont.comp hinv_cont ((mapsTo_bleisteinInv g s α).mono_right hsU)
      · rintro _ ⟨t, ht, rfl⟩
        rw [leftInvOn_bleisteinInv hinj ht]
        exact hd t ht
    · rintro _ ⟨t, ht, rfl⟩
      dsimp only
      rw [(hinv_diff t ht).deriv, leftInvOn_bleisteinInv hinj ht]

/-- Continuity of the transformed amplitude `bleisteinAmplitude lam g q s α` on
`bleisteinCoord g α '' s` when `q` is continuous on `s ⊆ Ioi 0`. -/
theorem continuousOn_bleisteinAmplitude {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {lam : ℝ} {g : ℝ → ℝ} {q : ℝ → E} {U s : Set ℝ} {α : ℝ}
    (hU : IsOpen U) (hs : IsOpen s) (hsU : s ⊆ U) (hs0 : s ⊆ Ioi 0)
    (hw : ContDiffOn ℝ 1 (bleisteinCoord g α) U) (hinj : InjOn (bleisteinCoord g α) s)
    (hw_pos : ∀ t ∈ s, 0 < bleisteinCoord g α t)
    (hd : ∀ t ∈ s, deriv (bleisteinCoord g α) t ≠ 0) (hq : ContinuousOn q s) :
    ContinuousOn (bleisteinAmplitude lam g q s α) (bleisteinCoord g α '' s) := by
  have hinv_cont : ContinuousOn (bleisteinInv g s α) (bleisteinCoord g α '' s) :=
    (contDiffOn_bleisteinInv hU hs hsU hw hinj hd).continuousOn
  have hmaps : MapsTo (bleisteinInv g s α) (bleisteinCoord g α '' s) s :=
    mapsTo_bleisteinInv g s α
  have hw_deriv_cont : ContinuousOn (deriv (bleisteinCoord g α)) U :=
    hw.continuousOn_deriv_of_isOpen hU le_rfl
  have hrat : ContinuousOn (fun w ↦ (bleisteinInv g s α w / w) ^ (lam - 1))
      (bleisteinCoord g α '' s) := by
    refine ContinuousOn.rpow_const (hinv_cont.div continuousOn_id ?_) ?_
    · rintro _ ⟨t, ht, rfl⟩
      exact (hw_pos t ht).ne'
    · rintro _ ⟨t, ht, rfl⟩
      exact Or.inl (div_pos (hs0 (hmaps ⟨t, ht, rfl⟩)) (hw_pos t ht)).ne'
  have hden : ContinuousOn (fun w ↦ deriv (bleisteinCoord g α) (bleisteinInv g s α w))
      (bleisteinCoord g α '' s) :=
    hw_deriv_cont.comp hinv_cont (hmaps.mono_right hsU)
  refine (hrat.div hden ?_).smul (hq.comp hinv_cont hmaps)
  rintro _ ⟨t, ht, rfl⟩
  rw [leftInvOn_bleisteinInv hinj ht]
  exact hd t ht

/-- Pointwise Jacobian cancellation between the transformed integrand at `w = bleisteinCoord g α t`
and the original integrand at `t`. -/
private theorem abs_deriv_smul_bleistein_integrand {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {lam x : ℝ} {g : ℝ → ℝ} {q : ℝ → E} {s : Set ℝ} {α t : ℝ}
    (ht : t ∈ s) (ht0 : 0 < t) (h0 : g α ≤ g 0) (hmin : g α ≤ g t)
    (hw_pos : 0 < bleisteinCoord g α t) (hinj : InjOn (bleisteinCoord g α) s)
    (hdpos : 0 < deriv (bleisteinCoord g α) t) :
    |deriv (bleisteinCoord g α) t| •
        ((Real.exp (-x * (bleisteinCoord g α t ^ 2 / 2 -
            bleisteinCenter g α * bleisteinCoord g α t)) *
          bleisteinCoord g α t ^ (lam - 1)) •
        bleisteinAmplitude lam g q s α (bleisteinCoord g α t)) =
      Real.exp (x * g 0) • ((Real.exp (-x * g t) * t ^ (lam - 1)) • q t) := by
  have hleft : bleisteinInv g s α (bleisteinCoord g α t) = t := leftInvOn_bleisteinInv hinj ht
  have hrpow : bleisteinCoord g α t ^ (lam - 1) *
      (t / bleisteinCoord g α t) ^ (lam - 1) = t ^ (lam - 1) := by
    rw [← Real.mul_rpow hw_pos.le (div_nonneg ht0.le hw_pos.le), mul_div_cancel₀ _ hw_pos.ne']
  have hexp : Real.exp (-x * (bleisteinCoord g α t ^ 2 / 2 -
        bleisteinCenter g α * bleisteinCoord g α t)) =
      Real.exp (x * g 0) * Real.exp (-x * g t) := by
    rw [half_sq_bleisteinCoord_sub_mul_eq_sub h0 hmin, ← Real.exp_add]
    congr 1
    ring
  rw [bleisteinAmplitude, hleft, abs_of_pos hdpos, smul_smul, smul_smul, smul_smul, hexp]
  congr 1
  calc deriv (bleisteinCoord g α) t *
        (Real.exp (x * g 0) * Real.exp (-x * g t) * bleisteinCoord g α t ^ (lam - 1)) *
        ((t / bleisteinCoord g α t) ^ (lam - 1) / deriv (bleisteinCoord g α) t)
      = Real.exp (x * g 0) * Real.exp (-x * g t) *
          (bleisteinCoord g α t ^ (lam - 1) * (t / bleisteinCoord g α t) ^ (lam - 1)) *
          (deriv (bleisteinCoord g α) t / deriv (bleisteinCoord g α) t) := by ring
    _ = Real.exp (x * g 0) * (Real.exp (-x * g t) * t ^ (lam - 1)) := by
          rw [hrpow, div_self hdpos.ne', mul_one, mul_assoc]

/-- Equivalence of integrability of the original Laplace integral (DLMF 2.3.24) on `s ⊆ Ioi 0` and
of Bleistein's transformed integral (DLMF 2.3.29) on `bleisteinCoord g α '' s`. -/
theorem integrableOn_bleistein_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {lam x : ℝ} {g : ℝ → ℝ} {q : ℝ → E} {s : Set ℝ} {α : ℝ}
    (hs : MeasurableSet s) (hs0 : s ⊆ Ioi 0) (h0 : g α ≤ g 0) (hmin : ∀ t ∈ s, g α ≤ g t)
    (hw_pos : ∀ t ∈ s, 0 < bleisteinCoord g α t) (hinj : InjOn (bleisteinCoord g α) s)
    (hderiv : ∀ t ∈ s, HasDerivWithinAt (bleisteinCoord g α) (deriv (bleisteinCoord g α) t) s t)
    (hdpos : ∀ t ∈ s, 0 < deriv (bleisteinCoord g α) t) :
    IntegrableOn (fun w ↦
        (Real.exp (-x * (w ^ 2 / 2 - bleisteinCenter g α * w)) * w ^ (lam - 1)) •
          bleisteinAmplitude lam g q s α w)
      (bleisteinCoord g α '' s) ↔
      IntegrableOn (fun t ↦ (Real.exp (-x * g t) * t ^ (lam - 1)) • q t) s := by
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul hs hderiv hinj]
  rw [integrableOn_congr_fun (fun t ht ↦ abs_deriv_smul_bleistein_integrand ht (hs0 ht) h0
    (hmin t ht) (hw_pos t ht) hinj (hdpos t ht)) hs]
  exact integrable_smul_iff (Real.exp_ne_zero (x * g 0)) _

/-- Bleistein's change of variables in the integral (DLMF 2.3.24, 2.3.29–2.3.30), multiplied by
`exp (x * g 0)`:
`exp (x * g 0) • ∫_{s} exp (-x * g t) * t ^ (λ - 1) • q t` equals the canonical quadratic integral
over `bleisteinCoord g α '' s`. -/
theorem exp_mul_integral_bleistein_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {lam x : ℝ} {g : ℝ → ℝ} {q : ℝ → E} {s : Set ℝ} {α : ℝ}
    (hs : MeasurableSet s) (hs0 : s ⊆ Ioi 0) (h0 : g α ≤ g 0) (hmin : ∀ t ∈ s, g α ≤ g t)
    (hw_pos : ∀ t ∈ s, 0 < bleisteinCoord g α t) (hinj : InjOn (bleisteinCoord g α) s)
    (hderiv : ∀ t ∈ s, HasDerivWithinAt (bleisteinCoord g α) (deriv (bleisteinCoord g α) t) s t)
    (hdpos : ∀ t ∈ s, 0 < deriv (bleisteinCoord g α) t) :
    Real.exp (x * g 0) • (∫ t in s, (Real.exp (-x * g t) * t ^ (lam - 1)) • q t) =
      ∫ w in bleisteinCoord g α '' s,
        (Real.exp (-x * (w ^ 2 / 2 - bleisteinCenter g α * w)) * w ^ (lam - 1)) •
          bleisteinAmplitude lam g q s α w := by
  rw [integral_image_eq_integral_abs_deriv_smul hs hderiv hinj,
    setIntegral_congr_fun hs (fun t ht ↦ abs_deriv_smul_bleistein_integrand ht (hs0 ht) h0
      (hmin t ht) (hw_pos t ht) hinj (hdpos t ht)),
    integral_smul]

/-- Unscaled form of Bleistein's integral identity (DLMF 2.3.29). -/
theorem integral_bleistein_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {lam x : ℝ} {g : ℝ → ℝ} {q : ℝ → E} {s : Set ℝ} {α : ℝ}
    (hs : MeasurableSet s) (hs0 : s ⊆ Ioi 0) (h0 : g α ≤ g 0) (hmin : ∀ t ∈ s, g α ≤ g t)
    (hw_pos : ∀ t ∈ s, 0 < bleisteinCoord g α t) (hinj : InjOn (bleisteinCoord g α) s)
    (hderiv : ∀ t ∈ s, HasDerivWithinAt (bleisteinCoord g α) (deriv (bleisteinCoord g α) t) s t)
    (hdpos : ∀ t ∈ s, 0 < deriv (bleisteinCoord g α) t) :
    (∫ t in s, (Real.exp (-x * g t) * t ^ (lam - 1)) • q t) =
      Real.exp (-x * g 0) • ∫ w in bleisteinCoord g α '' s,
        (Real.exp (-x * (w ^ 2 / 2 - bleisteinCenter g α * w)) * w ^ (lam - 1)) •
          bleisteinAmplitude lam g q s α w := by
  rw [← exp_mul_integral_bleistein_eq hs hs0 h0 hmin hw_pos hinj hderiv hdpos, smul_smul,
    ← Real.exp_add, (by ring : -x * g 0 + x * g 0 = 0), Real.exp_zero, one_smul]

end TauCeti
