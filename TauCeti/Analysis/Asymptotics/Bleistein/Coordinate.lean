/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Exp
import TauCeti.Analysis.Calculus.ContDiff.Differentiable
import TauCeti.Topology.Order.Interval

/-!
# Bleistein's canonical coordinate for coalescing critical points

For Laplace-type integrals `∫ t in (0, k), exp (-x * p(α, t)) * t ^ (lam - 1) • q(α, t)` in which
an interior minimum `t = α` of `p(α, ·)` may approach or cross the endpoint `t = 0`, Bleistein's
method (1966; DLMF §2.3(v), 2.3.24–2.3.28) maps `p(α, t)` onto the quadratic normal form
`w ^ 2 / 2 - a(α) * w + p(α, 0)` while fixing both `w(α, 0) = 0` and `w(α, α) = a(α)`:

* `TauCeti.bleisteinOffset p α = (SignType.sign α : ℝ) * √(2 * (p 0 - p α))`, the critical-point
  parameter `a(α)` whose sign is determined by `w(α, 0) = 0` and whose modulus is DLMF 2.3.26;
* `TauCeti.bleisteinCoord p α t`, the canonical coordinate
  `w(α, t) = a(α) + (SignType.sign (t - α) : ℝ) * √(2 * (p t - p α))`.

When `p` is `C¹` on an open set `U` containing `α` with `deriv (deriv p) α > 0` and `p α < p t`
for `t ≠ α`, `bleisteinCoord p α` is `C¹` on `U` with derivative `deriv p t / (w - a)` away from
`t = α` (DLMF 2.3.28) and `√(deriv (deriv p) α) > 0` at `t = α`. Under the derivative sign
conditions `deriv p < 0` on `U ∩ (-∞, α)` and `deriv p > 0` on `U ∩ (α, ∞)` on a convex open
domain `U`, `bleisteinCoord p α` is strictly increasing with strictly positive derivative. If
`p(t) → +∞` along a filter eventually to the right of `α`, then `w(α, t) → +∞`; having `k = +∞`
alone does not force `κ = +∞` (`TauCeti.tendsto_bleisteinCoord_one_sub_exp_neg_sq`).

## Main definitions

* `TauCeti.bleisteinOffset`: the normal-form critical parameter `a(α)`.
* `TauCeti.bleisteinCoord`: Bleistein's canonical coordinate `w(α, t)`.

## Main results

* `TauCeti.half_sq_bleisteinCoord_sub_mul_add`: quadratic phase identity
  `w ^ 2 / 2 - a * w + p 0 = p t` (DLMF 2.3.25).
* `TauCeti.strictMonoOn_bleisteinCoord`, `TauCeti.strictMonoOn_bleisteinCoord_of_deriv_sign`:
  strict monotonicity of `bleisteinCoord p α`.
* `TauCeti.tendsto_bleisteinCoord`, `TauCeti.tendsto_bleisteinCoord_atTop`: finite and infinite
  limit characterizations of `bleisteinCoord p α`.
* `TauCeti.hasDerivAt_bleisteinCoord_of_ne`, `TauCeti.hasDerivAt_bleisteinCoord_self`,
  `TauCeti.contDiffOn_bleisteinCoord`: derivative formulas (DLMF 2.3.28) and `C¹` regularity
  across the critical point `t = α`.
* `TauCeti.image_bleisteinCoord_Ioo_eq_Ioo_of_deriv_sign`,
  `TauCeti.image_bleisteinCoord_Ioo_eq_Ioi_of_deriv_sign`,
  `TauCeti.image_bleisteinCoord_Ioi_eq_Ioo_of_deriv_sign`,
  `TauCeti.image_bleisteinCoord_Ioi_eq_Ioi_of_deriv_sign`: exact interval images of `(0, k)` and
  `(0, ∞)` under derivative-sign hypotheses.

## References

* N. Bleistein, *Uniform asymptotic expansions of integrals with stationary point near algebraic
  singularity*, Comm. Pure Appl. Math. **19** (1966), 353–370.
* N. Bleistein and R. A. Handelsman, *Asymptotic Expansions of Integrals*, Holt, Rinehart and
  Winston, 1975; reprinted Dover, 1986. Chapter 9, §9.4.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted A K Peters,
  1997. Chapter 9, §10.
* NIST Digital Library of Mathematical Functions, §2.3(v), <https://dlmf.nist.gov/2.3.v>.
-/

public section

open Filter Set Function
open scoped ContDiff Topology

namespace TauCeti

/-! ### Algebraic and order properties of `bleisteinOffset` and `bleisteinCoord` -/

/-- The critical-point parameter `a(α) = sgn(α) √(2 (p 0 - p α))` in Bleistein's quadratic normal
form `w ^ 2 / 2 - a(α) * w + p 0 = p t`, with `sgn 0 = 0` so that `w(α, 0) = 0`. -/
noncomputable def bleisteinOffset (p : ℝ → ℝ) (α : ℝ) : ℝ :=
  (SignType.sign α : ℝ) * Real.sqrt (2 * (p 0 - p α))

/-- Unfolding identity for `bleisteinOffset`. -/
theorem bleisteinOffset_def (p : ℝ → ℝ) (α : ℝ) :
    bleisteinOffset p α = (SignType.sign α : ℝ) * Real.sqrt (2 * (p 0 - p α)) :=
  (rfl)

/-- When the critical point coincides with the endpoint `0`, the offset `a(0)` vanishes. -/
@[simp]
theorem bleisteinOffset_zero (p : ℝ → ℝ) : bleisteinOffset p 0 = 0 := by
  simp [bleisteinOffset]

/-- Branch formula for `bleisteinOffset` on `[0, ∞)`: `a(α) = √(2 (p 0 - p α))`. -/
theorem bleisteinOffset_of_nonneg {p : ℝ → ℝ} {α : ℝ} (hα : 0 ≤ α) :
    bleisteinOffset p α = Real.sqrt (2 * (p 0 - p α)) := by
  rcases hα.eq_or_lt with rfl | hα'
  · simp
  · simp [bleisteinOffset, sign_pos hα']

/-- Branch formula for `bleisteinOffset` on `(-∞, 0]`: `a(α) = -√(2 (p 0 - p α))`. -/
theorem bleisteinOffset_of_nonpos {p : ℝ → ℝ} {α : ℝ} (hα : α ≤ 0) :
    bleisteinOffset p α = -Real.sqrt (2 * (p 0 - p α)) := by
  rcases hα.eq_or_lt with rfl | hα'
  · simp
  · simp [bleisteinOffset, sign_neg hα']

/-- Modulus of `bleisteinOffset` (DLMF 2.3.26): `|a(α)| = √(2 (p 0 - p α))`. -/
theorem abs_bleisteinOffset (p : ℝ → ℝ) (α : ℝ) :
    |bleisteinOffset p α| = Real.sqrt (2 * (p 0 - p α)) := by
  rcases le_total 0 α with hα | hα
  · rw [bleisteinOffset_of_nonneg hα, abs_of_nonneg (Real.sqrt_nonneg _)]
  · rw [bleisteinOffset_of_nonpos hα, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- Square of `bleisteinOffset`: `a(α) ^ 2 = 2 * (p 0 - p α)` when `p α ≤ p 0`. -/
theorem sq_bleisteinOffset {p : ℝ → ℝ} {α : ℝ} (hp : p α ≤ p 0) :
    bleisteinOffset p α ^ 2 = 2 * (p 0 - p α) := by
  rw [← sq_abs, abs_bleisteinOffset, Real.sq_sqrt (by linarith)]

/-- For `α > 0` with `p α < p 0`, the offset `a(α)` is strictly positive. -/
theorem bleisteinOffset_pos {p : ℝ → ℝ} {α : ℝ} (hα : 0 < α) (hp : p α < p 0) :
    0 < bleisteinOffset p α := by
  rw [bleisteinOffset_of_nonneg hα.le]
  exact Real.sqrt_pos_of_pos (by linarith)

/-- For `α < 0` with `p α < p 0`, the offset `a(α)` is strictly negative. -/
theorem bleisteinOffset_neg {p : ℝ → ℝ} {α : ℝ} (hα : α < 0) (hp : p α < p 0) :
    bleisteinOffset p α < 0 := by
  rw [bleisteinOffset_of_nonpos hα.le, neg_lt_zero]
  exact Real.sqrt_pos_of_pos (by linarith)

/-- For `α ≥ 0`, `bleisteinOffset p α` is nonnegative. -/
theorem bleisteinOffset_nonneg {p : ℝ → ℝ} {α : ℝ} (hα : 0 ≤ α) :
    0 ≤ bleisteinOffset p α := by
  rw [bleisteinOffset_of_nonneg hα]
  exact Real.sqrt_nonneg _

/-- For `α ≤ 0`, `bleisteinOffset p α` is nonpositive. -/
theorem bleisteinOffset_nonpos {p : ℝ → ℝ} {α : ℝ} (hα : α ≤ 0) :
    bleisteinOffset p α ≤ 0 := by
  rw [bleisteinOffset_of_nonpos hα, neg_nonpos]
  exact Real.sqrt_nonneg _

/-- Bleistein's canonical coordinate `w(α, t) = a(α) + sgn(t - α) √(2 (p t - p α))`, which maps the
endpoint `t = 0` to `0`, the critical point `t = α` to `a(α)`, and transforms `p t` into
`w ^ 2 / 2 - a(α) * w + p 0`. -/
noncomputable def bleisteinCoord (p : ℝ → ℝ) (α t : ℝ) : ℝ :=
  bleisteinOffset p α + (SignType.sign (t - α) : ℝ) * Real.sqrt (2 * (p t - p α))

/-- Unfolding identity for `bleisteinCoord`. -/
theorem bleisteinCoord_def (p : ℝ → ℝ) (α t : ℝ) :
    bleisteinCoord p α t =
      bleisteinOffset p α + (SignType.sign (t - α) : ℝ) * Real.sqrt (2 * (p t - p α)) :=
  (rfl)

/-- At the critical point `t = α`, `bleisteinCoord` equals `bleisteinOffset`. -/
@[simp]
theorem bleisteinCoord_self (p : ℝ → ℝ) (α : ℝ) :
    bleisteinCoord p α α = bleisteinOffset p α := by
  simp [bleisteinCoord]

/-- At the integration endpoint `t = 0`, `bleisteinCoord` vanishes for every `α`. -/
@[simp]
theorem bleisteinCoord_zero (p : ℝ → ℝ) (α : ℝ) : bleisteinCoord p α 0 = 0 := by
  rw [bleisteinCoord, bleisteinOffset, zero_sub, Left.sign_neg, SignType.coe_neg]
  ring

/-- Branch formula for `bleisteinCoord` to the right of `α` (`α ≤ t`):
`w(α, t) = a(α) + √(2 (p t - p α))`. -/
theorem bleisteinCoord_of_ge {p : ℝ → ℝ} {α t : ℝ} (ht : α ≤ t) :
    bleisteinCoord p α t = bleisteinOffset p α + Real.sqrt (2 * (p t - p α)) := by
  rcases ht.eq_or_lt with rfl | ht'
  · simp
  · simp [bleisteinCoord, sign_pos (sub_pos.mpr ht')]

/-- Branch formula for `bleisteinCoord` to the left of `α` (`t ≤ α`):
`w(α, t) = a(α) - √(2 (p t - p α))`. -/
theorem bleisteinCoord_of_le {p : ℝ → ℝ} {α t : ℝ} (ht : t ≤ α) :
    bleisteinCoord p α t = bleisteinOffset p α - Real.sqrt (2 * (p t - p α)) := by
  rcases ht.eq_or_lt with rfl | ht'
  · simp
  · rw [bleisteinCoord, sign_neg (sub_neg.mpr ht')]
    simp [sub_eq_add_neg]

/-- Difference between `bleisteinCoord` and `bleisteinOffset`. -/
theorem bleisteinCoord_sub_bleisteinOffset (p : ℝ → ℝ) (α t : ℝ) :
    bleisteinCoord p α t - bleisteinOffset p α =
      (SignType.sign (t - α) : ℝ) * Real.sqrt (2 * (p t - p α)) :=
  add_sub_cancel_left _ _

/-- Distance from `bleisteinCoord p α t` to `bleisteinOffset p α`:
`|w(α, t) - a(α)| = √(2 (p t - p α))`. -/
theorem abs_bleisteinCoord_sub (p : ℝ → ℝ) (α t : ℝ) :
    |bleisteinCoord p α t - bleisteinOffset p α| = Real.sqrt (2 * (p t - p α)) := by
  rcases le_total α t with ht | ht
  · rw [bleisteinCoord_of_ge ht, add_sub_cancel_left, abs_of_nonneg (Real.sqrt_nonneg _)]
  · rw [bleisteinCoord_of_le ht, sub_sub_cancel_left, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- Squared distance identity `(w(α, t) - a(α)) ^ 2 = 2 * (p t - p α)` when `p α ≤ p t`. -/
theorem sq_bleisteinCoord_sub {p : ℝ → ℝ} {α t : ℝ} (hp : p α ≤ p t) :
    (bleisteinCoord p α t - bleisteinOffset p α) ^ 2 = 2 * (p t - p α) := by
  rw [← sq_abs, abs_bleisteinCoord_sub, Real.sq_sqrt (by linarith)]

/-- Bleistein's quadratic phase identity (DLMF 2.3.25):
`w(α, t) ^ 2 / 2 - a(α) * w(α, t) + p 0 = p t` whenever `p α ≤ p 0` and `p α ≤ p t`. -/
theorem half_sq_bleisteinCoord_sub_mul_add {p : ℝ → ℝ} {α t : ℝ}
    (hp0 : p α ≤ p 0) (hpt : p α ≤ p t) :
    bleisteinCoord p α t ^ 2 / 2 - bleisteinOffset p α * bleisteinCoord p α t + p 0 = p t := by
  have h0 := sq_bleisteinOffset hp0
  have ht := sq_bleisteinCoord_sub hpt
  linear_combination ht / 2 - h0 / 2

/-- Shifted form of Bleistein's quadratic phase identity:
`w(α, t) ^ 2 / 2 - a(α) * w(α, t) = p t - p 0` whenever `p α ≤ p 0` and `p α ≤ p t`. -/
theorem half_sq_bleisteinCoord_sub_mul {p : ℝ → ℝ} {α t : ℝ}
    (hp0 : p α ≤ p 0) (hpt : p α ≤ p t) :
    bleisteinCoord p α t ^ 2 / 2 - bleisteinOffset p α * bleisteinCoord p α t = p t - p 0 := by
  linarith [half_sq_bleisteinCoord_sub_mul_add hp0 hpt]

/-- To the left of `α`, `bleisteinCoord p α t < bleisteinOffset p α` whenever `p α < p t`. -/
theorem bleisteinCoord_lt_bleisteinOffset {p : ℝ → ℝ} {α t : ℝ} (ht : t < α) (hp : p α < p t) :
    bleisteinCoord p α t < bleisteinOffset p α := by
  rw [bleisteinCoord_of_le ht.le]
  linarith [Real.sqrt_pos_of_pos (x := 2 * (p t - p α)) (by linarith)]

/-- To the right of `α`, `bleisteinOffset p α < bleisteinCoord p α t` whenever `p α < p t`. -/
theorem bleisteinOffset_lt_bleisteinCoord {p : ℝ → ℝ} {α t : ℝ} (ht : α < t) (hp : p α < p t) :
    bleisteinOffset p α < bleisteinCoord p α t := by
  rw [bleisteinCoord_of_ge ht.le]
  linarith [Real.sqrt_pos_of_pos (x := 2 * (p t - p α)) (by linarith)]

/-- Away from `α`, `bleisteinCoord p α t ≠ bleisteinOffset p α` whenever `p α < p t`. -/
theorem bleisteinCoord_ne_bleisteinOffset {p : ℝ → ℝ} {α t : ℝ} (ht : t ≠ α) (hp : p α < p t) :
    bleisteinCoord p α t ≠ bleisteinOffset p α := by
  rcases ht.lt_or_gt with h | h
  · exact (bleisteinCoord_lt_bleisteinOffset h hp).ne
  · exact (bleisteinOffset_lt_bleisteinCoord h hp).ne'

/-- Continuity of `bleisteinCoord p α` on any set `s` on which `p` is continuous. -/
theorem continuousOn_bleisteinCoord {p : ℝ → ℝ} {α : ℝ} {s : Set ℝ} (hp : ContinuousOn p s) :
    ContinuousOn (bleisteinCoord p α) s := by
  intro t ht
  rcases lt_trichotomy t α with hlt | rfl | hgt
  · have hc : ContinuousWithinAt
        (fun u ↦ bleisteinOffset p α - Real.sqrt (2 * (p u - p α))) s t :=
      continuousWithinAt_const.sub <| Real.continuous_sqrt.continuousAt.comp_continuousWithinAt <|
        continuousWithinAt_const.mul ((hp t ht).sub continuousWithinAt_const)
    refine hc.congr_of_eventuallyEq ?_ (bleisteinCoord_of_le hlt.le)
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hlt)] with u hu
    exact bleisteinCoord_of_le (le_of_lt hu)
  · rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    have hrad : Tendsto (fun u ↦ Real.sqrt (2 * (p u - p t))) (𝓝[s] t) (𝓝 0) := by
      simpa only [Function.comp_def, sub_self, mul_zero, Real.sqrt_zero] using
        (Real.continuous_sqrt.continuousAt.tendsto.comp
          (((hp t ht).tendsto.sub_const (p t)).const_mul 2))
    refine hrad.congr fun u ↦ ?_
    rw [bleisteinCoord_self, Real.norm_eq_abs, abs_bleisteinCoord_sub]
  · have hc : ContinuousWithinAt
        (fun u ↦ bleisteinOffset p α + Real.sqrt (2 * (p u - p α))) s t :=
      continuousWithinAt_const.add <| Real.continuous_sqrt.continuousAt.comp_continuousWithinAt <|
        continuousWithinAt_const.mul ((hp t ht).sub continuousWithinAt_const)
    refine hc.congr_of_eventuallyEq ?_ (bleisteinCoord_of_ge hgt.le)
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hgt)] with u hu
    exact bleisteinCoord_of_ge (le_of_lt hu)

/-! ### Monotonicity and upper limit `κ` -/

/-- If `p` is strictly decreasing on `s ∩ (-∞, α]`, strictly increasing on `s ∩ [α, ∞)`, and
strictly above `p α` on `s \ {α}`, then `bleisteinCoord p α` is strictly increasing on `s`. -/
theorem strictMonoOn_bleisteinCoord_of_forall_lt {p : ℝ → ℝ} {α : ℝ} {s : Set ℝ}
    (hleft : StrictAntiOn p (s ∩ Iic α)) (hright : StrictMonoOn p (s ∩ Ici α))
    (hpos : ∀ t ∈ s, t ≠ α → p α < p t) :
    StrictMonoOn (bleisteinCoord p α) s := by
  intro t₁ ht₁ t₂ ht₂ hlt
  rcases lt_trichotomy t₂ α with ht₂α | rfl | hαt₂
  · have ht₁α : t₁ < α := hlt.trans ht₂α
    have hp₂ : p α < p t₂ := hpos t₂ ht₂ ht₂α.ne
    have hp₁₂ : p t₂ < p t₁ := hleft ⟨ht₁, ht₁α.le⟩ ⟨ht₂, ht₂α.le⟩ hlt
    have hsq : Real.sqrt (2 * (p t₂ - p α)) < Real.sqrt (2 * (p t₁ - p α)) :=
      Real.sqrt_lt_sqrt (by linarith) (by linarith)
    rw [bleisteinCoord_of_le ht₁α.le, bleisteinCoord_of_le ht₂α.le]
    linarith
  · simpa using bleisteinCoord_lt_bleisteinOffset hlt (hpos t₁ ht₁ hlt.ne)
  · rcases lt_trichotomy t₁ α with ht₁α | rfl | hαt₁
    · exact (bleisteinCoord_lt_bleisteinOffset ht₁α (hpos t₁ ht₁ ht₁α.ne)).trans
        (bleisteinOffset_lt_bleisteinCoord hαt₂ (hpos t₂ ht₂ hαt₂.ne'))
    · simpa using bleisteinOffset_lt_bleisteinCoord hαt₂ (hpos t₂ ht₂ hαt₂.ne')
    · have hp₁ : p α < p t₁ := hpos t₁ ht₁ hαt₁.ne'
      have hp₁₂ : p t₁ < p t₂ := hright ⟨ht₁, hαt₁.le⟩ ⟨ht₂, hαt₂.le⟩ hlt
      have hsq : Real.sqrt (2 * (p t₁ - p α)) < Real.sqrt (2 * (p t₂ - p α)) :=
        Real.sqrt_lt_sqrt (by linarith) (by linarith)
      rw [bleisteinCoord_of_ge hαt₁.le, bleisteinCoord_of_ge hαt₂.le]
      linarith

/-- If `α ∈ s`, `p` is strictly decreasing on `s ∩ (-∞, α]`, and `p` is strictly increasing on
`s ∩ [α, ∞)`, then `bleisteinCoord p α` is strictly increasing on `s`. -/
theorem strictMonoOn_bleisteinCoord {p : ℝ → ℝ} {α : ℝ} {s : Set ℝ} (hα : α ∈ s)
    (hleft : StrictAntiOn p (s ∩ Iic α)) (hright : StrictMonoOn p (s ∩ Ici α)) :
    StrictMonoOn (bleisteinCoord p α) s := by
  refine strictMonoOn_bleisteinCoord_of_forall_lt hleft hright fun t ht hne ↦ ?_
  rcases hne.lt_or_gt with hlt | hgt
  · exact hleft ⟨ht, hlt.le⟩ ⟨hα, le_rfl⟩ hlt
  · exact hright ⟨hα, le_rfl⟩ ⟨ht, hgt.le⟩ hgt

/-- When `bleisteinCoord p α` is strictly increasing on `s` containing `0`, it is positive for
`t > 0` in `s`. -/
theorem bleisteinCoord_pos {p : ℝ → ℝ} {α t : ℝ} {s : Set ℝ}
    (hmono : StrictMonoOn (bleisteinCoord p α) s) (h0 : 0 ∈ s) (ht : t ∈ s) (ht0 : 0 < t) :
    0 < bleisteinCoord p α t := by
  simpa [bleisteinCoord_zero] using hmono h0 ht ht0

/-- When `bleisteinCoord p α` is strictly increasing on `s` containing `0`, it is negative for
`t < 0` in `s`. -/
theorem bleisteinCoord_neg {p : ℝ → ℝ} {α t : ℝ} {s : Set ℝ}
    (hmono : StrictMonoOn (bleisteinCoord p α) s) (h0 : 0 ∈ s) (ht : t ∈ s) (ht0 : t < 0) :
    bleisteinCoord p α t < 0 := by
  simpa [bleisteinCoord_zero] using hmono ht h0 ht0

/-- Along any filter eventually to the right of `α` on which `p` tends to `+∞`,
`bleisteinCoord p α` also tends to `+∞`. -/
theorem tendsto_bleisteinCoord_atTop {p : ℝ → ℝ} {α : ℝ} {l : Filter ℝ}
    (hl : ∀ᶠ t in l, α ≤ t) (hp : Tendsto p l atTop) :
    Tendsto (bleisteinCoord p α) l atTop := by
  have hsq : Tendsto (fun t ↦ bleisteinOffset p α + Real.sqrt (2 * (p t - p α))) l atTop :=
    tendsto_atTop_add_const_left _ _ <| Real.tendsto_sqrt_atTop.comp <|
      (tendsto_atTop_add_const_right _ (-p α) hp).const_mul_atTop zero_lt_two
  exact hsq.congr' (hl.mono fun _ ht ↦ (bleisteinCoord_of_ge ht).symm)

/-- If `p t → +∞` as `t → +∞`, then `bleisteinCoord p α t → +∞` as `t → +∞` (`κ = ∞`). -/
theorem tendsto_bleisteinCoord_atTop_atTop {p : ℝ → ℝ} {α : ℝ} (hp : Tendsto p atTop atTop) :
    Tendsto (bleisteinCoord p α) atTop atTop :=
  tendsto_bleisteinCoord_atTop (eventually_ge_atTop α) hp

/-- If `α < k` and `p t → +∞` as `t → k⁻`, then `bleisteinCoord p α t → +∞` as `t → k⁻`
(`κ = ∞`). -/
theorem tendsto_bleisteinCoord_nhdsLT_atTop {p : ℝ → ℝ} {α k : ℝ} (hαk : α < k)
    (hp : Tendsto p (𝓝[<] k) atTop) :
    Tendsto (bleisteinCoord p α) (𝓝[<] k) atTop :=
  tendsto_bleisteinCoord_atTop
    (eventually_nhdsWithin_of_eventually_nhds ((eventually_gt_nhds hαk).mono fun _ ↦ le_of_lt)) hp

/-- Along any filter eventually to the right of `α` on which `p` tends to a finite limit `pb`,
`bleisteinCoord p α` tends to `a(α) + √(2 (pb - p α))`. -/
theorem tendsto_bleisteinCoord {p : ℝ → ℝ} {α pb : ℝ} {l : Filter ℝ}
    (hl : ∀ᶠ t in l, α ≤ t) (hp : Tendsto p l (𝓝 pb)) :
    Tendsto (bleisteinCoord p α) l
      (𝓝 (bleisteinOffset p α + Real.sqrt (2 * (pb - p α)))) := by
  have hlim : Tendsto (fun t ↦ bleisteinOffset p α + Real.sqrt (2 * (p t - p α))) l
      (𝓝 (bleisteinOffset p α + Real.sqrt (2 * (pb - p α)))) :=
    tendsto_const_nhds.add <| Real.continuous_sqrt.continuousAt.tendsto.comp <|
      (hp.sub_const (p α)).const_mul 2
  exact hlim.congr' (hl.mono fun _ ht ↦ (bleisteinCoord_of_ge ht).symm)

/-- If `p t → pb` as `t → +∞`, then `bleisteinCoord p α t` tends to the finite upper limit
`κ = a(α) + √(2 (pb - p α))` as `t → +∞`. -/
theorem tendsto_bleisteinCoord_atTop_nhds {p : ℝ → ℝ} {α pb : ℝ} (hp : Tendsto p atTop (𝓝 pb)) :
    Tendsto (bleisteinCoord p α) atTop
      (𝓝 (bleisteinOffset p α + Real.sqrt (2 * (pb - p α)))) :=
  tendsto_bleisteinCoord (eventually_ge_atTop α) hp

/-- If `α < k` and `p t → pb` as `t → k⁻`, then `bleisteinCoord p α t` tends to the finite upper
limit `κ = a(α) + √(2 (pb - p α))`. -/
theorem tendsto_bleisteinCoord_nhdsLT {p : ℝ → ℝ} {α k pb : ℝ} (hαk : α < k)
    (hp : Tendsto p (𝓝[<] k) (𝓝 pb)) :
    Tendsto (bleisteinCoord p α) (𝓝[<] k)
      (𝓝 (bleisteinOffset p α + Real.sqrt (2 * (pb - p α)))) :=
  tendsto_bleisteinCoord
    (eventually_nhdsWithin_of_eventually_nhds ((eventually_gt_nhds hαk).mono fun _ ↦ le_of_lt)) hp

/-- Having upper integration limit `k = +∞` does not by itself force `κ = +∞`: for the smooth phase
`p t = 1 - exp (-t ^ 2)` with critical point `α = 0`, `bleisteinCoord p 0 t` tends to the finite
limit `√2` as `t → +∞`. -/
theorem tendsto_bleisteinCoord_one_sub_exp_neg_sq :
    Tendsto (bleisteinCoord (fun t ↦ 1 - Real.exp (-t ^ 2)) 0) atTop (𝓝 (Real.sqrt 2)) := by
  have hp : Tendsto (fun t : ℝ ↦ 1 - Real.exp (-t ^ 2)) atTop (𝓝 1) := by
    have hexp : Tendsto (fun t : ℝ ↦ Real.exp (-t ^ 2)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp <| tendsto_neg_atTop_atBot.comp <|
        Filter.tendsto_pow_atTop (by norm_num)
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hexp
  simpa using tendsto_bleisteinCoord_atTop_nhds (α := 0) hp

/-! ### Derivatives and `C¹` regularity of `bleisteinCoord` -/

/-- Derivative of `bleisteinCoord` away from the critical point `t = α` (DLMF 2.3.28):
`dw/dt = p' / (w - a)`. -/
theorem hasDerivAt_bleisteinCoord_of_ne {p : ℝ → ℝ} {α t p' : ℝ} (ht : t ≠ α) (hpt : p α < p t)
    (hp : HasDerivAt p p' t) :
    HasDerivAt (bleisteinCoord p α) (p' / (bleisteinCoord p α t - bleisteinOffset p α)) t := by
  have hpos : 0 < 2 * (p t - p α) := by linarith
  have hrad : HasDerivAt (fun s ↦ Real.sqrt (2 * (p s - p α)))
      (p' / Real.sqrt (2 * (p t - p α))) t :=
    (((hp.sub_const (p α)).const_mul 2).sqrt hpos.ne').congr_deriv
      (mul_div_mul_left p' _ two_ne_zero)
  rcases ht.lt_or_gt with hlt | hgt
  · have heq : bleisteinCoord p α =ᶠ[𝓝 t]
        fun s ↦ bleisteinOffset p α - Real.sqrt (2 * (p s - p α)) := by
      filter_upwards [Iio_mem_nhds hlt] with s hs
      exact bleisteinCoord_of_le hs.le
    refine (hrad.const_sub (bleisteinOffset p α)).congr_of_eventuallyEq heq |>.congr_deriv ?_
    rw [bleisteinCoord_of_le hlt.le, sub_sub_cancel_left, div_neg]
  · have heq : bleisteinCoord p α =ᶠ[𝓝 t]
        fun s ↦ bleisteinOffset p α + Real.sqrt (2 * (p s - p α)) := by
      filter_upwards [Ioi_mem_nhds hgt] with s hs
      exact bleisteinCoord_of_ge hs.le
    refine (hrad.const_add (bleisteinOffset p α)).congr_of_eventuallyEq heq |>.congr_deriv ?_
    rw [bleisteinCoord_of_ge hgt.le, add_sub_cancel_left]

/-- Value of `deriv (bleisteinCoord p α) t` for `t ≠ α` when `p α < p t` (DLMF 2.3.28). -/
theorem deriv_bleisteinCoord_of_ne {p : ℝ → ℝ} {α t : ℝ} (ht : t ≠ α) (hpt : p α < p t)
    (hp : DifferentiableAt ℝ p t) :
    deriv (bleisteinCoord p α) t =
      deriv p t / (bleisteinCoord p α t - bleisteinOffset p α) :=
  (hasDerivAt_bleisteinCoord_of_ne ht hpt hp.hasDerivAt).deriv

/-- Difference quotient identity `(w(α, t) - w(α, α)) / (t - α) = √(2 (p t - p α) / (t - α) ^ 2)`
for `t ≠ α`. -/
theorem slope_bleisteinCoord_eq_sqrt (p : ℝ → ℝ) (α : ℝ) {t : ℝ} (ht : t ≠ α) :
    slope (bleisteinCoord p α) α t = Real.sqrt (2 * (p t - p α) / (t - α) ^ 2) := by
  have hsub : t - α ≠ 0 := sub_ne_zero.mpr ht
  rw [slope_def_field, bleisteinCoord_self, bleisteinCoord_sub_bleisteinOffset,
    Real.sqrt_div' _ (sq_nonneg (t - α)), Real.sqrt_sq_eq_abs]
  rcases lt_or_gt_of_ne hsub with hneg | hpos
  · simp only [sign_neg hneg, SignType.coe_neg, SignType.coe_one, neg_one_mul, abs_of_neg hneg,
      div_neg, neg_div]
  · simp only [sign_pos hpos, SignType.coe_one, one_mul, abs_of_pos hpos]

/-- At the critical point `t = α`, `bleisteinCoord p α` is differentiable with derivative `√p''`. -/
theorem hasDerivAt_bleisteinCoord_self {p : ℝ → ℝ} {α p'' : ℝ}
    (hp : ∀ᶠ t in 𝓝 α, DifferentiableAt ℝ p t) (hp'0 : deriv p α = 0)
    (hp'' : HasDerivAt (deriv p) p'' α) :
    HasDerivAt (bleisteinCoord p α) (Real.sqrt p'') α := by
  have hp_cont : ContinuousAt p α := hp.self_of_nhds.continuousAt
  have hdg : ∀ t : ℝ, HasDerivAt (fun s ↦ (s - α) ^ 2) (2 * (t - α)) t := fun t ↦
    (((hasDerivAt_id t).sub_const α).pow 2).congr_deriv (by simp)
  have hnum0 : Tendsto (fun t ↦ 2 * (p t - p α)) (𝓝 α) (𝓝 0) := by
    simpa using (hp_cont.tendsto.sub_const (p α)).const_mul 2
  have hden0 : Tendsto (fun t ↦ (t - α) ^ 2) (𝓝 α) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ ↦ (t - α) ^ 2) := (continuous_id.sub continuous_const).pow 2
    simpa using hc.tendsto α
  have hratio : Tendsto (fun t ↦ 2 * deriv p t / (2 * (t - α))) (𝓝[≠] α) (𝓝 p'') := by
    refine (hasDerivAt_iff_tendsto_slope.mp hp'').congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t _
    rw [slope_def_field, hp'0, sub_zero, mul_div_mul_left _ _ two_ne_zero]
  have hq : Tendsto (fun t ↦ 2 * (p t - p α) / (t - α) ^ 2) (𝓝[≠] α) (𝓝 p'') :=
    HasDerivAt.lhopital_zero_nhdsNE
      ((hp.filter_mono nhdsWithin_le_nhds).mono fun _ ht ↦
        (ht.hasDerivAt.sub_const (p α)).const_mul 2)
      (Eventually.of_forall hdg)
      (eventually_mem_nhdsWithin.mono fun _ ht ↦ mul_ne_zero two_ne_zero (sub_ne_zero.mpr ht))
      (hnum0.mono_left nhdsWithin_le_nhds) (hden0.mono_left nhdsWithin_le_nhds) hratio
  rw [hasDerivAt_iff_tendsto_slope]
  refine (Real.continuous_sqrt.continuousAt.tendsto.comp hq).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (slope_bleisteinCoord_eq_sqrt p α ht).symm

/-- `ContDiffAt` form of `hasDerivAt_bleisteinCoord_self`: if `p` is `C²` at `α` with
`deriv p α = 0`, then `bleisteinCoord p α` has derivative `√(deriv (deriv p) α)` at `α`. -/
theorem hasDerivAt_bleisteinCoord_self_of_contDiffAt {p : ℝ → ℝ} {α : ℝ}
    (hp : ContDiffAt ℝ 2 p α) (hp'0 : deriv p α = 0) :
    HasDerivAt (bleisteinCoord p α) (Real.sqrt (deriv (deriv p) α)) α :=
  hasDerivAt_bleisteinCoord_self (hp.eventually_differentiableAt one_le_two) hp'0
    hp.differentiableAt_deriv_two.hasDerivAt

/-- Value of `deriv (bleisteinCoord p α) α` when `p` is differentiable near `α` with
`deriv p α = 0` and `deriv p` differentiable at `α`. -/
theorem deriv_bleisteinCoord_self {p : ℝ → ℝ} {α : ℝ}
    (hp : ∀ᶠ t in 𝓝 α, DifferentiableAt ℝ p t) (hp'0 : deriv p α = 0)
    (hp' : DifferentiableAt ℝ (deriv p) α) :
    deriv (bleisteinCoord p α) α = Real.sqrt (deriv (deriv p) α) :=
  (hasDerivAt_bleisteinCoord_self hp hp'0 hp'.hasDerivAt).deriv

/-- Positivity of `deriv (bleisteinCoord p α) α` at a nondegenerate minimum (`p''(α) > 0`). -/
theorem deriv_bleisteinCoord_self_pos {p : ℝ → ℝ} {α : ℝ}
    (hp : ∀ᶠ t in 𝓝 α, DifferentiableAt ℝ p t) (hp'0 : deriv p α = 0)
    (hp'' : 0 < deriv (deriv p) α) :
    0 < deriv (bleisteinCoord p α) α := by
  rw [deriv_bleisteinCoord_self hp hp'0 (differentiableAt_of_deriv_ne_zero hp''.ne')]
  exact Real.sqrt_pos_of_pos hp''

/-- Continuity of `deriv (bleisteinCoord p α)` at the critical point `t = α` when `p''(α) > 0`. -/
theorem continuousAt_deriv_bleisteinCoord_self {p : ℝ → ℝ} {α p'' : ℝ}
    (hp : ∀ᶠ t in 𝓝 α, DifferentiableAt ℝ p t) (hp'0 : deriv p α = 0)
    (hp'' : HasDerivAt (deriv p) p'' α) (hp''_pos : 0 < p'') :
    ContinuousAt (deriv (bleisteinCoord p α)) α := by
  rw [continuousAt_iff_punctured_nhds, (hasDerivAt_bleisteinCoord_self hp hp'0 hp'').deriv]
  have hnum : Tendsto (fun t ↦ slope (deriv p) α t) (𝓝[≠] α) (𝓝 p'') :=
    hasDerivAt_iff_tendsto_slope.mp hp''
  have hden : Tendsto (fun t ↦ slope (bleisteinCoord p α) α t) (𝓝[≠] α) (𝓝 (Real.sqrt p'')) :=
    hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_bleisteinCoord_self hp hp'0 hp'')
  have hq_pos : ∀ᶠ t in 𝓝[≠] α, p α < p t := by
    filter_upwards [hden.eventually (Ioi_mem_nhds (Real.sqrt_pos_of_pos hp''_pos)),
      self_mem_nhdsWithin] with t hpos (ht : t ≠ α)
    rw [slope_bleisteinCoord_eq_sqrt p α ht, Real.sqrt_pos] at hpos
    have hmul : 0 < 2 * (p t - p α) :=
      (div_pos_iff_of_pos_right (sq_pos_of_ne_zero (sub_ne_zero.mpr ht))).mp hpos
    linarith
  have hdiv : Tendsto (fun t ↦ slope (deriv p) α t / slope (bleisteinCoord p α) α t)
      (𝓝[≠] α) (𝓝 (Real.sqrt p'')) := by
    simpa [Pi.div_def, Real.div_sqrt] using hnum.div hden (Real.sqrt_pos_of_pos hp''_pos).ne'
  refine hdiv.congr' ?_
  filter_upwards [hq_pos, hp.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t hpt hdt ht
  rw [slope_def_field, slope_def_field, deriv_bleisteinCoord_of_ne ht hpt hdt, bleisteinCoord_self,
    hp'0, sub_zero, div_div_div_cancel_right₀ (sub_ne_zero.mpr ht)]

/-- Fermat's theorem on an open set `U`: if `p α < p t` for every `t ∈ U \ {α}`, then
`deriv p α = 0`. -/
private lemma deriv_eq_zero_of_isOpen_forall_lt {p : ℝ → ℝ} {α : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hα : α ∈ U) (hppos : ∀ t ∈ U, t ≠ α → p α < p t) :
    deriv p α = 0 :=
  IsLocalMin.deriv_eq_zero <| eventually_of_mem (hU.mem_nhds hα) fun t ht ↦
    (eq_or_ne t α).elim (fun h ↦ h ▸ le_rfl) fun hne ↦ (hppos t ht hne).le

/-- `C¹` regularity of `bleisteinCoord p α` on an open set `U` containing the critical point `α`,
assuming `p` is `C¹` on `U`, `deriv (deriv p) α > 0`, and `p α < p t` for `t ∈ U \ {α}`. -/
theorem contDiffOn_bleisteinCoord {p : ℝ → ℝ} {α : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hα : α ∈ U) (hp : ContDiffOn ℝ 1 p U)
    (hp'' : 0 < deriv (deriv p) α) (hppos : ∀ t ∈ U, t ≠ α → p α < p t) :
    ContDiffOn ℝ 1 (bleisteinCoord p α) U := by
  have hp'0 : deriv p α = 0 := deriv_eq_zero_of_isOpen_forall_lt hU hα hppos
  have hp1 : ∀ᶠ s in 𝓝 α, DifferentiableAt ℝ p s :=
    (hp.contDiffAt (hU.mem_nhds hα)).eventually_differentiableAt le_rfl
  have hp2 : HasDerivAt (deriv p) (deriv (deriv p) α) α :=
    (differentiableAt_of_deriv_ne_zero hp''.ne').hasDerivAt
  have hdiff : DifferentiableOn ℝ (bleisteinCoord p α) U := by
    intro t ht
    rcases eq_or_ne α t with rfl | hne
    · exact (hasDerivAt_bleisteinCoord_self hp1 hp'0 hp2).differentiableAt.differentiableWithinAt
    · have hpt : DifferentiableAt ℝ p t :=
        (hp.contDiffAt (hU.mem_nhds ht)).differentiableAt one_ne_zero
      exact (hasDerivAt_bleisteinCoord_of_ne hne.symm (hppos t ht hne.symm)
        hpt.hasDerivAt).differentiableAt.differentiableWithinAt
  refine (contDiffOn_succ_iff_deriv_of_isOpen (n := 0) hU).mpr
    ⟨hdiff, by simp, contDiffOn_zero.mpr fun t ht ↦ ?_⟩
  rcases eq_or_ne α t with rfl | hne
  · exact (continuousAt_deriv_bleisteinCoord_self hp1 hp'0 hp2 hp'').continuousWithinAt
  · have hopen : IsOpen (U \ {α}) := hU.sdiff isClosed_singleton
    have hmem : U \ {α} ∈ 𝓝 t := hopen.mem_nhds ⟨ht, hne.symm⟩
    have hp'_cont : ContinuousAt (deriv p) t :=
      (hp.continuousOn_deriv_of_isOpen hU le_rfl).continuousAt (hU.mem_nhds ht)
    have hw_cont : ContinuousAt (bleisteinCoord p α) t :=
      hdiff.continuousOn.continuousAt (hU.mem_nhds ht)
    have hquot : ContinuousAt
        (fun s ↦ deriv p s / (bleisteinCoord p α s - bleisteinOffset p α)) t :=
      hp'_cont.div (hw_cont.sub continuousAt_const)
        (sub_ne_zero.mpr (bleisteinCoord_ne_bleisteinOffset hne.symm (hppos t ht hne.symm)))
    refine (hquot.congr ?_).continuousWithinAt
    filter_upwards [hmem] with s hs
    have hds : DifferentiableAt ℝ p s :=
      (hp.contDiffAt (hU.mem_nhds hs.1)).differentiableAt one_ne_zero
    exact (deriv_bleisteinCoord_of_ne hs.2 (hppos s hs.1 hs.2) hds).symm

/-- Positivity of `deriv (bleisteinCoord p α)` throughout `U` when `p` is differentiable on open
`U`, `deriv p < 0` to the left of `α`, `deriv p > 0` to the right of `α`, and
`deriv (deriv p) α > 0`. -/
theorem deriv_bleisteinCoord_pos {p : ℝ → ℝ} {α : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hα : α ∈ U) (hp : DifferentiableOn ℝ p U)
    (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0)
    (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (hppos : ∀ t ∈ U, t ≠ α → p α < p t) {t : ℝ} (ht : t ∈ U) :
    0 < deriv (bleisteinCoord p α) t := by
  rcases eq_or_ne α t with rfl | hne
  · have hp'0 : deriv p α = 0 := deriv_eq_zero_of_isOpen_forall_lt hU hα hppos
    have hp1 : ∀ᶠ s in 𝓝 α, DifferentiableAt ℝ p s :=
      eventually_of_mem (hU.mem_nhds hα) fun _ hs ↦ hp.differentiableAt (hU.mem_nhds hs)
    exact deriv_bleisteinCoord_self_pos hp1 hp'0 hp''
  · have hdt : DifferentiableAt ℝ p t := hp.differentiableAt (hU.mem_nhds ht)
    rw [deriv_bleisteinCoord_of_ne hne.symm (hppos t ht hne.symm) hdt]
    rcases hne.symm.lt_or_gt with hlt | hgt
    · exact div_pos_of_neg_of_neg (hpleft t ht hlt)
        (sub_neg.mpr (bleisteinCoord_lt_bleisteinOffset hlt (hppos t ht hne.symm)))
    · exact div_pos (hpright t ht hgt)
        (sub_pos.mpr (bleisteinOffset_lt_bleisteinCoord hgt (hppos t ht hne.symm)))

/-- If `bleisteinCoord p α` is injective on `U` containing `α`, then `p α < p t` for every
`t ∈ U \ {α}`. -/
theorem lt_of_injOn_bleisteinCoord {p : ℝ → ℝ} {α : ℝ} {U : Set ℝ}
    (hinj : InjOn (bleisteinCoord p α) U) (hα : α ∈ U) {t : ℝ} (ht : t ∈ U) (hne : t ≠ α) :
    p α < p t := by
  by_contra! hle
  refine hne (hinj ht hα ?_)
  simp [bleisteinCoord, Real.sqrt_eq_zero_of_nonpos (x := p t - p α) (by linarith)]

/-- If `bleisteinCoord p α` is injective on `U` containing `α`, then `p α ≤ p t` for every
`t ∈ U`. -/
theorem le_of_injOn_bleisteinCoord {p : ℝ → ℝ} {α : ℝ} {U : Set ℝ}
    (hinj : InjOn (bleisteinCoord p α) U) (hα : α ∈ U) {t : ℝ} (ht : t ∈ U) :
    p α ≤ p t :=
  (eq_or_ne t α).elim (fun h ↦ h ▸ le_rfl) fun hne ↦
    (lt_of_injOn_bleisteinCoord hinj hα ht hne).le

/-- On a convex set `U` (such as any interval in `ℝ`) containing `α`, continuity of `p` together
with the derivative sign conditions `t < α → deriv p t < 0` and `α < t → 0 < deriv p t` imply
`StrictMonoOn (bleisteinCoord p α) U`. -/
theorem strictMonoOn_bleisteinCoord_of_deriv_sign {p : ℝ → ℝ} {α : ℝ} {U : Set ℝ}
    (hconv : Convex ℝ U) (hα : α ∈ U) (hp : ContinuousOn p U)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0)
    (hpright : ∀ t ∈ U, α < t → 0 < deriv p t) :
    StrictMonoOn (bleisteinCoord p α) U := by
  have hanti : StrictAntiOn p (U ∩ Iic α) :=
    strictAntiOn_of_deriv_neg (hconv.inter (convex_Iic α)) (hp.mono inter_subset_left) fun s hs ↦ by
      rw [interior_inter, interior_Iic] at hs
      exact hpleft s (interior_subset hs.1) hs.2
  have hmono : StrictMonoOn p (U ∩ Ici α) :=
    strictMonoOn_of_deriv_pos (hconv.inter (convex_Ici α)) (hp.mono inter_subset_left) fun s hs ↦ by
      rw [interior_inter, interior_Ici] at hs
      exact hpright s (interior_subset hs.1) hs.2
  exact strictMonoOn_bleisteinCoord hα hanti hmono

/-- `C¹` regularity of `bleisteinCoord p α` on an open convex set `U` containing `α` under
derivative-sign hypotheses on `p`. -/
theorem contDiffOn_bleisteinCoord_of_deriv_sign {p : ℝ → ℝ} {α : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hα : α ∈ U) (hp : ContDiffOn ℝ 1 p U)
    (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0)
    (hpright : ∀ t ∈ U, α < t → 0 < deriv p t) :
    ContDiffOn ℝ 1 (bleisteinCoord p α) U := by
  have hmono := strictMonoOn_bleisteinCoord_of_deriv_sign hconv hα hp.continuousOn hpleft hpright
  exact contDiffOn_bleisteinCoord hU hα hp hp'' fun _ ht hne ↦
    lt_of_injOn_bleisteinCoord hmono.injOn hα ht hne

/-- Positivity of `deriv (bleisteinCoord p α)` on an open convex set `U` containing `α` under
derivative-sign hypotheses on `p`. -/
theorem deriv_bleisteinCoord_pos_of_deriv_sign {p : ℝ → ℝ} {α : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hα : α ∈ U) (hp : DifferentiableOn ℝ p U)
    (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0)
    (hpright : ∀ t ∈ U, α < t → 0 < deriv p t) {t : ℝ} (ht : t ∈ U) :
    0 < deriv (bleisteinCoord p α) t := by
  have hmono := strictMonoOn_bleisteinCoord_of_deriv_sign hconv hα hp.continuousOn hpleft hpright
  exact deriv_bleisteinCoord_pos hU hα hp hp'' hpleft hpright
    (fun _ hs hne ↦ lt_of_injOn_bleisteinCoord hmono.injOn hα hs hne) ht

/-- Image of `(0, k)` under `bleisteinCoord p α` with finite limit `κ = lim_{t → k⁻} w(α, t)`
under derivative-sign hypotheses on a convex domain `U`. -/
theorem image_bleisteinCoord_Ioo_eq_Ioo_of_deriv_sign {p : ℝ → ℝ} {α k κ : ℝ} {U : Set ℝ}
    (hk : 0 < k) (hIco : Ico 0 k ⊆ U) (hconv : Convex ℝ U) (hα : α ∈ U) (hp : ContinuousOn p U)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0) (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (htend : Tendsto (bleisteinCoord p α) (𝓝[<] k) (𝓝 κ)) :
    bleisteinCoord p α '' Ioo 0 k = Ioo 0 κ := by
  have hmono := strictMonoOn_bleisteinCoord_of_deriv_sign hconv hα hp hpleft hpright
  simpa [bleisteinCoord_zero] using
    ((continuousOn_bleisteinCoord hp).mono hIco).image_Ioo_of_strictMonoOn_of_tendsto
      hk (hmono.mono hIco) htend

/-- Image of `(0, k)` under `bleisteinCoord p α` when `p t → +∞` as `t → k⁻` (`κ = +∞`) under
derivative-sign hypotheses on a convex domain `U`. -/
theorem image_bleisteinCoord_Ioo_eq_Ioi_of_deriv_sign {p : ℝ → ℝ} {α k : ℝ} {U : Set ℝ}
    (hk : 0 < k) (hIco : Ico 0 k ⊆ U) (hconv : Convex ℝ U) (hα : α ∈ U) (hp : ContinuousOn p U)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0) (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (htend : Tendsto p (𝓝[<] k) atTop) :
    bleisteinCoord p α '' Ioo 0 k = Ioi 0 := by
  have hαk : α < k := by
    by_contra! hkα
    have hkU : k ∈ U := hconv.ordConnected.out (hIco ⟨le_rfl, hk⟩) hα ⟨hk.le, hkα⟩
    have hnhds : Tendsto p (𝓝[<] k) (𝓝 (p k)) :=
      (hp k hkU).tendsto.mono_left <| nhdsWithin_le_iff.mpr <|
        mem_of_superset (Ioo_mem_nhdsLT hk) (Ioo_subset_Ico_self.trans hIco)
    exact not_tendsto_nhds_of_tendsto_atTop htend (p k) hnhds
  have hmono := strictMonoOn_bleisteinCoord_of_deriv_sign hconv hα hp hpleft hpright
  simpa [bleisteinCoord_zero] using
    ((continuousOn_bleisteinCoord hp).mono hIco).image_Ioo_of_strictMonoOn_of_tendsto_atTop
      hk (hmono.mono hIco) (tendsto_bleisteinCoord_nhdsLT_atTop hαk htend)

/-- Image of `(0, ∞)` under `bleisteinCoord p α` with finite limit `κ = lim_{t → +∞} w(α, t)`
under derivative-sign hypotheses on a convex domain `U`. -/
theorem image_bleisteinCoord_Ioi_eq_Ioo_of_deriv_sign {p : ℝ → ℝ} {α κ : ℝ} {U : Set ℝ}
    (hIci : Ici 0 ⊆ U) (hconv : Convex ℝ U) (hα : α ∈ U) (hp : ContinuousOn p U)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0) (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (htend : Tendsto (bleisteinCoord p α) atTop (𝓝 κ)) :
    bleisteinCoord p α '' Ioi 0 = Ioo 0 κ := by
  have hmono := strictMonoOn_bleisteinCoord_of_deriv_sign hconv hα hp hpleft hpright
  simpa [bleisteinCoord_zero] using
    ((continuousOn_bleisteinCoord hp).mono hIci).image_Ioi_of_strictMonoOn_of_tendsto
      (hmono.mono hIci) htend

/-- Image of `(0, ∞)` under `bleisteinCoord p α` when `p t → +∞` as `t → +∞` (`κ = +∞`) under
derivative-sign hypotheses on a convex domain `U`. -/
theorem image_bleisteinCoord_Ioi_eq_Ioi_of_deriv_sign {p : ℝ → ℝ} {α : ℝ} {U : Set ℝ}
    (hIci : Ici 0 ⊆ U) (hconv : Convex ℝ U) (hα : α ∈ U) (hp : ContinuousOn p U)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0) (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (htend : Tendsto p atTop atTop) :
    bleisteinCoord p α '' Ioi 0 = Ioi 0 := by
  have hmono := strictMonoOn_bleisteinCoord_of_deriv_sign hconv hα hp hpleft hpright
  simpa [bleisteinCoord_zero] using
    ((continuousOn_bleisteinCoord hp).mono hIci).image_Ioi_of_strictMonoOn
      (hmono.mono hIci) (tendsto_bleisteinCoord_atTop_atTop htend)

end TauCeti
