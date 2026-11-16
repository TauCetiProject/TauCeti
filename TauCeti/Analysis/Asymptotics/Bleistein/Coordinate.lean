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
public import Mathlib.Topology.Instances.Sign
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Order.IntermediateValue

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

When `p` is `C²` on an open set `U` containing `α` with `deriv p α = 0`, `deriv (deriv p) α > 0`,
and `p α < p t` for `t ≠ α`, `bleisteinCoord p α` is `C¹` on `U` with derivative
`deriv p t / (w - a)` away from `t = α` (DLMF 2.3.28) and `√(deriv (deriv p) α) > 0` at `t = α`.
Under the derivative sign conditions `deriv p < 0` on `U ∩ (-∞, α)` and `deriv p > 0` on
`U ∩ (α, ∞)` on a convex open domain `U`, `bleisteinCoord p α` is strictly increasing with
strictly positive derivative and maps `(0, k)` or `(0, ∞)` onto `(0, κ)` where
`κ = lim_{t → k} w(α, t)`. If `p(t) → +∞` as `t → k`, then `κ = +∞`; having `k = +∞` alone does
not force `κ = +∞` (`TauCeti.tendsto_bleisteinCoord_one_sub_exp_neg_sq`).

## Main definitions

* `TauCeti.bleisteinOffset`: the normal-form critical parameter `a(α)`.
* `TauCeti.bleisteinCoord`: Bleistein's canonical coordinate `w(α, t)`.

## Main results

* `TauCeti.half_sq_bleisteinCoord_sub_mul_add`: quadratic phase identity
  `w ^ 2 / 2 - a * w + p 0 = p t` (DLMF 2.3.25).
* `TauCeti.strictMonoOn_bleisteinCoord`, `TauCeti.strictMonoOn_bleisteinCoord_of_deriv_sign`:
  strict monotonicity of `bleisteinCoord p α`.
* `TauCeti.hasDerivAt_bleisteinCoord_of_ne`, `TauCeti.hasDerivAt_bleisteinCoord_self`,
  `TauCeti.contDiffOn_bleisteinCoord`: derivative formulas (DLMF 2.3.28) and `C¹` regularity
  across the critical point `t = α`.
* `TauCeti.hasStrictDerivAt_invFunOn_bleisteinCoord`, `TauCeti.image_bleisteinCoord_Ioo_eq_Ioo`,
  `TauCeti.image_bleisteinCoord_Ioo_eq_Ioi`, `TauCeti.image_bleisteinCoord_Ioi_eq_Ioo`,
  `TauCeti.image_bleisteinCoord_Ioi_eq_Ioi`: inverse coordinate regularity and interval images.

## References

* N. Bleistein, *Uniform asymptotic expansions of integrals with stationary point near algebraic
  singularity*, Comm. Pure Appl. Math. **19** (1966), 353–370.
* N. Bleistein and R. A. Handelsman, *Asymptotic Expansions of Integrals*, Holt, Rinehart and
  Winston, 1975; reprinted Dover, 1986. Chapter 9, §9.4.
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

/-- Modulus of `bleisteinOffset` (DLMF 2.3.26): `|a(α)| = √(2 (p 0 - p α))` when `p α ≤ p 0`. -/
theorem abs_bleisteinOffset {p : ℝ → ℝ} {α : ℝ} (hp : p α ≤ p 0) :
    |bleisteinOffset p α| = Real.sqrt (2 * (p 0 - p α)) := by
  rcases lt_trichotomy α 0 with hα | rfl | hα
  · simp [bleisteinOffset, sign_neg hα, abs_of_nonneg (Real.sqrt_nonneg _)]
  · simp
  · simp [bleisteinOffset, sign_pos hα, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- Square of `bleisteinOffset`: `a(α) ^ 2 = 2 * (p 0 - p α)` when `p α ≤ p 0`. -/
theorem sq_bleisteinOffset {p : ℝ → ℝ} {α : ℝ} (hp : p α ≤ p 0) :
    bleisteinOffset p α ^ 2 = 2 * (p 0 - p α) := by
  rw [← sq_abs, abs_bleisteinOffset hp, Real.sq_sqrt (by linarith)]

/-- For `α > 0` with `p α < p 0`, the offset `a(α)` is strictly positive. -/
theorem bleisteinOffset_pos {p : ℝ → ℝ} {α : ℝ} (hα : 0 < α) (hp : p α < p 0) :
    0 < bleisteinOffset p α := by
  simp only [bleisteinOffset, sign_pos hα, SignType.coe_one, one_mul]
  exact Real.sqrt_pos_of_pos (by linarith)

/-- For `α < 0` with `p α < p 0`, the offset `a(α)` is strictly negative. -/
theorem bleisteinOffset_neg {p : ℝ → ℝ} {α : ℝ} (hα : α < 0) (hp : p α < p 0) :
    bleisteinOffset p α < 0 := by
  simp only [bleisteinOffset, sign_neg hα, SignType.coe_neg, SignType.coe_one, neg_one_mul,
    neg_lt_zero]
  exact Real.sqrt_pos_of_pos (by linarith)

/-- For `α ≥ 0`, `bleisteinOffset p α` is nonnegative. -/
theorem bleisteinOffset_nonneg {p : ℝ → ℝ} {α : ℝ} (hα : 0 ≤ α) :
    0 ≤ bleisteinOffset p α := by
  rcases hα.eq_or_lt with rfl | hα'
  · simp
  · simp [bleisteinOffset, sign_pos hα', Real.sqrt_nonneg]

/-- For `α ≤ 0`, `bleisteinOffset p α` is nonpositive. -/
theorem bleisteinOffset_nonpos {p : ℝ → ℝ} {α : ℝ} (hα : α ≤ 0) :
    bleisteinOffset p α ≤ 0 := by
  rcases hα.eq_or_lt with rfl | hα'
  · simp
  · simp [bleisteinOffset, sign_neg hα', Real.sqrt_nonneg]

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

/-- Difference between `bleisteinCoord` and `bleisteinOffset`. -/
theorem bleisteinCoord_sub_bleisteinOffset (p : ℝ → ℝ) (α t : ℝ) :
    bleisteinCoord p α t - bleisteinOffset p α =
      (SignType.sign (t - α) : ℝ) * Real.sqrt (2 * (p t - p α)) :=
  add_sub_cancel_left _ _

/-- Distance from `bleisteinCoord p α t` to `bleisteinOffset p α` when `p α ≤ p t`. -/
theorem abs_bleisteinCoord_sub {p : ℝ → ℝ} {α t : ℝ} (hp : p α ≤ p t) :
    |bleisteinCoord p α t - bleisteinOffset p α| = Real.sqrt (2 * (p t - p α)) := by
  rw [bleisteinCoord_sub_bleisteinOffset]
  rcases lt_trichotomy t α with ht | rfl | ht
  · simp [sign_neg (sub_neg.mpr ht), abs_of_nonneg (Real.sqrt_nonneg _)]
  · simp
  · simp [sign_pos (sub_pos.mpr ht), abs_of_nonneg (Real.sqrt_nonneg _)]

/-- Squared distance identity `(w(α, t) - a(α)) ^ 2 = 2 * (p t - p α)` when `p α ≤ p t`. -/
theorem sq_bleisteinCoord_sub {p : ℝ → ℝ} {α t : ℝ} (hp : p α ≤ p t) :
    (bleisteinCoord p α t - bleisteinOffset p α) ^ 2 = 2 * (p t - p α) := by
  rw [← sq_abs, abs_bleisteinCoord_sub hp, Real.sq_sqrt (by linarith)]

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
  simp only [bleisteinCoord, sign_neg (sub_neg.mpr ht), SignType.coe_neg, SignType.coe_one,
    neg_one_mul]
  linarith [Real.sqrt_pos_of_pos (x := 2 * (p t - p α)) (by linarith)]

/-- To the right of `α`, `bleisteinOffset p α < bleisteinCoord p α t` whenever `p α < p t`. -/
theorem bleisteinOffset_lt_bleisteinCoord {p : ℝ → ℝ} {α t : ℝ} (ht : α < t) (hp : p α < p t) :
    bleisteinOffset p α < bleisteinCoord p α t := by
  simp only [bleisteinCoord, sign_pos (sub_pos.mpr ht), SignType.coe_one, one_mul]
  linarith [Real.sqrt_pos_of_pos (x := 2 * (p t - p α)) (by linarith)]

/-- Away from `α`, `bleisteinCoord p α t ≠ bleisteinOffset p α` whenever `p α < p t`. -/
theorem bleisteinCoord_ne_bleisteinOffset {p : ℝ → ℝ} {α t : ℝ} (ht : t ≠ α) (hp : p α < p t) :
    bleisteinCoord p α t ≠ bleisteinOffset p α := by
  rcases ht.lt_or_gt with h | h
  · exact (bleisteinCoord_lt_bleisteinOffset h hp).ne
  · exact (bleisteinOffset_lt_bleisteinCoord h hp).ne'

/-! ### Monotonicity and upper limit `κ` -/

/-- If `p` is strictly decreasing on `s ∩ (-∞, α]`, strictly increasing on `s ∩ [α, ∞)`, and
strictly above `p α` on `s \ {α}`, then `bleisteinCoord p α` is strictly increasing on `s`. -/
theorem strictMonoOn_bleisteinCoord_of_ne {p : ℝ → ℝ} {α : ℝ} {s : Set ℝ}
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
    simp only [bleisteinCoord, sign_neg (sub_neg.mpr ht₁α), sign_neg (sub_neg.mpr ht₂α),
      SignType.coe_neg, SignType.coe_one, neg_one_mul]
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
      simp only [bleisteinCoord, sign_pos (sub_pos.mpr hαt₁), sign_pos (sub_pos.mpr hαt₂),
        SignType.coe_one, one_mul]
      linarith

/-- If `α ∈ s`, `p` is strictly decreasing on `s ∩ (-∞, α]`, and `p` is strictly increasing on
`s ∩ [α, ∞)`, then `bleisteinCoord p α` is strictly increasing on `s`. -/
theorem strictMonoOn_bleisteinCoord {p : ℝ → ℝ} {α : ℝ} {s : Set ℝ} (hα : α ∈ s)
    (hleft : StrictAntiOn p (s ∩ Iic α)) (hright : StrictMonoOn p (s ∩ Ici α)) :
    StrictMonoOn (bleisteinCoord p α) s := by
  refine strictMonoOn_bleisteinCoord_of_ne hleft hright fun t ht hne ↦ ?_
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
    (hl : ∀ᶠ t in l, α < t) (hp : Tendsto p l atTop) :
    Tendsto (bleisteinCoord p α) l atTop := by
  have hsq : Tendsto (fun t ↦ bleisteinOffset p α + Real.sqrt (2 * (p t - p α))) l atTop :=
    tendsto_atTop_add_const_left _ _ <| Real.tendsto_sqrt_atTop.comp <|
      (tendsto_atTop_add_const_right _ (-p α) hp).const_mul_atTop zero_lt_two
  refine hsq.congr' (hl.mono fun t ht ↦ ?_)
  simp [bleisteinCoord, sign_pos (sub_pos.mpr ht)]

/-- If `p t → +∞` as `t → +∞`, then `bleisteinCoord p α t → +∞` as `t → +∞` (`κ = ∞`). -/
theorem tendsto_bleisteinCoord_atTop_atTop {p : ℝ → ℝ} {α : ℝ} (hp : Tendsto p atTop atTop) :
    Tendsto (bleisteinCoord p α) atTop atTop :=
  tendsto_bleisteinCoord_atTop (eventually_gt_atTop α) hp

/-- If `α < k` and `p t → +∞` as `t → k⁻`, then `bleisteinCoord p α t → +∞` as `t → k⁻`
(`κ = ∞`). -/
theorem tendsto_bleisteinCoord_nhdsLT_atTop {p : ℝ → ℝ} {α k : ℝ} (hαk : α < k)
    (hp : Tendsto p (𝓝[<] k) atTop) :
    Tendsto (bleisteinCoord p α) (𝓝[<] k) atTop :=
  tendsto_bleisteinCoord_atTop
    (eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hαk)) hp

/-- If `α < k` and `p t → pb` as `t → k⁻`, then `bleisteinCoord p α t` tends to the finite upper
limit `κ = a(α) + √(2 (pb - p α))`. -/
theorem tendsto_bleisteinCoord_nhdsLT {p : ℝ → ℝ} {α k pb : ℝ} (hαk : α < k)
    (hp : Tendsto p (𝓝[<] k) (𝓝 pb)) :
    Tendsto (bleisteinCoord p α) (𝓝[<] k)
      (𝓝 (bleisteinOffset p α + Real.sqrt (2 * (pb - p α)))) := by
  have hlim : Tendsto (fun t ↦ bleisteinOffset p α + Real.sqrt (2 * (p t - p α))) (𝓝[<] k)
      (𝓝 (bleisteinOffset p α + Real.sqrt (2 * (pb - p α)))) :=
    tendsto_const_nhds.add <| Real.continuous_sqrt.continuousAt.tendsto.comp <|
      (hp.sub_const (p α)).const_mul 2
  refine hlim.congr' ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hαk)] with t ht
  simp [bleisteinCoord, sign_pos (sub_pos.mpr ht)]

/-- Having upper integration limit `k = +∞` does not by itself force `κ = +∞`: for the smooth phase
`p t = 1 - exp (-t ^ 2)` with critical point `α = 0`, `bleisteinCoord p 0 t` tends to the finite
limit `√2` as `t → +∞`. -/
theorem tendsto_bleisteinCoord_one_sub_exp_neg_sq :
    Tendsto (bleisteinCoord (fun t ↦ 1 - Real.exp (-t ^ 2)) 0) atTop (𝓝 (Real.sqrt 2)) := by
  have hexp : Tendsto (fun t : ℝ ↦ Real.exp (-t ^ 2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp <| tendsto_neg_atTop_atBot.comp <|
      Filter.tendsto_pow_atTop (by norm_num)
  have hinner : Tendsto (fun t : ℝ ↦ 2 * (1 - Real.exp (-t ^ 2))) atTop (𝓝 2) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hexp).const_mul 2
  refine (Real.continuous_sqrt.continuousAt.tendsto.comp hinner).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simp [bleisteinCoord, sign_pos ht]

/-! ### Derivatives and `C¹` regularity of `bleisteinCoord` -/

/-- Derivative of `bleisteinCoord` away from the critical point `t = α` (DLMF 2.3.28):
`dw/dt = p' / (w - a)`. -/
theorem hasDerivAt_bleisteinCoord_of_ne {p : ℝ → ℝ} {α t p' : ℝ} (ht : t ≠ α) (hpt : p α < p t)
    (hp : HasDerivAt p p' t) :
    HasDerivAt (bleisteinCoord p α) (p' / (bleisteinCoord p α t - bleisteinOffset p α)) t := by
  have hpos : 0 < 2 * (p t - p α) := by linarith
  have hrad : HasDerivAt (fun s ↦ Real.sqrt (2 * (p s - p α)))
      (p' / Real.sqrt (2 * (p t - p α))) t := by
    convert ((hp.sub_const (p α)).const_mul 2).sqrt hpos.ne' using 1
    field_simp [(Real.sqrt_pos_of_pos hpos).ne']
  rcases ht.lt_or_gt with hlt | hgt
  · have heq : bleisteinCoord p α =ᶠ[𝓝 t]
        fun s ↦ bleisteinOffset p α + (-1) * Real.sqrt (2 * (p s - p α)) := by
      filter_upwards [Iio_mem_nhds hlt] with s hs
      simp [bleisteinCoord, sign_neg (sub_neg.mpr hs)]
    refine ((hrad.const_mul (-1)).const_add (bleisteinOffset p α)).congr_of_eventuallyEq heq
      |>.congr_deriv ?_
    simp only [bleisteinCoord_sub_bleisteinOffset, sign_neg (sub_neg.mpr hlt), SignType.coe_neg,
      SignType.coe_one]
    ring
  · have heq : bleisteinCoord p α =ᶠ[𝓝 t]
        fun s ↦ bleisteinOffset p α + 1 * Real.sqrt (2 * (p s - p α)) := by
      filter_upwards [Ioi_mem_nhds hgt] with s hs
      simp [bleisteinCoord, sign_pos (sub_pos.mpr hs)]
    refine ((hrad.const_mul 1).const_add (bleisteinOffset p α)).congr_of_eventuallyEq heq
      |>.congr_deriv ?_
    simp only [bleisteinCoord_sub_bleisteinOffset, sign_pos (sub_pos.mpr hgt), SignType.coe_one]
    ring

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
    HasDerivAt (bleisteinCoord p α) (Real.sqrt (deriv (deriv p) α)) α := by
  have hp1 : ∀ᶠ t in 𝓝 α, DifferentiableAt ℝ p t :=
    (hp.eventually (by simp)).mono fun _ ht ↦ ht.differentiableAt (by norm_num)
  have hp2 : HasDerivAt (deriv p) (deriv (deriv p) α) α :=
    ((hp.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasDerivAt
  exact hasDerivAt_bleisteinCoord_self hp1 hp'0 hp2

/-- Value of `deriv (bleisteinCoord p α) α` when `p` is `C²` at `α` with `deriv p α = 0`. -/
theorem deriv_bleisteinCoord_self {p : ℝ → ℝ} {α : ℝ}
    (hp : ContDiffAt ℝ 2 p α) (hp'0 : deriv p α = 0) :
    deriv (bleisteinCoord p α) α = Real.sqrt (deriv (deriv p) α) :=
  (hasDerivAt_bleisteinCoord_self_of_contDiffAt hp hp'0).deriv

/-- Positivity of `deriv (bleisteinCoord p α) α` at a nondegenerate minimum (`p''(α) > 0`). -/
theorem deriv_bleisteinCoord_self_pos {p : ℝ → ℝ} {α : ℝ}
    (hp : ContDiffAt ℝ 2 p α) (hp'0 : deriv p α = 0) (hp'' : 0 < deriv (deriv p) α) :
    0 < deriv (bleisteinCoord p α) α := by
  rw [deriv_bleisteinCoord_self hp hp'0]
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

/-- `C¹` regularity of `bleisteinCoord p α` on an open set `U` containing the critical point `α`,
assuming `p` is `C²` on `U`, `deriv p α = 0`, `deriv (deriv p) α > 0`, and `p α < p t` for
`t ∈ U \ {α}`. -/
theorem contDiffOn_bleisteinCoord {p : ℝ → ℝ} {α : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hα : α ∈ U) (hp : ContDiffOn ℝ 2 p U)
    (hp'0 : deriv p α = 0) (hp'' : 0 < deriv (deriv p) α)
    (hppos : ∀ t ∈ U, t ≠ α → p α < p t) :
    ContDiffOn ℝ 1 (bleisteinCoord p α) U := by
  have hp_at : ContDiffAt ℝ 2 p α := hp.contDiffAt (hU.mem_nhds hα)
  have hdiff : DifferentiableOn ℝ (bleisteinCoord p α) U := by
    intro t ht
    rcases eq_or_ne α t with rfl | hne
    · exact (hasDerivAt_bleisteinCoord_self_of_contDiffAt hp_at
        hp'0).differentiableAt.differentiableWithinAt
    · have hpt : DifferentiableAt ℝ p t :=
        (hp.contDiffAt (hU.mem_nhds ht)).differentiableAt (by norm_num)
      exact (hasDerivAt_bleisteinCoord_of_ne hne.symm (hppos t ht hne.symm)
        hpt.hasDerivAt).differentiableAt.differentiableWithinAt
  refine (contDiffOn_succ_iff_deriv_of_isOpen (n := 0) hU).mpr
    ⟨hdiff, by simp, contDiffOn_zero.mpr fun t ht ↦ ?_⟩
  rcases eq_or_ne α t with rfl | hne
  · have hp1 : ∀ᶠ s in 𝓝 α, DifferentiableAt ℝ p s :=
      (hp_at.eventually (by simp)).mono fun _ hs ↦ hs.differentiableAt (by norm_num)
    have hp2 : HasDerivAt (deriv p) (deriv (deriv p) α) α :=
      ((hp_at.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasDerivAt
    exact (continuousAt_deriv_bleisteinCoord_self hp1 hp'0 hp2 hp'').continuousWithinAt
  · have hopen : IsOpen (U \ {α}) := hU.sdiff isClosed_singleton
    have hmem : U \ {α} ∈ 𝓝 t := hopen.mem_nhds ⟨ht, hne.symm⟩
    have hp'_cont : ContinuousAt (deriv p) t :=
      (hp.continuousOn_deriv_of_isOpen hU (by norm_num)).continuousAt (hU.mem_nhds ht)
    have hw_cont : ContinuousAt (bleisteinCoord p α) t :=
      hdiff.continuousOn.continuousAt (hU.mem_nhds ht)
    have hquot : ContinuousAt
        (fun s ↦ deriv p s / (bleisteinCoord p α s - bleisteinOffset p α)) t :=
      hp'_cont.div (hw_cont.sub continuousAt_const)
        (sub_ne_zero.mpr (bleisteinCoord_ne_bleisteinOffset hne.symm (hppos t ht hne.symm)))
    refine (hquot.congr ?_).continuousWithinAt
    filter_upwards [hmem] with s hs
    have hds : DifferentiableAt ℝ p s :=
      (hp.contDiffAt (hU.mem_nhds hs.1)).differentiableAt (by norm_num)
    exact (deriv_bleisteinCoord_of_ne hs.2 (hppos s hs.1 hs.2) hds).symm

/-- Positivity of `deriv (bleisteinCoord p α)` throughout `U` when `deriv p < 0` to the left of `α`,
`deriv p > 0` to the right of `α`, and `deriv (deriv p) α > 0`. -/
theorem deriv_bleisteinCoord_pos {p : ℝ → ℝ} {α : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hα : α ∈ U) (hp : ContDiffOn ℝ 2 p U)
    (hp'0 : deriv p α = 0) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0)
    (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (hppos : ∀ t ∈ U, t ≠ α → p α < p t) {t : ℝ} (ht : t ∈ U) :
    0 < deriv (bleisteinCoord p α) t := by
  rcases eq_or_ne α t with rfl | hne
  · exact deriv_bleisteinCoord_self_pos (hp.contDiffAt (hU.mem_nhds hα)) hp'0 hp''
  · have hdt : DifferentiableAt ℝ p t :=
      (hp.contDiffAt (hU.mem_nhds ht)).differentiableAt (by norm_num)
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

/-- On a convex set `U` (such as any interval in `ℝ`) containing `α`, the derivative sign
conditions `t < α → deriv p t < 0` and `α < t → 0 < deriv p t` imply
`StrictMonoOn (bleisteinCoord p α) U`. -/
theorem strictMonoOn_bleisteinCoord_of_deriv_sign {p : ℝ → ℝ} {α : ℝ} {U : Set ℝ}
    (hconv : Convex ℝ U) (hα : α ∈ U) (hp : DifferentiableOn ℝ p U)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0)
    (hpright : ∀ t ∈ U, α < t → 0 < deriv p t) :
    StrictMonoOn (bleisteinCoord p α) U := by
  have hanti : StrictAntiOn p (U ∩ Iic α) := by
    intro t₁ ht₁ t₂ ht₂ hlt
    have hIcc : Icc t₁ t₂ ⊆ U := hconv.ordConnected.out ht₁.1 ht₂.1
    have hsub : StrictAntiOn p (Icc t₁ t₂) :=
      strictAntiOn_of_deriv_neg (convex_Icc t₁ t₂) (hp.continuousOn.mono hIcc) fun s hs ↦ by
        rw [interior_Icc] at hs
        exact hpleft s (hIcc ⟨hs.1.le, hs.2.le⟩) (hs.2.trans_le ht₂.2)
    exact hsub ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt
  have hmono : StrictMonoOn p (U ∩ Ici α) := by
    intro t₁ ht₁ t₂ ht₂ hlt
    have hIcc : Icc t₁ t₂ ⊆ U := hconv.ordConnected.out ht₁.1 ht₂.1
    have hsub : StrictMonoOn p (Icc t₁ t₂) :=
      strictMonoOn_of_deriv_pos (convex_Icc t₁ t₂) (hp.continuousOn.mono hIcc) fun s hs ↦ by
        rw [interior_Icc] at hs
        exact hpright s (hIcc ⟨hs.1.le, hs.2.le⟩) (ht₁.2.trans_lt hs.1)
    exact hsub ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt
  exact strictMonoOn_bleisteinCoord hα hanti hmono

/-- `C¹` regularity of `bleisteinCoord p α` on an open convex set `U` containing `α` under
derivative-sign hypotheses on `p`. -/
theorem contDiffOn_bleisteinCoord_of_deriv_sign {p : ℝ → ℝ} {α : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hα : α ∈ U) (hp : ContDiffOn ℝ 2 p U)
    (hp'0 : deriv p α = 0) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0)
    (hpright : ∀ t ∈ U, α < t → 0 < deriv p t) :
    ContDiffOn ℝ 1 (bleisteinCoord p α) U := by
  have hmono := strictMonoOn_bleisteinCoord_of_deriv_sign hconv hα
    (hp.differentiableOn (by norm_num)) hpleft hpright
  exact contDiffOn_bleisteinCoord hU hα hp hp'0 hp'' fun _ ht hne ↦
    lt_of_injOn_bleisteinCoord hmono.injOn hα ht hne

/-- Positivity of `deriv (bleisteinCoord p α)` on an open convex set `U` containing `α` under
derivative-sign hypotheses on `p`. -/
theorem deriv_bleisteinCoord_pos_of_deriv_sign {p : ℝ → ℝ} {α : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hα : α ∈ U) (hp : ContDiffOn ℝ 2 p U)
    (hp'0 : deriv p α = 0) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0)
    (hpright : ∀ t ∈ U, α < t → 0 < deriv p t) {t : ℝ} (ht : t ∈ U) :
    0 < deriv (bleisteinCoord p α) t := by
  have hmono := strictMonoOn_bleisteinCoord_of_deriv_sign hconv hα
    (hp.differentiableOn (by norm_num)) hpleft hpright
  exact deriv_bleisteinCoord_pos hU hα hp hp'0 hp'' hpleft hpright
    (fun _ hs hne ↦ lt_of_injOn_bleisteinCoord hmono.injOn hα hs hne) ht

/-! ### Inverse coordinate and interval images -/

/-- Strict derivative of `Set.invFunOn (bleisteinCoord p α) U` at `bleisteinCoord p α t` for
every `t ∈ U`. -/
theorem hasStrictDerivAt_invFunOn_bleisteinCoord {p : ℝ → ℝ} {α : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hw : ContDiffOn ℝ 1 (bleisteinCoord p α) U)
    (hinj : InjOn (bleisteinCoord p α) U)
    (hw' : ∀ t ∈ U, deriv (bleisteinCoord p α) t ≠ 0) {t : ℝ} (ht : t ∈ U) :
    HasStrictDerivAt (invFunOn (bleisteinCoord p α) U)
      (deriv (bleisteinCoord p α) t)⁻¹ (bleisteinCoord p α t) := by
  have hstrict : HasStrictDerivAt (bleisteinCoord p α) (deriv (bleisteinCoord p α) t) t :=
    (hw.contDiffAt (hU.mem_nhds ht)).hasStrictDerivAt_deriv one_ne_zero
  refine hstrict.to_local_left_inverse (hw' t ht) ?_
  filter_upwards [hU.mem_nhds ht] with s hs
  exact hinj.leftInvOn_invFunOn hs

/-- Under `ContDiffOn ℝ 1` and nonvanishing derivative on an open set `U`, the image
`bleisteinCoord p α '' U` is open. -/
theorem isOpen_image_bleisteinCoord {p : ℝ → ℝ} {α : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hw : ContDiffOn ℝ 1 (bleisteinCoord p α) U)
    (hw' : ∀ t ∈ U, deriv (bleisteinCoord p α) t ≠ 0) :
    IsOpen (bleisteinCoord p α '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨t, ht, rfl⟩
  have hstrict : HasStrictDerivAt (bleisteinCoord p α) (deriv (bleisteinCoord p α) t) t :=
    (hw.contDiffAt (hU.mem_nhds ht)).hasStrictDerivAt_deriv one_ne_zero
  rw [← hstrict.map_nhds_eq (hw' t ht)]
  exact image_mem_map (hU.mem_nhds ht)

/-- Continuity of the inverse coordinate `Set.invFunOn (bleisteinCoord p α) U` on the image
`bleisteinCoord p α '' U`. -/
theorem continuousOn_invFunOn_bleisteinCoord {p : ℝ → ℝ} {α : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hw : ContDiffOn ℝ 1 (bleisteinCoord p α) U)
    (hinj : InjOn (bleisteinCoord p α) U)
    (hw' : ∀ t ∈ U, deriv (bleisteinCoord p α) t ≠ 0) :
    ContinuousOn (invFunOn (bleisteinCoord p α) U) (bleisteinCoord p α '' U) := by
  rintro _ ⟨t, ht, rfl⟩
  exact (hasStrictDerivAt_invFunOn_bleisteinCoord hU hw hinj hw'
    ht).hasDerivAt.continuousAt.continuousWithinAt

/-- Image of `(0, k)` under `bleisteinCoord p α` when `w(α, t) → κ` as `t → k⁻`. -/
theorem image_bleisteinCoord_Ioo_eq_Ioo {p : ℝ → ℝ} {α k κ : ℝ} (hk : 0 < k)
    (hcont : ContinuousOn (bleisteinCoord p α) (Ico 0 k))
    (hmono : StrictMonoOn (bleisteinCoord p α) (Ico 0 k))
    (htend : Tendsto (bleisteinCoord p α) (𝓝[<] k) (𝓝 κ)) :
    bleisteinCoord p α '' Ioo 0 k = Ioo 0 κ := by
  have ht0 : Tendsto (bleisteinCoord p α) (𝓝[Ioo 0 k] 0) (𝓝 0) := by
    simpa [bleisteinCoord_zero] using
      ((hcont 0 ⟨le_rfl, hk⟩).mono Ioo_subset_Ico_self).tendsto
  have htk : Tendsto (bleisteinCoord p α) (𝓝[Ioo 0 k] k) (𝓝 κ) := by
    rwa [nhdsWithin_Ioo_eq_nhdsLT hk]
  have := left_nhdsWithin_Ioo_neBot hk
  have := right_nhdsWithin_Ioo_neBot hk
  refine Subset.antisymm ?_ <| isPreconnected_Ioo.intermediate_value_Ioo
    (l₁ := 𝓝[Ioo 0 k] 0) (l₂ := 𝓝[Ioo 0 k] k)
    inf_le_right inf_le_right (hcont.mono Ioo_subset_Ico_self) ht0 htk
  rintro _ ⟨t, ht, rfl⟩
  have hmid : (t + k) / 2 ∈ Ioo t k := ⟨by linarith [ht.2], by linarith [ht.2]⟩
  have hle : bleisteinCoord p α ((t + k) / 2) ≤ κ := by
    refine ge_of_tendsto htend ?_
    filter_upwards [Ioo_mem_nhdsLT hmid.2] with s hs
    exact hmono.monotoneOn ⟨by linarith [ht.1, hmid.1], hmid.2⟩
      ⟨by linarith [ht.1, hmid.1, hs.1], hs.2⟩ hs.1.le
  exact ⟨bleisteinCoord_pos hmono ⟨le_rfl, hk⟩ ⟨ht.1.le, ht.2⟩ ht.1,
    (hmono ⟨ht.1.le, ht.2⟩ ⟨by linarith [ht.1, hmid.1], hmid.2⟩ hmid.1).trans_le hle⟩

/-- Image of `(0, k)` under `bleisteinCoord p α` when `w(α, t) → +∞` as `t → k⁻`. -/
theorem image_bleisteinCoord_Ioo_eq_Ioi {p : ℝ → ℝ} {α k : ℝ} (hk : 0 < k)
    (hcont : ContinuousOn (bleisteinCoord p α) (Ico 0 k))
    (hmono : StrictMonoOn (bleisteinCoord p α) (Ico 0 k))
    (htend : Tendsto (bleisteinCoord p α) (𝓝[<] k) atTop) :
    bleisteinCoord p α '' Ioo 0 k = Ioi 0 := by
  have ht0 : Tendsto (bleisteinCoord p α) (𝓝[Ioo 0 k] 0) (𝓝 0) := by
    simpa [bleisteinCoord_zero] using
      ((hcont 0 ⟨le_rfl, hk⟩).mono Ioo_subset_Ico_self).tendsto
  have htk : Tendsto (bleisteinCoord p α) (𝓝[Ioo 0 k] k) atTop := by
    rwa [nhdsWithin_Ioo_eq_nhdsLT hk]
  have := left_nhdsWithin_Ioo_neBot hk
  have := right_nhdsWithin_Ioo_neBot hk
  refine Subset.antisymm ?_ <| isPreconnected_Ioo.intermediate_value_Ioi
    (l₁ := 𝓝[Ioo 0 k] 0) (l₂ := 𝓝[Ioo 0 k] k)
    inf_le_right inf_le_right (hcont.mono Ioo_subset_Ico_self) ht0 htk
  rintro _ ⟨t, ht, rfl⟩
  exact bleisteinCoord_pos hmono ⟨le_rfl, hk⟩ ⟨ht.1.le, ht.2⟩ ht.1

/-- Image of `(0, ∞)` under `bleisteinCoord p α` when `w(α, t) → κ` as `t → +∞`. -/
theorem image_bleisteinCoord_Ioi_eq_Ioo {p : ℝ → ℝ} {α κ : ℝ}
    (hcont : ContinuousOn (bleisteinCoord p α) (Ici 0))
    (hmono : StrictMonoOn (bleisteinCoord p α) (Ici 0))
    (htend : Tendsto (bleisteinCoord p α) atTop (𝓝 κ)) :
    bleisteinCoord p α '' Ioi 0 = Ioo 0 κ := by
  have ht0 : Tendsto (bleisteinCoord p α) (𝓝[>] 0) (𝓝 0) := by
    simpa [bleisteinCoord_zero] using
      ((hcont 0 self_mem_Ici).mono Ioi_subset_Ici_self).tendsto
  have := nhdsGT_neBot (0 : ℝ)
  refine Subset.antisymm ?_ <| isPreconnected_Ioi.intermediate_value_Ioo
    (l₁ := 𝓝[>] 0) (l₂ := atTop)
    inf_le_right (le_principal_iff.mpr (Ioi_mem_atTop 0))
    (hcont.mono Ioi_subset_Ici_self) ht0 htend
  rintro _ ⟨t, ht, rfl⟩
  have ht_pos : 0 < t := ht
  have hle : bleisteinCoord p α (t + 1) ≤ κ := by
    refine ge_of_tendsto htend ?_
    filter_upwards [eventually_ge_atTop (t + 1)] with s hs
    exact hmono.monotoneOn (mem_Ici.mpr (by linarith)) (mem_Ici.mpr (by linarith)) hs
  exact ⟨bleisteinCoord_pos hmono self_mem_Ici ht_pos.le ht_pos,
    (hmono ht_pos.le (mem_Ici.mpr (by linarith)) (lt_add_one t)).trans_le hle⟩

/-- Image of `(0, ∞)` under `bleisteinCoord p α` when `w(α, t) → +∞` as `t → +∞`. -/
theorem image_bleisteinCoord_Ioi_eq_Ioi {p : ℝ → ℝ} {α : ℝ}
    (hcont : ContinuousOn (bleisteinCoord p α) (Ici 0))
    (hmono : StrictMonoOn (bleisteinCoord p α) (Ici 0))
    (htend : Tendsto (bleisteinCoord p α) atTop atTop) :
    bleisteinCoord p α '' Ioi 0 = Ioi 0 := by
  simpa [bleisteinCoord_zero] using hcont.image_Ioi_of_strictMonoOn hmono htend

end TauCeti
