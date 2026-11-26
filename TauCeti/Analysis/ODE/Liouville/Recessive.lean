/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Liouville.Green
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Complex.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.Calculus.Deriv.Growth
import TauCeti.Analysis.Calculus.IteratedDeriv.Basic
import TauCeti.Analysis.ODE.SecondOrder.Linear
import TauCeti.Analysis.ODE.Wronskian

/-!
# Recessive and dominant Liouville–Green solutions at `+∞`

Let `f` be positive on `(a, ∞)` and let `ξ` be a primitive of `f^{1/2}` there. The
Liouville–Green approximants of the solutions of a second-order equation `w'' = q w` are

  `y₋ = f^{-1/4} e^{-ξ}` and `y₊ = f^{-1/4} e^{ξ}`.

When `ξ(x) → ∞` as `x → ∞`, a solution `w₂ ∼ y₋` is *recessive* at `+∞`, and every solution
whose Wronskian with it does not vanish is *dominant*. Precisely, if `w₂ ∼ y₋` then every
solution `w` satisfies

  `w / y₊ → W(w₂, w) / 2`,

where `W(w₂, w) = w₂ w' - w₂' w` is the (constant) Wronskian
(`TauCeti.tendsto_div_liouvilleGreen_atTop`). Consequently:
* every solution `w` with `W(w₂, w) ≠ 0` satisfies `w₂ / w → 0`
  (`TauCeti.tendsto_div_of_wronskian_ne_zero_atTop`);
* if `q` is continuous on `(a, ∞)`, then `w₂` is the only solution with `w₂ ∼ y₋`
  (`TauCeti.eqOn_of_isEquivalent_liouvilleGreen_atTop`);
* if `q` is continuous on `(a, ∞)`, then there is a solution `w₃ ∼ y₊`, and `w₂ / w₃ → 0`
  (`TauCeti.exists_liouvilleGreen_dominant_atTop`).
The solution `w₃` is not unique: `w₃ + c w₂` has the same property for every constant `c`.

For the Liouville–Green equation `w'' = (f + g) w`, under the hypotheses of the Liouville–Green
theorem `TauCeti.exists_liouvilleGreen_atTop`, its solution `w₂ = y₋ (1 + ε)` has `ε(x) → 0`,
so `w₂ ∼ y₋` (`TauCeti.exists_liouvilleGreen_isEquivalent_atTop`, DLMF 2.7.26). This holds
without `ξ(x) → ∞`; the characterization of `w₂` by this property, and the results above, use it.

## Proof

On a neighbourhood of `+∞` where `w₂` does not vanish, `(w / w₂)' = W / w₂²`. Writing
`w₂ = y₋ ρ` with `ρ → 1`, one has `1 / w₂² = f^{1/2} e^{2ξ} / ρ²`, so
`G = w / w₂ - (W / 2) e^{2ξ}` has derivative `(W / 2) (ρ⁻² - 1) (e^{2ξ})'`, which is
`o((e^{2ξ})')`. Since `e^{2ξ} → ∞`, L'Hôpital's rule for little-o
(`TauCeti.isLittleO_atTop_of_hasDerivAt`) gives `G = o(e^{2ξ})`, and
`w / y₊ = (W / 2 + G e^{-2ξ}) ρ → W / 2`. The uniqueness of `w₂` follows: a solution `w ∼ y₋`
must have `W(w₂, w) = 0`, since otherwise `|w / y₋| = |w / y₊| e^{2ξ} → ∞`, and then `w` is a
multiple of `w₂` (`TauCeti.eqOn_mul_of_wronskian_eq_zero`), necessarily `w₂` itself. The dominant
solution is the solution with `w₃(x₀) = 0` and `w₃'(x₀) = 2 / w₂(x₀)`, whose Wronskian with
`w₂` is `2` (`TauCeti.exists_contDiffOn_iteratedDeriv_eq_mul`).

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted
  A K Peters, 1997. Chapter 6, §2.
* NIST Digital Library of Mathematical Functions, §2.7(iii), equations (2.7.26)–(2.7.30),
  <https://dlmf.nist.gov/2.7.iii>.
-/

public section

open Set Filter Asymptotics MeasureTheory
open scoped Topology

namespace TauCeti

variable {f ξ : ℝ → ℝ} {q w₂ w : ℝ → ℂ} {a : ℝ}

/-- The approximant `y₋ = f^{-1/4} e^{-ξ}` and the derivative `2 f^{1/2} e^{2ξ}` of `e^{2ξ}`
satisfy `y₋² · 2 f^{1/2} e^{2ξ} = 2`. -/
private lemma liouvilleGreen_approximant_sq_mul_deriv_exp {x : ℝ} (hfx : 0 < f x) :
    ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ) ^ 2 *
      ((Real.exp (2 * ξ x) * (2 * √(f x)) : ℝ) : ℂ) = 2 := by
  have he : Real.exp (-ξ x) ^ 2 * Real.exp (2 * ξ x) = 1 := by
    rw [← Real.exp_natCast_mul, ← Real.exp_add]; simp
  have hr : (f x ^ (-(1 / 4) : ℝ)) ^ 2 * √(f x) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hfx.le, ← Real.rpow_add hfx]
    norm_num
  have h : (f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x)) ^ 2 * (Real.exp (2 * ξ x) * (2 * √(f x))) =
      2 := by
    linear_combination (2 * Real.exp (-ξ x) ^ 2 * Real.exp (2 * ξ x)) * hr + 2 * he
  exact_mod_cast h

/-- The approximants `y₋ = f^{-1/4} e^{-ξ}` and `y₊ = f^{-1/4} e^{ξ}` satisfy `y₋ e^{2ξ} = y₊`. -/
private lemma liouvilleGreen_approximant_mul_exp {x : ℝ} :
    ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ) * ((Real.exp (2 * ξ x) : ℝ) : ℂ) =
      ((f x ^ (-(1 / 4) : ℝ) * Real.exp (ξ x) : ℝ) : ℂ) := by
  have h : f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) * Real.exp (2 * ξ x) =
      f x ^ (-(1 / 4) : ℝ) * Real.exp (ξ x) := by
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
  exact_mod_cast h

/-- The approximant `f^{-1/4} e^{σ ξ}` does not vanish where `f > 0`. -/
private lemma liouvilleGreen_approximant_ne_zero {x σ : ℝ} (hfx : 0 < f x) :
    ((f x ^ (-(1 / 4) : ℝ) * Real.exp σ : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.2 (mul_ne_zero (Real.rpow_pos_of_pos hfx _).ne' (Real.exp_pos _).ne')

/-- Where `f > 0`, the quotients by the approximants `y₋ = f^{-1/4} e^{-ξ}` and
`y₊ = f^{-1/4} e^{ξ}` are related by `u / y₋ = (u / y₊) e^{2ξ}`. -/
private lemma div_approximant_eq_div_mul_exp {u : ℂ} {x : ℝ} (hfx : 0 < f x) :
    u / ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ) =
      u / ((f x ^ (-(1 / 4) : ℝ) * Real.exp (ξ x) : ℝ) : ℂ) * ((Real.exp (2 * ξ x) : ℝ) : ℂ) := by
  have hyx := liouvilleGreen_approximant_ne_zero (σ := -ξ x) hfx
  have hEx : ((Real.exp (2 * ξ x) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
  rw [← liouvilleGreen_approximant_mul_exp]
  generalize ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ) = A at hyx ⊢
  generalize ((Real.exp (2 * ξ x) : ℝ) : ℂ) = C at hEx ⊢
  field_simp

/-- A function asymptotic to `y₋ = f^{-1/4} e^{-ξ}` has ratio to it tending to `1`. -/
private lemma tendsto_div_of_isEquivalent_approximant {u : ℝ → ℂ} (hf0 : ∀ x ∈ Ioi a, 0 < f x)
    (hu : u ~[atTop] fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ)) :
    Tendsto (fun x ↦ u x / ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ)) atTop (𝓝 1) :=
  (isEquivalent_iff_tendsto_one ((eventually_gt_atTop a).mono fun x hx ↦
    liouvilleGreen_approximant_ne_zero (hf0 x hx))).1 hu

/-- A function asymptotic to `y₋ = f^{-1/4} e^{-ξ}` eventually does not vanish. -/
private lemma eventually_ne_zero_of_isEquivalent_approximant {u : ℝ → ℂ}
    (hf0 : ∀ x ∈ Ioi a, 0 < f x)
    (hu : u ~[atTop] fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ)) :
    ∀ᶠ x in atTop, x ∈ Ioi a ∧ u x ≠ 0 :=
  (eventually_gt_atTop a).and <| hu.eventually_ne_zero <| (eventually_gt_atTop a).mono
    fun x hx ↦ liouvilleGreen_approximant_ne_zero (hf0 x hx)

/-- Where `w₂ ≠ 0`, the function `w / w₂ - (W / 2) e^{2ξ}` has derivative
`(W / 2) ((w₂ / y₋)⁻² - 1) (e^{2ξ})'`, where `W = w₂ w' - w₂' w` and `y₋ = f^{-1/4} e^{-ξ}`. -/
private lemma hasDerivAt_div_sub_exp {x : ℝ} {W : ℂ} (hfx : 0 < f x)
    (hξx : HasDerivAt ξ (√(f x)) x) (hw₂x : HasDerivAt w₂ (deriv w₂ x) x)
    (hwx : HasDerivAt w (deriv w x) x) (hx2 : w₂ x ≠ 0)
    (hW : w₂ x * deriv w x - deriv w₂ x * w x = W) :
    HasDerivAt (fun t ↦ w t / w₂ t - W / 2 * ((Real.exp (2 * ξ t) : ℝ) : ℂ))
      (W / 2 * ((w₂ x / ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ))⁻¹ ^ 2 - 1) *
        ((Real.exp (2 * ξ x) * (2 * √(f x)) : ℝ) : ℂ)) x := by
  convert (hwx.div hw₂x hx2).sub ((hξx.const_mul 2).exp.ofReal_comp.const_mul (W / 2)) using 1
  have hid := liouvilleGreen_approximant_sq_mul_deriv_exp (ξ := ξ) hfx
  have hyx := liouvilleGreen_approximant_ne_zero (σ := -ξ x) hfx
  rw [mul_comm (deriv w x), mul_comm (w x), hW]
  generalize ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ) = A at hid hyx ⊢
  generalize ((Real.exp (2 * ξ x) * (2 * √(f x)) : ℝ) : ℂ) = B at hid ⊢
  generalize w₂ x = V at hx2 ⊢
  field_simp
  linear_combination W * hid

/-- With `W = w₂ w' - w₂' w` the Wronskian, `w / w₂ - (W / 2) e^{2ξ} = o(e^{2ξ})`, by L'Hôpital's
rule for little-o. -/
private lemma isLittleO_div_sub_exp {W : ℂ} (hf0 : ∀ x ∈ Ioi a, 0 < f x)
    (hξ : ∀ x ∈ Ioi a, HasDerivAt ξ (√(f x)) x) (hξt : Tendsto ξ atTop atTop)
    (hw₂ : ContDiffOn ℝ 2 w₂ (Ioi a))
    (hw₂e : w₂ ~[atTop] fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ))
    (hw : ContDiffOn ℝ 2 w (Ioi a)) (hW : ∀ x ∈ Ioi a, w₂ x * deriv w x - deriv w₂ x * w x = W) :
    (fun x ↦ w x / w₂ x - W / 2 * ((Real.exp (2 * ξ x) : ℝ) : ℂ)) =o[atTop]
      fun x ↦ ((Real.exp (2 * ξ x) : ℝ) : ℂ) := by
  refine Complex.isLittleO_ofReal_right.2 <| isLittleO_atTop_of_hasDerivAt
    ((eventually_ne_zero_of_isEquivalent_approximant hf0 hw₂e).mono fun x hx ↦
      hasDerivAt_div_sub_exp (hf0 x hx.1) (hξ x hx.1)
        (hw₂.hasDerivAt_and_hasDerivAt_deriv isOpen_Ioi hx.1).1
        (hw.hasDerivAt_and_hasDerivAt_deriv isOpen_Ioi hx.1).1 hx.2 (hW x hx.1))
    ((eventually_gt_atTop a).mono fun x hx ↦ ((hξ x hx).const_mul 2).exp)
    (Eventually.of_forall fun x ↦ by positivity)
    (Real.tendsto_exp_atTop.comp (hξt.const_mul_atTop two_pos)) ?_
  have hc := (((tendsto_div_of_isEquivalent_approximant hf0 hw₂e).inv₀ one_ne_zero).pow 2
    |>.sub_const 1).const_mul (W / 2)
  rw [inv_one, one_pow, sub_self, mul_zero] at hc
  refine IsLittleO.of_bound fun c hc0 ↦ ?_
  filter_upwards [hc.eventually (Metric.closedBall_mem_nhds (0 : ℂ) hc0)] with x hx
  rw [dist_zero_right] at hx
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

/-- **Dominant behaviour of the solutions independent of a recessive one.** Let `f > 0` on
`(a, ∞)`, let `ξ` be a primitive of `f^{1/2}` there with `ξ(x) → ∞`, and let `w₂` be a solution
of `w'' = q w`, `C²` on `(a, ∞)`, with `w₂ ∼ f^{-1/4} e^{-ξ}` as `x → ∞`. Then every solution `w`
satisfies `w / (f^{-1/4} e^{ξ}) → W / 2`, where `W = w₂ w' - w₂' w` is their Wronskian, at any
point `x₀ > a`. -/
theorem tendsto_div_liouvilleGreen_atTop (hf0 : ∀ x ∈ Ioi a, 0 < f x)
    (hξ : ∀ x ∈ Ioi a, HasDerivAt ξ (√(f x)) x) (hξt : Tendsto ξ atTop atTop)
    (hw₂ : ContDiffOn ℝ 2 w₂ (Ioi a)) (hw₂q : ∀ x ∈ Ioi a, iteratedDeriv 2 w₂ x = q x * w₂ x)
    (hw₂e : w₂ ~[atTop] fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ))
    (hw : ContDiffOn ℝ 2 w (Ioi a)) (hwq : ∀ x ∈ Ioi a, iteratedDeriv 2 w x = q x * w x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Ioi a) :
    Tendsto (fun x ↦ w x / ((f x ^ (-(1 / 4) : ℝ) * Real.exp (ξ x) : ℝ) : ℂ)) atTop
      (𝓝 ((w₂ x₀ * deriv w x₀ - deriv w₂ x₀ * w x₀) / 2)) := by
  set W := w₂ x₀ * deriv w x₀ - deriv w₂ x₀ * w x₀
  have hGo := isLittleO_div_sub_exp hf0 hξ hξt hw₂ hw₂e hw fun x hx ↦
    wronskian_eq_of_iteratedDeriv_eq_mul isOpen_Ioi isPreconnected_Ioi hw₂ hw₂q hw hwq hx hx₀
  have hGE := hGo.tendsto_div_nhds_zero
  -- `w / y₊ = (W / 2 + (w / w₂ - (W / 2) e^{2ξ}) e^{-2ξ}) (w₂ / y₋)`
  have hlim := (hGE.const_add (W / 2)).mul (tendsto_div_of_isEquivalent_approximant hf0 hw₂e)
  rw [add_zero, mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_zero_of_isEquivalent_approximant hf0 hw₂e] with x hx
  have hyx := liouvilleGreen_approximant_ne_zero (σ := -ξ x) (hf0 x hx.1)
  have hEx : ((Real.exp (2 * ξ x) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
  refine mul_right_cancel₀ hEx ?_
  rw [← div_approximant_eq_div_mul_exp (hf0 x hx.1)]
  generalize ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ) = A at hyx ⊢
  generalize ((Real.exp (2 * ξ x) : ℝ) : ℂ) = C at hEx ⊢
  have := hx.2
  field_simp
  ring

/-- Under the hypotheses of `TauCeti.tendsto_div_liouvilleGreen_atTop`, a solution `w` whose
Wronskian with `w₂` does not vanish satisfies `|w / y₋| → ∞`, since `w / y₋ = (w / y₊) e^{2ξ}`. -/
private lemma tendsto_norm_div_approximant_atTop (hf0 : ∀ x ∈ Ioi a, 0 < f x)
    (hξ : ∀ x ∈ Ioi a, HasDerivAt ξ (√(f x)) x) (hξt : Tendsto ξ atTop atTop)
    (hw₂ : ContDiffOn ℝ 2 w₂ (Ioi a)) (hw₂q : ∀ x ∈ Ioi a, iteratedDeriv 2 w₂ x = q x * w₂ x)
    (hw₂e : w₂ ~[atTop] fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ))
    (hw : ContDiffOn ℝ 2 w (Ioi a)) (hwq : ∀ x ∈ Ioi a, iteratedDeriv 2 w x = q x * w x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Ioi a) (hW : w₂ x₀ * deriv w x₀ - deriv w₂ x₀ * w x₀ ≠ 0) :
    Tendsto (fun x ↦ ‖w x / ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ)‖) atTop atTop := by
  have h := tendsto_div_liouvilleGreen_atTop hf0 hξ hξt hw₂ hw₂q hw₂e hw hwq hx₀
  refine ((h.norm.pos_mul_atTop (norm_pos_iff.2 (div_ne_zero hW two_ne_zero))
    (Real.tendsto_exp_atTop.comp (hξt.const_mul_atTop two_pos)))).congr' ?_
  filter_upwards [eventually_gt_atTop a] with x hx
  rw [Function.comp_apply, div_approximant_eq_div_mul_exp (hf0 x hx), norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]

/-- **Recessive solutions.** Under the hypotheses of `TauCeti.tendsto_div_liouvilleGreen_atTop`,
every solution `w` whose Wronskian with `w₂` is not zero dominates `w₂`: `w₂ / w → 0`. -/
theorem tendsto_div_of_wronskian_ne_zero_atTop (hf0 : ∀ x ∈ Ioi a, 0 < f x)
    (hξ : ∀ x ∈ Ioi a, HasDerivAt ξ (√(f x)) x) (hξt : Tendsto ξ atTop atTop)
    (hw₂ : ContDiffOn ℝ 2 w₂ (Ioi a)) (hw₂q : ∀ x ∈ Ioi a, iteratedDeriv 2 w₂ x = q x * w₂ x)
    (hw₂e : w₂ ~[atTop] fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ))
    (hw : ContDiffOn ℝ 2 w (Ioi a)) (hwq : ∀ x ∈ Ioi a, iteratedDeriv 2 w x = q x * w x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Ioi a) (hW : w₂ x₀ * deriv w x₀ - deriv w₂ x₀ * w x₀ ≠ 0) :
    Tendsto (fun x ↦ w₂ x / w x) atTop (𝓝 0) := by
  -- `|w₂ / w| = |w₂ / y₋| / |w / y₋|`, with `|w₂ / y₋| → 1` and `|w / y₋| → ∞`
  refine tendsto_zero_iff_norm_tendsto_zero.2 <|
    ((tendsto_div_of_isEquivalent_approximant hf0 hw₂e).norm.div_atTop
      (tendsto_norm_div_approximant_atTop hf0 hξ hξt hw₂ hw₂q hw₂e hw hwq hx₀ hW)).congr' ?_
  filter_upwards [eventually_gt_atTop a] with x hx
  rw [norm_div, norm_div, norm_div, div_div_div_cancel_right₀
    (norm_ne_zero_iff.2 (liouvilleGreen_approximant_ne_zero (hf0 x hx)))]

/-- **Uniqueness of the recessive solution.** Let `f > 0` on `(a, ∞)`, let `ξ` be a primitive of
`f^{1/2}` there with `ξ(x) → ∞`, and let `q` be continuous on `(a, ∞)`. Two solutions of
`w'' = q w`, `C²` on `(a, ∞)`, that are both `∼ f^{-1/4} e^{-ξ}` as `x → ∞` agree on `(a, ∞)`. -/
theorem eqOn_of_isEquivalent_liouvilleGreen_atTop (hf0 : ∀ x ∈ Ioi a, 0 < f x)
    (hξ : ∀ x ∈ Ioi a, HasDerivAt ξ (√(f x)) x) (hξt : Tendsto ξ atTop atTop)
    (hq : ContinuousOn q (Ioi a))
    (hw₂ : ContDiffOn ℝ 2 w₂ (Ioi a)) (hw₂q : ∀ x ∈ Ioi a, iteratedDeriv 2 w₂ x = q x * w₂ x)
    (hw₂e : w₂ ~[atTop] fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ))
    (hw : ContDiffOn ℝ 2 w (Ioi a)) (hwq : ∀ x ∈ Ioi a, iteratedDeriv 2 w x = q x * w x)
    (hwe : w ~[atTop] fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ)) :
    EqOn w w₂ (Ioi a) := by
  have h₂ := tendsto_div_of_isEquivalent_approximant hf0 hw₂e
  have h₁ := tendsto_div_of_isEquivalent_approximant hf0 hwe
  obtain ⟨x₀, hx₀, hw₂x₀⟩ := (eventually_ne_zero_of_isEquivalent_approximant hf0 hw₂e).exists
  -- the Wronskian vanishes, since otherwise `|w / y₋| → ∞`
  have hW : w₂ x₀ * deriv w x₀ - deriv w₂ x₀ * w x₀ = 0 := by
    by_contra hW
    exact not_tendsto_nhds_of_tendsto_atTop
      (tendsto_norm_div_approximant_atTop hf0 hξ hξt hw₂ hw₂q hw₂e hw hwq hx₀ hW) _ h₁.norm
  -- so `w = c w₂` on `(a, ∞)`, and `c = 1` since both are `∼ y₋`
  have hc := eqOn_mul_of_wronskian_eq_zero isOpen_Ioi ordConnected_Ioi hq hw₂ hw₂q hw hwq hx₀
    hw₂x₀ hW
  have hc1 : w x₀ / w₂ x₀ = 1 := by
    refine tendsto_nhds_unique ?_ h₁
    refine (h₂.const_mul (w x₀ / w₂ x₀)).congr' ?_ |>.trans (by rw [mul_one])
    filter_upwards [eventually_gt_atTop a] with x hx
    rw [hc hx, mul_div_assoc]
  intro x hx
  rw [hc hx]
  simp [hc1]

/-- **Dominant solutions.** Let `f > 0` on `(a, ∞)`, let `ξ` be a primitive of `f^{1/2}` there
with `ξ(x) → ∞`, let `q` be continuous on `(a, ∞)`, and let `w₂` be a solution of `w'' = q w`,
`C²` on `(a, ∞)`, with `w₂ ∼ f^{-1/4} e^{-ξ}` as `x → ∞`. Then there is a solution `w₃`, `C²` on
`(a, ∞)`, with `w₃ ∼ f^{-1/4} e^{ξ}` and `w₂ / w₃ → 0` as `x → ∞` (DLMF 2.7.29–2.7.30). -/
theorem exists_liouvilleGreen_dominant_atTop (hf0 : ∀ x ∈ Ioi a, 0 < f x)
    (hξ : ∀ x ∈ Ioi a, HasDerivAt ξ (√(f x)) x) (hξt : Tendsto ξ atTop atTop)
    (hq : ContinuousOn q (Ioi a))
    (hw₂ : ContDiffOn ℝ 2 w₂ (Ioi a)) (hw₂q : ∀ x ∈ Ioi a, iteratedDeriv 2 w₂ x = q x * w₂ x)
    (hw₂e : w₂ ~[atTop] fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ)) :
    ∃ w₃ : ℝ → ℂ, ContDiffOn ℝ 2 w₃ (Ioi a) ∧
      (∀ x ∈ Ioi a, iteratedDeriv 2 w₃ x = q x * w₃ x) ∧
      (w₃ ~[atTop] fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (ξ x) : ℝ) : ℂ)) ∧
      Tendsto (fun x ↦ w₂ x / w₃ x) atTop (𝓝 0) := by
  obtain ⟨x₀, hx₀, hw₂x₀⟩ := (eventually_ne_zero_of_isEquivalent_approximant hf0 hw₂e).exists
  -- the solution with `w₃(x₀) = 0` and `w₃'(x₀) = 2 / w₂(x₀)` has Wronskian `2` with `w₂`
  obtain ⟨w₃, hw₃, hw₃q, hw₃0, hw₃1⟩ := exists_contDiffOn_iteratedDeriv_eq_mul isOpen_Ioi
    ordConnected_Ioi hq hx₀ 0 (2 / w₂ x₀)
  have hW : w₂ x₀ * deriv w₃ x₀ - deriv w₂ x₀ * w₃ x₀ = 2 := by
    rw [hw₃0, hw₃1]
    field_simp
    ring
  have h := tendsto_div_liouvilleGreen_atTop hf0 hξ hξt hw₂ hw₂q hw₂e hw₃ hw₃q hx₀
  rw [hW, div_self two_ne_zero] at h
  exact ⟨w₃, hw₃, hw₃q, isEquivalent_of_tendsto_one h,
    tendsto_div_of_wronskian_ne_zero_atTop hf0 hξ hξt hw₂ hw₂q hw₂e hw₃ hw₃q hx₀
      (hW ▸ two_ne_zero)⟩

/-- **The Liouville–Green solution is asymptotic to its approximant.** Under the hypotheses of the
Liouville–Green theorem `TauCeti.exists_liouvilleGreen_atTop` (`f` positive and `C²`, `g`
continuous, `ξ` a primitive of `f^{1/2}` on `(a, ∞)`, and `Φ` integrable on `(x, ∞)` for every
`x > a`), the equation `w'' = (f + g) w` has a solution `w`, `C²` on `(a, ∞)`, with
`w ∼ f^{-1/4} e^{-ξ}` as `x → ∞` (DLMF 2.7.26). -/
theorem exists_liouvilleGreen_isEquivalent_atTop {g Φ : ℝ → ℂ} (hf : ContDiffOn ℝ 2 f (Ioi a))
    (hf0 : ∀ x ∈ Ioi a, 0 < f x) (hg : ContinuousOn g (Ioi a))
    (hξ : ∀ x ∈ Ioi a, HasDerivAt ξ (√(f x)) x)
    (hΦ : ∀ x ∈ Ioi a, Φ x = ↑(f x ^ (-(1 / 4) : ℝ) *
      iteratedDeriv 2 (fun t ↦ f t ^ (-(1 / 4) : ℝ)) x) - g x / ↑√(f x))
    (hΦi : ∀ x ∈ Ioi a, IntegrableOn Φ (Ioi x)) :
    ∃ w : ℝ → ℂ, ContDiffOn ℝ 2 w (Ioi a) ∧
      (∀ x ∈ Ioi a, iteratedDeriv 2 w x = (f x + g x) * w x) ∧
      w ~[atTop] fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ) := by
  obtain ⟨w, ε, hw, -, hwε⟩ := exists_liouvilleGreen_atTop hf hf0 hg hξ hΦ hΦi
  refine ⟨w, hw, fun x hx ↦ (hwε x hx).1, isEquivalent_of_tendsto_one ?_⟩
  -- `‖ε(x)‖ ≤ exp(V(x) / 2) - 1 → 0`, since `V(x) = ∫ₓ^∞ |Φ| → 0`
  have hV : Tendsto (fun x ↦ Real.exp ((∫ v in Ioi x, ‖Φ v‖) / 2) - 1) atTop (𝓝 0) := by
    have h := ((tendsto_integral_Ioi_zero (f := fun v ↦ ‖Φ v‖)
      (μ := volume) tendsto_id).div_const 2).rexp.sub_const 1
    simpa using h
  have hε : Tendsto ε atTop (𝓝 0) :=
    squeeze_zero_norm' ((eventually_gt_atTop a).mono fun x hx ↦ (hwε x hx).2.2.1) hV
  have h := hε.const_add 1
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop a] with x hx
  rw [Pi.div_apply, (hwε x hx).2.1,
    mul_div_cancel_left₀ _ (liouvilleGreen_approximant_ne_zero (hf0 x hx))]

end TauCeti
