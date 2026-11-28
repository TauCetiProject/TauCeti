/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Liouville.Interval
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.Calculus.Deriv.Growth
import TauCeti.Analysis.Calculus.IteratedDeriv.Basic
import TauCeti.Analysis.ODE.SecondOrder.Linear
import TauCeti.Analysis.ODE.Wronskian
import TauCeti.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Order.Filter.AtTopBot.Group
import TauCeti.Order.Filter.Basic

/-!
# Recessive and dominant Liouville–Green solutions

Let `I = (a₁, a₂)` be an open interval of `ℝ`, with `-∞ ≤ a₁ < a₂ ≤ ∞`, let `f` be positive on
`I` and let `ξ` be a primitive of `f^{1/2}` there. The Liouville–Green approximants of the
solutions of a second-order equation `w'' = q w` are

  `y₋ = f^{-1/4} e^{-ξ}` and `y₊ = f^{-1/4} e^{ξ}`.

The limits `x → a₂-` and `x → a₁+` within `I` are the images `map (↑) atTop` and
`map (↑) atBot` of the filters `atTop` and `atBot` on the subtype `I`. For `I = (a₁, a₂)` with
`a₂` finite, the first is `𝓝[<] a₂` (`Filter.map_coe_Ioo_atTop`); for `I = (a₁, ∞)` it is
`atTop` (`Filter.map_val_Ioi_atTop`), and dually at the left end.

When `ξ(x) → ∞` as `x → a₂-`, a solution `w₂ ∼ y₋` is *recessive* at `a₂`, and every solution
whose Wronskian with it does not vanish is *dominant*. Precisely, if `w₂ ∼ y₋` as `x → a₂-` then
every solution `w` satisfies

  `w / y₊ → W(w₂, w) / 2` as `x → a₂-`,

where `W(w₂, w) = w₂ w' - w₂' w` is the (constant) Wronskian
(`TauCeti.tendsto_div_liouvilleGreen_atTop`). Consequently:
* every solution `w` with `W(w₂, w) ≠ 0` satisfies `w₂ / w → 0`
  (`TauCeti.tendsto_div_of_wronskian_ne_zero_atTop`);
* if `q` is continuous on `I`, then `w₂` is the only solution with `w₂ ∼ y₋`
  (`TauCeti.eqOn_of_isEquivalent_liouvilleGreen_atTop`);
* if `q` is continuous on `I`, then there is a solution `w₃ ∼ y₊`, and `w₂ / w₃ → 0`
  (`TauCeti.exists_liouvilleGreen_dominant_atTop`).
The solution `w₃` is not unique: `w₃ + c w₂` has the same property for every constant `c`.

At the left end the roles of `y₋` and `y₊` are exchanged. When `ξ(x) → -∞` as `x → a₁+`, a
solution `w₁ ∼ y₊` there is recessive: every solution `w` satisfies
`w / y₋ → -W(w₁, w) / 2` (`TauCeti.tendsto_div_liouvilleGreen_atBot`), the solutions with
`W(w₁, w) ≠ 0` dominate `w₁` (`TauCeti.tendsto_div_of_wronskian_ne_zero_atBot`), `w₁` is the only
solution with `w₁ ∼ y₊` (`TauCeti.eqOn_of_isEquivalent_liouvilleGreen_atBot`), and there is a
solution `w₄ ∼ y₋` with `w₁ / w₄ → 0` (`TauCeti.exists_liouvilleGreen_dominant_atBot`).

For the Liouville–Green equation `w'' = (f + g) w`, under the hypotheses of the Liouville–Green
theorem `TauCeti.exists_liouvilleGreen_right`, its solution `w₂ = y₋ (1 + ε)` has `ε(x) → 0`
as `x → a₂-`, so `w₂ ∼ y₋` there (`TauCeti.exists_liouvilleGreen_isEquivalent_atTop`); likewise
the solution `w₁ = y₊ (1 + ε)` of `TauCeti.exists_liouvilleGreen_left` has `w₁ ∼ y₊` as
`x → a₁+` (`TauCeti.exists_liouvilleGreen_isEquivalent_atBot`). This is DLMF 2.7.26, and holds
without `ξ` being unbounded; the characterization of `w₁` and `w₂` by this property, and the
results above, use it.

## Proof

On a neighbourhood of `a₂` where `w₂` does not vanish, `(w / w₂)' = W / w₂²`. Writing
`w₂ = y₋ ρ` with `ρ → 1`, one has `1 / w₂² = f^{1/2} e^{2ξ} / ρ²`, so
`G = w / w₂ - (W / 2) e^{2ξ}` has derivative `(W / 2) (ρ⁻² - 1) (e^{2ξ})'`, which is
`o((e^{2ξ})')`. Since `e^{2ξ} → ∞`, L'Hôpital's rule for little-o at the right end of an interval
(`TauCeti.isLittleO_map_val_atTop_of_hasDerivAt`) gives `G = o(e^{2ξ})`, and
`w / y₊ = (W / 2 + G e^{-2ξ}) ρ → W / 2`. The uniqueness of `w₂` follows: a solution `w ∼ y₋`
must have `W(w₂, w) = 0`, since otherwise `|w / y₋| = |w / y₊| e^{2ξ} → ∞`, and then `w` is a
multiple of `w₂` (`TauCeti.eqOn_mul_of_wronskian_eq_zero`), necessarily `w₂` itself. The dominant
solution is the solution with `w₃(x₀) = 0` and `w₃'(x₀) = 2 / w₂(x₀)`, whose Wronskian with
`w₂` is `2` (`TauCeti.exists_contDiffOn_iteratedDeriv_eq_mul`).

The left end reduces to the right end by the reflection `x ↦ -x`, which maps `I` to `-I`, the
filter `x → a₁+` to `t → -a₁-`, and the data `f`, `ξ`, `q` to `f(-t)`, `-ξ(-t)`, `q(-t)`. It
exchanges the two approximants and changes the sign of the Wronskian.

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

variable {I : Set ℝ} {f ξ : ℝ → ℝ} {q w₁ w₂ w : ℝ → ℂ}

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
private lemma tendsto_div_of_isEquivalent_approximant {l : Filter ℝ} {u : ℝ → ℂ}
    (hl : ∀ᶠ x in l, x ∈ I) (hf0 : ∀ x ∈ I, 0 < f x)
    (hu : u ~[l] fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ)) :
    Tendsto (fun x ↦ u x / ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ)) l (𝓝 1) :=
  (isEquivalent_iff_tendsto_one (hl.mono fun x hx ↦
    liouvilleGreen_approximant_ne_zero (hf0 x hx))).1 hu

/-- A function asymptotic to `y₋ = f^{-1/4} e^{-ξ}` eventually does not vanish. -/
private lemma eventually_ne_zero_of_isEquivalent_approximant {l : Filter ℝ} {u : ℝ → ℂ}
    (hl : ∀ᶠ x in l, x ∈ I) (hf0 : ∀ x ∈ I, 0 < f x)
    (hu : u ~[l] fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ)) :
    ∀ᶠ x in l, x ∈ I ∧ u x ≠ 0 :=
  hl.and <| hu.eventually_ne_zero <| hl.mono fun x hx ↦
    liouvilleGreen_approximant_ne_zero (hf0 x hx)

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

/-- With `W = w₂ w' - w₂' w` the Wronskian, `w / w₂ - (W / 2) e^{2ξ} = o(e^{2ξ})` as `x → a₂-`,
by L'Hôpital's rule for little-o. -/
private lemma isLittleO_div_sub_exp {W : ℂ} (hI : IsOpen I) (hIc : I.OrdConnected)
    (hf0 : ∀ x ∈ I, 0 < f x) (hξ : ∀ x ∈ I, HasDerivAt ξ (√(f x)) x)
    (hξt : Tendsto ξ (map ((↑) : I → ℝ) atTop) atTop) (hw₂ : ContDiffOn ℝ 2 w₂ I)
    (hw₂e : w₂ ~[map ((↑) : I → ℝ) atTop]
      fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ))
    (hw : ContDiffOn ℝ 2 w I) (hW : ∀ x ∈ I, w₂ x * deriv w x - deriv w₂ x * w x = W) :
    (fun x ↦ w x / w₂ x - W / 2 * ((Real.exp (2 * ξ x) : ℝ) : ℂ)) =o[map ((↑) : I → ℝ) atTop]
      fun x ↦ ((Real.exp (2 * ξ x) : ℝ) : ℂ) := by
  have hl := eventually_mem_map_val (s := I) atTop
  refine Complex.isLittleO_ofReal_right.2 <| isLittleO_map_val_atTop_of_hasDerivAt hIc
    ((eventually_ne_zero_of_isEquivalent_approximant hl hf0 hw₂e).mono fun x hx ↦
      hasDerivAt_div_sub_exp (hf0 x hx.1) (hξ x hx.1)
        (hw₂.hasDerivAt_and_hasDerivAt_deriv hI hx.1).1
        (hw.hasDerivAt_and_hasDerivAt_deriv hI hx.1).1 hx.2 (hW x hx.1))
    (hl.mono fun x hx ↦ ((hξ x hx).const_mul 2).exp)
    (Eventually.of_forall fun x ↦ by positivity)
    (Real.tendsto_exp_atTop.comp (hξt.const_mul_atTop two_pos)) ?_
  have hc := (((tendsto_div_of_isEquivalent_approximant hl hf0 hw₂e).inv₀ one_ne_zero).pow 2
    |>.sub_const 1).const_mul (W / 2)
  rw [inv_one, one_pow, sub_self, mul_zero] at hc
  refine IsLittleO.of_bound fun c hc0 ↦ ?_
  filter_upwards [hc.eventually (Metric.closedBall_mem_nhds (0 : ℂ) hc0)] with x hx
  rw [dist_zero_right] at hx
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

/-- **Dominant behaviour of the solutions independent of a recessive one.** Let `I = (a₁, a₂)` be
an open interval, let `f > 0` on `I`, let `ξ` be a primitive of `f^{1/2}` there with `ξ(x) → ∞` as
`x → a₂-`, and let `w₂` be a solution of `w'' = q w`, `C²` on `I`, with `w₂ ∼ f^{-1/4} e^{-ξ}` as
`x → a₂-`. Then every solution `w` satisfies `w / (f^{-1/4} e^{ξ}) → W / 2` as `x → a₂-`, where
`W = w₂ w' - w₂' w` is their Wronskian, at any point `x₀ ∈ I`. -/
theorem tendsto_div_liouvilleGreen_atTop (hI : IsOpen I) (hIc : I.OrdConnected)
    (hf0 : ∀ x ∈ I, 0 < f x) (hξ : ∀ x ∈ I, HasDerivAt ξ (√(f x)) x)
    (hξt : Tendsto ξ (map ((↑) : I → ℝ) atTop) atTop)
    (hw₂ : ContDiffOn ℝ 2 w₂ I) (hw₂q : ∀ x ∈ I, iteratedDeriv 2 w₂ x = q x * w₂ x)
    (hw₂e : w₂ ~[map ((↑) : I → ℝ) atTop]
      fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ))
    (hw : ContDiffOn ℝ 2 w I) (hwq : ∀ x ∈ I, iteratedDeriv 2 w x = q x * w x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    Tendsto (fun x ↦ w x / ((f x ^ (-(1 / 4) : ℝ) * Real.exp (ξ x) : ℝ) : ℂ))
      (map ((↑) : I → ℝ) atTop)
      (𝓝 ((w₂ x₀ * deriv w x₀ - deriv w₂ x₀ * w x₀) / 2)) := by
  have hl := eventually_mem_map_val (s := I) atTop
  set W := w₂ x₀ * deriv w x₀ - deriv w₂ x₀ * w x₀
  have hGo := isLittleO_div_sub_exp hI hIc hf0 hξ hξt hw₂ hw₂e hw fun x hx ↦
    wronskian_eq_of_iteratedDeriv_eq_mul hI hIc.isPreconnected hw₂ hw₂q hw hwq hx hx₀
  have hGE := hGo.tendsto_div_nhds_zero
  -- `w / y₊ = (W / 2 + (w / w₂ - (W / 2) e^{2ξ}) e^{-2ξ}) (w₂ / y₋)`
  have hlim := (hGE.const_add (W / 2)).mul (tendsto_div_of_isEquivalent_approximant hl hf0 hw₂e)
  rw [add_zero, mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_zero_of_isEquivalent_approximant hl hf0 hw₂e] with x hx
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
private lemma tendsto_norm_div_approximant_atTop (hI : IsOpen I) (hIc : I.OrdConnected)
    (hf0 : ∀ x ∈ I, 0 < f x) (hξ : ∀ x ∈ I, HasDerivAt ξ (√(f x)) x)
    (hξt : Tendsto ξ (map ((↑) : I → ℝ) atTop) atTop)
    (hw₂ : ContDiffOn ℝ 2 w₂ I) (hw₂q : ∀ x ∈ I, iteratedDeriv 2 w₂ x = q x * w₂ x)
    (hw₂e : w₂ ~[map ((↑) : I → ℝ) atTop]
      fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ))
    (hw : ContDiffOn ℝ 2 w I) (hwq : ∀ x ∈ I, iteratedDeriv 2 w x = q x * w x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) (hW : w₂ x₀ * deriv w x₀ - deriv w₂ x₀ * w x₀ ≠ 0) :
    Tendsto (fun x ↦ ‖w x / ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ)‖)
      (map ((↑) : I → ℝ) atTop)
      atTop := by
  have h := tendsto_div_liouvilleGreen_atTop hI hIc hf0 hξ hξt hw₂ hw₂q hw₂e hw hwq hx₀
  refine ((h.norm.pos_mul_atTop (norm_pos_iff.2 (div_ne_zero hW two_ne_zero))
    (Real.tendsto_exp_atTop.comp (hξt.const_mul_atTop two_pos)))).congr' ?_
  filter_upwards [eventually_mem_map_val (s := I) atTop] with x hx
  rw [Function.comp_apply, div_approximant_eq_div_mul_exp (hf0 x hx), norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]

/-- **Recessive solutions.** Under the hypotheses of `TauCeti.tendsto_div_liouvilleGreen_atTop`,
every solution `w` whose Wronskian with `w₂` is not zero dominates `w₂`: `w₂ / w → 0` as
`x → a₂-`. -/
theorem tendsto_div_of_wronskian_ne_zero_atTop (hI : IsOpen I) (hIc : I.OrdConnected)
    (hf0 : ∀ x ∈ I, 0 < f x) (hξ : ∀ x ∈ I, HasDerivAt ξ (√(f x)) x)
    (hξt : Tendsto ξ (map ((↑) : I → ℝ) atTop) atTop)
    (hw₂ : ContDiffOn ℝ 2 w₂ I) (hw₂q : ∀ x ∈ I, iteratedDeriv 2 w₂ x = q x * w₂ x)
    (hw₂e : w₂ ~[map ((↑) : I → ℝ) atTop]
      fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ))
    (hw : ContDiffOn ℝ 2 w I) (hwq : ∀ x ∈ I, iteratedDeriv 2 w x = q x * w x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) (hW : w₂ x₀ * deriv w x₀ - deriv w₂ x₀ * w x₀ ≠ 0) :
    Tendsto (fun x ↦ w₂ x / w x) (map ((↑) : I → ℝ) atTop) (𝓝 0) := by
  have hl := eventually_mem_map_val (s := I) atTop
  -- `|w₂ / w| = |w₂ / y₋| / |w / y₋|`, with `|w₂ / y₋| → 1` and `|w / y₋| → ∞`
  refine tendsto_zero_iff_norm_tendsto_zero.2 <|
    ((tendsto_div_of_isEquivalent_approximant hl hf0 hw₂e).norm.div_atTop
      (tendsto_norm_div_approximant_atTop hI hIc hf0 hξ hξt hw₂ hw₂q hw₂e hw hwq hx₀
        hW)).congr' ?_
  filter_upwards [hl] with x hx
  rw [norm_div, norm_div, norm_div, div_div_div_cancel_right₀
    (norm_ne_zero_iff.2 (liouvilleGreen_approximant_ne_zero (hf0 x hx)))]

/-- **Uniqueness of the recessive solution.** Let `I = (a₁, a₂)` be an open interval, let `f > 0`
on `I`, let `ξ` be a primitive of `f^{1/2}` there with `ξ(x) → ∞` as `x → a₂-`, and let `q` be
continuous on `I`. Two solutions of `w'' = q w`, `C²` on `I`, that are both
`∼ f^{-1/4} e^{-ξ}` as `x → a₂-` agree on `I`. -/
theorem eqOn_of_isEquivalent_liouvilleGreen_atTop (hI : IsOpen I) (hIc : I.OrdConnected)
    (hf0 : ∀ x ∈ I, 0 < f x) (hξ : ∀ x ∈ I, HasDerivAt ξ (√(f x)) x)
    (hξt : Tendsto ξ (map ((↑) : I → ℝ) atTop) atTop) (hq : ContinuousOn q I)
    (hw₂ : ContDiffOn ℝ 2 w₂ I) (hw₂q : ∀ x ∈ I, iteratedDeriv 2 w₂ x = q x * w₂ x)
    (hw₂e : w₂ ~[map ((↑) : I → ℝ) atTop]
      fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ))
    (hw : ContDiffOn ℝ 2 w I) (hwq : ∀ x ∈ I, iteratedDeriv 2 w x = q x * w x)
    (hwe : w ~[map ((↑) : I → ℝ) atTop]
      fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ)) :
    EqOn w w₂ I := by
  rcases I.eq_empty_or_nonempty with rfl | hne
  · exact eqOn_empty _ _
  have : Nonempty I := hne.to_subtype
  have hl := eventually_mem_map_val (s := I) atTop
  have h₂ := tendsto_div_of_isEquivalent_approximant hl hf0 hw₂e
  have h₁ := tendsto_div_of_isEquivalent_approximant hl hf0 hwe
  obtain ⟨x₀, hx₀, hw₂x₀⟩ := (eventually_ne_zero_of_isEquivalent_approximant hl hf0 hw₂e).exists
  -- the Wronskian vanishes, since otherwise `|w / y₋| → ∞`
  have hW : w₂ x₀ * deriv w x₀ - deriv w₂ x₀ * w x₀ = 0 := by
    by_contra hW
    exact not_tendsto_nhds_of_tendsto_atTop
      (tendsto_norm_div_approximant_atTop hI hIc hf0 hξ hξt hw₂ hw₂q hw₂e hw hwq hx₀ hW) _
      h₁.norm
  -- so `w = c w₂` on `I`, and `c = 1` since both are `∼ y₋`
  have hc := eqOn_mul_of_wronskian_eq_zero hI hIc hq hw₂ hw₂q hw hwq hx₀ hw₂x₀ hW
  have hc1 : w x₀ / w₂ x₀ = 1 := by
    refine tendsto_nhds_unique ?_ h₁
    refine (h₂.const_mul (w x₀ / w₂ x₀)).congr' ?_ |>.trans (by rw [mul_one])
    filter_upwards [hl] with x hx
    rw [hc hx, mul_div_assoc]
  intro x hx
  rw [hc hx]
  simp [hc1]

/-- **Dominant solutions.** Let `I = (a₁, a₂)` be an open interval, let `f > 0` on `I`, let `ξ` be
a primitive of `f^{1/2}` there with `ξ(x) → ∞` as `x → a₂-`, let `q` be continuous on `I`, and
let `w₂` be a solution of `w'' = q w`, `C²` on `I`, with `w₂ ∼ f^{-1/4} e^{-ξ}` as `x → a₂-`.
Then there is a solution `w₃`, `C²` on `I`, with `w₃ ∼ f^{-1/4} e^{ξ}` and `w₂ / w₃ → 0` as
`x → a₂-` (DLMF 2.7.29–2.7.30). -/
theorem exists_liouvilleGreen_dominant_atTop (hI : IsOpen I) (hIc : I.OrdConnected)
    (hf0 : ∀ x ∈ I, 0 < f x) (hξ : ∀ x ∈ I, HasDerivAt ξ (√(f x)) x)
    (hξt : Tendsto ξ (map ((↑) : I → ℝ) atTop) atTop) (hq : ContinuousOn q I)
    (hw₂ : ContDiffOn ℝ 2 w₂ I) (hw₂q : ∀ x ∈ I, iteratedDeriv 2 w₂ x = q x * w₂ x)
    (hw₂e : w₂ ~[map ((↑) : I → ℝ) atTop]
      fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ)) :
    ∃ w₃ : ℝ → ℂ, ContDiffOn ℝ 2 w₃ I ∧ (∀ x ∈ I, iteratedDeriv 2 w₃ x = q x * w₃ x) ∧
      (w₃ ~[map ((↑) : I → ℝ) atTop] fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (ξ x) : ℝ) : ℂ)) ∧
      Tendsto (fun x ↦ w₂ x / w₃ x) (map ((↑) : I → ℝ) atTop) (𝓝 0) := by
  rcases I.eq_empty_or_nonempty with rfl | hne
  · have hbot : map ((↑) : (∅ : Set ℝ) → ℝ) atTop = ⊥ := by
      rw [filter_eq_bot_of_isEmpty (atTop : Filter (∅ : Set ℝ)), map_bot]
    exact ⟨0, contDiffOn_empty, fun x hx ↦ hx.elim,
      by rw [hbot]; exact IsLittleO.of_bound fun _ _ ↦ eventually_bot,
      by rw [hbot]; exact tendsto_bot⟩
  have : Nonempty I := hne.to_subtype
  have hl := eventually_mem_map_val (s := I) atTop
  obtain ⟨x₀, hx₀, hw₂x₀⟩ := (eventually_ne_zero_of_isEquivalent_approximant hl hf0 hw₂e).exists
  -- the solution with `w₃(x₀) = 0` and `w₃'(x₀) = 2 / w₂(x₀)` has Wronskian `2` with `w₂`
  obtain ⟨w₃, hw₃, hw₃q, hw₃0, hw₃1⟩ := exists_contDiffOn_iteratedDeriv_eq_mul hI hIc hq hx₀ 0
    (2 / w₂ x₀)
  have hW : w₂ x₀ * deriv w₃ x₀ - deriv w₂ x₀ * w₃ x₀ = 2 := by
    rw [hw₃0, hw₃1]
    field_simp
    ring
  have h := tendsto_div_liouvilleGreen_atTop hI hIc hf0 hξ hξt hw₂ hw₂q hw₂e hw₃ hw₃q hx₀
  rw [hW, div_self two_ne_zero] at h
  exact ⟨w₃, hw₃, hw₃q, isEquivalent_of_tendsto_one h,
    tendsto_div_of_wronskian_ne_zero_atTop hI hIc hf0 hξ hξt hw₂ hw₂q hw₂e hw₃ hw₃q hx₀
      (hW ▸ two_ne_zero)⟩

/-- A function `w = f^{-1/4} e^{σ} (1 + ε)` whose relative error is bounded by
`|ε| ≤ exp(V / 2) - 1`, where `V → 0` along a filter `l` on `I`, is asymptotic to
`f^{-1/4} e^{σ}` along `l`. -/
private lemma isEquivalent_approximant_of_tendsto {l : Filter ℝ} {w ε : ℝ → ℂ} {σ V : ℝ → ℝ}
    (hl : ∀ᶠ x in l, x ∈ I) (hf0 : ∀ x ∈ I, 0 < f x)
    (hwε : ∀ x ∈ I, w x = ↑(f x ^ (-(1 / 4) : ℝ) * Real.exp (σ x)) * (1 + ε x) ∧
      ‖ε x‖ ≤ Real.exp (V x / 2) - 1)
    (hV : Tendsto V l (𝓝 0)) :
    w ~[l] fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (σ x) : ℝ) : ℂ) := by
  refine isEquivalent_of_tendsto_one ?_
  have hε : Tendsto ε l (𝓝 0) := squeeze_zero_norm' (hl.mono fun x hx ↦ (hwε x hx).2)
    (by simpa using ((hV.div_const 2).rexp.sub_const 1))
  have h := hε.const_add 1
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [hl] with x hx
  rw [Pi.div_apply, (hwε x hx).1,
    mul_div_cancel_left₀ _ (liouvilleGreen_approximant_ne_zero (hf0 x hx))]

/-- **The Liouville–Green solution is asymptotic to its approximant at the right end.** Under the
hypotheses of the Liouville–Green theorem `TauCeti.exists_liouvilleGreen_right` on an open
interval `I = (a₁, a₂)` (`f` positive and `C²`, `g` continuous, `ξ` a primitive of `f^{1/2}`
on `I`, and `Φ` integrable on `(x, a₂)` for every `x ∈ I`), the equation `w'' = (f + g) w` has
a solution `w`, `C²` on `I`, with `w ∼ f^{-1/4} e^{-ξ}` as `x → a₂-` (DLMF 2.7.26). -/
theorem exists_liouvilleGreen_isEquivalent_atTop {g Φ : ℝ → ℂ} (hI : IsOpen I)
    (hIc : I.OrdConnected) (hf : ContDiffOn ℝ 2 f I) (hf0 : ∀ x ∈ I, 0 < f x)
    (hg : ContinuousOn g I) (hξ : ∀ x ∈ I, HasDerivAt ξ (√(f x)) x)
    (hΦ : ∀ x ∈ I, Φ x = ↑(f x ^ (-(1 / 4) : ℝ) *
      iteratedDeriv 2 (fun t ↦ f t ^ (-(1 / 4) : ℝ)) x) - g x / ↑√(f x))
    (hΦi : ∀ x ∈ I, IntegrableOn Φ (Ioi x ∩ I)) :
    ∃ w : ℝ → ℂ, ContDiffOn ℝ 2 w I ∧ (∀ x ∈ I, iteratedDeriv 2 w x = (f x + g x) * w x) ∧
      w ~[map ((↑) : I → ℝ) atTop] fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ) := by
  obtain ⟨w, ε, hw, -, hwε⟩ := exists_liouvilleGreen_right hI hIc hf hf0 hg hξ hΦ hΦi
  -- `‖ε(x)‖ ≤ exp(V(x) / 2) - 1 → 0`, since `V(x) = ∫_{(x, a₂)} |Φ| → 0`
  exact ⟨w, hw, fun x hx ↦ (hwε x hx).1, isEquivalent_approximant_of_tendsto
    (eventually_mem_map_val atTop) hf0 (fun x hx ↦ ⟨(hwε x hx).2.1, (hwε x hx).2.2.1⟩)
    (tendsto_setIntegral_Ioi_inter_map_val_atTop hIc fun x hx ↦ (hΦi x hx).norm)⟩

/-! ### The left end

The results at the left end `a₁` follow from those at the right end by the reflection
`x ↦ -x`. -/

/-- The reflection `t ↦ w(-t)` of a solution of `w'' = q w`, `C²` on `I`, is a solution of
`w'' = q(-t) w`, `C²` on `-I`. -/
private lemma contDiffOn_and_iteratedDeriv_comp_neg (hw : ContDiffOn ℝ 2 w I)
    (hwq : ∀ x ∈ I, iteratedDeriv 2 w x = q x * w x) :
    ContDiffOn ℝ 2 (fun t ↦ w (-t)) (Neg.neg ⁻¹' I) ∧
      ∀ t ∈ Neg.neg ⁻¹' I, iteratedDeriv 2 (fun t ↦ w (-t)) t = q (-t) * w (-t) :=
  ⟨hw.comp contDiff_neg.contDiffOn fun _ ht ↦ ht, fun t ht ↦ by
    rw [iteratedDeriv_comp_neg, neg_one_sq, one_smul, hwq _ ht]⟩

/-- The reflection `x ↦ -x` turns an open order-connected `I = (a₁, a₂)`, a positive `f` and a
primitive `ξ` of `f^{1/2}` with `ξ(x) → -∞` as `x → a₁+` into the open order-connected `-I`, the
positive `f(-t)` and the primitive `-ξ(-t)` of `f(-t)^{1/2}`, which tends to `∞` as
`t → (-a₁)-`. -/
private lemma liouvilleGreen_data_comp_neg (hI : IsOpen I) (hIc : I.OrdConnected)
    (hf0 : ∀ x ∈ I, 0 < f x) (hξ : ∀ x ∈ I, HasDerivAt ξ (√(f x)) x)
    (hξt : Tendsto ξ (map ((↑) : I → ℝ) atBot) atBot) :
    IsOpen (Neg.neg ⁻¹' I) ∧ (Neg.neg ⁻¹' I).OrdConnected ∧ (∀ t ∈ Neg.neg ⁻¹' I, 0 < f (-t)) ∧
      (∀ t ∈ Neg.neg ⁻¹' I, HasDerivAt (fun t ↦ -ξ (-t)) (√(f (-t))) t) ∧
      Tendsto (fun t ↦ -ξ (-t)) (map ((↑) : (Neg.neg ⁻¹' I : Set ℝ) → ℝ) atTop) atTop := by
  refine ⟨hI.preimage continuous_neg, hIc.preimage_anti fun _ _ h ↦ neg_le_neg h,
    fun t ht ↦ hf0 _ ht, fun t ht ↦ ?_,
    tendsto_neg_atBot_atTop.comp (hξt.comp (tendsto_neg_map_val_atTop I))⟩
  convert ((hξ _ ht).comp t (hasDerivAt_neg t)).neg using 1
  · ext
    simp
  · ring

/-- A function asymptotic to `f^{-1/4} e^{ξ}` as `x → a₁+` has its reflection `t ↦ u(-t)`
asymptotic, as `t → (-a₁)-`, to the approximant `f(-t)^{-1/4} e^{-(-ξ(-t))}` of the reflected
data. -/
private lemma isEquivalent_comp_neg {u : ℝ → ℂ} (h : u ~[map ((↑) : I → ℝ) atBot]
      fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (ξ x) : ℝ) : ℂ)) :
    (fun t ↦ u (-t)) ~[map ((↑) : (Neg.neg ⁻¹' I : Set ℝ) → ℝ) atTop]
      fun t ↦ ((f (-t) ^ (-(1 / 4) : ℝ) * Real.exp (-(-ξ (-t))) : ℝ) : ℂ) :=
  (h.comp_tendsto (tendsto_neg_map_val_atTop I)).congr_right
    (.of_forall fun t ↦ by simp only [Function.comp_apply, neg_neg])

/-- **Dominant behaviour at the left end.** Let `I = (a₁, a₂)` be an open interval, let `f > 0`
on `I`, let `ξ` be a primitive of `f^{1/2}` there with `ξ(x) → -∞` as `x → a₁+`, and let `w₁` be
a solution of `w'' = q w`, `C²` on `I`, with `w₁ ∼ f^{-1/4} e^{ξ}` as `x → a₁+`. Then every
solution `w` satisfies `w / (f^{-1/4} e^{-ξ}) → -W / 2` as `x → a₁+`, where
`W = w₁ w' - w₁' w` is their Wronskian, at any point `x₀ ∈ I`. -/
theorem tendsto_div_liouvilleGreen_atBot (hI : IsOpen I) (hIc : I.OrdConnected)
    (hf0 : ∀ x ∈ I, 0 < f x) (hξ : ∀ x ∈ I, HasDerivAt ξ (√(f x)) x)
    (hξt : Tendsto ξ (map ((↑) : I → ℝ) atBot) atBot)
    (hw₁ : ContDiffOn ℝ 2 w₁ I) (hw₁q : ∀ x ∈ I, iteratedDeriv 2 w₁ x = q x * w₁ x)
    (hw₁e : w₁ ~[map ((↑) : I → ℝ) atBot]
      fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (ξ x) : ℝ) : ℂ))
    (hw : ContDiffOn ℝ 2 w I) (hwq : ∀ x ∈ I, iteratedDeriv 2 w x = q x * w x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    Tendsto (fun x ↦ w x / ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ))
      (map ((↑) : I → ℝ) atBot) (𝓝 (-(w₁ x₀ * deriv w x₀ - deriv w₁ x₀ * w x₀) / 2)) := by
  obtain ⟨hI', hIc', hf0', hξ', hξt'⟩ := liouvilleGreen_data_comp_neg hI hIc hf0 hξ hξt
  obtain ⟨hw₁', hw₁q'⟩ := contDiffOn_and_iteratedDeriv_comp_neg hw₁ hw₁q
  obtain ⟨hw', hwq'⟩ := contDiffOn_and_iteratedDeriv_comp_neg hw hwq
  have h := (tendsto_div_liouvilleGreen_atTop hI' hIc' hf0' hξ' hξt' hw₁' hw₁q'
    (isEquivalent_comp_neg hw₁e) hw' hwq' (x₀ := -x₀) (by simpa using hx₀)).comp
    (tendsto_neg_map_val_atBot I)
  simp only [Function.comp_def, deriv_comp_neg, neg_neg] at h
  convert h using 3
  ring

/-- **Recessive solutions at the left end.** Under the hypotheses of
`TauCeti.tendsto_div_liouvilleGreen_atBot`, every solution `w` whose Wronskian with `w₁` is not
zero dominates `w₁`: `w₁ / w → 0` as `x → a₁+`. -/
theorem tendsto_div_of_wronskian_ne_zero_atBot (hI : IsOpen I) (hIc : I.OrdConnected)
    (hf0 : ∀ x ∈ I, 0 < f x) (hξ : ∀ x ∈ I, HasDerivAt ξ (√(f x)) x)
    (hξt : Tendsto ξ (map ((↑) : I → ℝ) atBot) atBot)
    (hw₁ : ContDiffOn ℝ 2 w₁ I) (hw₁q : ∀ x ∈ I, iteratedDeriv 2 w₁ x = q x * w₁ x)
    (hw₁e : w₁ ~[map ((↑) : I → ℝ) atBot]
      fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (ξ x) : ℝ) : ℂ))
    (hw : ContDiffOn ℝ 2 w I) (hwq : ∀ x ∈ I, iteratedDeriv 2 w x = q x * w x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) (hW : w₁ x₀ * deriv w x₀ - deriv w₁ x₀ * w x₀ ≠ 0) :
    Tendsto (fun x ↦ w₁ x / w x) (map ((↑) : I → ℝ) atBot) (𝓝 0) := by
  obtain ⟨hI', hIc', hf0', hξ', hξt'⟩ := liouvilleGreen_data_comp_neg hI hIc hf0 hξ hξt
  obtain ⟨hw₁', hw₁q'⟩ := contDiffOn_and_iteratedDeriv_comp_neg hw₁ hw₁q
  obtain ⟨hw', hwq'⟩ := contDiffOn_and_iteratedDeriv_comp_neg hw hwq
  have h := (tendsto_div_of_wronskian_ne_zero_atTop hI' hIc' hf0' hξ' hξt' hw₁' hw₁q'
    (isEquivalent_comp_neg hw₁e) hw' hwq' (x₀ := -x₀) (by simpa using hx₀) ?_).comp
    (tendsto_neg_map_val_atBot I)
  · simpa [Function.comp_def] using h
  · -- the Wronskian of the reflected solutions is `-W`
    simp only [deriv_comp_neg, neg_neg]
    intro h0
    exact hW (by linear_combination -h0)

/-- **Uniqueness of the recessive solution at the left end.** Let `I = (a₁, a₂)` be an open
interval, let `f > 0` on `I`, let `ξ` be a primitive of `f^{1/2}` there with `ξ(x) → -∞` as
`x → a₁+`, and let `q` be continuous on `I`. Two solutions of `w'' = q w`, `C²` on `I`, that are
both `∼ f^{-1/4} e^{ξ}` as `x → a₁+` agree on `I`. -/
theorem eqOn_of_isEquivalent_liouvilleGreen_atBot (hI : IsOpen I) (hIc : I.OrdConnected)
    (hf0 : ∀ x ∈ I, 0 < f x) (hξ : ∀ x ∈ I, HasDerivAt ξ (√(f x)) x)
    (hξt : Tendsto ξ (map ((↑) : I → ℝ) atBot) atBot) (hq : ContinuousOn q I)
    (hw₁ : ContDiffOn ℝ 2 w₁ I) (hw₁q : ∀ x ∈ I, iteratedDeriv 2 w₁ x = q x * w₁ x)
    (hw₁e : w₁ ~[map ((↑) : I → ℝ) atBot]
      fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (ξ x) : ℝ) : ℂ))
    (hw : ContDiffOn ℝ 2 w I) (hwq : ∀ x ∈ I, iteratedDeriv 2 w x = q x * w x)
    (hwe : w ~[map ((↑) : I → ℝ) atBot]
      fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (ξ x) : ℝ) : ℂ)) :
    EqOn w w₁ I := by
  obtain ⟨hI', hIc', hf0', hξ', hξt'⟩ := liouvilleGreen_data_comp_neg hI hIc hf0 hξ hξt
  obtain ⟨hw₁', hw₁q'⟩ := contDiffOn_and_iteratedDeriv_comp_neg hw₁ hw₁q
  obtain ⟨hw', hwq'⟩ := contDiffOn_and_iteratedDeriv_comp_neg hw hwq
  have h := eqOn_of_isEquivalent_liouvilleGreen_atTop hI' hIc' hf0' hξ' hξt'
    (hq.comp continuous_neg.continuousOn fun _ ht ↦ ht) hw₁' hw₁q' (isEquivalent_comp_neg hw₁e)
    hw' hwq' (isEquivalent_comp_neg hwe)
  intro x hx
  simpa using h (x := -x) (by simpa using hx)

/-- **Dominant solutions at the left end.** Let `I = (a₁, a₂)` be an open interval, let `f > 0`
on `I`, let `ξ` be a primitive of `f^{1/2}` there with `ξ(x) → -∞` as `x → a₁+`, let `q` be
continuous on `I`, and let `w₁` be a solution of `w'' = q w`, `C²` on `I`, with
`w₁ ∼ f^{-1/4} e^{ξ}` as `x → a₁+`. Then there is a solution `w₄`, `C²` on `I`, with
`w₄ ∼ f^{-1/4} e^{-ξ}` and `w₁ / w₄ → 0` as `x → a₁+` (DLMF 2.7.30). -/
theorem exists_liouvilleGreen_dominant_atBot (hI : IsOpen I) (hIc : I.OrdConnected)
    (hf0 : ∀ x ∈ I, 0 < f x) (hξ : ∀ x ∈ I, HasDerivAt ξ (√(f x)) x)
    (hξt : Tendsto ξ (map ((↑) : I → ℝ) atBot) atBot) (hq : ContinuousOn q I)
    (hw₁ : ContDiffOn ℝ 2 w₁ I) (hw₁q : ∀ x ∈ I, iteratedDeriv 2 w₁ x = q x * w₁ x)
    (hw₁e : w₁ ~[map ((↑) : I → ℝ) atBot]
      fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (ξ x) : ℝ) : ℂ)) :
    ∃ w₄ : ℝ → ℂ, ContDiffOn ℝ 2 w₄ I ∧ (∀ x ∈ I, iteratedDeriv 2 w₄ x = q x * w₄ x) ∧
      (w₄ ~[map ((↑) : I → ℝ) atBot] fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) : ℝ) : ℂ)) ∧
      Tendsto (fun x ↦ w₁ x / w₄ x) (map ((↑) : I → ℝ) atBot) (𝓝 0) := by
  obtain ⟨hI', hIc', hf0', hξ', hξt'⟩ := liouvilleGreen_data_comp_neg hI hIc hf0 hξ hξt
  obtain ⟨hw₁', hw₁q'⟩ := contDiffOn_and_iteratedDeriv_comp_neg hw₁ hw₁q
  obtain ⟨w₃, hw₃, hw₃q, hw₃e, hw₃t⟩ := exists_liouvilleGreen_dominant_atTop hI' hIc' hf0' hξ' hξt'
    (hq.comp continuous_neg.continuousOn fun _ ht ↦ ht) hw₁' hw₁q' (isEquivalent_comp_neg hw₁e)
  -- the reflection `w₄(x) = w₃(-x)` of the dominant solution at `(-a₁)-`
  have hmaps : MapsTo Neg.neg I (Neg.neg ⁻¹' I) := fun x hx ↦ by simpa using hx
  refine ⟨fun x ↦ w₃ (-x), hw₃.comp contDiff_neg.contDiffOn hmaps, fun x hx ↦ ?_, ?_, ?_⟩
  · simpa using (contDiffOn_and_iteratedDeriv_comp_neg hw₃ hw₃q).2 x (by simpa using hx)
  · exact (hw₃e.comp_tendsto (tendsto_neg_map_val_atBot I)).congr_right
      (.of_forall fun x ↦ by simp only [Function.comp_apply, neg_neg])
  · simpa [Function.comp_def] using hw₃t.comp (tendsto_neg_map_val_atBot I)

/-- **The Liouville–Green solution is asymptotic to its approximant at the left end.** Under the
hypotheses of the Liouville–Green theorem `TauCeti.exists_liouvilleGreen_left` on an open
interval `I = (a₁, a₂)` (`f` positive and `C²`, `g` continuous, `ξ` a primitive of `f^{1/2}`
on `I`, and `Φ` integrable on `(a₁, x)` for every `x ∈ I`), the equation `w'' = (f + g) w` has
a solution `w`, `C²` on `I`, with `w ∼ f^{-1/4} e^{ξ}` as `x → a₁+` (DLMF 2.7.26). -/
theorem exists_liouvilleGreen_isEquivalent_atBot {g Φ : ℝ → ℂ} (hI : IsOpen I)
    (hIc : I.OrdConnected) (hf : ContDiffOn ℝ 2 f I) (hf0 : ∀ x ∈ I, 0 < f x)
    (hg : ContinuousOn g I) (hξ : ∀ x ∈ I, HasDerivAt ξ (√(f x)) x)
    (hΦ : ∀ x ∈ I, Φ x = ↑(f x ^ (-(1 / 4) : ℝ) *
      iteratedDeriv 2 (fun t ↦ f t ^ (-(1 / 4) : ℝ)) x) - g x / ↑√(f x))
    (hΦi : ∀ x ∈ I, IntegrableOn Φ (Iio x ∩ I)) :
    ∃ w : ℝ → ℂ, ContDiffOn ℝ 2 w I ∧ (∀ x ∈ I, iteratedDeriv 2 w x = (f x + g x) * w x) ∧
      w ~[map ((↑) : I → ℝ) atBot] fun x ↦ ((f x ^ (-(1 / 4) : ℝ) * Real.exp (ξ x) : ℝ) : ℂ) := by
  obtain ⟨w, ε, hw, -, hwε⟩ := exists_liouvilleGreen_left hI hIc hf hf0 hg hξ hΦ hΦi
  exact ⟨w, hw, fun x hx ↦ (hwε x hx).1, isEquivalent_approximant_of_tendsto
    (eventually_mem_map_val atBot) hf0 (fun x hx ↦ ⟨(hwε x hx).2.1, (hwε x hx).2.2.1⟩)
    (tendsto_setIntegral_Iio_inter_map_val_atBot hIc fun x hx ↦ (hΦi x hx).norm)⟩

end TauCeti
