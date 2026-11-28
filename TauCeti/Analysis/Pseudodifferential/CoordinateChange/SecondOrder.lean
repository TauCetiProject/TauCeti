/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.DifferentialSymbol
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-!
# Changes of coordinates of second-order operators on the line

Under a change of coordinates `y = κ(x)` a pseudodifferential operator of order `m` stays one of
order `m`, and its principal symbol transforms as a function on the cotangent bundle,
`σ(x, ξ) = σ(κ x, ξ / κ'(x))` (`TauCeti.ClassicalSymbol.exists_smul_quantizeSchwartzValue_comp_eq`
in `TauCeti.Analysis.Pseudodifferential.CoordinateChange.Chart`). The lower-order terms of the
full symbol do not transform in this way. This file computes the full symbol after a change of
coordinates for the second-order operators `a(y) D_y²` on `ℝ`, `D_y = -i ∂_y`, of left symbol
`a(y) η²`. By the chain rule, `u = g ∘ κ` has `u'' = κ'² (g'' ∘ κ) + κ'' (g' ∘ κ)`, so

`Op(a(y) η²) g (κ x) = Op(c₂(x) ξ² + c₁(x) i ξ) u (x)`,

with `c₂ = (a ∘ κ) / κ'²` and `c₁ = (a ∘ κ) κ'' / κ'³`
(`TauCeti.quantizeSchwartzValue_mul_sq_comp_eq`). The term `c₂ ξ²` is the transformed principal
symbol; the first-order term `c₁ i ξ` vanishes only where `κ'' = 0` or `a ∘ κ = 0`.

For `y = eˣ` and `a(y) = y²`, the principal symbol `y² η²` becomes `e^{2x} (ξ / eˣ)² = ξ²`, the
symbol of `D_x²`. Quantizing `y² η²` in the coordinate `y` and reading the result in `x`
nevertheless gives `Op(ξ² + i ξ) = -∂ₓ² + ∂ₓ` (`TauCeti.quantizeSchwartzValue_sq_mul_sq_comp_exp`).
This is the quantized form of the acceptance check
`TauCeti.GlobalQuantizationExample.neg_exp_sq_mul_deriv_deriv_eq` in
`TauCeti.Examples.Analysis.Pseudodifferential.GlobalQuantization`, which also evaluates both
operators on `f(x) = x` and shows that the first-order difference `i ξ` is not smoothing.

## Main results

* `TauCeti.quantizeSchwartzValue_mul_sq_comp_eq`: the full symbol of `a(y) D_y²` in the
  coordinate `x`, for `y = κ(x)` with `κ'(x) ≠ 0`.
* `TauCeti.quantizeSchwartzValue_sq_mul_sq_comp_exp`: for `y = eˣ`, `y² D_y²` becomes
  `Op(ξ² + i ξ) = -∂ₓ² + ∂ₓ`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8,
  (8.1)–(8.3) (the transformation of symbols under changes of coordinates).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  Theorem 18.1.17 (invariance of pseudodifferential operators under changes of coordinates).
-/

public section

noncomputable section

open Complex Filter
open scoped SchwartzMap Topology

namespace TauCeti

/-- **The full symbol of a second-order operator after a change of coordinates.** Let `κ` be a
function on `ℝ`, `C²` near `x` with `κ'(x) ≠ 0`, and let `u = g ∘ κ` near `x` for Schwartz
functions `u` and `g`. Then the operator `a(y) D_y²`, of left symbol `a(y) η²`, applied to `g` at
`κ x`, is the operator of left symbol `c₂ ξ² + c₁ i ξ` applied to `u` at `x`, with
`c₂ = a(κ x) / κ'(x)²` and `c₁ = a(κ x) κ''(x) / κ'(x)³`. The first term is the transformed
principal symbol `a(κ x) (ξ / κ'(x))²`; the second is a first-order correction. -/
theorem quantizeSchwartzValue_mul_sq_comp_eq (a : ℝ → ℂ) {κ : ℝ → ℝ} {g u : 𝓢(ℝ, ℂ)} {x : ℝ}
    (hu : (u : ℝ → ℂ) =ᶠ[𝓝 x] g ∘ κ) (hκ : ContDiffAt ℝ 2 κ x) (hx : deriv κ x ≠ 0) :
    quantizeSchwartzValue (fun p : ℝ × ℝ ↦ (a p.1 * (p.2 : ℂ) ^ 2) • (1 : ℂ →L[ℂ] ℂ)) g (κ x) =
      quantizeSchwartzValue (fun p : ℝ × ℝ ↦
        (a (κ p.1) / ((deriv κ p.1 : ℝ) : ℂ) ^ 2 * (p.2 : ℂ) ^ 2 +
          a (κ p.1) * ((deriv (deriv κ) p.1 : ℝ) : ℂ) / ((deriv κ p.1 : ℝ) : ℂ) ^ 3 * (I * p.2)) •
          (1 : ℂ →L[ℂ] ℂ)) u x := by
  rw [quantizeSchwartzValue_mul_sq, quantizeSchwartzValue_mul_sq_add_mul_I_mul
    (fun y ↦ a (κ y) / ((deriv κ y : ℝ) : ℂ) ^ 2)
    (fun y ↦ a (κ y) * ((deriv (deriv κ) y : ℝ) : ℂ) / ((deriv κ y : ℝ) : ℂ) ^ 3)]
  -- The chain rule for `u = g ∘ κ` near `x`, once and twice.
  have hu' : deriv u x = deriv κ x • deriv g (κ x) := by
    rw [hu.deriv_eq, deriv.scomp x g.differentiableAt (hκ.differentiableAt (by norm_num))]
  have hu'' : deriv (deriv u) x =
      deriv κ x ^ 2 • deriv (deriv g) (κ x) + deriv (deriv κ) x • deriv g (κ x) := by
    have h := iteratedDeriv_scomp_two (g.smooth 2).contDiffAt hκ
    simpa [iteratedDeriv_succ, ← hu.deriv.deriv_eq] using h
  rw [hu', hu'']
  simp only [Complex.real_smul, ofReal_pow]
  have hx' : ((deriv κ x : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hx
  field_simp
  ring

/-- **The coordinate change `y = eˣ`.** The operator `y² D_y² = -y² ∂_y²`, of left symbol `y² η²`,
read in the coordinate `x` with `y = eˣ`, is the operator `-∂ₓ² + ∂ₓ` of left symbol `ξ² + i ξ`,
although its principal symbol `e^{2x} (ξ / eˣ)² = ξ²` is that of `-∂ₓ²`. Here `u = g ∘ exp`
near `x`. -/
theorem quantizeSchwartzValue_sq_mul_sq_comp_exp {g u : 𝓢(ℝ, ℂ)} {x : ℝ}
    (hu : (u : ℝ → ℂ) =ᶠ[𝓝 x] g ∘ Real.exp) :
    quantizeSchwartzValue (fun p : ℝ × ℝ ↦ ((p.1 : ℂ) ^ 2 * (p.2 : ℂ) ^ 2) • (1 : ℂ →L[ℂ] ℂ)) g
        (Real.exp x) =
      quantizeSchwartzValue (fun p : ℝ × ℝ ↦ ((p.2 : ℂ) ^ 2 + I * p.2) • (1 : ℂ →L[ℂ] ℂ)) u x := by
  rw [quantizeSchwartzValue_mul_sq_comp_eq (fun y ↦ (y : ℂ) ^ 2) hu Real.contDiff_exp.contDiffAt
    (by simp [Real.exp_ne_zero])]
  congr 1
  funext p
  have he : (Real.exp p.1 : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.exp_ne_zero _)
  simp only [Real.deriv_exp]
  congr 1
  field_simp

end TauCeti
