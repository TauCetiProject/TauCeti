/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.DifferentialSymbol
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

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
nevertheless gives `Op(ξ² + i ξ) = -∂ₓ² + ∂ₓ` (`TauCeti.quantizeSchwartzValue_sq_mul_sq_comp_exp`),
which differs from `Op(ξ²) = -∂ₓ²` by the first-order operator `∂ₓ`
(`TauCeti.quantizeSchwartzValue_sq_mul_sq_comp_exp_sub`), not by an operator of order `-∞`. On a
function equal to `x` near `0` the two operators take the values `1` and `0` at `0`
(`TauCeti.exists_quantizeSchwartzValue_sq_mul_sq_comp_exp_eq_one`). So local quantizations in two
overlapping charts that share the principal symbol only agree modulo lower order: an operator on a
manifold patched from local quantizations is independent of the atlas modulo order `-∞` only when
its local full symbols are related by the complete transformation formula, not merely through
their principal symbols.

## Main results

* `TauCeti.quantizeSchwartzValue_mul_sq_comp_eq`: the full symbol of `a(y) D_y²` in the
  coordinate `x`, for `y = κ(x)` with `κ'(x) ≠ 0`.
* `TauCeti.quantizeSchwartzValue_sq_mul_sq_comp_exp`: for `y = eˣ`, `y² D_y²` becomes
  `Op(ξ² + i ξ) = -∂ₓ² + ∂ₓ`.
* `TauCeti.quantizeSchwartzValue_sq_mul_sq_comp_exp_sub`: its difference with `Op(ξ²) = -∂ₓ²`
  is `∂ₓ`.
* `TauCeti.exists_quantizeSchwartzValue_sq_mul_sq_comp_exp_eq_one`: on a function equal to `x`
  near `0`, the two operators take the values `1` and `0` at `0`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8,
  (8.1)–(8.3) (the transformation of symbols under changes of coordinates).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  Theorem 18.1.17 (invariance of pseudodifferential operators under changes of coordinates).
-/

public section

noncomputable section

open Complex Filter Metric Set
open scoped SchwartzMap Topology ContDiff

namespace TauCeti

/-- The quantization of the second-order symbol `c₂(x) ξ² + c₁(x) i ξ` on `ℝ` is the
differential operator `-c₂ ∂² + c₁ ∂`. -/
private theorem quantizeSchwartzValue_mul_sq_add_mul_I_mul (c₂ c₁ : ℝ → ℂ) (u : 𝓢(ℝ, ℂ))
    (x : ℝ) :
    quantizeSchwartzValue
      (fun p : ℝ × ℝ ↦ (c₂ p.1 * (p.2 : ℂ) ^ 2 + c₁ p.1 * (I * p.2)) • (1 : ℂ →L[ℂ] ℂ)) u x =
      -c₂ x * deriv (deriv u) x + c₁ x * deriv u x := by
  have hsym : (fun p : ℝ × ℝ ↦ (c₂ p.1 * (p.2 : ℂ) ^ 2 + c₁ p.1 * (I * p.2)) •
      (1 : ℂ →L[ℂ] ℂ)) = differentialSymbol (ι := Fin 2) (k := ![2, 1]) Finset.univ
      (fun _ _ ↦ (1 : ℝ))
      ![fun y ↦ (-c₂ y) • (1 : ℂ →L[ℂ] ℂ), fun y ↦ c₁ y • (1 : ℂ →L[ℂ] ℂ)] := by
    funext p
    simp [differentialSymbol_def, Fin.sum_univ_two, smul_smul, ← add_smul, mul_pow,
      Finset.card_univ]
    congr 1
    ring_nf
  rw [hsym, quantizeSchwartzValue_differentialSymbol_eq_sum_iteratedFDeriv]
  simp [Fin.sum_univ_two, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedDeriv_succ]

/-- **The full symbol of a second-order operator after a change of coordinates.** Let `κ` be a
function on `ℝ`, `C²` near `x` with `κ'(x) ≠ 0`, and let `u = g ∘ κ` for Schwartz functions `u`
and `g`. Then the operator `a(y) D_y²`, of left symbol `a(y) η²`, applied to `g` at `κ x`, is
the operator of left symbol `c₂ ξ² + c₁ i ξ` applied to `u` at `x`, with `c₂ = a(κ x) / κ'(x)²`
and `c₁ = a(κ x) κ''(x) / κ'(x)³`. The first term is the transformed principal symbol
`a(κ x) (ξ / κ'(x))²`; the second is a first-order correction. -/
theorem quantizeSchwartzValue_mul_sq_comp_eq (a : ℝ → ℂ) {κ : ℝ → ℝ} {g u : 𝓢(ℝ, ℂ)}
    (hu : ∀ x, u x = g (κ x)) {x : ℝ} (hκ : ContDiffAt ℝ 2 κ x) (hx : deriv κ x ≠ 0) :
    quantizeSchwartzValue (fun p : ℝ × ℝ ↦ (a p.1 * (p.2 : ℂ) ^ 2) • (1 : ℂ →L[ℂ] ℂ)) g (κ x) =
      quantizeSchwartzValue (fun p : ℝ × ℝ ↦
        (a (κ p.1) / ((deriv κ p.1 : ℝ) : ℂ) ^ 2 * (p.2 : ℂ) ^ 2 +
          a (κ p.1) * ((deriv (deriv κ) p.1 : ℝ) : ℂ) / ((deriv κ p.1 : ℝ) : ℂ) ^ 3 * (I * p.2)) •
          (1 : ℂ →L[ℂ] ℂ)) u x := by
  have hl := quantizeSchwartzValue_mul_sq_add_mul_I_mul a 0 g (κ x)
  simp only [Pi.zero_apply, zero_mul, add_zero] at hl
  rw [hl, quantizeSchwartzValue_mul_sq_add_mul_I_mul
    (fun y ↦ a (κ y) / ((deriv κ y : ℝ) : ℂ) ^ 2)
    (fun y ↦ a (κ y) * ((deriv (deriv κ) y : ℝ) : ℂ) / ((deriv κ y : ℝ) : ℂ) ^ 3)]
  -- The chain rule for `u = g ∘ κ`, once and twice.
  have hu₀ : (u : ℝ → ℂ) = g ∘ κ := funext hu
  have hu' : deriv u x = deriv κ x • deriv g (κ x) := by
    rw [hu₀, deriv.scomp x g.differentiableAt (hκ.differentiableAt (by norm_num))]
  have hu'' : deriv (deriv u) x =
      deriv κ x ^ 2 • deriv (deriv g) (κ x) + deriv (deriv κ) x • deriv g (κ x) := by
    have h := iteratedDeriv_scomp_two (g.smooth 2).contDiffAt hκ
    simpa [iteratedDeriv_succ, ← hu₀] using h
  rw [hu', hu'']
  simp only [Complex.real_smul, ofReal_pow]
  have hx' : ((deriv κ x : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hx
  field_simp
  ring

/-- **The coordinate change `y = eˣ`.** The operator `y² D_y² = -y² ∂_y²`, of left symbol `y² η²`,
read in the coordinate `x` with `y = eˣ`, is the operator `-∂ₓ² + ∂ₓ` of left symbol `ξ² + i ξ`,
although its principal symbol `e^{2x} (ξ / eˣ)² = ξ²` is that of `-∂ₓ²`. Here `u = g ∘ exp`. -/
theorem quantizeSchwartzValue_sq_mul_sq_comp_exp {g u : 𝓢(ℝ, ℂ)}
    (hu : ∀ x, u x = g (Real.exp x)) (x : ℝ) :
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

/-- **Equal principal symbols, a first-order difference.** For `y = eˣ` and `u = g ∘ exp`, the
operator `y² D_y²` read in the coordinate `x` minus the operator `D_x² = -∂ₓ²`, of the same
principal symbol `ξ²`, is the first-order operator `∂ₓ`. -/
theorem quantizeSchwartzValue_sq_mul_sq_comp_exp_sub {g u : 𝓢(ℝ, ℂ)}
    (hu : ∀ x, u x = g (Real.exp x)) (x : ℝ) :
    quantizeSchwartzValue (fun p : ℝ × ℝ ↦ ((p.1 : ℂ) ^ 2 * (p.2 : ℂ) ^ 2) • (1 : ℂ →L[ℂ] ℂ)) g
        (Real.exp x) -
      quantizeSchwartzValue (fun p : ℝ × ℝ ↦ ((p.2 : ℂ) ^ 2) • (1 : ℂ →L[ℂ] ℂ)) u x =
      deriv u x := by
  rw [quantizeSchwartzValue_sq_mul_sq_comp_exp hu]
  have h₁ := quantizeSchwartzValue_mul_sq_add_mul_I_mul 1 1 u x
  have h₀ := quantizeSchwartzValue_mul_sq_add_mul_I_mul 1 0 u x
  simp only [Pi.one_apply, Pi.zero_apply, one_mul, zero_mul, add_zero] at h₁ h₀
  rw [h₁, h₀]
  ring

/-- A Schwartz function `u = g ∘ exp`, for a Schwartz function `g`, equal to `x` near `0`: take
`g = ψ log` for a bump `ψ` equal to `1` near `1` and supported in `(1/2, 3/2)`, so that
`u(x) = ψ(eˣ) x`. -/
private theorem exists_comp_exp_eventuallyEq_ofReal :
    ∃ g u : 𝓢(ℝ, ℂ), (∀ x, u x = g (Real.exp x)) ∧ (u : ℝ → ℂ) =ᶠ[𝓝 0] fun x ↦ (x : ℂ) := by
  let ψ : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have hψ₀ {y : ℝ} (hy : 1 / 2 ≤ dist y 1) : ψ y = 0 := ψ.zero_of_le_dist hy
  let g₀ : ℝ → ℂ := fun y ↦ ((ψ y * Real.log y : ℝ) : ℂ)
  -- `g₀` is smooth: it is `ψ log` on `(0, ∞)` and vanishes on `(-∞, 1/2)`.
  have hg₀ : ContDiff ℝ ∞ g₀ := by
    refine contDiff_iff_contDiffAt.2 fun y ↦ ?_
    rcases lt_or_ge 0 y with hy | hy
    · exact ofRealCLM.contDiff.contDiffAt.comp y
        (ψ.contDiff.contDiffAt.mul (Real.contDiffAt_log.2 hy.ne'))
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds (show y < 1 / 2 by linarith)] with z hz
      have hz' : z < 1 / 2 := hz
      have : ψ z = 0 := hψ₀ (by rw [Real.dist_eq, abs_of_neg (by linarith)]; linarith)
      simp [g₀, this]
  have hg₀c : HasCompactSupport g₀ := by
    refine HasCompactSupport.intro (isCompact_closedBall (1 : ℝ) (1 / 2)) fun y hy ↦ ?_
    simp [g₀, hψ₀ (le_of_lt (not_le.1 (mt mem_closedBall.2 hy)))]
  let u₀ : ℝ → ℂ := fun x ↦ ((ψ (Real.exp x) * x : ℝ) : ℂ)
  have hu₀ : ContDiff ℝ ∞ u₀ :=
    ofRealCLM.contDiff.comp ((ψ.contDiff.comp Real.contDiff_exp).mul contDiff_id)
  -- `u₀` vanishes unless `1/2 < eˣ < 3/2`.
  have hu₀c : HasCompactSupport u₀ := by
    refine HasCompactSupport.intro (isCompact_Icc (a := Real.log (1 / 2)) (b := Real.log (3 / 2)))
      fun x hx ↦ ?_
    suffices ψ (Real.exp x) = 0 by simp [u₀, this]
    refine hψ₀ ?_
    rw [Real.dist_eq]
    rcases not_and_or.1 hx with hx | hx
    · have := Real.exp_lt_exp.2 (not_le.1 hx)
      rw [Real.exp_log (by norm_num)] at this
      rw [abs_of_neg (by linarith)]
      linarith
    · have := Real.exp_lt_exp.2 (not_le.1 hx)
      rw [Real.exp_log (by norm_num)] at this
      rw [abs_of_pos (by linarith)]
      linarith
  refine ⟨hg₀c.toSchwartzMap hg₀, hu₀c.toSchwartzMap hu₀, fun x ↦ ?_, ?_⟩
  · simp [u₀, g₀, Real.log_exp]
  -- Near `0`, `eˣ` is within `1/4` of `1`, where `ψ = 1`, so `u₀ = x`.
  have h := Real.continuous_exp.tendsto 0
  rw [Real.exp_zero] at h
  filter_upwards [h (closedBall_mem_nhds (1 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4))] with x hx
  simp [u₀, ψ.one_of_mem_closedBall hx]

/-- **The check on `x`.** There are Schwartz functions `g` and `u = g ∘ exp`, with `u` equal to `x`
near `0`, such that the operator `y² D_y²` read in the coordinate `x`, with `y = eˣ`, sends `u` to
a function with value `1` at `0`, whereas `D_x² = -∂ₓ²`, of the same principal symbol, sends `u`
to a function with value `0` at `0`. So the two operators do not differ by an operator of order
`-∞`, although their principal symbols agree. -/
theorem exists_quantizeSchwartzValue_sq_mul_sq_comp_exp_eq_one :
    ∃ g u : 𝓢(ℝ, ℂ), (∀ x, u x = g (Real.exp x)) ∧ (∀ᶠ x in 𝓝 0, u x = x) ∧
      quantizeSchwartzValue (fun p : ℝ × ℝ ↦ ((p.1 : ℂ) ^ 2 * (p.2 : ℂ) ^ 2) • (1 : ℂ →L[ℂ] ℂ))
        g 1 = 1 ∧
      quantizeSchwartzValue (fun p : ℝ × ℝ ↦ ((p.2 : ℂ) ^ 2) • (1 : ℂ →L[ℂ] ℂ)) u 0 = 0 := by
  obtain ⟨g, u, hcomp, hux⟩ := exists_comp_exp_eventuallyEq_ofReal
  have hid : deriv (fun x : ℝ ↦ (x : ℂ)) = fun _ ↦ 1 :=
    funext fun x ↦ ((hasDerivAt_id x).ofReal_comp).deriv
  have hd : deriv u 0 = 1 := by rw [hux.deriv_eq, hid]
  have hdd : deriv (deriv u) 0 = 0 := by rw [hux.deriv.deriv_eq, hid, deriv_const]
  refine ⟨g, u, hcomp, hux, ?_, ?_⟩
  · rw [← Real.exp_zero, quantizeSchwartzValue_sq_mul_sq_comp_exp hcomp]
    have h := quantizeSchwartzValue_mul_sq_add_mul_I_mul 1 1 u 0
    simp only [Pi.one_apply, one_mul] at h
    rw [h, hd, hdd]
    ring
  · have h := quantizeSchwartzValue_mul_sq_add_mul_I_mul 1 0 u 0
    simp only [Pi.one_apply, Pi.zero_apply, one_mul, zero_mul, add_zero] at h
    rw [h, hdd]
    ring

end TauCeti
