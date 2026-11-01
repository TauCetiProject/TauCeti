/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Wronskian
public import TauCeti.AlgebraicGeometry.EllipticCurve.RealPeriod
-- Proof-only: the quotient rule, and the derivative of a polynomial function.
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# The real period under an isogeny

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over `ℝ`, with `x ∘ φ = r(x)` for
`r = N / D = φ.xRatFunc`, pulling the invariant differential back as `φ^*ω₂ = c ω₁`. Over `ℝ` every
isogeny is separable, so `c ≠ 0`. This file shows that `|c|` times the real period integral of
`W₁` is the integral of `dx' / √Ψ₂Sq₂(x')` over `Ψ₂Sq₂(x') > 0`, weighted by the number of `x` with
`Ψ₂Sq₁(x) > 0` and `r(x) = x'`; when almost every such fibre has `n` elements,
`|c| Ω(W₁) = n Ω(W₂)`.

This is the substitution theorem
`WeierstrassCurve.ofReal_abs_mul_realPeriodLIntegral_eq_setLIntegral_encard` applied to the
substitution `x' = r(x)`. Its two hypotheses, `r' = c s` and `Ψ₂Sq₂(r) = s² Ψ₂Sq₁`, hold off the
finitely many zeros of `D` and of the Wronskian `w = D N' - D' N`, with `s = w / (c D²)`: the first
is the quotient rule, the second is `TauCeti.Isogeny.eval_wronskian_xRatFunc_sq_mul_eval_Ψ₂Sq`.

## Main results

* `TauCeti.Isogeny.ofReal_abs_mul_realPeriodLIntegral_eq_setLIntegral_encard`: the fibre-counted
  transformation formula for the real period integral under an isogeny.
* `TauCeti.Isogeny.abs_mul_realPeriod_eq_of_ae_encard_eq`: `|c| Ω(W₁) = n Ω(W₂)` when almost every
  fibre has `n` elements.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and III.5.
-/

public section

open MeasureTheory Polynomial Set WeierstrassCurve.Affine
open scoped ENNReal

namespace TauCeti.Isogeny

variable {W₁ W₂ : WeierstrassCurve.Affine ℝ} [W₁.IsElliptic] [W₂.IsElliptic]

/-- The exceptional set where the substitution theorem's hypotheses may fail: the zeros of `D` and
of the Wronskian, finitely many since both are nonzero polynomials. -/
private theorem countable_exceptional (φ : Isogeny W₁ W₂) {c : ℝ}
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁) :
    ({x | φ.xRatFunc.denom.IsRoot x} ∪
      {x | (wronskian φ.xRatFunc.denom φ.xRatFunc.num).IsRoot x}).Countable :=
  ((finite_setOfPred_isRoot φ.xRatFunc.denom_ne_zero).union (finite_setOfPred_isRoot
    (wronskian_xRatFunc_ne_zero hc
      (ne_zero_of_pullbackDifferential_eq_smul φ hc)))).countable

/-- The odd part `s = w / (c D²)` of `φ`, as a function on `ℝ`. -/
private noncomputable def oddPart (φ : Isogeny W₁ W₂) (c x : ℝ) : ℝ :=
  (wronskian φ.xRatFunc.denom φ.xRatFunc.num).eval x / (c * φ.xRatFunc.denom.eval x ^ 2)

/-- The hypotheses of the substitution theorem, off the zeros of `D` and of the Wronskian. -/
private theorem substitution_hypotheses (φ : Isogeny W₁ W₂) {c : ℝ}
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁)
    {x : ℝ} (hD : φ.xRatFunc.denom.eval x ≠ 0)
    (hw : (wronskian φ.xRatFunc.denom φ.xRatFunc.num).eval x ≠ 0) :
    HasDerivAt (fun x ↦ φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x) (c * oddPart φ c x) x ∧
      oddPart φ c x ≠ 0 ∧
      W₂.Ψ₂Sq.eval (φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x) =
        oddPart φ c x ^ 2 * W₁.Ψ₂Sq.eval x := by
  have hc0 := ne_zero_of_pullbackDifferential_eq_smul φ hc
  refine ⟨?_, div_ne_zero hw (mul_ne_zero hc0 (pow_ne_zero 2 hD)), ?_⟩
  · convert HasDerivAt.div (φ.xRatFunc.num.hasDerivAt x) (φ.xRatFunc.denom.hasDerivAt x) hD
      using 1
    rw [oddPart, wronskian]
    simp only [eval_sub, eval_mul]
    field_simp
  · rw [oddPart, div_pow, div_mul_eq_mul_div,
      eval_wronskian_xRatFunc_sq_mul_eval_Ψ₂Sq hc hD]
    field_simp

/-- **The real period integral under an isogeny, counting fibres.** Let `φ : W₁ → W₂` be an
isogeny over `ℝ` with `φ^*ω₂ = c ω₁` and `x ∘ φ = r(x)`, where `r = N / D = φ.xRatFunc`. Then
`|c|` times the real period integral of `W₁` is the integral over `Ψ₂Sq₂(x') > 0` of
`dx' / √Ψ₂Sq₂(x')`, weighted by the number of `x` with `Ψ₂Sq₁(x) > 0` and `N(x) / D(x) = x'`. -/
theorem ofReal_abs_mul_realPeriodLIntegral_eq_setLIntegral_encard (φ : Isogeny W₁ W₂) {c : ℝ}
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁) :
    ENNReal.ofReal |c| * W₁.realPeriodLIntegral =
      ∫⁻ y in {y | 0 < W₂.Ψ₂Sq.eval y},
        ({x | 0 < W₁.Ψ₂Sq.eval x} ∩
            (fun x ↦ φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x) ⁻¹' {y}).encard *
          ENNReal.ofReal (√(W₂.Ψ₂Sq.eval y))⁻¹ := by
  refine W₁.ofReal_abs_mul_realPeriodLIntegral_eq_setLIntegral_encard
    (ne_zero_of_pullbackDifferential_eq_smul φ hc) (countable_exceptional φ hc)
    (s := oddPart φ c)
    (fun x _ hx ↦ ?_) (fun x _ hx ↦ ?_) (fun x _ hx ↦ ?_) <;>
  · simp only [mem_union, mem_ofPred_eq, IsRoot.def, not_or] at hx
    have := substitution_hypotheses φ hc hx.1 hx.2
    tauto

/-- **The real period under an isogeny with constant fibre count.** Let `φ : W₁ → W₂` be an
isogeny over `ℝ` with `φ^*ω₂ = c ω₁` and `x ∘ φ = r(x)`, where `r = N / D = φ.xRatFunc`. If
almost every `x'` with `Ψ₂Sq₂(x') > 0` is `N(x) / D(x)` for exactly `n` values `x` with
`Ψ₂Sq₁(x) > 0`, then `|c| Ω(W₁) = n Ω(W₂)`. -/
theorem abs_mul_realPeriod_eq_of_ae_encard_eq (φ : Isogeny W₁ W₂) {c : ℝ}
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁)
    {n : ℕ} (hn : ∀ᵐ y, 0 < W₂.Ψ₂Sq.eval y → ({x | 0 < W₁.Ψ₂Sq.eval x} ∩
      (fun x ↦ φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x) ⁻¹' {y}).encard = n) :
    |c| * W₁.realPeriod = n * W₂.realPeriod := by
  refine W₁.abs_mul_realPeriod_eq_of_ae_encard_eq (ne_zero_of_pullbackDifferential_eq_smul φ hc)
    (countable_exceptional φ hc)
    (s := oddPart φ c)
    (fun x _ hx ↦ ?_) (fun x _ hx ↦ ?_) (fun x _ hx ↦ ?_) hn <;>
  · simp only [mem_union, mem_ofPred_eq, IsRoot.def, not_or] at hx
    have := substitution_hypotheses φ hc hx.1 hx.2
    tauto

end TauCeti.Isogeny
