/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Differential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.XRatFunc
public import Mathlib.RingTheory.Polynomial.Wronskian

/-!
# The Wronskian of the `x`-coordinate of an isogeny

Let `φ : W₁ → W₂` be an isogeny of elliptic curves, with `x ∘ φ = r(x)` for the rational function
`r = N / D = φ.xRatFunc` in lowest terms, and suppose that `φ` pulls the invariant differential
`ω₂ = dx / u₂` back to `c ω₁`, where `u = 2y + a₁x + a₃`. Pulling `ω₂` back coordinate by
coordinate gives `φ^*ω₂ = d(r(x)) / φ^*u₂ = r'(x) dx / φ^*u₂`, and comparing with `c dx / u₁`
yields

  `w(x) u₁ = c D(x)² φ^*u₂`,  where  `w = D N' - D' N`

is the **Wronskian** `Polynomial.wronskian D N` of the denominator and numerator, so that
`r' = w / D²`. In the language of Silverman III.4, when `φ` is separable (`c ≠ 0`),
`φ^*u₂ = s(x) u₁` for the odd part `s = w / (c D²)` of `φ`, and the identity says `r' = c s`. For
inseparable `φ` both `c` and `w` vanish, and the identity carries no information about `s`.

Squaring it and using `u² = Ψ₂Sq(x) = 4x³ + b₂x² + 2b₄x + b₆` on both curves turns it into an
identity of polynomials, with no reference to `y`:

  `w² Ψ₂Sq₁ = c² D · D³ Ψ₂Sq₂(N / D)`,

where `D³ Ψ₂Sq₂(N / D) = 4N³ + b₂'N²D + 2b₄'ND² + b₆'D³`. Evaluated at a point where `D` does not
vanish, and when `c ≠ 0`, this is `Ψ₂Sq₂(r(x)) = s(x)² Ψ₂Sq₁(x)` with `s = w / (c D²)`. These are
the two identities by which the real period integral transforms under `x ↦ r(x)`
(`WeierstrassCurve.ofReal_abs_mul_realPeriodLIntegral_eq_setLIntegral_encard`).

For `φ = [n]` the first identity is
`TauCeti.Isogeny.wronskian_Φ_ΨSq_mul_invariantDifferentialDenom`, there stated with the division
polynomials `Φₙ` and `ΨSqₙ` in place of `N` and `D`.

## Main results

* `TauCeti.Isogeny.aeval_wronskian_xRatFunc_mul_invariantDifferentialDenom`:
  `w(x) u₁ = c D(x)² φ^*u₂` in the function field of `W₁`.
* `TauCeti.Isogeny.wronskian_xRatFunc_ne_zero`: for a separable isogeny (`c ≠ 0`) the Wronskian is
  nonzero.
* `TauCeti.Isogeny.wronskian_xRatFunc_sq_mul_Ψ₂Sq`: the polynomial identity
  `w² Ψ₂Sq₁ = c² D (4N³ + b₂'N²D + 2b₄'ND² + b₆'D³)`.
* `TauCeti.Isogeny.eval_wronskian_xRatFunc_sq_mul_eval_Ψ₂Sq`: its value at a point `x₀` with
  `D(x₀) ≠ 0`, `w(x₀)² Ψ₂Sq₁(x₀) = c² D(x₀)⁴ Ψ₂Sq₂(r(x₀))`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 (the shape
  `φ(x, y) = (r(x), y s(x) + t(x))` of an isogeny) and III.5 (`φ^*ω₂ = c ω₁`).
-/

public section

open Polynomial WeierstrassCurve.Affine

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic]
  [W₂.IsElliptic]

private theorem aeval_denom_ne_zero (φ : Isogeny W₁ W₂) :
    aeval (genericX W₁) φ.xRatFunc.denom ≠ 0 := fun h ↦ φ.xRatFunc.denom_ne_zero <|
  transcendental_iff_injective.mp (transcendental_genericX W₁) (h.trans (map_zero _).symm)

variable {φ : Isogeny W₁ W₂} {c : F}
  (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁)
include hc

/-- **The Wronskian identity of an isogeny**: if `φ^*ω₂ = c ω₁`, then

  `w(x) u₁ = c D(x)² φ^*u₂`,

where `w` is the Wronskian of `φ.xRatFunc = N / D` and `u = 2y + a₁x + a₃` is the denominator of
the invariant differential. -/
-- Proof: `φ^*ω₂ = d(N(x) / D(x)) / φ^*u₂` by the quotient rule is `w(x) / (D(x)² φ^*u₂) dx`, and
-- `c ω₁ = c / u₁ dx`; the common factor `dx` cancels.
theorem aeval_wronskian_xRatFunc_mul_invariantDifferentialDenom :
    aeval (genericX W₁) (wronskian φ.xRatFunc.denom φ.xRatFunc.num) *
        invariantDifferentialDenom W₁ =
      algebraMap F W₁.FunctionField c * aeval (genericX W₁) φ.xRatFunc.denom ^ 2 *
        φ.fieldPullback (invariantDifferentialDenom W₂) := by
  have hD := aeval_denom_ne_zero φ
  have hu : invariantDifferentialDenom W₁ ≠ 0 := invariantDifferentialDenom_ne_zero W₁
  have hpu : φ.fieldPullback (invariantDifferentialDenom W₂) ≠ 0 :=
    (map_ne_zero φ.fieldPullback).2 (invariantDifferentialDenom_ne_zero W₂)
  have hDx : KaehlerDifferential.D F W₁.FunctionField (genericX W₁) ≠ 0 :=
    TauCeti.D_ne_zero_of_separating (transcendental_genericX W₁)
  rw [invariantDifferential_def, invariantDifferential_def, pullbackDifferential_smul,
    pullbackDifferential_D, map_inv₀, fieldPullback_genericX_eq_aeval_div, Derivation.leibniz_div,
    Derivation.map_aeval, Derivation.map_aeval, ← algebraMap_smul W₁.FunctionField c] at hc
  simp only [smul_smul, ← sub_smul] at hc
  have hscal := smul_left_injective W₁.FunctionField hDx hc
  rw [wronskian, map_sub, map_mul, map_mul]
  field_simp at hscal
  linear_combination hscal

/-- **The Wronskian of a separable isogeny is nonzero**: if `φ^*ω₂ = c ω₁` with `c ≠ 0`, then
`D N' - D' N ≠ 0`, so the `x`-coordinate `r = N / D` of `φ` has nonzero derivative. -/
theorem wronskian_xRatFunc_ne_zero (hc0 : c ≠ 0) :
    wronskian φ.xRatFunc.denom φ.xRatFunc.num ≠ 0 := by
  intro h
  have h' := aeval_wronskian_xRatFunc_mul_invariantDifferentialDenom hc
  rw [h, map_zero, zero_mul, eq_comm] at h'
  refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero 2 (aeval_denom_ne_zero φ)))
    ((map_ne_zero φ.fieldPullback).2 (invariantDifferentialDenom_ne_zero W₂)) h'
  exact (map_ne_zero_iff _ (algebraMap F W₁.FunctionField).injective).2 hc0

/-- **The Wronskian identity with `y` eliminated**: if `φ^*ω₂ = c ω₁`, then

  `w² Ψ₂Sq₁ = c² D (4N³ + b₂'N²D + 2b₄'ND² + b₆'D³)`,

an identity of polynomials, for `N / D = φ.xRatFunc` in lowest terms, `w` its Wronskian,
`Ψ₂Sq₁ = 4X³ + b₂X² + 2b₄X + b₆` that of `W₁`, and `b₂', b₄', b₆'` the invariants of `W₂`. The
last factor is `D³ Ψ₂Sq₂(N / D)`. -/
-- Proof: square `aeval_wronskian_xRatFunc_mul_invariantDifferentialDenom`, use `u² = Ψ₂Sq(x)` on
-- both curves, and conclude since `x` is transcendental over `F`.
theorem wronskian_xRatFunc_sq_mul_Ψ₂Sq :
    wronskian φ.xRatFunc.denom φ.xRatFunc.num ^ 2 * W₁.Ψ₂Sq =
      C (c ^ 2) * φ.xRatFunc.denom *
        (C 4 * φ.xRatFunc.num ^ 3 + C W₂.b₂ * φ.xRatFunc.num ^ 2 * φ.xRatFunc.denom +
          C (2 * W₂.b₄) * φ.xRatFunc.num * φ.xRatFunc.denom ^ 2 +
            C W₂.b₆ * φ.xRatFunc.denom ^ 3) := by
  have hD := aeval_denom_ne_zero φ
  have h := congrArg (· ^ 2) (aeval_wronskian_xRatFunc_mul_invariantDifferentialDenom hc)
  simp only [mul_pow, ← map_pow φ.fieldPullback, invariantDifferentialDenom_sq] at h
  rw [← Polynomial.aeval_algHom_apply, fieldPullback_genericX_eq_aeval_div] at h
  refine (transcendental_iff_injective.mp (transcendental_genericX W₁)) ?_
  simp only [WeierstrassCurve.Ψ₂Sq, map_add, map_mul, map_pow, aeval_X, aeval_C] at h ⊢
  field_simp at h
  linear_combination h

/-- **`Ψ₂Sq₂(r(x₀)) = s(x₀)² Ψ₂Sq₁(x₀)`, cleared of denominators**: if `φ^*ω₂ = c ω₁`, then at
every `x₀` where the denominator `D` of `r = φ.xRatFunc` does not vanish,

  `w(x₀)² Ψ₂Sq₁(x₀) = c² D(x₀)⁴ Ψ₂Sq₂(N(x₀) / D(x₀))`.

When `c ≠ 0` (`φ` separable), with `s = w / (c D²)` this is
`Ψ₂Sq₂(r(x₀)) = s(x₀)² Ψ₂Sq₁(x₀)`. -/
theorem eval_wronskian_xRatFunc_sq_mul_eval_Ψ₂Sq {x₀ : F}
    (hx₀ : φ.xRatFunc.denom.eval x₀ ≠ 0) :
    (wronskian φ.xRatFunc.denom φ.xRatFunc.num).eval x₀ ^ 2 * W₁.Ψ₂Sq.eval x₀ =
      c ^ 2 * φ.xRatFunc.denom.eval x₀ ^ 4 *
        W₂.Ψ₂Sq.eval (φ.xRatFunc.num.eval x₀ / φ.xRatFunc.denom.eval x₀) := by
  have h := congrArg (eval x₀) (wronskian_xRatFunc_sq_mul_Ψ₂Sq hc)
  simp only [eval_mul, eval_pow, eval_C, eval_add] at h
  rw [h, WeierstrassCurve.Ψ₂Sq]
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
  field_simp

end TauCeti.Isogeny
