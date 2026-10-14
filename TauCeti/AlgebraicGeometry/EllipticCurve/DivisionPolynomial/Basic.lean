/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# Identities among the division polynomials

Two identities the Nagell–Lutz route needs and Mathlib lacks — one univariate, one bivariate —
and the consumer the univariate one exists for, followed by three evaluations of `Ψ₃` that
reduce a Weierstrass curve to Tate normal form.

Mathlib gives the univariate polynomials `Φₙ` in two registers. `Φ_three` and `Φ_four` are stated
through the division polynomials `Ψ₃`, `preΨ₄` and `Ψ₂Sq`; `Φ_two` is stated through the
`b`-invariants, as `X ^ 4 - C b₄ * X ^ 2 - C (2 * b₆) * X - C b₈`. This file supplies the `n = 2`
member of the first register, which Mathlib does not have, together with the one evaluation
identity that the same Nagell–Lutz route needs and Mathlib likewise lacks: what `ψ₂` reduces to on
a curve in characteristic-≠-2 normal form.

## Main results

* `WeierstrassCurve.Φ_two_eq_X_mul_Ψ₂Sq_sub_Ψ₃`: `Φ₂ = X · Ψ₂Sq - Ψ₃`.
* `WeierstrassCurve.eval_Ψ₃_eq_sub_mul_eval_Ψ₂Sq`: its consumer — from the cleared doubling
  relation `x' · ΨSq₂(x) = Φ₂(x)`, the factorisation `Ψ₃(x) = (x - x') · Ψ₂Sq(x)`.
* `WeierstrassCurve.evalEval_ψ₂_of_isCharNeTwoNF`: `ψ₂(x, y) = 2y` whenever `a₁ = a₃ = 0`. The
  two-division polynomial is `2y + a₁x + a₃`, so Mathlib's `IsCharNeTwoNF` collapses it. It sits
  here rather than with its consumer because it is a plain identity among Mathlib's division
  polynomials over any commutative ring — the same reason as the two above — and because a
  consumer-side home would tie its availability to torsion imports it does not need.
* `WeierstrassCurve.eval_Ψ₃`: `Ψ₃(x) = 3x⁴ + b₂x³ + 3b₄x² + 3b₆x + b₈`, the value of `Ψ₃` at a
  point through the `b`-invariants.
* `WeierstrassCurve.variableChange_b₈_eq_eval_Ψ₃`: after a change of variables `C`, the invariant
  `b₈` is `u⁻⁸ Ψ₃(r)`.
* `WeierstrassCurve.a₂_mul_ψ₂_sq_eq_eval_Ψ₃`: if `(x, y)` lies on `W` and
  `sψ₂ = a₄ + 2a₂x - a₁y + 3x²`, where `ψ₂ = 2y + a₁x + a₃`, then
  `(a₂ - sa₁ + 3x - s²) ψ₂² = Ψ₃(x)`. The factor `a₂ - sa₁ + 3x - s²` is the coefficient `a₂` of
  `W` after the change of variables `(1, x, s, y)`.
* `WeierstrassCurve.eval_variableChange_Ψ₂Sq`: after a change of variables `C`, the polynomial
  `Ψ₂Sq` becomes `u⁻⁶ Ψ₂Sq(u²x + r)`.
* `WeierstrassCurve.eval_variableChange_Ψ₃`: after a change of variables `C`, the polynomial
  `Ψ₃` becomes `u⁻⁸ Ψ₃(u²x + r)`.

Everything here holds over an arbitrary commutative ring, with no ellipticity and no division. Of
the first three, the first has no hypothesis at all; the second's is an equation between ring
elements; the third's is Mathlib's `IsCharNeTwoNF` instance, which is a condition on the curve's
coefficients rather than on a point. The first two are statements about univariate polynomials and
mention no point at all; the third evaluates the bivariate `ψ₂`, but at an arbitrary `(x, y)` — it
does not ask that the pair lie on the curve.

The last three evaluate `Ψ₃` and `ψ₂` at a point and are what reduces a Weierstrass curve to Tate
normal form (`TauCeti/AlgebraicGeometry/EllipticCurve/TateNormalForm.lean`): once the point is
moved to `(0, 0)` with horizontal tangent, `b₈ = a₂a₃²`, so the normalisation `a₂ = a₃` is read off
`Ψ₃`. Only `a₂_mul_ψ₂_sq_eq_eval_Ψ₃` asks that the point lie on the curve.

The change-of-variables formula for `Ψ₂Sq` is what the real period of a Weierstrass curve over `ℝ`,
an integral of `Ψ₂Sq(x)^(-1/2)`, needs in order to scale by `|u|` under a change of variables
(`TauCeti/AlgebraicGeometry/EllipticCurve/RealPeriod.lean`). The one for `Ψ₃` transports the
condition that a point has order `3` along a change of variables
(`TauCeti/AlgebraicGeometry/EllipticCurve/LevelThreeNormalForm.lean`).

Declarations here are stated in the root
`WeierstrassCurve` namespace, not under `TauCeti`, because they extend Mathlib's own
division-polynomial API and mention nothing of this repository's — the same call
`DivisionPolynomial/Invariant.lean` makes for `invar`, `C_Ψ₃` and `preΨ₄_add_Ψ₂Sq_sq`, and what
`scripts/lint-dot-notation.py` requires so that `W.Φ_two_eq_X_mul_Ψ₂Sq_sub_Ψ₃` elaborates.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, Layer 6, item "The torsion subgroup and Nagell–Lutz",
names the discriminant half of the theorem twice: at `:827` as
"`lutz_nagell_integrality_general`, with its discriminant companion", and in the Layer 6 note at
`:1163`–`:1170` as "the `κ² ∣ 4Δ` discriminant form". The `Φ 2` identity is the step that turns the
doubling formula for the `x`-coordinate into the factorisation `Ψ₃(x) = (x - x')·Ψ₂Sq(x)` that
argument runs on, and `evalEval_ψ₂_of_isCharNeTwoNF` is what turns `ψ₂` into `2y` once the model
is short. The rest of that route has since landed — the point-level doubling formula in
`DivisionPolynomial/Descent.lean` and the integrality theorem as
`isInteger_or_order_two_of_torsion` — so the consumers named above now exist. Nothing in this file
assumes them: every declaration here is a statement about polynomials.

## Provenance

Ported from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at `dev/modular-curves @
9fec8eba7652`, the revision that roadmap pins for `projects/NagellLutz` (`:1071`).

The `Φ 2` identity is **unnamed** in the source. It appears only as the inner `show` of the
`eval`-level wrapper `Phi2_eval_eq`, in two files and with byte-identical proofs:
`LutzNagell/LutzNagellTheorem/PIDMain.lean:305` and
`LutzNagell/LutzNagellTheorem/GeneralDiscriminant.lean:89`. Naming it at polynomial level is the
adaptation; the tactic script is the source's, with its bare `simp` squeezed to `simp only`.

The factorisation is also unnamed there: it is the anonymous
`have hPsi3_eq : eval x Ψ₃ = (x - x') * eval x Ψ₂Sq := by linarith` inside
`kappa_sq_dvd_four_Psi3` (`GeneralDiscriminant.lean:153`), stated over `ℚ` after both `eval`-level
wrappers have fired. `PIDMain.lean:390` carries a variant of the same step with `κ₀ ^ 2` already
substituted for `Ψ₂Sq(x)`. Here it is stated over any commutative ring, since nothing in it needs a
field, and it takes the doubling relation as a hypothesis rather than reconstructing it.

`evalEval_ψ₂_of_isCharNeTwoNF` is **not** from that source. It began as a `shortCurve`-specific
identity in the short-model port and was generalised to `IsCharNeTwoNF` when review observed that
its one-line proof never uses `a₂ = 0`; `shortCurve` picks it up through Mathlib's
`isCharNeTwoNF_of_isShortNF`.

The source's two `eval`-level wrappers themselves are deliberately not ported. `Phi2_eval_eq` is
the `Φ 2` identity followed by `eval_sub, eval_mul, eval_X`, and `PsiSq_two_eval_eq` is Mathlib's
`ΨSq_two` under `eval`; neither earns a declaration once the polynomial identity has one.
-/

public section

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- **`Φ 2` through the division polynomials**: `Φ₂ = X · Ψ₂Sq - Ψ₃`.

The index-`2` companion to Mathlib's `Φ_three` and `Φ_four`, which are stated in the division
polynomials where `Φ_two` is stated in the `b`-invariants. It is the shape the `x`-coordinate of a
doubled point is read in, that coordinate being `Φ₂/ΨSq₂`. -/
theorem Φ_two_eq_X_mul_Ψ₂Sq_sub_Ψ₃ : W.Φ 2 = X * W.Ψ₂Sq - W.Ψ₃ := by
  -- `Φ n = X * ΨSq n - preΨ (n + 1) * preΨ (n - 1) * (if Even n then 1 else Ψ₂Sq)`; at `n = 2` the
  -- three division polynomials involved are `ΨSq 2 = Ψ₂Sq`, `preΨ 3 = Ψ₃` and `preΨ 1 = 1`.
  rw [WeierstrassCurve.Φ, ΨSq_two]
  simp only [Int.reduceAdd, preΨ_three, Int.reduceSub, preΨ_one, mul_one, even_two, ↓reduceIte]

/-- **`Ψ₃` factorises through the doubling formula**: if `x'` and `x` satisfy the `x`-coordinate
doubling relation in its cleared form `x' · ΨSq₂(x) = Φ₂(x)`, then `Ψ₃(x) = (x - x') · Ψ₂Sq(x)`.

The hypothesis is an equation between ring elements rather than the quotient `x' = Φ₂(x)/ΨSq₂(x)`,
so this holds over an arbitrary commutative ring, with no division and no hypothesis that
`ΨSq₂(x)` is a non-zero-divisor. -/
theorem eval_Ψ₃_eq_sub_mul_eval_Ψ₂Sq {x x' : R} (h : x' * (W.ΨSq 2).eval x = (W.Φ 2).eval x) :
    (W.Ψ₃).eval x = (x - x') * (W.Ψ₂Sq).eval x := by
  rw [ΨSq_two, W.Φ_two_eq_X_mul_Ψ₂Sq_sub_Ψ₃, eval_sub, eval_mul, eval_X] at h
  linear_combination h

/-- **In characteristic-≠-2 normal form, `ψ₂` is `2y`.** The two-division polynomial is
`2y + a₁x + a₃`, so `a₁ = a₃ = 0` collapses it — and that collapse is what turns the long model's
order-two exception into the classical `y = 0`.

Stated at `IsCharNeTwoNF` rather than at `shortCurve`, which is the weakest hypothesis the one-line
proof uses: `y² = x³ + a₂x² + a₄x + a₆` needs no `a₂ = 0`. Mathlib's
`isCharNeTwoNF_of_isShortNF` hands the instance to `shortCurve` for free, so the short-model call
sites are unchanged. Over any commutative ring, because both `ℤ` (for the integral conclusion) and
`ℚ` (for the point) need it. -/
@[simp] lemma evalEval_ψ₂_of_isCharNeTwoNF {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    [W.IsCharNeTwoNF] (x y : R) : W.ψ₂.evalEval x y = 2 * y := by
  simp [WeierstrassCurve.ψ₂, Affine.polynomialY, evalEval]

/-- The `3`-division polynomial `Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈` at a point. -/
theorem eval_Ψ₃ (x : R) :
    W.Ψ₃.eval x = 3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ := by
  simp [Ψ₃]

/-- After a change of variables `C`, the invariant `b₈` is `u⁻⁸ Ψ₃(r)`. -/
theorem variableChange_b₈_eq_eval_Ψ₃ (C : VariableChange R) :
    (C • W).b₈ = C.u⁻¹ ^ 8 * W.Ψ₃.eval C.r := by
  rw [variableChange_b₈, eval_Ψ₃]
  ring

/-- If `(x, y)` lies on `W` and `sψ₂ = a₄ + 2a₂x - a₁y + 3x²`, where `ψ₂ = 2y + a₁x + a₃`, then
`(a₂ - sa₁ + 3x - s²) ψ₂² = Ψ₃(x)`. The factor `a₂ - sa₁ + 3x - s²` is the coefficient `a₂` of `W`
after the change of variables `(u, r, s, t) = (1, x, s, y)`, and the hypothesis on `s` says that
this change of variables makes `a₄` vanish. -/
theorem a₂_mul_ψ₂_sq_eq_eval_Ψ₃ {W : WeierstrassCurve R} {x y : R} (h : W.toAffine.Equation x y)
    {s : R} (hs : s * (2 * y + W.a₁ * x + W.a₃) = W.a₄ + 2 * x * W.a₂ - y * W.a₁ + 3 * x ^ 2) :
    (W.a₂ - s * W.a₁ + 3 * x - s ^ 2) * (2 * y + W.a₁ * x + W.a₃) ^ 2 = W.Ψ₃.eval x := by
  rw [Affine.equation_iff] at h
  rw [eval_Ψ₃, b₂, b₄, b₆, b₈]
  linear_combination (-W.a₁ * (2 * y + W.a₁ * x + W.a₃) - (s * (2 * y + W.a₁ * x + W.a₃) +
    (W.a₄ + 2 * x * W.a₂ - y * W.a₁ + 3 * x ^ 2))) * hs + (W.a₁ ^ 2 + 4 * W.a₂ + 12 * x) * h

/-- `x = u⁻² (u² x)` for the scaling `u` of a change of variables. -/
private theorem VariableChange.eq_inv_sq_mul (C : VariableChange R) (x : R) :
    x = ((C.u⁻¹ : Rˣ) : R) ^ 2 * (C.u ^ 2 * x) := by
  linear_combination (-(x * ((C.u⁻¹ : Rˣ) : R) * C.u) - x) * C.u.inv_mul

/-- After a change of variables `C`, the polynomial `Ψ₂Sq`, which agrees with `(2y + a₁x + a₃)²`
on the curve, transforms as `Ψ₂Sq'(x) = u⁻⁶ Ψ₂Sq(u²x + r)`. -/
theorem eval_variableChange_Ψ₂Sq (C : VariableChange R) (x : R) :
    (C • W).Ψ₂Sq.eval x = C.u⁻¹ ^ 6 * W.Ψ₂Sq.eval (C.u ^ 2 * x + C.r) := by
  -- write `x` as `u⁻² (u² x)`, after which both sides are the same polynomial in `u² x`
  conv_lhs => rw [VariableChange.eq_inv_sq_mul C x]
  simp only [Ψ₂Sq, eval_add, eval_mul, eval_pow, eval_C, eval_X, variableChange_b₂,
    variableChange_b₄, variableChange_b₆]
  ring

/-- After a change of variables `C`, the `3`-division polynomial transforms as
`Ψ₃'(x) = u⁻⁸ Ψ₃(u²x + r)`. -/
theorem eval_variableChange_Ψ₃ (C : VariableChange R) (x : R) :
    (C • W).Ψ₃.eval x = C.u⁻¹ ^ 8 * W.Ψ₃.eval (C.u ^ 2 * x + C.r) := by
  -- write `x` as `u⁻² (u² x)`, after which both sides are the same polynomial in `u² x`
  conv_lhs => rw [VariableChange.eq_inv_sq_mul C x]
  simp only [eval_Ψ₃, variableChange_b₂, variableChange_b₄, variableChange_b₆, variableChange_b₈]
  ring

end WeierstrassCurve
