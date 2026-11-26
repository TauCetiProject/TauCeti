/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
public import TauCeti.AlgebraicGeometry.EllipticCurve.QuadraticTwist.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Discriminant
import TauCeti.AlgebraicGeometry.EllipticCurve.SingularPointCount

/-!
# Point counts of Weierstrass models over odd finite fields as character sums

Let `F` be a finite field of odd characteristic with `q` elements and quadratic character `χ`.
Completing the square in `y`, the equation `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` of a
Weierstrass model `W` reads `(2y + a₁x + a₃)² = Ψ₂Sq(x)`, where
`Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆` is Mathlib's `WeierstrassCurve.Ψ₂Sq`. Since `y ↦ 2y + a₁x + a₃`
is a bijection of `F`, the number of solutions with first coordinate `x` is the number of square
roots of `Ψ₂Sq(x)`, which is `1 + χ(Ψ₂Sq(x))`. Summing over `x` and adding the point at infinity,

  `#W(F) = q + 1 + ∑ₓ χ(Ψ₂Sq(x))`, so `a_q(W) = -∑ₓ χ(Ψ₂Sq(x))`.

This is an identity of projective equation counts (`WeierstrassCurve.pointCount`): it needs no
ellipticity, and a singular solution is counted like any other. For a model in the normal form
`a₁ = a₃ = 0` one has `Ψ₂Sq = 4f` with `f = X³ + a₂X² + a₄X + a₆`, and `χ(4) = 1`, so the sum may be
taken over `χ(f(x))` instead.

Two classical consequences follow from symmetries of the summand.

* If `b₂ = b₆ = 0`, for instance for `y² = x³ + ax`, the cubic `Ψ₂Sq` is odd. When `-1` is not a
  square, which for a finite field means `q ≡ 3 mod 4` (`FiniteField.isSquare_neg_one_iff`), the
  values of `χ` at `x` and `-x` cancel, so the trace is `0` and the count is `q + 1`.
* The quadratic twist `W.quadraticTwistOf t n` has invariants `b₂, b₄, b₆` scaled by `D, D², D³`,
  where `D = t² - 4n`. Hence its cubic at `Dz` is `D³ Ψ₂Sq(z)`, and the substitution `x = Dz` shows
  that its trace is `χ(D) a_q(W)`. At `(t, n) = (0, -d/4)` the twisting discriminant `D` is `d`.
  When `D = 0` the twist is a cusp and its trace is `0 = χ(0) a_q(W)`.

## Main results

* `WeierstrassCurve.card_equation_eq_quadraticChar_add_one`: the number of solutions of the affine
  equation over a fixed `x` is `1 + χ(Ψ₂Sq(x))`.
* `WeierstrassCurve.pointCount_eq_card_add_sum_quadraticChar` and
  `WeierstrassCurve.frobeniusTrace_eq_neg_sum_quadraticChar`: the count and the trace as character
  sums over `Ψ₂Sq`, with the normal-form versions
  `WeierstrassCurve.pointCount_eq_card_add_sum_quadraticChar_of_isCharNeTwoNF` and
  `WeierstrassCurve.frobeniusTrace_eq_neg_sum_quadraticChar_of_isCharNeTwoNF` over the cubic
  `x³ + a₂x² + a₄x + a₆`.
* `WeierstrassCurve.frobeniusTrace_eq_zero_of_b₂_eq_zero_of_b₆_eq_zero` and
  `WeierstrassCurve.pointCount_eq_card_add_one_of_b₂_eq_zero_of_b₆_eq_zero`: when `-1` is a
  nonsquare, a model with odd `2`-division cubic has trace `0` and `q + 1` points.
* `WeierstrassCurve.frobeniusTrace_quadraticTwistOf`: the trace of the quadratic twist by `(t, n)`
  is `χ(t² - 4n)` times the trace of `W`, with the three cases
  `WeierstrassCurve.frobeniusTrace_quadraticTwistOf_eq_zero`,
  `WeierstrassCurve.frobeniusTrace_quadraticTwistOf_of_isSquare` and
  `WeierstrassCurve.frobeniusTrace_quadraticTwistOf_of_not_isSquare`, and its form
  `WeierstrassCurve.frobeniusTrace_quadraticTwistOf_zero_neg_div_four` for the classical twist
  `y² = x³ + da₂x² + d²a₄x + d³a₆` by `d`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], V.1.
* N. Koblitz, *Introduction to Elliptic Curves and Modular Forms*, Graduate Texts in Mathematics
  97, Springer, 1984, p. 41, for `y² = x³ - n²x` over `𝔽_p` with `p ≡ 3 mod 4`.
-/

public section

open Finset Polynomial

namespace WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

section CharacterSum

variable [Fintype F] [DecidableEq F]

/-- **The number of points over a given `x`**: over a finite field of odd characteristic, the
affine equation of `W` has `1 + χ(Ψ₂Sq(x))` solutions `y` over `x`, where `χ` is the quadratic
character and `Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆`. -/
theorem card_equation_eq_quadraticChar_add_one (hF : ringChar F ≠ 2) (x : F) :
    (Nat.card {y // W.toAffine.Equation x y} : ℤ) = quadraticChar F (W.Ψ₂Sq.eval x) + 1 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  -- `y ↦ ψ₂(x, y) = 2y + a₁x + a₃` carries the solutions over `x` onto the square roots of
  -- `Ψ₂Sq(x)`
  let e : F ≃ F := (Equiv.mulLeft₀ 2 h2).trans (Equiv.addRight (W.a₁ * x + W.a₃))
  have he : Nat.card {y // W.toAffine.Equation x y} =
      Nat.card {s : F // s ^ 2 = W.Ψ₂Sq.eval x} :=
    Nat.card_congr <| e.subtypeEquiv fun y ↦ by
      rw [← W.evalEval_ψ₂_sq_eq_iff h2, ψ₂, Affine.evalEval_polynomialY]
      simp [e, add_assoc]
  rw [he, ← quadraticChar_card_sqrts hF, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Set.toFinset_ofPred]

/-- **The point count as a character sum**: over a finite field of odd characteristic with `q`
elements, the projective Weierstrass model `W` has `q + 1 + ∑ₓ χ(Ψ₂Sq(x))` points, where `χ` is the
quadratic character and `Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆`. Singular models are included. -/
theorem pointCount_eq_card_add_sum_quadraticChar (hF : ringChar F ≠ 2) :
    (W.pointCount : ℤ) = Fintype.card F + 1 + ∑ x : F, quadraticChar F (W.Ψ₂Sq.eval x) := by
  rw [pointCount_def, Nat.card_congr
    (Equiv.subtypeProdEquivSigmaSubtype fun x y ↦ W.toAffine.Equation x y), Nat.card_sigma]
  push_cast
  simp_rw [W.card_equation_eq_quadraticChar_add_one hF, sum_add_distrib, sum_const, card_univ,
    nsmul_eq_mul, mul_one]
  ring

/-- **The Frobenius trace as a character sum**: over a finite field of odd characteristic,
`a_q(W) = -∑ₓ χ(Ψ₂Sq(x))`, where `χ` is the quadratic character and
`Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆`. Singular models are included. -/
theorem frobeniusTrace_eq_neg_sum_quadraticChar (hF : ringChar F ≠ 2) :
    W.frobeniusTrace = -∑ x : F, quadraticChar F (W.Ψ₂Sq.eval x) := by
  rw [frobeniusTrace_def, W.pointCount_eq_card_add_sum_quadraticChar hF, Nat.card_eq_fintype_card]
  ring

/-- In normal form `Ψ₂Sq = 4 (X³ + a₂X² + a₄X + a₆)`, and `χ(4) = 1`. -/
private theorem sum_quadraticChar_eval_Ψ₂Sq_of_isCharNeTwoNF (hF : ringChar F ≠ 2)
    [W.IsCharNeTwoNF] :
    ∑ x : F, quadraticChar F (W.Ψ₂Sq.eval x) =
      ∑ x : F, quadraticChar F (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) := by
  refine sum_congr rfl fun x _ ↦ ?_
  rw [W.eval_Ψ₂Sq_of_isCharNeTwoNF, map_mul, show (4 : F) = 2 ^ 2 by norm_num,
    quadraticChar_sq_one' (Ring.two_ne_zero hF), one_mul]

/-- **The point count of a normal-form model as a character sum**: over a finite field of odd
characteristic with `q` elements, `y² = x³ + a₂x² + a₄x + a₆` has
`q + 1 + ∑ₓ χ(x³ + a₂x² + a₄x + a₆)` projective points, where `χ` is the quadratic
character. Singular models are included. -/
theorem pointCount_eq_card_add_sum_quadraticChar_of_isCharNeTwoNF (hF : ringChar F ≠ 2)
    [W.IsCharNeTwoNF] :
    (W.pointCount : ℤ) =
      Fintype.card F + 1 + ∑ x : F, quadraticChar F (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) := by
  rw [W.pointCount_eq_card_add_sum_quadraticChar hF,
    W.sum_quadraticChar_eval_Ψ₂Sq_of_isCharNeTwoNF hF]

/-- **The Frobenius trace of a normal-form model as a character sum**: over a finite field of odd
characteristic, `y² = x³ + a₂x² + a₄x + a₆` has trace `-∑ₓ χ(x³ + a₂x² + a₄x + a₆)`, where `χ` is
the quadratic character. Singular models are included. -/
theorem frobeniusTrace_eq_neg_sum_quadraticChar_of_isCharNeTwoNF (hF : ringChar F ≠ 2)
    [W.IsCharNeTwoNF] :
    W.frobeniusTrace = -∑ x : F, quadraticChar F (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) := by
  rw [W.frobeniusTrace_eq_neg_sum_quadraticChar hF,
    W.sum_quadraticChar_eval_Ψ₂Sq_of_isCharNeTwoNF hF]

end CharacterSum

section Finite

variable [Finite F]

/-- **A model with odd `2`-division cubic has trace zero when `-1` is a nonsquare.** If
`b₂ = b₆ = 0`, then `Ψ₂Sq = 4X³ + 2b₄X` is odd; over a finite field in which `-1` is not a square,
that is with `q ≡ 3 mod 4` elements (`FiniteField.isSquare_neg_one_iff`), the character values at
`x` and `-x` cancel. This covers `y² = x³ + ax` for every `a`, including the cusp `a = 0`. -/
theorem frobeniusTrace_eq_zero_of_b₂_eq_zero_of_b₆_eq_zero (hF : ¬IsSquare (-1 : F))
    (hb₂ : W.b₂ = 0) (hb₆ : W.b₆ = 0) : W.frobeniusTrace = 0 := by
  classical
  have := Fintype.ofFinite F
  have hF₂ : ringChar F ≠ 2 := fun h ↦ hF (FiniteField.isSquare_of_char_two h _)
  rw [W.frobeniusTrace_eq_neg_sum_quadraticChar hF₂, neg_eq_zero]
  refine quadraticChar_sum_comp_eq_zero_of_odd hF fun x ↦ ?_
  simp only [Ψ₂Sq, hb₂, hb₆, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  ring

/-- **A model with odd `2`-division cubic has `q + 1` points when `-1` is a nonsquare**: if
`b₂ = b₆ = 0` and `-1` is not a square in the finite field `F`, then the projective model has
`#F + 1` points. -/
theorem pointCount_eq_card_add_one_of_b₂_eq_zero_of_b₆_eq_zero (hF : ¬IsSquare (-1 : F))
    (hb₂ : W.b₂ = 0) (hb₆ : W.b₆ = 0) : W.pointCount = Nat.card F + 1 := by
  have h := W.frobeniusTrace_eq_zero_of_b₂_eq_zero_of_b₆_eq_zero hF hb₂ hb₆
  rw [frobeniusTrace_def] at h
  omega

/-- **The twist by a parameter pair of discriminant zero has trace zero**: if `t² - 4n = 0`, then
`W.quadraticTwistOf t n` is a cusp, with `Δ = c₄ = 0`. No restriction on the characteristic is
needed. -/
theorem frobeniusTrace_quadraticTwistOf_eq_zero {t n : F} (h : t ^ 2 - 4 * n = 0) :
    (W.quadraticTwistOf t n).frobeniusTrace = 0 :=
  frobeniusTrace_eq_zero_of_c₄_eq_zero _ (by simp [h]) (by simp [h])

end Finite

section Twist

variable [Fintype F] [DecidableEq F]

/-- **The Frobenius trace of a quadratic twist**: over a finite field of odd characteristic, the
quadratic twist of `W` by `(t, n)` has trace `χ(t² - 4n) a_q(W)`, where `χ` is the quadratic
character. At `(t, n) = (0, -d/4)` the twisting discriminant `t² - 4n` is `d`. No ellipticity is
assumed, and `t² - 4n` may vanish. -/
theorem frobeniusTrace_quadraticTwistOf (hF : ringChar F ≠ 2) (t n : F) :
    (W.quadraticTwistOf t n).frobeniusTrace =
      quadraticChar F (t ^ 2 - 4 * n) * W.frobeniusTrace := by
  rcases eq_or_ne (t ^ 2 - 4 * n) 0 with hD | hD
  · rw [W.frobeniusTrace_quadraticTwistOf_eq_zero hD, hD, quadraticChar_zero, zero_mul]
  -- substitute `x = (t² - 4n) z` in the character sum of the twist
  rw [frobeniusTrace_eq_neg_sum_quadraticChar _ hF, W.frobeniusTrace_eq_neg_sum_quadraticChar hF,
    mul_neg, mul_sum, neg_inj]
  refine (Fintype.sum_bijective _ (mulLeft_bijective₀ _ hD) _ _ fun z ↦ ?_).symm
  rw [W.eval_Ψ₂Sq_quadraticTwistOf]
  generalize t ^ 2 - 4 * n = D at hD ⊢
  rw [pow_succ, mul_assoc, map_mul, quadraticChar_sq_one' hD, one_mul, map_mul]

/-- **The Frobenius trace of the classical twist by `d`**: over a finite field of odd
characteristic, the quadratic twist by `(0, -d/4)`, whose twisting discriminant is `d`, has trace
`χ(d) a_q(W)`. For `y² = x³ + a₂x² + a₄x + a₆` this twist is `y² = x³ + da₂x² + d²a₄x + d³a₆`. -/
theorem frobeniusTrace_quadraticTwistOf_zero_neg_div_four (hF : ringChar F ≠ 2) (d : F) :
    (W.quadraticTwistOf 0 (-d / 4)).frobeniusTrace = quadraticChar F d * W.frobeniusTrace := by
  have h4 : (4 : F) ≠ 0 := by
    simpa [show (4 : F) = 2 ^ 2 by norm_num] using Ring.two_ne_zero hF
  rw [W.frobeniusTrace_quadraticTwistOf hF, show (0 : F) ^ 2 - 4 * (-d / 4) = d by field_simp; ring]

end Twist

section TwistCases

variable [Finite F]

/-- **The twist by a nonzero square keeps the trace**: over a finite field of odd characteristic,
if `t² - 4n` is a nonzero square then `W.quadraticTwistOf t n` has the same trace as `W`. -/
theorem frobeniusTrace_quadraticTwistOf_of_isSquare (hF : ringChar F ≠ 2) {t n : F}
    (hD : t ^ 2 - 4 * n ≠ 0) (hsq : IsSquare (t ^ 2 - 4 * n)) :
    (W.quadraticTwistOf t n).frobeniusTrace = W.frobeniusTrace := by
  classical
  have := Fintype.ofFinite F
  rw [W.frobeniusTrace_quadraticTwistOf hF, (quadraticChar_one_iff_isSquare hD).mpr hsq, one_mul]

/-- **The twist by a nonsquare negates the trace**: over a finite field, if `t² - 4n` is not a
square then `W.quadraticTwistOf t n` has trace `-a_q(W)`. A nonsquare forces odd
characteristic. -/
theorem frobeniusTrace_quadraticTwistOf_of_not_isSquare {t n : F}
    (hsq : ¬IsSquare (t ^ 2 - 4 * n)) :
    (W.quadraticTwistOf t n).frobeniusTrace = -W.frobeniusTrace := by
  classical
  have := Fintype.ofFinite F
  have hF : ringChar F ≠ 2 := fun h ↦ hsq (FiniteField.isSquare_of_char_two h _)
  rw [W.frobeniusTrace_quadraticTwistOf hF, quadraticChar_neg_one_iff_not_isSquare.mpr hsq,
    neg_one_mul]

end TwistCases

end WeierstrassCurve

end
