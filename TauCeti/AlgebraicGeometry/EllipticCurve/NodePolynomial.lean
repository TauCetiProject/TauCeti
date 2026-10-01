/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import TauCeti.Algebra.Polynomial.QuadraticDiscriminant

/-!
# The node polynomial of a Weierstrass curve

For a nodal Weierstrass curve, the node polynomial is the quadratic
`c₄ T² + a₁ c₄ T - (54 b₆ - 3 b₂ b₄ + a₂ c₄)`. Its splitting over the residue field
distinguishes split from nonsplit multiplicative reduction.

This file defines `WeierstrassCurve.nodePolynomial` over a commutative ring and proves:

* its discriminant is `-c₄ c₆`;
* it commutes with base change;
* a change of variables `(u, r, s, t)` acts by the substitution `T ↦ u T + s` and the
  scalar `u⁻⁶`, preserving splitting over a field;
* after mapping to a field where `c₄` remains nonzero, splitting is equivalent to the
  discriminant being a square in characteristic different from two, and to an Artin–Schreier
  condition in characteristic two.

These criteria apply to any ring homomorphism to a field. Their relation to
`WeierstrassCurve.HasSplitMultiplicativeReduction` is developed in `MinimalModel/Basic.lean` and
`LocalPolynomial.lean`. The constant-coefficient formula also describes the effect of quadratic
twisting in `QuadraticTwist/Basic.lean`.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`, commit `bc2fe8ff7396`, FLT PR #1088,
Apache 2.0): the node-polynomial block of
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean` (authors Kevin Buzzard, William Coram,
Claude), and `splitPolynomial_discrim` from
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean` (authors Kevin Buzzard, Claude).
-/

public section

namespace WeierstrassCurve

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B] {k : Type*} [Field k]

/-- The **node polynomial** `c₄ T² + a₁ c₄ T - (54 b₆ - 3 b₂ b₄ + a₂ c₄)`, whose roots are the
slopes of the two tangent directions at the node of a multiplicative reduction. This is the
polynomial Mathlib writes out inline in `WeierstrassCurve.HasSplitMultiplicativeReduction`, which
asks for the splitting over the residue field of this polynomial formed from the *integral model*
`W.integralModel R`, as its one extra condition on top of `HasMultiplicativeReduction`. -/
noncomputable def nodePolynomial (W : WeierstrassCurve A) : Polynomial A :=
  .C W.c₄ * .X ^ 2 + .C (W.a₁ * W.c₄) * .X - .C (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)

/-- The defining formula for the node polynomial. The definition's body is not exposed across the
module boundary, so this is how downstream modules see it;
`nodePolynomial_map_eq_quadratic` is the corresponding statement for its image under a ring
homomorphism. -/
lemma nodePolynomial_def (W : WeierstrassCurve A) :
    W.nodePolynomial = .C W.c₄ * .X ^ 2 + .C (W.a₁ * W.c₄) * .X
      - .C (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄) := by
  simp only [nodePolynomial]

/-- The constant coefficient of the node polynomial. Note the sign: `nodePolynomial` *subtracts*
`54 b₆ - 3 b₂ b₄ + a₂ c₄`, so `coeff 0` is minus that combination, not it.

Deliberately not `@[simp]`: the normal form wanted downstream rewrites a twisted curve's
coefficient back to the base curve's (`nodePolynomial_coeff_zero_quadraticTwistOf`), and that
lemma's left-hand side is exactly this one's, so tagging both would make the twist lemma
non-normal-form. -/
lemma nodePolynomial_coeff_zero (W : WeierstrassCurve A) :
    W.nodePolynomial.coeff 0 = -(54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄) := by
  simp [nodePolynomial_def]

/-- **The node polynomial as `c₄` times a monic quadratic.** If `c₄ n` is the constant coefficient
of the node polynomial, the node polynomial is `c₄ · (T² + a₁ T + n)`. When `c₄` is a unit such an
`n` exists and is unique. This is a purely algebraic factorization; when the reduction of a
minimal model is multiplicative, the roots of the reduced quadratic `T² + a₁ T + n` are the slopes
of the two tangent directions at the node of the reduced curve. -/
theorem nodePolynomial_eq_C_mul (W : WeierstrassCurve A) {n : A}
    (hn : W.c₄ * n = W.nodePolynomial.coeff 0) :
    W.nodePolynomial = .C W.c₄ * (.X ^ 2 + .C W.a₁ * .X + .C n) := by
  rw [nodePolynomial_coeff_zero] at hn
  have hC := congrArg Polynomial.C hn
  rw [nodePolynomial_def]
  simp only [map_mul, map_sub, map_add, map_neg, map_ofNat] at hC ⊢
  linear_combination -hC

/-- The discriminant of the node polynomial is `-c₄ c₆`. Hence — away from residue characteristic
two, and provided `c₄` survives the reduction — the tangent directions at the node are rational
over the residue field exactly when the image of `-c₄ c₆` is a square there
(`splits_nodePolynomial_map_iff_isSquare`); twisting by `(t, n)` multiplies `-c₄ c₆` by
`(t² - 4n)⁵ = (t² - 4n)⁴ · (t² - 4n)`, i.e. by the twisting parameter up to a square. -/
theorem discrim_nodePolynomial (W : WeierstrassCurve A) :
    discrim W.c₄ (W.a₁ * W.c₄) (-(54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄))
      = -(W.c₄ * W.c₆) := by
  simp only [discrim, c₄, c₆, b₂, b₄, b₆]; ring

/-- The node polynomial is natural in the coefficient ring: it commutes with base change of the
Weierstrass equation along any ring homomorphism. -/
@[simp]
lemma map_nodePolynomial (φ : A →+* B) (W : WeierstrassCurve A) :
    (W.map φ).nodePolynomial = W.nodePolynomial.map φ := by
  simp only [nodePolynomial, WeierstrassCurve.map_c₄, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_b₂,
    WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆, WeierstrassCurve.map_a₂, Polynomial.map_add,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_ofNat, map_add, map_sub, map_mul, map_ofNat]

/-- The reduced node polynomial, presented as a quadratic with an additive constant term — the
shape `C a * X ^ 2 + C b * X + C c` that the criteria of
`TauCeti/Algebra/Polynomial/QuadraticDiscriminant.lean` consume. -/
lemma nodePolynomial_map_eq_quadratic {B : Type*} [Ring B] (φ : A →+* B) (W : WeierstrassCurve A) :
    W.nodePolynomial.map φ = .C (φ W.c₄) * .X ^ 2 + .C (φ (W.a₁ * W.c₄)) * .X
      + .C (-φ (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)) := by
  simp only [nodePolynomial, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
  rw [map_neg, sub_eq_add_neg]

/-- The image of `discrim_nodePolynomial` under a ring homomorphism, in the shape produced by the
quadratic criteria applied to `nodePolynomial_map_eq_quadratic`. -/
lemma discrim_map_nodePolynomial {B : Type*} [Ring B] (φ : A →+* B) (W : WeierstrassCurve A) :
    discrim (φ W.c₄) (φ (W.a₁ * W.c₄)) (-φ (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄))
      = φ (-(W.c₄ * W.c₆)) := by
  simpa only [discrim, map_sub, map_mul, map_neg, map_pow, map_ofNat] using
    congrArg φ W.discrim_nodePolynomial

/-- Under a change of variables `C = (u, r, s, t)`, the node polynomial transforms by the affine
substitution `T ↦ u T + s` and the unit scalar `u⁻⁶` — reflecting that the tangent slopes `λ`
transform as `λ ↦ (λ - s)/u`. Over a field this makes splitting invariant; see
`splits_variableChange_nodePolynomial_map_iff`. -/
lemma variableChange_nodePolynomial (W : WeierstrassCurve A) (C : VariableChange A) :
    (C • W).nodePolynomial = .C ((↑C.u⁻¹ : A) ^ 6)
      * W.nodePolynomial.comp (.C (↑C.u : A) * .X + .C C.s) := by
  -- `ring` treats `↑u` and `↑u⁻¹` as unrelated constants, so the two cancellations it needs are
  -- supplied to `linear_combination` using the unit identity and its square.
  have hu : Polynomial.C (↑C.u⁻¹ : A) * Polynomial.C (↑C.u : A) = 1 := by
    rw [← Polynomial.C_mul, C.u.inv_mul, Polynomial.C_1]
  have hc₄ : Polynomial.C W.c₄ = Polynomial.C W.b₂ ^ 2 - 24 * Polynomial.C W.b₄ := by
    rw [c₄]
    simp only [Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow, map_ofNat]
  simp only [nodePolynomial, variableChange_a₁, variableChange_a₂, variableChange_c₄,
    variableChange_b₂, variableChange_b₄, variableChange_b₆, Polynomial.mul_comp,
    Polynomial.add_comp, Polynomial.sub_comp, Polynomial.C_comp, Polynomial.X_comp, pow_two,
    mul_add, add_mul, mul_sub, sub_mul, Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub,
    Polynomial.C_pow, map_ofNat, Polynomial.ofNat_comp]
  -- the `r`-shift contributes `c₄` through `variableChange_a₂`, in expanded form
  linear_combination
    (-Polynomial.C W.c₄ * Polynomial.X ^ 2 * Polynomial.C (↑C.u⁻¹ : A) ^ 4) *
      pow_mul_pow_eq_one 2 hu
    + (-(2 * Polynomial.C W.c₄ * Polynomial.C C.s + Polynomial.C W.a₁ * Polynomial.C W.c₄)
        * Polynomial.X * Polynomial.C (↑C.u⁻¹ : A) ^ 5) * hu
    + (-3 * Polynomial.C (↑C.u⁻¹ : A) ^ 6 * Polynomial.C C.r) * hc₄

/-- **Invariance of the node polynomial's splitting under change of variables.** Since a change of
variables transforms the node polynomial by an affine substitution and a unit scalar
(`variableChange_nodePolynomial`), whether it splits over a field `k` is unchanged. This is what
makes split multiplicative reduction an isomorphism invariant rather than a property of the
equation. -/
lemma splits_variableChange_nodePolynomial_map_iff (φ : A →+* k) (W : WeierstrassCurve A)
    (C : VariableChange A) :
    ((C • W).nodePolynomial.map φ).Splits ↔ (W.nodePolynomial.map φ).Splits := by
  have hu : φ (↑C.u : A) ≠ 0 := (RingHom.isUnit_map φ C.u.isUnit).ne_zero
  have hu6 : φ ((↑C.u⁻¹ : A) ^ 6) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero 6 (RingHom.isUnit_map φ C.u⁻¹.isUnit).ne_zero
  simp only [variableChange_nodePolynomial, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X]
  rw [Polynomial.splits_mul_iff_right (Polynomial.C_ne_zero.mpr hu6) (Polynomial.Splits.C _)]
  exact (Polynomial.splits_iff_comp_splits_of_natDegree_eq_one
    (Polynomial.natDegree_linear hu)).symm

/-- **Split criterion away from residue characteristic two.** Over a field `k` with `2 ≠ 0`, and
provided `c₄` does not die under `φ` — the condition that makes the reduced polynomial genuinely
quadratic, and which multiplicative reduction supplies — the node polynomial splits, i.e. the two
tangent directions at the node are `k`-rational, exactly when `φ (-(c₄ * c₆))`, the image of its
discriminant (`discrim_nodePolynomial`), is a square in `k`. Applied to a quadratic twist via
`-c₄' c₆' = (t² - 4n)⁵ · (-c₄ c₆)`, this criterion identifies the square class of twists that
turns nonsplit reduction into split reduction. -/
lemma splits_nodePolynomial_map_iff_isSquare [NeZero (2 : k)] (φ : A →+* k) (W : WeierstrassCurve A)
    (hc₄ : φ W.c₄ ≠ 0) :
    (W.nodePolynomial.map φ).Splits ↔ IsSquare (φ (-(W.c₄ * W.c₆))) := by
  rw [nodePolynomial_map_eq_quadratic, Polynomial.splits_quadratic_iff_isSquare hc₄,
    discrim_map_nodePolynomial]

/-- **Split criterion in residue characteristic two.** Over a field `k` of characteristic `2`,
where the square-class criterion `splits_nodePolynomial_map_iff_isSquare` says nothing, the node
polynomial splits exactly when its Artin-Schreier invariant lies in the image of `z ↦ z² + z`.
Only `c₄` need be assumed nonzero: in characteristic two `c₄ = a₁⁴`, so the linear coefficient
`a₁ c₄` is also nonzero. -/
lemma splits_nodePolynomial_map_iff_exists_artinSchreier_of_two_eq_zero (h2 : (2 : k) = 0)
    (φ : A →+* k) (W : WeierstrassCurve A) (hc₄ : φ W.c₄ ≠ 0) :
    (W.nodePolynomial.map φ).Splits ↔ ∃ z, φ (W.a₁ * W.c₄) ^ 2 * (z ^ 2 + z)
      = φ W.c₄ * (-φ (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)) := by
  let : CharP k 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 h2
  have ha₁ : φ W.a₁ ≠ 0 := by
    have h := (W.map φ).c₄_of_char_two
    rw [map_c₄, map_a₁] at h
    exact fun h0 ↦ hc₄ (by simp [h, h0])
  have hb : φ (W.a₁ * W.c₄) ≠ 0 := by
    rw [map_mul]
    exact mul_ne_zero ha₁ hc₄
  rw [nodePolynomial_map_eq_quadratic,
    Polynomial.splits_quadratic_iff_exists_artinSchreier_of_two_eq_zero h2 hc₄ hb]

end WeierstrassCurve

end
