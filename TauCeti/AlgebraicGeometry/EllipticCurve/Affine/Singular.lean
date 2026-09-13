/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-!
# The singular points of a Weierstrass model

A Weierstrass model has at most one singular point. This file introduces the predicate for it and
proves that uniqueness, over any reduced commutative ring.

Singularity is taken to be the Jacobian criterion: the equation and both of its formal partial
derivatives vanish. That is what makes sense over an arbitrary commutative ring, and over a field
it is Mathlib's condition, whose `Nonsingular` carries the note that it "is only mathematically
accurate for fields".

Over a general commutative ring uniqueness is not available, but the cube of the difference of the
`x`-coordinates and the fourth power of the difference of the `y`-coordinates vanish, so the two
points differ by a nilpotent in each coordinate; reducedness is exactly what turns that into
equality. Every statement here holds in any characteristic, including two and three.

## Main definitions

* `WeierstrassCurve.Affine.IsSingular`: the equation and both formal partials vanish at a point.

## Main results

* `WeierstrassCurve.Affine.isSingular_iff'` and `WeierstrassCurve.Affine.isSingular_iff`: the
  coefficient-level restatements, the second as the two equalities `Nonsingular` negates.
* `WeierstrassCurve.Affine.isSingular_zero`: singularity at the origin is `a₃ = a₄ = a₆ = 0`.
* `WeierstrassCurve.Affine.isSingular_iff_variableChange`: singularity at a point is singularity at
  the origin of the model translated there.
* `WeierstrassCurve.Affine.isSingular_iff_equation_and_not_nonsingular`: the comparison with
  Mathlib's `Nonsingular`.
* `WeierstrassCurve.Affine.IsSingular.map`, `map_isSingular`, `IsSingular.baseChange` and
  `baseChange_isSingular`: singularity is carried along a coefficient map or a base change, and
  reflected by an injective one.
* `WeierstrassCurve.Affine.pow_sub_eq_zero_of_isSingular_of_isSingular`: two singular points
  satisfy `(x₂ - x₁) ^ 3 = 0` and `(y₂ - y₁) ^ 4 = 0`.
* `WeierstrassCurve.Affine.isNilpotent_sub_of_isSingular_of_isSingular`: so each coordinate
  difference is nilpotent.
* `WeierstrassCurve.Affine.subsingleton_singular`: over a reduced ring they coincide, so a
  Weierstrass model has at most one singular point.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1.
-/

public section

namespace WeierstrassCurve.Affine

open Polynomial

variable {R : Type*} [CommRing R] {W : WeierstrassCurve.Affine R} {x₁ y₁ x₂ y₂ : R}

/-- **A point of a Weierstrass model where the equation and both formal partial derivatives
vanish** — the Jacobian criterion for singularity, which makes sense over any commutative ring.

Over a field this is `W.Equation x y ∧ ¬ W.Nonsingular x y`, recorded as
`isSingular_iff_equation_and_not_nonsingular`. It is stated separately because Mathlib's
`Nonsingular` carries the note that it "is only mathematically accurate for fields", so over a
general ring the three vanishing conditions are what one can actually say. -/
def IsSingular (W : WeierstrassCurve.Affine R) (x y : R) : Prop :=
  W.Equation x y ∧ W.polynomialX.evalEval x y = 0 ∧ W.polynomialY.evalEval x y = 0

/-- **The coefficient-level form of the Jacobian criterion.** -/
theorem isSingular_iff' (W : WeierstrassCurve.Affine R) (x y : R) : W.IsSingular x y ↔
    W.Equation x y ∧ W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 0 ∧
      2 * y + W.a₁ * x + W.a₃ = 0 := by
  rw [IsSingular, evalEval_polynomialX, evalEval_polynomialY]

/-- **The Jacobian criterion as two equalities**, the form `Nonsingular` negates. -/
theorem isSingular_iff (W : WeierstrassCurve.Affine R) (x y : R) : W.IsSingular x y ↔
    W.Equation x y ∧ W.a₁ * y = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ∧ y = -y - W.a₁ * x - W.a₃ := by
  rw [isSingular_iff', sub_eq_zero, ← sub_eq_zero (a := y)]
  congr! 3
  ring1

/-- **A Weierstrass model is singular at the origin exactly when `a₃`, `a₄` and `a₆` vanish**, so
its equation reads `y (y + a₁x) = x² (x + a₂)`. -/
@[simp]
theorem isSingular_zero (W : WeierstrassCurve.Affine R) :
    W.IsSingular 0 0 ↔ W.a₆ = 0 ∧ W.a₄ = 0 ∧ W.a₃ = 0 := by
  rw [IsSingular, equation_zero, evalEval_polynomialX_zero, evalEval_polynomialY_zero, neg_eq_zero]

/-- **The Jacobian criterion is Mathlib's singularity condition**, `Nonsingular` being the
conjunction of the equation with the negation of both partials vanishing. -/
theorem isSingular_iff_equation_and_not_nonsingular {W : WeierstrassCurve.Affine R} {x y : R} :
    W.IsSingular x y ↔ W.Equation x y ∧ ¬ W.Nonsingular x y := by
  rw [IsSingular, Nonsingular, not_and_or, not_or, not_ne_iff, not_ne_iff]
  exact and_congr_right fun h ↦ ⟨Or.inr, fun hd ↦ hd.resolve_left (not_not_intro h)⟩

/-- **Singularity at a point is singularity at the origin of the model translated there**,
parallel to `equation_iff_variableChange` and `nonsingular_iff_variableChange`. -/
theorem isSingular_iff_variableChange (W : WeierstrassCurve.Affine R) (x y : R) :
    W.IsSingular x y ↔ (VariableChange.mk 1 x 0 y • W).toAffine.IsSingular 0 0 := by
  rw [isSingular_iff_equation_and_not_nonsingular, isSingular_iff_equation_and_not_nonsingular,
    ← equation_iff_variableChange, ← nonsingular_iff_variableChange]

/-- **Singularity is carried along a coefficient map.** -/
theorem IsSingular.map {S : Type*} [CommRing S] (f : R →+* S) {x y : R} (h : W.IsSingular x y) :
    (W.map f).IsSingular (f x) (f y) := by
  obtain ⟨hE, hX, hY⟩ := h
  refine ⟨hE.map f, ?_, ?_⟩
  · rw [map_polynomialX, map_mapRingHom_evalEval, hX, map_zero]
  · rw [map_polynomialY, map_mapRingHom_evalEval, hY, map_zero]

/-- **An injective coefficient map reflects singularity as well.** -/
theorem map_isSingular {S : Type*} [CommRing S] {f : R →+* S} (hf : Function.Injective f)
    (W : WeierstrassCurve.Affine R) (x y : R) :
    (W.map f).IsSingular (f x) (f y) ↔ W.IsSingular x y := by
  simp only [IsSingular, W.map_equation hf, map_polynomialX, map_polynomialY,
    map_mapRingHom_evalEval, map_eq_zero_iff f hf]

/-- **Singularity is carried along a base change.** -/
theorem IsSingular.baseChange {A B : Type*} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) {x y : A} (h : (W⁄A).IsSingular x y) : (W⁄B).IsSingular (f x) (f y) := by
  convert! IsSingular.map f.toRingHom h using 2
  rw [AlgHom.toRingHom_eq_coe, map_baseChange]

/-- **An injective base change reflects singularity as well.** -/
theorem baseChange_isSingular {A B : Type*} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    {f : A →ₐ[R] B} (hf : Function.Injective f)
    (W : WeierstrassCurve.Affine R) (x y : A) :
    (W⁄B).IsSingular (f x) (f y) ↔ (W⁄A).IsSingular x y := by
  rw [← map_isSingular hf, AlgHom.toRingHom_eq_coe, map_baseChange, RingHom.coe_coe]

/-- **Two singular points of a Weierstrass model have `(x₂ - x₁) ^ 3 = 0` and
`(y₂ - y₁) ^ 4 = 0`.** The nilpotence and equality forms below follow from these. -/
theorem pow_sub_eq_zero_of_isSingular_of_isSingular (h₁ : W.IsSingular x₁ y₁)
    (h₂ : W.IsSingular x₂ y₂) : (x₂ - x₁) ^ 3 = 0 ∧ (y₂ - y₁) ^ 4 = 0 := by
  obtain ⟨hE₁, hX₁, hY₁⟩ := h₁
  obtain ⟨hE₂, hX₂, hY₂⟩ := h₂
  rw [evalEval_polynomialX] at hX₁ hX₂
  rw [evalEval_polynomialY] at hY₁ hY₂
  rw [equation_iff'] at hE₁ hE₂
  -- one linear combination of the six relations, with no division by `2` or `3`
  have hu3 : (x₂ - x₁) ^ 3 = 0 := by
    linear_combination (x₁ - x₂) * hX₂ + (y₁ - y₂) * hY₂ + 2 * hE₂ + (x₁ - x₂) * hX₁ +
      (y₁ - y₂) * hY₁ - 2 * hE₁
  refine ⟨hu3, ?_⟩
  -- the equation at the second point, reduced by the first; `a₂ + 3 x₁` is the translated `a₂`
  have hv2 : (y₂ - y₁) ^ 2 =
      (W.a₂ + 3 * x₁) * (x₂ - x₁) ^ 2 - W.a₁ * (x₂ - x₁) * (y₂ - y₁) := by
    linear_combination hE₂ + hu3 + (x₁ - x₂) * hX₁ - hE₁ + (y₁ - y₂) * hY₁
  have hu4 : (x₂ - x₁) ^ 4 = 0 := pow_eq_zero_of_le (by omega) hu3
  have hu3v : (x₂ - x₁) ^ 3 * (y₂ - y₁) = 0 := by simp [hu3]
  have hu2v2 : (x₂ - x₁) ^ 2 * (y₂ - y₁) ^ 2 = 0 := by
    rw [hv2]; linear_combination (W.a₂ + 3 * x₁) * hu4 - W.a₁ * hu3v
  -- the reshape exposes the square that `hv2` rewrites; `linear_combination` cannot see it
  rw [show (y₂ - y₁) ^ 4 = ((y₂ - y₁) ^ 2) ^ 2 by ring, hv2]
  linear_combination (W.a₂ + 3 * x₁) ^ 2 * hu4 -
    2 * W.a₁ * (W.a₂ + 3 * x₁) * hu3v + W.a₁ ^ 2 * hu2v2

/-- **Each coordinate difference of two singular points of a Weierstrass model is nilpotent.** -/
theorem isNilpotent_sub_of_isSingular_of_isSingular (h₁ : W.IsSingular x₁ y₁)
    (h₂ : W.IsSingular x₂ y₂) : IsNilpotent (x₂ - x₁) ∧ IsNilpotent (y₂ - y₁) := by
  obtain ⟨hx, hy⟩ := pow_sub_eq_zero_of_isSingular_of_isSingular h₁ h₂
  exact ⟨⟨3, hx⟩, 4, hy⟩

/-- **Over a reduced ring a Weierstrass model has at most one singular point.** -/
theorem eq_of_isSingular_of_isSingular [IsReduced R] (h₁ : W.IsSingular x₁ y₁)
    (h₂ : W.IsSingular x₂ y₂) : x₁ = x₂ ∧ y₁ = y₂ := by
  obtain ⟨hx, hy⟩ := isNilpotent_sub_of_isSingular_of_isSingular h₁ h₂
  exact ⟨(sub_eq_zero.1 hx.eq_zero).symm, (sub_eq_zero.1 hy.eq_zero).symm⟩

/-- **A Weierstrass model over a reduced ring has at most one singular point**, in Mathlib's
vocabulary. -/
theorem subsingleton_singular [IsReduced R] (W : WeierstrassCurve.Affine R) (p q : R × R)
    (hp : W.Equation p.1 p.2) (hp' : ¬ W.Nonsingular p.1 p.2) (hq : W.Equation q.1 q.2)
    (hq' : ¬ W.Nonsingular q.1 q.2) : p = q := by
  obtain ⟨hx, hy⟩ :=
    eq_of_isSingular_of_isSingular (isSingular_iff_equation_and_not_nonsingular.2 ⟨hp, hp'⟩)
      (isSingular_iff_equation_and_not_nonsingular.2 ⟨hq, hq'⟩)
  exact Prod.ext hx hy

end WeierstrassCurve.Affine

end
