/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import TauCeti.AlgebraicGeometry.EllipticCurve.CurveX3SubX
public import TauCeti.AlgebraicGeometry.EllipticCurve.FreyCurve.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.QuadraticTwist.Basic
-- Proof-only: `Point.cast_some`, the coordinates of a point transported along `AddEquiv.cast`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic

/-!
# The Legendre equation and its scaled form

For an element `l` of a commutative ring, the **Legendre equation** is the Weierstrass curve

  `y² = x (x - 1) (x - l)`,

with `a₂ = -(1 + l)`, `a₄ = l` and `a₁ = a₃ = a₆ = 0`. For a second element `d`, the **scaled
Legendre equation** is

  `y² = x (x - d) (x - d l)`,

with `a₂ = -d (1 + l)` and `a₄ = d² l`; its cubic has the ordered roots `0`, `d` and `d l`. Both
are coefficient models, defined for every `l` and `d`, including the singular values. They are the
Frey–Hellegouarch curves `y² = x (x - A) (x + B)` at `(A, B) = (1, -l)` and `(A, B) = (d, -d l)`,
and their invariants are specialisations of the Frey identities:

  `Δ = 16 d⁶ l² (1 - l)²`,  `c₄ = 16 d² (l² - l + 1)`,

so over a field with `2 ≠ 0` the scaled equation is elliptic exactly when `d ≠ 0`, `l ≠ 0` and
`l ≠ 1`, and then `j = 256 (l² - l + 1)³ / (l² (1 - l)²)` does not depend on `d`.

The scalar `d` is a quadratic twist: the twist of `y² = x (x - 1) (x - l)` by the parameters
`(0, n)`, whose twisting discriminant is `-4 n`, is the scaled equation with `d = -4 n`, over every
commutative ring. Over a field with `2 ≠ 0` the scaled equation with scalar `d` is therefore the
twist with parameters `(0, -d / 4)`, of twisting discriminant `d`. Scaling `d` by a square `u²` is
instead a change of variables, `x ↦ u² x`, `y ↦ u³ y`, and so an isomorphism of point groups.

The scaled equations serve as normal forms for elliptic curves whose cubic splits: the curve
`y² = (x - e₀) (x - e₁) (x - e₂)` with distinct roots becomes, after the translation
`x ↦ x + e₀`, the scaled equation with `d = e₁ - e₀` and `l = (e₂ - e₀) / (e₁ - e₀)`. At
`l = -1` the Legendre equation is `y² = x³ - x`, the curve `TauCeti.CurveX3SubX.curve`.

## Main definitions

* `TauCeti.legendre`: the Legendre equation `y² = x (x - 1) (x - l)`.
* `TauCeti.scaledLegendre`: the scaled Legendre equation `y² = x (x - d) (x - d l)`.
* `TauCeti.scaledLegendrePointEquiv`: the isomorphism of point groups between the scaled
  equations with scalars `d` and `u² d`, sending `(x, y)` to `(u² x, u³ y)`.

## Main results

* `TauCeti.legendre_eq_freyCurve`, `TauCeti.scaledLegendre_eq_freyCurve`: the comparisons with
  the Frey–Hellegouarch curve.
* `TauCeti.equation_legendre_iff`, `TauCeti.equation_scaledLegendre_iff`: the factored affine
  equations.
* `TauCeti.legendre_Δ`, `TauCeti.legendre_c₄`, `TauCeti.scaledLegendre_Δ`,
  `TauCeti.scaledLegendre_c₄`: the discriminant and `c₄`.
* `TauCeti.isElliptic_legendre_iff_ne_zero`, `TauCeti.isElliptic_scaledLegendre_iff_ne_zero`:
  ellipticity over a field with `2 ≠ 0`; `TauCeti.isElliptic_legendre_iff` and
  `TauCeti.isElliptic_scaledLegendre_iff` are the criteria over a commutative ring.
* `TauCeti.legendre_j`, `TauCeti.scaledLegendre_j`: the `j`-invariant;
  `TauCeti.scaledLegendre_j_eq_legendre_j`: over a commutative ring it does not depend on the
  scalar.
* `TauCeti.quadraticTwistOf_legendre`, `TauCeti.scaledLegendre_eq_quadraticTwistOf`: the scaled
  equation is a quadratic twist of the Legendre equation.
* `TauCeti.smul_scaledLegendre`: scaling by `u⁻¹` carries the scalar `d` to `u² d`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1, for the Weierstrass
  invariants and the Legendre form.
* M. A. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short character
  sums*, Ann. of Math. 191 (2020), 355–392, §6, equation (17) and the proof of Lemma 6.6, for the
  scaled Legendre equation.
-/

public section

namespace TauCeti

open WeierstrassCurve

section CommRing

variable {R : Type*} [CommRing R]

/-- The **Legendre equation** `y² = x (x - 1) (x - l)`, that is `a₂ = -(1 + l)` and `a₄ = l`, the
other coefficients being `0`. It is defined for every `l`; at `l = 0` and `l = 1` its cubic has a
double root and its discriminant vanishes. -/
def legendre (l : R) : WeierstrassCurve R where
  a₁ := 0
  a₂ := -(1 + l)
  a₃ := 0
  a₄ := l
  a₆ := 0

/-- The **scaled Legendre equation** `y² = x (x - d) (x - d l)`, that is `a₂ = -d (1 + l)` and
`a₄ = d² l`, the other coefficients being `0`. The roots of its cubic are `0`, `d` and `d l`, in
this order. At `d = 0` all its coefficients vanish. -/
def scaledLegendre (d l : R) : WeierstrassCurve R where
  a₁ := 0
  a₂ := -(d * (1 + l))
  a₃ := 0
  a₄ := d ^ 2 * l
  a₆ := 0

variable (d l : R)

/-- The Legendre equation is in the normal form `a₁ = a₃ = 0`. -/
instance isCharNeTwoNF_legendre : (legendre l).IsCharNeTwoNF :=
  ⟨rfl, rfl⟩

/-- The scaled Legendre equation is in the normal form `a₁ = a₃ = 0`. -/
instance isCharNeTwoNF_scaledLegendre : (scaledLegendre d l).IsCharNeTwoNF :=
  ⟨rfl, rfl⟩

-- Through these instances, the coefficients `a₁ = a₃ = 0` are `a₁_of_isCharNeTwoNF` and
-- `a₃_of_isCharNeTwoNF`.
@[simp] theorem legendre_a₂ : (legendre l).a₂ = -(1 + l) := (rfl)
@[simp] theorem legendre_a₄ : (legendre l).a₄ = l := (rfl)
@[simp] theorem legendre_a₆ : (legendre l).a₆ = 0 := (rfl)

@[simp] theorem scaledLegendre_a₂ : (scaledLegendre d l).a₂ = -(d * (1 + l)) := (rfl)
@[simp] theorem scaledLegendre_a₄ : (scaledLegendre d l).a₄ = d ^ 2 * l := (rfl)
@[simp] theorem scaledLegendre_a₆ : (scaledLegendre d l).a₆ = 0 := (rfl)

/-- The scaled Legendre equation with scalar `1` is the Legendre equation. -/
@[simp]
theorem scaledLegendre_one : scaledLegendre 1 l = legendre l := by
  ext <;> simp

/-- The Legendre equation is the Frey–Hellegouarch curve `y² = x (x - A) (x + B)` at
`(A, B) = (1, -l)`. -/
theorem legendre_eq_freyCurve : legendre l = freyCurve 1 (-l) := by
  ext <;> simp
  ring

/-- The scaled Legendre equation is the Frey–Hellegouarch curve `y² = x (x - A) (x + B)` at
`(A, B) = (d, -d l)`. -/
theorem scaledLegendre_eq_freyCurve : scaledLegendre d l = freyCurve d (-(d * l)) := by
  ext <;> simp <;> ring

/-- At `l = -1` the Legendre equation is `y² = x³ - x`. -/
theorem legendre_neg_one : legendre (-1 : R) = CurveX3SubX.curve R := by
  ext <;> simp

/-- The image of a Legendre equation under a ring homomorphism is the Legendre equation of the
image. -/
@[simp]
theorem map_legendre {S : Type*} [CommRing S] (f : R →+* S) :
    (legendre l).map f = legendre (f l) := by
  ext <;> simp

/-- The image of a scaled Legendre equation under a ring homomorphism is the scaled Legendre
equation of the images. -/
@[simp]
theorem map_scaledLegendre {S : Type*} [CommRing S] (f : R →+* S) :
    (scaledLegendre d l).map f = scaledLegendre (f d) (f l) := by
  ext <;> simp

/-- The Legendre parameter is determined by the equation: it is the coefficient `a₄`. -/
theorem legendre_injective : Function.Injective (legendre : R → WeierstrassCurve R) :=
  fun _ _ h ↦ congrArg a₄ h

/-- Two Legendre equations are equal exactly when their parameters are. -/
@[simp]
theorem legendre_inj {l l' : R} : legendre l = legendre l' ↔ l = l' :=
  legendre_injective.eq_iff

/-- The affine points of the Legendre equation are the solutions of `y² = x (x - 1) (x - l)`. -/
theorem equation_legendre_iff (x y : R) :
    (legendre l).toAffine.Equation x y ↔ y ^ 2 = x * (x - 1) * (x - l) := by
  rw [Affine.equation_iff]
  simp only [a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF, legendre_a₂, legendre_a₄, legendre_a₆]
  constructor <;> intro h <;> linear_combination h

/-- The affine points of the scaled Legendre equation are the solutions of
`y² = x (x - d) (x - d l)`. -/
theorem equation_scaledLegendre_iff (x y : R) :
    (scaledLegendre d l).toAffine.Equation x y ↔ y ^ 2 = x * (x - d) * (x - d * l) := by
  rw [Affine.equation_iff]
  simp only [a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF, scaledLegendre_a₂, scaledLegendre_a₄,
    scaledLegendre_a₆]
  constructor <;> intro h <;> linear_combination h

/-! ### Invariants and ellipticity

The factored forms of `c₄` and `Δ` below are not `simp` lemmas: through the `IsCharNeTwoNF`
instances, `simp` already rewrites `c₄` and `Δ` by `c₄_of_isCharNeTwoNF` and `Δ_of_isCharNeTwoNF`
into polynomials in the coefficients. -/

/-- The `c₄` of the scaled Legendre equation is `16 d² (l² - l + 1)`. -/
theorem scaledLegendre_c₄ : (scaledLegendre d l).c₄ = 16 * d ^ 2 * (l ^ 2 - l + 1) := by
  rw [scaledLegendre_eq_freyCurve, freyCurve_c₄]
  ring

/-- The discriminant of the scaled Legendre equation is `16 d⁶ l² (1 - l)²`. -/
theorem scaledLegendre_Δ : (scaledLegendre d l).Δ = 16 * d ^ 6 * l ^ 2 * (1 - l) ^ 2 := by
  rw [scaledLegendre_eq_freyCurve, freyCurve_Δ]
  ring

/-- The `c₄` of the Legendre equation is `16 (l² - l + 1)`. -/
theorem legendre_c₄ : (legendre l).c₄ = 16 * (l ^ 2 - l + 1) := by
  rw [← scaledLegendre_one, scaledLegendre_c₄]
  ring

/-- The discriminant of the Legendre equation is `16 l² (1 - l)²`. -/
theorem legendre_Δ : (legendre l).Δ = 16 * l ^ 2 * (1 - l) ^ 2 := by
  rw [← scaledLegendre_one, scaledLegendre_Δ]
  ring

/-- **The scaled Legendre equation is elliptic exactly when `2 d l (l - 1)` is a unit.** Over a
commutative ring this is the right criterion, rather than nonvanishing of the factors; over a
field with `2 ≠ 0` it is `isElliptic_scaledLegendre_iff_ne_zero`. -/
theorem isElliptic_scaledLegendre_iff :
    (scaledLegendre d l).IsElliptic ↔ IsUnit (2 * d * l * (l - 1)) := by
  rw [isElliptic_iff, scaledLegendre_Δ,
    show (16 : R) * d ^ 6 * l ^ 2 * (1 - l) ^ 2 = 2 ^ 4 * d ^ 6 * l ^ 2 * (l - 1) ^ 2 by ring]
  simp only [IsUnit.mul_iff, isUnit_pow_iff (by norm_num : (4 : ℕ) ≠ 0),
    isUnit_pow_iff (by norm_num : (6 : ℕ) ≠ 0), isUnit_pow_iff (by norm_num : (2 : ℕ) ≠ 0)]

/-- **The Legendre equation is elliptic exactly when `2 l (l - 1)` is a unit.** -/
theorem isElliptic_legendre_iff : (legendre l).IsElliptic ↔ IsUnit (2 * l * (l - 1)) := by
  rw [← scaledLegendre_one, isElliptic_scaledLegendre_iff, mul_one]

/-- The quadratic twist of the Legendre equation by the parameters `(0, n)`, whose twisting
discriminant is `-4 n`, is the scaled Legendre equation with scalar `-4 n`. -/
theorem quadraticTwistOf_legendre (n : R) :
    (legendre l).quadraticTwistOf 0 n = scaledLegendre (-(4 * n)) l := by
  ext <;> simp
  ring

/-- If the scaled Legendre equation with some scalar is elliptic, so is the Legendre equation. -/
theorem isElliptic_legendre_of_scaledLegendre (h : (scaledLegendre d l).IsElliptic) :
    (legendre l).IsElliptic := by
  rw [isElliptic_scaledLegendre_iff] at h
  rw [isElliptic_legendre_iff]
  simp only [IsUnit.mul_iff] at h ⊢
  exact ⟨⟨h.1.1.1, h.1.2⟩, h.2⟩

/-- **The `j`-invariant of an elliptic scaled Legendre equation does not depend on the
scalar:** the scaled equation is a quadratic twist of the Legendre equation
(`quadraticTwistOf_legendre`), and `j` is a twist invariant (`j_quadraticTwistOf`). -/
theorem scaledLegendre_j_eq_legendre_j [(legendre l).IsElliptic]
    [(scaledLegendre d l).IsElliptic] : (scaledLegendre d l).j = (legendre l).j := by
  have h := (isElliptic_scaledLegendre_iff d l).mp ‹_›
  simp only [IsUnit.mul_iff] at h
  have h4 : IsUnit (4 : R) := by
    convert h.1.1.1.mul h.1.1.1
    norm_num
  have e : (legendre l).quadraticTwistOf 0 (-(d * ↑h4.unit⁻¹)) = scaledLegendre d l := by
    rw [quadraticTwistOf_legendre]
    congr 1
    linear_combination d * h4.mul_val_inv
  have : ((legendre l).quadraticTwistOf 0 (-(d * ↑h4.unit⁻¹))).IsElliptic := e ▸ ‹_›
  convert j_quadraticTwistOf (legendre l) 0 _ this using 2
  exact e.symm

/-- **The change of variables with scaling `u⁻¹` multiplies the scalar by `u²`.** It is
`x = u⁻² x'`, `y = u⁻³ y'`, so a point `(x, y)` of the scaled Legendre equation with scalar `d`
corresponds to the point `(u² x, u³ y)` of the one with scalar `u² d`. -/
theorem smul_scaledLegendre (u : Rˣ) :
    (⟨u⁻¹, 0, 0, 0⟩ : VariableChange R) • scaledLegendre d l = scaledLegendre (u ^ 2 * d) l := by
  ext <;> simp [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆] <;> ring

/-- A pair `(x, y)` is a nonsingular point of the scaled Legendre equation with scalar `d` exactly
when `(u² x, u³ y)` is a nonsingular point of the one with scalar `u² d`. -/
theorem nonsingular_scaledLegendre_mul_iff (u : Rˣ) (x y : R) :
    (scaledLegendre (u ^ 2 * d) l).toAffine.Nonsingular (u ^ 2 * x) (u ^ 3 * y) ↔
      (scaledLegendre d l).toAffine.Nonsingular x y := by
  rw [← smul_scaledLegendre, ← Affine.variableChange_nonsingular]
  simp [← mul_assoc, ← mul_pow]

end CommRing

section Field

variable {K : Type*} [Field K] (d l : K)

/-- **Over a field with `2 ≠ 0`, the scaled Legendre equation is elliptic exactly when `d`, `l`
and `l - 1` are nonzero.** -/
theorem isElliptic_scaledLegendre_iff_ne_zero (h2 : (2 : K) ≠ 0) :
    (scaledLegendre d l).IsElliptic ↔ d ≠ 0 ∧ l ≠ 0 ∧ l ≠ 1 := by
  simp [isElliptic_scaledLegendre_iff, h2, sub_eq_zero, and_assoc]

/-- **Over a field with `2 ≠ 0`, the Legendre equation is elliptic exactly when `l ≠ 0` and
`l ≠ 1`.** -/
theorem isElliptic_legendre_iff_ne_zero (h2 : (2 : K) ≠ 0) :
    (legendre l).IsElliptic ↔ l ≠ 0 ∧ l ≠ 1 := by
  simp [← scaledLegendre_one, isElliptic_scaledLegendre_iff_ne_zero _ _ h2]

/-- The `j`-invariant of an elliptic Legendre equation is
`256 (l² - l + 1)³ / (l² (1 - l)²)`. -/
@[simp]
theorem legendre_j [(legendre l).IsElliptic] :
    (legendre l).j = 256 * (l ^ 2 - l + 1) ^ 3 / (l ^ 2 * (1 - l) ^ 2) := by
  have : (freyCurve 1 (-l)).IsElliptic := legendre_eq_freyCurve l ▸ ‹_›
  convert freyCurve_j (1 : K) (-l) using 1
  · simp only [legendre_eq_freyCurve]
  · ring

/-- The `j`-invariant of an elliptic scaled Legendre equation is
`256 (l² - l + 1)³ / (l² (1 - l)²)`, whatever the scalar. -/
@[simp]
theorem scaledLegendre_j [(scaledLegendre d l).IsElliptic] :
    (scaledLegendre d l).j = 256 * (l ^ 2 - l + 1) ^ 3 / (l ^ 2 * (1 - l) ^ 2) := by
  have := isElliptic_legendre_of_scaledLegendre d l ‹_›
  rw [scaledLegendre_j_eq_legendre_j, legendre_j]

/-- **Over a field with `2 ≠ 0`, the scaled Legendre equation is a quadratic twist of the Legendre
equation:** the twist with parameters `(0, -d / 4)`, whose twisting discriminant is `d`. -/
theorem scaledLegendre_eq_quadraticTwistOf (h2 : (2 : K) ≠ 0) :
    scaledLegendre d l = (legendre l).quadraticTwistOf 0 (-(d / 4)) := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  rw [quadraticTwistOf_legendre, mul_neg, neg_neg, mul_div_cancel₀ d h4]

variable [DecidableEq K]

/-- **Scaling the scalar of a scaled Legendre equation by a square is an isomorphism of point
groups:** the point `(x, y)` of the equation with scalar `d` goes to the point `(u² x, u³ y)` of the
one with scalar `u² d` (`scaledLegendrePointEquiv_some`). It is induced by the change of variables
of `smul_scaledLegendre`. -/
noncomputable def scaledLegendrePointEquiv (u : Kˣ) :
    (scaledLegendre d l).toAffine.Point ≃+ (scaledLegendre (u ^ 2 * d) l).toAffine.Point :=
  (Affine.Point.addEquivVariableChange (scaledLegendre d l) ⟨u⁻¹, 0, 0, 0⟩).symm.trans
    (AddEquiv.cast (M := fun V : WeierstrassCurve K ↦ V.toAffine.Point)
      (smul_scaledLegendre d l u))

/-- What `scaledLegendrePointEquiv` does to a point given by coordinates. -/
@[simp]
theorem scaledLegendrePointEquiv_some (u : Kˣ) {x y : K}
    (h : (scaledLegendre d l).toAffine.Nonsingular x y) :
    scaledLegendrePointEquiv d l u (.some x y h) =
      .some (u ^ 2 * x) (u ^ 3 * y) ((nonsingular_scaledLegendre_mul_iff d l u x y).mpr h) := by
  rw [scaledLegendrePointEquiv, AddEquiv.trans_apply, AddEquiv.cast_apply,
    Affine.Point.coe_addEquivVariableChange_symm, Affine.Point.equivVariableChange_symm_some,
    Affine.Point.cast_some (smul_scaledLegendre d l u)]
  simp [VariableChange.inv_def]

end Field

end TauCeti
