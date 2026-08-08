/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula

/-!
# Transformation of the affine group-law formulae under a change of variables

Mathlib's `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean` develops `negY`, `addX`,
`negAddY`, `addY` and `slope` for a fixed Weierstrass curve. This file records how each of them,
together with `Equation`, `Nonsingular` and the Weierstrass polynomial and its two partial
derivatives, transforms under an admissible change of variables `C : VariableChange R`, which
carries a point `(x, y)` of `C • W` to the point `(u²x + r, u³y + u²sx + t)` of `W`.

Everything except the slope is stated over an arbitrary commutative ring, matching the
generality of Mathlib's `Formula` file; `↑C.u⁻¹ * ↑C.u = 1` is fed to `grobner` to cancel the unit.
Only `slope` needs a field.

These are the coordinate-level laws that
`TauCeti/AlgebraicGeometry/EllipticCurve/Affine/Point.lean` assembles into the induced
isomorphism of point groups, which is what the quadratic-twist layer of
`TauCetiRoadmap/EllipticCurves/README.md` (§Layer 5) consumes.

Adapted from the FLT project's quadratic-twist development (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`, FLT PR #1088, merged there as
`bc2fe8ff7396`, Apache 2.0, by Michael Stoll and Claude). Following the repository's convention
for adapted material, the source authorship is credited here rather than in the copyright
header. Ported with the transformation laws generalised from a field to a commutative ring and
the ellipticity hypothesis removed.

The cocycle laws `variableChange_X_mul`/`variableChange_Y_mul` and the base-change naturality
`variableChange_X_map`/`variableChange_Y_map` are not in the FLT source; they follow
`ModularCurves/ForMathlib/AffinePointVariableChange.lean` (`vcX_comp`, `vcY_comp`, `vcX_map`,
`vcY_map`) in `CBirkbeck/AINTLIB` (Apache 2.0, by Chris Birkbeck), restated here for the
`(x, y) ↦ (u²x + r, u³y + u²sx + t)` direction this file uses.
-/

public section

namespace WeierstrassCurve.Affine

/-! ### Transformation of the group-law formulae under a change of variables

Exactly six laws are registered as `simp` lemmas: `variableChange_addY`, the three
`variableChange_evalEval_*`, `variableChange_equation` and `variableChange_nonsingular`. The
others are deliberately not. `variableChange_negY`, `variableChange_addX`,
`variableChange_negAddY` and `variableChange_X_inj` have left-hand sides that `simp` rewrites
first — the first three are headed by `negY`, `addX` and `negAddY`, which `simp` unfolds, and
the fourth is cancelled by `add_left_inj` — so those sides are never in simp-normal form and the
`simpNF` linter rejects the attribute. `variableChange_Y_inj`, `variableChange_negY_ne` and
`variableChange_slope` are conditional rather than unconditional normalisation laws.

Throughout, the change of variables carries a point `(x, y)` of `C • W` to the point
`(u²x + r, u³y + u²sx + t)` of `W`. Every law here except the three slope laws is stated over an
arbitrary commutative ring, with `↑C.u⁻¹ * ↑C.u = 1` fed to `grobner` to cancel the unit; the
slope laws need a field, since `slope` itself is only defined over one. -/

section Ring

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (C : VariableChange R)

/-- The change of variables intertwines negation: `negY` of the image point is the image of
`negY` of the original point. -/
lemma variableChange_negY (x y : R) :
    W.toAffine.negY ((C.u : R) ^ 2 * x + C.r)
        ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      = (C.u : R) ^ 3 * (C • W).toAffine.negY x y + (C.u : R) ^ 2 * C.s * x + C.t := by
  have hu := C.u.inv_mul
  simp only [negY, variableChange_a₁, variableChange_a₃]
  grobner

/-- The change of variables intertwines the `x`-coordinate of addition: `addX` of the image
points along the transformed slope is the image of `addX` of the original points. -/
lemma variableChange_addX (x₁ x₂ ℓ : R) :
    W.toAffine.addX ((C.u : R) ^ 2 * x₁ + C.r) ((C.u : R) ^ 2 * x₂ + C.r) ((C.u : R) * ℓ + C.s)
      = (C.u : R) ^ 2 * (C • W).toAffine.addX x₁ x₂ ℓ + C.r := by
  have hu := C.u.inv_mul
  simp only [addX, variableChange_a₁, variableChange_a₂]
  grobner

/-- The change of variables intertwines the negated `y`-coordinate of addition (`negAddY`). -/
lemma variableChange_negAddY (x₁ x₂ y₁ ℓ : R) :
    W.toAffine.negAddY ((C.u : R) ^ 2 * x₁ + C.r) ((C.u : R) ^ 2 * x₂ + C.r)
        ((C.u : R) ^ 3 * y₁ + (C.u : R) ^ 2 * C.s * x₁ + C.t) ((C.u : R) * ℓ + C.s)
      = (C.u : R) ^ 3 * (C • W).toAffine.negAddY x₁ x₂ y₁ ℓ
        + (C.u : R) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp only [negAddY]
  rw [variableChange_addX]
  ring1

/-- The change of variables intertwines the `y`-coordinate of addition (`addY`). -/
@[simp] lemma variableChange_addY (x₁ x₂ y₁ ℓ : R) :
    W.toAffine.addY ((C.u : R) ^ 2 * x₁ + C.r) ((C.u : R) ^ 2 * x₂ + C.r)
        ((C.u : R) ^ 3 * y₁ + (C.u : R) ^ 2 * C.s * x₁ + C.t) ((C.u : R) * ℓ + C.s)
      = (C.u : R) ^ 3 * (C • W).toAffine.addY x₁ x₂ y₁ ℓ
        + (C.u : R) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp only [addY, variableChange_negAddY, variableChange_addX, variableChange_negY]

/-- The Weierstrass polynomial at the image point is `u⁶` times that of `C • W` at the original
point. This is the scaling law behind `variableChange_equation`, and the companion of the
two partial-derivative laws below. -/
@[simp] lemma variableChange_evalEval_polynomial (x y : R) :
    W.toAffine.polynomial.evalEval ((C.u : R) ^ 2 * x + C.r)
        ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      = (C.u : R) ^ 6 * (C • W).toAffine.polynomial.evalEval x y := by
  have hu := C.u.inv_mul
  simp only [evalEval_polynomial, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆]
  grobner

/-- A point `(x, y)` lies on `C • W` if and only if `(u²x + r, u³y + u²sx + t)` lies on `W`: the
change of variables scales the Weierstrass polynomial by `u⁶`. -/
@[simp] lemma variableChange_equation (x y : R) :
    W.toAffine.Equation ((C.u : R) ^ 2 * x + C.r)
        ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      ↔ (C • W).toAffine.Equation x y := by
  unfold Equation
  rw [variableChange_evalEval_polynomial]
  exact (C.u.isUnit.pow 6).mul_right_eq_zero

/-- The partial derivative `∂/∂y` of the Weierstrass polynomial at the image point is `u³` times
that of `C • W` at the original point. -/
@[simp] lemma variableChange_evalEval_polynomialY (x y : R) :
    W.toAffine.polynomialY.evalEval ((C.u : R) ^ 2 * x + C.r)
        ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      = (C.u : R) ^ 3 * (C • W).toAffine.polynomialY.evalEval x y := by
  have hu := C.u.inv_mul
  simp only [evalEval_polynomialY, variableChange_a₁, variableChange_a₃]
  grobner

/-- The partial derivative `∂/∂x` of the Weierstrass polynomial at the image point, in terms of
the two partial derivatives of `C • W` at the original point (the chain rule for the change of
variables). -/
@[simp] lemma variableChange_evalEval_polynomialX (x y : R) :
    W.toAffine.polynomialX.evalEval ((C.u : R) ^ 2 * x + C.r)
        ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      = (C.u : R) ^ 4 * (C • W).toAffine.polynomialX.evalEval x y
        - C.s * ((C.u : R) ^ 3 * (C • W).toAffine.polynomialY.evalEval x y) := by
  have hu := C.u.inv_mul
  simp only [evalEval_polynomialX, evalEval_polynomialY, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄]
  grobner

/-- A point `(x, y)` is a nonsingular point of `C • W` if and only if its image
`(u²x + r, u³y + u²sx + t)` is a nonsingular point of `W`. This holds for an arbitrary
Weierstrass curve over a commutative ring — no ellipticity hypothesis. -/
@[simp] lemma variableChange_nonsingular (x y : R) :
    W.toAffine.Nonsingular ((C.u : R) ^ 2 * x + C.r)
        ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      ↔ (C • W).toAffine.Nonsingular x y := by
  have hX := variableChange_evalEval_polynomialX W C x y
  have hY := variableChange_evalEval_polynomialY W C x y
  unfold Nonsingular
  rw [variableChange_equation, hX, hY]
  refine and_congr_right fun _ ↦ ?_
  rcases eq_or_ne ((C • W).toAffine.polynomialY.evalEval x y) 0 with hy | hy
  · simp only [hy, mul_zero, sub_zero, ne_eq, (C.u.isUnit.pow 4).mul_right_eq_zero]
  · exact iff_of_true (.inr fun h ↦ hy ((C.u.isUnit.pow 3).mul_right_eq_zero.mp h)) (.inr hy)

/-- **Cocycle law for the `x`-coordinate.** Composing changes of variables composes their
coordinate maps: `Φ_{C * C'} = Φ_{C'} ∘ Φ_C`. -/
lemma variableChange_X_mul (C' : VariableChange R) (x : R) :
    ((C * C').u : R) ^ 2 * x + (C * C').r
      = (C'.u : R) ^ 2 * ((C.u : R) ^ 2 * x + C.r) + C'.r := by
  simp only [VariableChange.mul_def, Units.val_mul]
  ring

/-- **Cocycle law for the `y`-coordinate.** -/
lemma variableChange_Y_mul (C' : VariableChange R) (x y : R) :
    ((C * C').u : R) ^ 3 * y + ((C * C').u : R) ^ 2 * (C * C').s * x + (C * C').t
      = (C'.u : R) ^ 3 * ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
        + (C'.u : R) ^ 2 * C'.s * ((C.u : R) ^ 2 * x + C.r) + C'.t := by
  simp only [VariableChange.mul_def, Units.val_mul]
  ring

/-- **Naturality in the base ring** for the `x`-coordinate: the coordinate map commutes with a
ring homomorphism, so it is compatible with base change. -/
lemma variableChange_X_map {A : Type*} [CommRing A] (φ : R →+* A) (x : R) :
    ((C.map φ).u : A) ^ 2 * φ x + (C.map φ).r = φ ((C.u : R) ^ 2 * x + C.r) := by
  simp [VariableChange.map_u, VariableChange.map_r]

/-- **Naturality in the base ring** for the `y`-coordinate. -/
lemma variableChange_Y_map {A : Type*} [CommRing A] (φ : R →+* A) (x y : R) :
    ((C.map φ).u : A) ^ 3 * φ y + ((C.map φ).u : A) ^ 2 * (C.map φ).s * φ x + (C.map φ).t
      = φ ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t) := by
  simp [VariableChange.map_u, VariableChange.map_s, VariableChange.map_t]

/-- The change of variables is injective on `x`-coordinates: `u²x + r` determines `x`. -/
lemma variableChange_X_inj {x₁ x₂ : R} :
    (C.u : R) ^ 2 * x₁ + C.r = (C.u : R) ^ 2 * x₂ + C.r ↔ x₁ = x₂ :=
  ⟨fun h ↦ (C.u.isUnit.pow 2).mul_right_inj.mp (add_right_cancel h), fun h ↦ by rw [h]⟩

/-- The change of variables is injective on `y`-coordinates once the `x`-coordinates agree. -/
lemma variableChange_Y_inj {x₁ x₂ y₁ y₂ : R} (hx : x₁ = x₂) :
    (C.u : R) ^ 3 * y₁ + (C.u : R) ^ 2 * C.s * x₁ + C.t
      = (C.u : R) ^ 3 * y₂ + (C.u : R) ^ 2 * C.s * x₂ + C.t ↔ y₁ = y₂ := by
  subst hx
  exact ⟨fun h ↦ (C.u.isUnit.pow 3).mul_right_inj.mp (add_right_cancel (add_right_cancel h)),
    fun h ↦ by rw [h]⟩

/-- The image of a pair of points under the change of variables satisfies the `y₁ = -y₂`
degeneracy condition (`negY`) only if the original pair does. -/
lemma variableChange_negY_ne {x₁ x₂ y₁ y₂ : R}
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    ¬((C.u : R) ^ 2 * x₁ + C.r = (C.u : R) ^ 2 * x₂ + C.r ∧
      (C.u : R) ^ 3 * y₁ + (C.u : R) ^ 2 * C.s * x₁ + C.t = W.toAffine.negY
        ((C.u : R) ^ 2 * x₂ + C.r) ((C.u : R) ^ 3 * y₂ + (C.u : R) ^ 2 * C.s * x₂ + C.t)) := by
  rintro ⟨hX, hY⟩
  obtain rfl := (variableChange_X_inj C).mp hX
  rw [variableChange_negY] at hY
  exact hxy ⟨rfl, (variableChange_Y_inj C rfl).mp hY⟩

end Ring

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (C : VariableChange F)

/-- **Secant case.** For distinct `x`-coordinates the change of variables scales the slope
affinely: the secant through the image points is `u · ℓ + s`. -/
lemma variableChange_slope_of_X_ne [DecidableEq F] {x₁ x₂ y₁ y₂ : F} (hx : x₁ ≠ x₂) :
    W.toAffine.slope ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t)
        ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)
      = (C.u : F) * (C • W).toAffine.slope x₁ x₂ y₁ y₂ + C.s := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  have hΦx : (C.u : F) ^ 2 * x₁ + C.r ≠ (C.u : F) ^ 2 * x₂ + C.r :=
    fun h ↦ hx ((variableChange_X_inj C).mp h)
  rw [W.toAffine.slope_of_X_ne hΦx, (C • W).toAffine.slope_of_X_ne hx]
  have h1 := sub_ne_zero.mpr hΦx
  have h2 := sub_ne_zero.mpr hx
  field

/-- **Tangent case.** At a point that is not its own negative the change of variables scales the
tangent slope affinely. Both slopes are `-∂x/∂y`, and the change of variables scales the two
partial derivatives by `u⁴` (up to a multiple of `∂y`) and `u³`. -/
lemma variableChange_slope_of_Y_ne [DecidableEq F] {x₁ y₁ : F}
    (hy : y₁ ≠ (C • W).toAffine.negY x₁ y₁) :
    W.toAffine.slope ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₁ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t)
      = (C.u : F) * (C • W).toAffine.slope x₁ x₁ y₁ y₁ + C.s := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  have hΦy := fun h ↦ variableChange_negY_ne W C (fun hc ↦ hy hc.2) ⟨rfl, h⟩
  have hPY : (C • W).toAffine.polynomialY.evalEval x₁ y₁ ≠ 0 := by
    rw [evalEval_polynomialY]
    exact fun h ↦ hy (by rw [negY]; linear_combination h)
  rw [W.toAffine.slope_of_Y_ne_eq_evalEval rfl hΦy,
    (C • W).toAffine.slope_of_Y_ne_eq_evalEval rfl hy,
    variableChange_evalEval_polynomialX, variableChange_evalEval_polynomialY]
  field

/-- The change of variables transforms the slope of the line through two points affinely:
the slope through the image points is `u · ℓ + s` for `ℓ` the original slope. -/
lemma variableChange_slope [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
    (h₁ : (C • W).toAffine.Equation x₁ y₁) (h₂ : (C • W).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    W.toAffine.slope ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t)
        ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)
      = (C.u : F) * (C • W).toAffine.slope x₁ x₂ y₁ y₂ + C.s := by
  rcases eq_or_ne x₁ x₂ with rfl | hx
  · have hy : y₁ ≠ (C • W).toAffine.negY x₁ y₂ := fun h ↦ hxy ⟨rfl, h⟩
    obtain rfl := Y_eq_of_Y_ne h₁ h₂ rfl hy
    exact variableChange_slope_of_Y_ne W C hy
  · exact variableChange_slope_of_X_ne W C hx

end WeierstrassCurve.Affine

end
