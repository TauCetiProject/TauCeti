/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
public import TauCeti.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Tactic.DeriveFintype

/-!
# The universal elliptic curve

This file defines the universal Weierstrass curve (`Universal.curve`) over the
polynomial ring `ℤ[A₁,A₂,A₃,A₄,A₆]`, and its base change `Universal.pointedCurve`, an elliptic curve
with distinguished point `(X,Y)`, over the field of fractions (`Universal.Field`) of
`Universal.Ring = Universal.Poly/⟨P⟩ = ℤ[A₁,A₂,A₃,A₄,A₆,X,Y]/⟨P⟩` (where `P` is the Weierstrass
polynomial). `Universal.Ring` classifies Weierstrass curves together with an affine point
(`ringEval`), and `pointedCurve` is the generic such curve over its fraction field.

It also defines the universal elliptic Weierstrass curve (`Universal.ellipticCurve`) over
`Universal.EllipticRing = ℤ[A₁,A₂,A₃,A₄,A₆][Δ⁻¹]`, the polynomial ring localised away from the
discriminant `Δ` of the universal curve, and the classifying homomorphism
(`WeierstrassCurve.specializeElliptic`) along which an elliptic Weierstrass curve over any
commutative ring is the base change of that curve.

## Main definitions

* `WeierstrassCurve.Universal.curve`: the universal Weierstrass curve, over `ℤ[A₁,⋯,A₆]`.
* `WeierstrassCurve.Universal.Poly`, `.Ring`, `.Field`: the polynomial ring `ℤ[A₁,⋯,A₆,X,Y]`, its
  quotient by the Weierstrass polynomial, and that quotient's field of fractions; `polyToField` is
  the composite `Poly →+* Field`.
* `WeierstrassCurve.Universal.pointedCurve`: the universal curve over `Universal.Field`. It is an
  elliptic curve, and carries the distinguished point `Universal.Affine.point`
  (`Universal.Jacobian.point` in Jacobian coordinates).
* `WeierstrassCurve.specialize`: for a Weierstrass curve `W` over a commutative ring `R`, the
  specialization homomorphism `ℤ[A₁,⋯,A₆] →+* R` substituting `W`'s coefficients.
* `WeierstrassCurve.Universal.polyEval`, `.ringEval`: the homomorphism `Universal.Poly →+* R`
  induced by a point `(x,y)` of the affine plane, and its factorisation `Universal.Ring →+* R`
  through the Weierstrass polynomial when `(x,y)` lies on `W`.
* `WeierstrassCurve.Universal.EllipticRing`: the ring `ℤ[A₁,⋯,A₆][Δ⁻¹]`, a Noetherian integral
  domain.
* `WeierstrassCurve.Universal.ellipticCurve`: the universal curve over `Universal.EllipticRing`. It
  is an elliptic curve.
* `WeierstrassCurve.specializeElliptic`: for an elliptic Weierstrass curve `W` over a commutative
  ring `R`, the classifying homomorphism `ℤ[A₁,⋯,A₆][Δ⁻¹] →+* R` extending `W.specialize`.

## Main results

* `WeierstrassCurve.Universal.polyToField_polynomial`: the Weierstrass polynomial vanishes in
  `Universal.Field` — the relation `Universal.Ring` is the quotient by.
* `WeierstrassCurve.Universal.equation_point`: `(X,Y)` satisfies the affine Weierstrass equation
  of `pointedCurve` — the universal curve really is pointed.
* `WeierstrassCurve.map_specialize`: every Weierstrass curve is a specialization of the universal
  one.
* `WeierstrassCurve.specialize_Δ`: `specialize` sends the discriminant of the universal curve to
  the discriminant of `W`.
* `WeierstrassCurve.Universal.map_ringEval`: pushing the universal curve over
  `Universal.Ring` along `ringEval` returns `W`, so one identity **over `curveRing`** is the same
  identity for every curve and every point on it. Note the restriction: `ringEval` maps out of
  `Universal.Ring`, so it transports identities over `curveRing`, not over `pointedCurve`, which
  lives over `Universal.Field`. An identity stated there needs its denominators cleared into
  `Universal.Ring` first.
* `WeierstrassCurve.Universal.map_polyToField`: `curvePoly` pushed along `polyToField` is
  `pointedCurve`, so a Jacobian formula transported from `Poly` lands on `pointedCurve` rather than
  on an unreduced base change.
* `WeierstrassCurve.map_specializeElliptic`: every elliptic Weierstrass curve is the base change of
  `Universal.ellipticCurve` along its classifying homomorphism.
* `WeierstrassCurve.specializeElliptic_map_ellipticCurve`: a homomorphism out of
  `Universal.EllipticRing` is the classifying homomorphism of the curve it produces, so the
  classifying homomorphism is unique. `WeierstrassCurve.Universal.EllipticRing.ringHom_ext` is the
  extensionality behind it: the images of the five indeterminates determine the homomorphism.
* `WeierstrassCurve.specializeElliptic_map`: the classifying homomorphism is natural in the base
  ring.
* `WeierstrassCurve.exists_map_eq_of_isElliptic`: an elliptic Weierstrass curve over a commutative
  ring in `Type u` is the base change of an elliptic Weierstrass curve over a Noetherian integral
  domain in `Type u`.
* `WeierstrassCurve.exists_map_eq_and_map_eq_of_isElliptic`: the same holds for an elliptic
  Weierstrass curve together with a change of variables.

## Implementation notes

The cusp curve `Y² = X³` carries the rational point `(1,1)`, with the nice property that
`ψₙ(1,1) = n`. Specializing along it is therefore the cheap route to nonvanishing of the universal
`ψₙ` for `n ≠ 0`, which shows that `(X,Y)` is a point of infinite order on
`pointedCurve`. The `CharZero Universal.Ring` instance is the first use of that argument.

## Provenance

Ported from J. Xu's `LutzNagell/Universal.lean` in AINTLIB (`github.com/CBirkbeck/AINTLIB`,
Apache 2.0, `main` at `1c1c7466`, `projects/NagellLutz/LutzNagell/Universal.lean`), whose header
reads `Authors: Junyan Xu`. **Most** declarations here come from that file: the `Coeff` index type
and the bulk of the `Universal` namespace (`curve`, `Poly`, `Ring`, `Field`, `polyToField`,
`pointedCurve`, `Affine.point`, `Jacobian.point`, `curvePoly` and `curveRing` with their lemmas),
and the specialization API (`specialize`, `polyEval`, `ringEval` with their compatibility lemmas).
`map_polyToField` is new; upstream that identity is definitional. The `CharZero Universal.Ring`
instance replaces the source's `Poly.two_ne_zero` and `Field.two_ne_zero`, and Mathlib derives
`CharZero Universal.Field` from it through `IsFractionRing.charZero`. The source's three opening
lemmas, `CoordinateRing.algebraMap_poly_injective`, `CoordinateRing.algebraMap_injective'` and
`Affine.Point.some_eq_some_iff`, are not ported: the first two are
`FaithfulSMul.algebraMap_injective` for Mathlib's `FaithfulSMul` instances on the coordinate ring,
and the third is the `Iff` form of the auto-generated `some.injEq`.

The section on the universal elliptic Weierstrass curve has a second source: the ModularCurves
project of AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache 2.0, commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, under `projects/ModularCurves/ModularCurves/`). Adapted
from it are `WeierstrassAtlasRing` with its `IsDomain` and `IsNoetherianRing` instances and
`universalWeierstrassLoc` with its `IsElliptic` instance (`Moduli/WeierstrassAtlas.lean`),
`classifyRingHom` and `universalWeierstrassLoc_map_classifyRingHom`
(`EllipticCurve/WeierstrassAtlasBundle.lean`), `classifyRingHom_map` and
`classifyRingHom_universalWeierstrassLoc` (`EllipticCurve/AdditionBaseChange.lean`), and
`ringHomOfEllipticW_ellipticWOfRingHom` (`Moduli/MellWeierstrass.lean`). Those headers read
`Authors: Chris Birkbeck`, except that of `WeierstrassAtlasBundle.lean`, which reads
`Authors: The AINTLIB Authors`.

The source builds these on a second universal curve, `universalWeierstrass` over
`MvPolynomial (Fin 5) ℤ`, with its own coefficient maps `classifyCoeffHom` and `specializeAt`. Here
they are built on this file's `Universal.curve` and `specialize`, so there is one universal curve
and `specializeElliptic` extends `specialize`. `EllipticRing.ringHom_ext` is new: the source repeats
`IsLocalization.ringHom_ext` and `MvPolynomial.ringHom_ext` inside each proof.
`specializeElliptic_map` and `specializeElliptic_ellipticCurve` are corollaries of
`specializeElliptic_map_ellipticCurve` rather than separate computations, and
`specializeElliptic_map` takes the ellipticity of `W.map f` from Mathlib's instance instead of a
second hypothesis. The Noetherian instance is not declared: instance search derives it from
Mathlib's instances once `Coeff` is a `Fintype`. The source's `ULift` copies in higher universes
(`WeierstrassAtlasRingU`, `universalWeierstrassLocU` and `classifyRingHomU`, in
`EllipticCurve/AdditionBaseChange.lean`) are not ported as declarations. In their place,
`exists_map_eq_of_isElliptic` states only that such a ring, curve and homomorphism exist. It is
adapted from those three, from the `IsDomain` instance on `WeierstrassAtlasRingU` and
`universalWeierstrassLocU_map_classifyRingHomU` (same file), and from the `IsNoetherianRing`
instance on `WeierstrassAtlasRingU` (`EllipticCurve/GroupLawAxioms.lean`, whose header reads
`Authors: The AINTLIB Authors`).
-/

public section

noncomputable section

/-! ## The universal Weierstrass curve -/

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

/-- A type whose elements represent the five coefficients `a₁`, `a₂`, `a₃`, `a₄` and `a₆` of the
Weierstrass polynomial. It indexes the variables of `MvPolynomial Coeff ℤ = ℤ[A₁,⋯,A₆]`, the ring
the universal curve is defined over. There is no `A₅` — the subscripts are weights, not positions —
and the constructors are uppercase as names of indeterminates: `specialize` sends `A₁` to `W.a₁`. -/
inductive Coeff : Type | A₁ : Coeff | A₂ : Coeff | A₃ : Coeff | A₄ : Coeff | A₆ : Coeff

-- `deriving Fintype` fails on this enumeration, so the instance comes from `derive_fintype%`.
/-- The five coefficient indices form a finite type, so `ℤ[A₁,⋯,A₆]` and its localisations are
Noetherian rings. -/
instance : Fintype Coeff := derive_fintype% _

namespace Universal

open Coeff

open MvPolynomial (X) in
/-- The universal Weierstrass curve: the curve over `ℤ[A₁,⋯,A₆] = MvPolynomial Coeff ℤ` (the
**universal polynomial ring** for Weierstrass curves) whose five coefficients are the five
indeterminates. Every Weierstrass curve is one of its specializations (`map_specialize`); its base
changes are `curvePoly`, `curveRing` and `pointedCurve`. -/
def curve : Affine (MvPolynomial Coeff ℤ) :=
  { a₁ := X A₁, a₂ := X A₂, a₃ := X A₃, a₄ := X A₄, a₆ := X A₆ }

open MvPolynomial (X) in
/-- The `a₁` coefficient of the universal curve is the indeterminate `A₁`, and likewise for `A₂`
through `A₆`. The definition body is unexposed, so these are how a consumer normalises a coefficient
of `curve` inside a polynomial identity. -/
@[simp] lemma curve_a₁ : curve.a₁ = X A₁ := (rfl)
open MvPolynomial (X) in
/-- The `a₂` coefficient of the universal curve is the indeterminate `A₂`. -/
@[simp] lemma curve_a₂ : curve.a₂ = X A₂ := (rfl)
open MvPolynomial (X) in
/-- The `a₃` coefficient of the universal curve is the indeterminate `A₃`. -/
@[simp] lemma curve_a₃ : curve.a₃ = X A₃ := (rfl)
open MvPolynomial (X) in
/-- The `a₄` coefficient of the universal curve is the indeterminate `A₄`. -/
@[simp] lemma curve_a₄ : curve.a₄ = X A₄ := (rfl)
open MvPolynomial (X) in
/-- The `a₆` coefficient of the universal curve is the indeterminate `A₆`. -/
@[simp] lemma curve_a₆ : curve.a₆ = X A₆ := (rfl)

/-- The discriminant of the universal Weierstrass curve is a nonzero polynomial in `ℤ[A₁,⋯,A₆]`,
i.e. a Weierstrass equation is not singular *identically* in its coefficients. Transported along
the injective `algebraMap` into `Universal.Field`, this is what makes `pointedCurve` elliptic over
`Universal.Field`. -/
lemma curve_Δ_ne_zero : curve.Δ ≠ 0 :=
  -- specialize `A₆ ↦ 1` and the rest to `0`: the curve `Y² = X³ + 1`, whose `Δ` is `-432`
  ne_of_apply_ne (MvPolynomial.eval (Coeff.rec 0 0 0 0 1)) <| by simp [Δ, b₂, b₄, b₆, b₈, curve]

/-- The polynomial ring `ℤ[A₁,A₂,A₃,A₄,A₆,X,Y]`: two variables adjoined to the universal polynomial
ring `ℤ[A₁,⋯,A₆]`, in Mathlib's iterated form `R[X][Y]`, so `Y` is the outer variable. The
Weierstrass polynomial `curve.polynomial` lives here; `Universal.Ring` is the quotient by it. -/
abbrev Poly : Type := (MvPolynomial Coeff ℤ)[X][Y]
/-- The universal ring for **pointed** Weierstrass curves: `ℤ[A₁,⋯,A₆,X,Y]/⟨P⟩`, for `P` the
Weierstrass polynomial. A Weierstrass curve over `R` together with an affine point on it determines
a ring homomorphism out of it — `ringEval` — and determines it uniquely, since the coefficients and
the two coordinates generate (Mathlib's `AdjoinRoot.ringHom_ext`, through which `ext` reduces to
them). Being an `abbrev` for `curve.CoordinateRing`, it inherits Mathlib's `Affine.CoordinateRing`
API. -/
protected abbrev Ring : Type := curve.CoordinateRing
/-- The field of fractions of the universal ring `Universal.Ring`, over which `pointedCurve` is
defined. -/
protected abbrev Field : Type := FractionRing Universal.Ring

/-- The ring homomorphism `ℤ[A₁,⋯,A₆,X,Y] → Universal.Field`: reduce modulo the Weierstrass
polynomial, then include the universal ring into its fraction field. Every statement about
`pointedCurve` is ultimately about the images of `X` and `Y` under this map. -/
def polyToField : Poly →+* Universal.Field :=
  (algebraMap Universal.Ring _).comp <| AdjoinRoot.mk _

/-- `polyToField` is reduction modulo the Weierstrass polynomial followed by the inclusion into
the fraction field. -/
@[simp]
lemma polyToField_apply (p : Poly) :
    polyToField p = algebraMap Universal.Ring _ (AdjoinRoot.mk _ p) := (rfl)

/-- **The Weierstrass polynomial vanishes in `Universal.Field`.** It is exactly the element
`Universal.Ring` quotients out, so `polyToField` kills it — which is how an identity over
`pointedCurve` discards the multiples of `curve.polynomial` that clearing denominators throws up. -/
-- Not `@[simp]`, unlike upstream: `polyToField_apply` is `@[simp]` here, so `simp` already reaches
-- `0` on its own and a full-library `lint-env` run rejects the tag as a simpNF duplicate.
lemma polyToField_polynomial : polyToField curve.polynomial = 0 := by
  rw [polyToField_apply, AdjoinRoot.mk_self, map_zero]

/-- The structure map of `Universal.Field` over the coefficient ring factors through `Poly`: the
coefficients `A₁,⋯,A₆` reach `Universal.Field` by the same route as `X` and `Y` do. Rewriting
with this turns a statement about `algebraMap` into one about `polyToField`. -/
lemma algebraMap_field_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) Universal.Field = polyToField.comp (algebraMap _ _) := (rfl)

/-- The `Universal.Ring` counterpart of `algebraMap_field_eq_comp`: the structure map from the
coefficient ring is the inclusion `ℤ[A₁,⋯,A₆] → Poly` followed by the quotient map. -/
lemma algebraMap_ring_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) Universal.Ring = (AdjoinRoot.mk _).comp (algebraMap _ _) :=
  (rfl)

/-- The generic pointed Weierstrass curve: the universal curve base-changed to `Universal.Field`,
over which it is an elliptic curve (instance below) carrying the distinguished point `(X, Y)`
(`equation_point`, packaged as `Affine.point`). Pointed curves are classified by `Universal.Ring`
(`ringEval`): an identity over `pointedCurve` reaches other curves once its denominators are
cleared into `Universal.Ring`. It is the third of the base changes `curvePoly`, `curveRing`,
`pointedCurve`. -/
abbrev pointedCurve : WeierstrassCurve Universal.Field := baseChange curve Universal.Field

/-- The discriminant of `pointedCurve` is the image of `curve.Δ`. Rewrite with this in place of
Mathlib's `map_Δ`, which `simp` and `rw` do not apply to `pointedCurve.Δ` on their own, since
neither unfolds `baseChange`. -/
@[simp]
lemma pointedCurve_Δ : pointedCurve.Δ = algebraMap _ Universal.Field curve.Δ :=
  map_Δ curve (algebraMap _ Universal.Field)

/-- `pointedCurve` is an elliptic curve: its discriminant is a unit, because `Δ` of the universal
curve is a nonzero polynomial and the coefficient ring embeds in `Universal.Field`. -/
instance : pointedCurve.IsElliptic where
  isUnit := by
    rw [pointedCurve_Δ]
    exact ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr curve_Δ_ne_zero).isUnit

open Polynomial in
/-- The pair `(X, Y)` — the images of the two adjoined variables in `Universal.Field` — satisfies
the affine Weierstrass equation of `pointedCurve`. This is what makes `pointedCurve` *pointed*;
`Affine.point` packages it as an element of the point group. -/
lemma equation_point : pointedCurve.toAffine.Equation (polyToField (C X)) (polyToField Y) := by
  -- Two steps at once, and neither is a rewrite: unfold `Equation` to its defining
  -- `evalEval _ _ polynomial = 0` (Mathlib's `equation_iff'` expands to the coefficient form
  -- instead, which is not what the argument below needs), and present `pointedCurve` as
  -- `curve.map (algebraMap _ _)` so that `Affine.map_polynomial` applies. The two curves are
  -- definitionally equal — `pointedCurve` is `baseChange curve Universal.Field` — so `change`
  -- is the step, not a `rw`.
  change evalEval (polyToField (C X)) (polyToField Y)
    ((curve.map (algebraMap _ Universal.Field)).toAffine.polynomial) = 0
  have h : (evalEvalRingHom (polyToField (C X)) (polyToField Y)).comp
      (mapRingHom <| mapRingHom (algebraMap _ Universal.Field)) = polyToField := by
    ext <;> simp [polyToField, algebraMap_field_eq_comp]
  have : ∀ p, evalEval (polyToField (C X)) (polyToField Y)
      (p.map (mapRingHom (algebraMap _ Universal.Field))) = polyToField p :=
    fun p ↦ congr($h p)
  -- The Weierstrass polynomial vanishes at `(X, Y)`: it is exactly what was quotiented out.
  rw [Affine.map_polynomial, this, polyToField_polynomial]

/-- The distinguished point `(X, Y)` on `pointedCurve`. -/
def Affine.point : (curve.baseChange Universal.Field).toAffine.Point :=
  .mk equation_point

/-- The affine distinguished point is `equation_point` packaged as a point of the group. The
definition body is not exposed, so this equation lemma is how a consumer recovers it. -/
@[simp]
theorem Affine.point_def : Affine.point = .mk equation_point := (rfl)

/-- The distinguished point `(X, Y)` on `pointedCurve`, in Jacobian coordinates. -/
def Jacobian.point : Jacobian.Point (curve.baseChange Universal.Field) :=
  Jacobian.Point.fromAffine Affine.point

/-- The Jacobian distinguished point is the affine one, moved along `fromAffine`. -/
@[simp]
theorem Jacobian.point_def : Jacobian.point = Jacobian.Point.fromAffine Affine.point := (rfl)

open Polynomial (CC)

/-- The `a₁` coefficient of `pointedCurve` is the image of the indeterminate `A₁` in
`Universal.Field`, read through `polyToField`; likewise `pointedCurve_a₂` through
`pointedCurve_a₆`. -/
-- None of the five is `@[simp]`: `simp` already rewrites `pointedCurve.a₁` to
-- `algebraMap _ _ curve.a₁` with Mathlib's `WeierstrassCurve.Affine.baseChange_a₁`, so these
-- left-hand sides are not in simp normal form.
lemma pointedCurve_a₁ : pointedCurve.a₁ = polyToField (CC curve.a₁) := (rfl)
/-- The `a₂` coefficient of `pointedCurve` is the image of the indeterminate `A₂`. -/
lemma pointedCurve_a₂ : pointedCurve.a₂ = polyToField (CC curve.a₂) := (rfl)
/-- The `a₃` coefficient of `pointedCurve` is the image of the indeterminate `A₃`. -/
lemma pointedCurve_a₃ : pointedCurve.a₃ = polyToField (CC curve.a₃) := (rfl)
/-- The `a₄` coefficient of `pointedCurve` is the image of the indeterminate `A₄`. -/
lemma pointedCurve_a₄ : pointedCurve.a₄ = polyToField (CC curve.a₄) := (rfl)
/-- The `a₆` coefficient of `pointedCurve` is the image of the indeterminate `A₆`. -/
lemma pointedCurve_a₆ : pointedCurve.a₆ = polyToField (CC curve.a₆) := (rfl)

/-- The base change of the universal curve from `ℤ[A₁,⋯,A₆]` to `ℤ[A₁,⋯,A₆,X,Y]`. -/
abbrev curvePoly : WeierstrassCurve Poly := curve.baseChange Poly
/-- The base change of the universal curve from `ℤ[A₁,⋯,A₆]` to `ℤ[A₁,⋯,A₆,X,Y]/⟨P⟩`
(the universal ring), where `P` is the Weierstrass polynomial. -/
abbrev curveRing : WeierstrassCurve Universal.Ring := curve.baseChange Universal.Ring

/-- Pushing `curvePoly` along `polyToField` gives `pointedCurve`: the base change of the universal
curve to `ℤ[A₁,⋯,A₆,X,Y]` and its base change to `Universal.Field` agree along `polyToField`.

The **curve-dependent** Jacobian transports state their left-hand side over `W.map f`, so pushing
one from `Poly` to `Universal.Field` produces `curvePoly.map polyToField` and needs this lemma to
land on `pointedCurve`: `map_dblZ`, `map_dblXYZ`, `map_addX`, `map_addY`, `map_addXYZ`. `map_addZ`
is **not** among them — `addZ` takes no curve argument, so its transport is curve-free. -/
-- Upstream this identity is `rfl` and is never named. It has to be named here — not because it
-- fails to be definitional in this file, where `algebraMap_field_eq_comp` is itself proved
-- `(rfl)`, but because `polyToField`'s body is unexposed, so no consumer outside this file can
-- compare the two coefficient families by unfolding. The proof is `congrArg` of that equation.
@[simp] lemma map_polyToField : curvePoly.map polyToField = pointedCurve :=
  (congrArg (WeierstrassCurve.map curve) algebraMap_field_eq_comp).symm

end Universal

open Universal
variable {R} [CommRing R] (W : WeierstrassCurve R)

/-- The specialization homomorphism from `ℤ[A₁, ⋯, A₆]`
to the ring of definition of the Weierstrass curve. -/
def specialize : MvPolynomial Coeff ℤ →+* R :=
  (MvPolynomial.aeval <| Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆).toRingHom

open MvPolynomial (X) in
/-- `specialize` sends each indeterminate to the corresponding coefficient of `W`. With
`curve_a₁`‥`curve_a₆` this normalises coefficient evaluation inside a polynomial identity, without
unfolding either definition. -/
@[simp]
lemma specialize_X (i : Coeff) :
    W.specialize (X i) = Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ i := by
  simp [specialize]

/-- Every Weierstrass curve is a specialization of the universal Weierstrass curve. -/
@[simp]
lemma map_specialize : Universal.curve.map W.specialize = W := by ext <;> simp

/-- `specialize` sends the discriminant of the universal curve to the discriminant of `W`. -/
@[simp]
lemma specialize_Δ : W.specialize Universal.curve.Δ = W.Δ := by
  simp only [← map_Δ, map_specialize]

namespace Universal

variable (x y : R)

open Polynomial (eval₂RingHom) in
/-- A point in the affine plane over `R` induces an evaluation homomorphism
from `ℤ[A₁, ⋯, A₆, X, Y]` to `R`. -/
def polyEval : Poly →+* R := eval₂RingHom (eval₂RingHom W.specialize x) y

open Polynomial in
/-- `polyEval` computes in the expected order: substitute `W`'s coefficients for the indeterminates
`A₁,⋯,A₆`, then evaluate the resulting bivariate polynomial at `(x, y)`. -/
@[simp]
lemma polyEval_apply (p : Poly) :
    polyEval W x y p = (p.map <| mapRingHom W.specialize).evalEval x y :=
  eval₂_eval₂RingHom_apply _ _ _ _

variable {W x y} (eqn : Affine.Equation W x y)

open Polynomial in
/-- A point on a Weierstrass curve over `R` induces a specialization homomorphism
from the universal ring to `R`. -/
def ringEval : Universal.Ring →+* R :=
  AdjoinRoot.lift (eval₂RingHom W.specialize x) y <| by
    simp_rw [← coe_eval₂RingHom, eval₂RingHom_eval₂RingHom, RingHom.comp_apply, coe_mapRingHom]
    rwa [← Affine.map_polynomial, map_specialize]

/-- `ringEval` is `polyEval` read on the quotient: evaluating a representative `p` gives the same
answer as evaluating `p` in `Poly`. The pointwise form of `ringEval_comp_mk`. -/
@[simp]
lemma ringEval_mk (p : Poly) : ringEval eqn (AdjoinRoot.mk _ p) = polyEval W x y p :=
  AdjoinRoot.lift_mk _ p

/-- The homomorphism-level form of `ringEval_mk`: `ringEval eqn` is the factorisation of
`polyEval W x y` through the quotient by the Weierstrass polynomial. Use this shape when composing
ring maps and `ringEval_mk` when rewriting underneath an application. -/
@[simp]
lemma ringEval_comp_mk : (ringEval eqn).comp (AdjoinRoot.mk _) = polyEval W x y :=
  RingHom.ext (ringEval_mk eqn)

/-- `ringEval` sends the distinguished `X` to the abscissa of the point. Together with
`ringEval_root` this is the coordinate-level content of the universal property: the pair
`(X, Y)` of `Universal.Ring` goes to the chosen point `(x, y)` of `W`. -/
@[simp]
lemma ringEval_of_X : ringEval eqn (AdjoinRoot.of _ Polynomial.X) = x := by
  rw [← AdjoinRoot.mk_C, ringEval_mk, polyEval_apply]
  simp [Polynomial.evalEval]

/-- `ringEval` sends the distinguished `Y` to the ordinate of the point. -/
@[simp]
lemma ringEval_root : ringEval eqn (AdjoinRoot.root _) = y := by
  rw [← AdjoinRoot.mk_X, ringEval_mk, polyEval_apply]
  simp [Polynomial.evalEval]

/-- Restricted to the coefficient ring, `polyEval W x y` is just `W.specialize`: evaluating at a
point does not disturb the substitution of `W`'s coefficients. -/
@[simp]
lemma polyEval_comp_eq_specialize : (polyEval W x y).comp (algebraMap _ _) = W.specialize := by
  ext <;> simp [polyEval]

/-- The `Universal.Ring` counterpart of `polyEval_comp_eq_specialize`: `ringEval eqn` also restricts
to `W.specialize` on the coefficient ring. This is the compatibility that makes
`map_ringEval`, and with it every specialization argument, go through. -/
@[simp]
lemma ringEval_comp_eq_specialize : (ringEval eqn).comp (algebraMap _ _) = W.specialize := by
  rw [algebraMap_ring_eq_comp, ← RingHom.comp_assoc, ringEval_comp_mk, polyEval_comp_eq_specialize]

/-- The universal ring has characteristic zero: specializing to the cusp curve at `(1, 1)` retracts
it onto `ℤ`. This is the first use of that specialization argument, and it is what gives
`(2 : Universal.Ring) ≠ 0` — needed by the halving steps of the group law and of the
division-polynomial recursion. -/
instance : CharZero Universal.Ring :=
  RingHom.charZero (ringEval (equation_cusp_one_one ℤ))

/-- Specialization is compatible with base change: pushing the universal curve over
`Universal.Ring` along `ringEval eqn` returns `W` itself. This is the mechanism the whole file
exists for — an identity proved once for `curveRing` and its distinguished point becomes the same
identity for every Weierstrass curve `W` and every point `(x, y)` on it. -/
@[simp]
lemma map_ringEval : curveRing.map (ringEval eqn) = W := by
  simp only [baseChange, map_map, ringEval_comp_eq_specialize, map_specialize]

end Universal

/-! ## The universal elliptic Weierstrass curve over `ℤ[A₁,⋯,A₆][Δ⁻¹]` -/

namespace Universal

/-- The universal ring for **elliptic** Weierstrass curves: `ℤ[A₁,⋯,A₆][Δ⁻¹]`, the universal
polynomial ring `ℤ[A₁,⋯,A₆]` localised away from the discriminant of the universal curve. Being an
`abbrev` for `Localization.Away curve.Δ`, it inherits Mathlib's localisation API, and with it the
Noetherian instance. -/
abbrev EllipticRing : Type := Localization.Away curve.Δ

/-- `ℤ[A₁,⋯,A₆][Δ⁻¹]` is an integral domain, since the universal discriminant is nonzero
(`curve_Δ_ne_zero`). -/
instance : IsDomain EllipticRing := Localization.Away.isDomain curve_Δ_ne_zero

/-- The universal **elliptic** Weierstrass curve: the universal curve base-changed to
`ℤ[A₁,⋯,A₆][Δ⁻¹]`, over which its discriminant (`ellipticCurve_Δ`) is a unit. Every elliptic
Weierstrass curve is its base change along exactly one ring homomorphism
(`map_specializeElliptic`, `specializeElliptic_map_ellipticCurve`). -/
abbrev ellipticCurve : WeierstrassCurve EllipticRing := curve.baseChange EllipticRing

/-- The discriminant of `ellipticCurve` is the image of `curve.Δ` in `ℤ[A₁,⋯,A₆][Δ⁻¹]`. Rewrite with
this in place of Mathlib's `map_Δ`, which `simp` and `rw` do not apply to `ellipticCurve.Δ` on their
own, since neither unfolds `baseChange`. -/
@[simp]
lemma ellipticCurve_Δ : ellipticCurve.Δ = algebraMap _ EllipticRing curve.Δ := by
  simp only [baseChange, map_Δ]

/-- The universal elliptic Weierstrass curve is an elliptic curve: its discriminant is the image of
`curve.Δ` in the localisation away from `curve.Δ`, hence a unit. -/
instance : ellipticCurve.IsElliptic where
  isUnit := ellipticCurve_Δ ▸ IsLocalization.Away.algebraMap_isUnit _

open MvPolynomial (X) in
/-- **Extensionality for homomorphisms out of `ℤ[A₁,⋯,A₆][Δ⁻¹]`.** Two ring homomorphisms out of
`Universal.EllipticRing` are equal as soon as they agree on the images of the five indeterminates
`A₁,⋯,A₆` — the coefficients of `ellipticCurve`. So a homomorphism out of `Universal.EllipticRing`
is determined by the Weierstrass curve it produces from `ellipticCurve`. -/
-- `high`, as for Mathlib's `Localization.algHom_ext`, so that `ext` tries this lemma before the
-- other extensionality lemmas for ring homomorphisms, such as `RingHom.ext`, which compares the two
-- homomorphisms on every element.
@[ext high]
lemma EllipticRing.ringHom_ext {S : Type*} [Semiring S] {f g : EllipticRing →+* S}
    (h : ∀ i, f (algebraMap (MvPolynomial Coeff ℤ) EllipticRing (X i)) =
      g (algebraMap (MvPolynomial Coeff ℤ) EllipticRing (X i))) : f = g :=
  IsLocalization.ringHom_ext (.powers curve.Δ) <|
    MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun i ↦ by
      simpa only [RingHom.comp_apply] using h i

end Universal

section SpecializeElliptic

variable [W.IsElliptic]

/-- The **classifying homomorphism** of an elliptic Weierstrass curve `W` over `R`: the ring
homomorphism `ℤ[A₁,⋯,A₆][Δ⁻¹] →+* R` extending `W.specialize`, which substitutes the coefficients
of `W` for the indeterminates (`specializeElliptic_comp_algebraMap`). The universal elliptic
Weierstrass curve maps to `W` along it (`map_specializeElliptic`), and it is the only homomorphism
with that property (`specializeElliptic_map_ellipticCurve`). -/
def specializeElliptic : Universal.EllipticRing →+* R :=
  IsLocalization.Away.lift Universal.curve.Δ (g := W.specialize) <| by
    simpa only [specialize_Δ] using W.isUnit_Δ

/-- Restricted to the coefficient ring `ℤ[A₁,⋯,A₆]`, the classifying homomorphism of `W` is
`W.specialize`. Use this shape when composing ring maps and `specializeElliptic_algebraMap` when
rewriting underneath an application. -/
@[simp]
lemma specializeElliptic_comp_algebraMap :
    W.specializeElliptic.comp (algebraMap _ _) = W.specialize :=
  IsLocalization.Away.lift_comp ..

/-- The classifying homomorphism of `W` sends the image of a polynomial `p` in the coefficients to
`W.specialize p`; with `specialize_X`, it sends the image of each indeterminate to the
corresponding coefficient of `W`. The pointwise form of `specializeElliptic_comp_algebraMap`. -/
@[simp]
lemma specializeElliptic_algebraMap (p : MvPolynomial Coeff ℤ) :
    W.specializeElliptic (algebraMap _ _ p) = W.specialize p :=
  IsLocalization.Away.lift_eq ..

/-- Every elliptic Weierstrass curve is the base change of the universal elliptic Weierstrass
curve along its classifying homomorphism. An identity that is compatible with base change, proved
once for `Universal.ellipticCurve` over the integral domain `Universal.EllipticRing`, thereby holds
for every elliptic Weierstrass curve over every commutative ring. See `map_specialize` for
Weierstrass curves that need not be elliptic. -/
@[simp]
lemma map_specializeElliptic : Universal.ellipticCurve.map W.specializeElliptic = W := by
  simp only [baseChange, map_map, specializeElliptic_comp_algebraMap, map_specialize]

/-- A ring homomorphism `f` out of `ℤ[A₁,⋯,A₆][Δ⁻¹]` is the classifying homomorphism of the
Weierstrass curve `ellipticCurve.map f` it produces. With `map_specializeElliptic`, this makes
`f ↦ ellipticCurve.map f` and `W ↦ W.specializeElliptic` mutually inverse: ring homomorphisms
`ℤ[A₁,⋯,A₆][Δ⁻¹] →+* R` correspond exactly to elliptic Weierstrass curves over `R`. -/
@[simp]
lemma specializeElliptic_map_ellipticCurve (f : Universal.EllipticRing →+* R) :
    (Universal.ellipticCurve.map f).specializeElliptic = f := by
  ext i
  cases i <;> simp

/-- The classifying homomorphism is natural in the base ring: the classifying homomorphism of the
base change `W.map f` is that of `W` followed by `f`. -/
-- Not `@[simp]`: with this lemma in the simp set, `simp` proves
-- `specializeElliptic_map_ellipticCurve` from it and `specializeElliptic_ellipticCurve`, and
-- `simpNF` then rejects the tag on that lemma as a duplicate. Tagging this lemma instead of that
-- one passes `simpNF`, but `simp` then rewrites `(W.map f).specializeElliptic` first and
-- `map_specializeElliptic` no longer applies to `ellipticCurve.map (W.map f).specializeElliptic`.
lemma specializeElliptic_map {S : Type*} [CommRing S] (f : R →+* S) :
    (W.map f).specializeElliptic = f.comp W.specializeElliptic := by
  simpa only [← map_map, map_specializeElliptic] using
    specializeElliptic_map_ellipticCurve (f.comp W.specializeElliptic)

/-- The universal elliptic Weierstrass curve is classified by the identity homomorphism of
`ℤ[A₁,⋯,A₆][Δ⁻¹]`. -/
@[simp]
lemma specializeElliptic_ellipticCurve :
    Universal.ellipticCurve.specializeElliptic = RingHom.id _ := by
  simpa only [map_id] using specializeElliptic_map_ellipticCurve (RingHom.id Universal.EllipticRing)

end SpecializeElliptic

section Universe

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]

/-- Every elliptic Weierstrass curve `W` over a commutative ring `R` in `Type u` is the base change
`W₀.map f` of an elliptic Weierstrass curve `W₀` over a Noetherian integral domain `R₀` in the same
universe `Type u`, along a ring homomorphism `f : R₀ →+* R`. Compare `map_specializeElliptic`,
whose base ring `Universal.EllipticRing` is a Noetherian integral domain in `Type`. -/
theorem exists_map_eq_of_isElliptic :
    ∃ (R₀ : Type u) (_ : CommRing R₀) (_ : IsDomain R₀) (_ : IsNoetherianRing R₀)
      (W₀ : WeierstrassCurve R₀) (_ : W₀.IsElliptic) (f : R₀ →+* R), W₀.map f = W :=
  -- the copy `ULift.{u} Universal.EllipticRing` of the universal ring in `Type u`
  ⟨ULift.{u} Universal.EllipticRing, inferInstance,
    ULift.ringEquiv.toMulEquiv.isDomain Universal.EllipticRing,
    isNoetherianRing_of_ringEquiv Universal.EllipticRing ULift.ringEquiv.symm,
    Universal.ellipticCurve.map ULift.ringEquiv.symm.toRingHom, inferInstance,
    W.specializeElliptic.comp ULift.ringEquiv.toRingHom, by
      rw [map_map, RingHom.comp_assoc, RingEquiv.toRingHom_comp_symm_toRingHom, RingHom.comp_id,
        map_specializeElliptic]⟩

variable (C : VariableChange R)

/-- Every pair of an elliptic Weierstrass curve `W` and a change of variables `C` over a
commutative ring `R` in `Type u` is the base change `(W₁.map g, C₁.map g)` of such a pair over a
Noetherian integral domain `R₁` in the same universe `Type u`, along a ring homomorphism
`g : R₁ →+* R`. The ring `R₁` is `R₀[u, r, s, t][u⁻¹]`, for the ring `R₀` of
`exists_map_eq_of_isElliptic`, and `C₁` is the change of variables `(u, r, s, t)`. -/
theorem exists_map_eq_and_map_eq_of_isElliptic :
    ∃ (R₁ : Type u) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsNoetherianRing R₁)
      (W₁ : WeierstrassCurve R₁) (_ : W₁.IsElliptic) (C₁ : VariableChange R₁) (g : R₁ →+* R),
      W₁.map g = W ∧ C₁.map g = C := by
  obtain ⟨R₀, _, _, _, W₀, _, f, rfl⟩ := W.exists_map_eq_of_isElliptic
  -- the ring `R₀[u, r, s, t][u⁻¹]`, a Noetherian integral domain
  set x : MvPolynomial (Fin 4) R₀ := MvPolynomial.X 0
  have : IsDomain (Localization.Away x) := Localization.Away.isDomain (MvPolynomial.X_ne_zero 0)
  -- the specialization `u, r, s, t ↦ C.u, C.r, C.s, C.t`
  set φ : MvPolynomial (Fin 4) R₀ →+* R :=
    MvPolynomial.eval₂Hom f ![(C.u : R), C.r, C.s, C.t]
  have hφ : IsUnit (φ x) := by simp [φ, x]
  refine ⟨Localization.Away x, inferInstance, inferInstance, inferInstance,
    W₀.map (algebraMap R₀ (Localization.Away x)), inferInstance,
    ⟨(IsLocalization.Away.algebraMap_isUnit x).unit,
      algebraMap (MvPolynomial (Fin 4) R₀) _ (.X 1), algebraMap (MvPolynomial (Fin 4) R₀) _ (.X 2),
      algebraMap (MvPolynomial (Fin 4) R₀) _ (.X 3)⟩,
    IsLocalization.Away.lift x hφ, ?_, ?_⟩
  · rw [map_map]
    congr 1
    ext r
    simp [IsScalarTower.algebraMap_apply R₀ (MvPolynomial (Fin 4) R₀) (Localization.Away x), φ]
  · ext <;> simp [VariableChange.map, φ, x]

end Universe

end WeierstrassCurve
