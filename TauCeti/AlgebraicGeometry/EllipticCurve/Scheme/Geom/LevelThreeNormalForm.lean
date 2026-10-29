/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Glue
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.LevelThreeNormalForm
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.GroupLaw

/-!
# The universal level-three normal form over a scheme

Let `E` be an elliptic curve over a scheme `S`, and let `P` and `Q` be sections of `E` which meet
the zero section over no point of `S`, are killed by multiplication by `3`, and such that `Q` is
neither `P` nor `-P` over any point of `S`. Over a field, these conditions say that `(P, Q)` is a
basis of the `3`-torsion. Then `(E, P, Q)` is the pullback of the universal level-three normal form

`Y² + 3μXY + (μ³ - 1)Y = X³`

over `Spec ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]`, with its basis `(0, 0)`,
`(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` of the `3`-torsion, along exactly one morphism
`S ⟶ Spec ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]` and by exactly one cartesian morphism from `E` carrying the
zero section to the zero section, `P` to `(0, 0)` and `Q` to the second basis point
(`EllipticCurveGeom.existsUnique_levelThreeNormalForm`). Conversely, two sections which are such a
pullback of the universal basis satisfy the conditions
(`EllipticCurveGeom.exists_levelThreeNormalForm_iff`). So `Spec ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]` is a fine
moduli scheme for elliptic curves with two sections satisfying the conditions, with universal
family the projective model of the universal level-three normal form. No hypothesis on `S` is
needed; in particular `S` may be nonreduced or non-affine, and `3` is not assumed to be invertible
on `S`: the conditions force it to be.

Over an affine base this is `WeierstrassCurve.existsUnique_levelThreeNormalForm`, and the passage to
an arbitrary base glues the affine statement over the pointed Weierstrass charts of `E`
(`EllipticCurveGeom.existsUnique_isPullback_of_forall_chart`).

The coefficient ring `ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]` (`WeierstrassCurve.UniversalLevelThree.Ring`)
lies in `Type`. For schemes in an arbitrary universe the universal level-three normal form is read
over its copy `ULift.{u} ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]`
(`WeierstrassCurve.UniversalLevelThree.curveULift`).

## Main definitions

* `WeierstrassCurve.UniversalLevelThree.curveULift`: the universal level-three normal form over
  `ULift.{u} ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]`.
* `WeierstrassCurve.UniversalLevelThree.firstPoint` and
  `WeierstrassCurve.UniversalLevelThree.secondPoint`: the points `(0, 0)` and
  `(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` of its projective model.
* `TauCeti.AlgebraicGeometry.UniversalLevelThree.curveGeom`: the universal level-three normal form
  as an elliptic curve over `Spec ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]`, with the basis points
  `TauCeti.AlgebraicGeometry.UniversalLevelThree.firstPointHom` and
  `TauCeti.AlgebraicGeometry.UniversalLevelThree.secondPointHom`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.existsUnique_levelThreeNormalForm`: two sections
  satisfying the conditions are the pullback of the universal basis along a unique cartesian
  pointed morphism to the universal level-three normal form.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.exists_levelThreeNormalForm_iff`: such a morphism
  exists exactly when the two sections satisfy the conditions.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.existsUnique_levelThreeNormalForm_curveGeom`: the
  same universal property, with the universal level-three normal form read as the elliptic curve
  `curveGeom`.
* `TauCeti.AlgebraicGeometry.UniversalLevelThree.firstPointHom_left_comp_mulBy_three_left`,
  `TauCeti.AlgebraicGeometry.UniversalLevelThree.secondPointHom_left_ne_firstPointHom_left` and
  their siblings: the universal basis satisfies the conditions.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 2.2.10 and 2.2.11 (naive level-three structures as
  rigidifiers) and Chapter 4 (fine moduli schemes of elliptic curves with level structure).
-/

public section

open CategoryTheory Limits AlgebraicGeometry TauCeti.AlgebraicGeometry

universe u

namespace WeierstrassCurve.UniversalLevelThree

/-! ### The universal curve in an arbitrary universe -/

/-- The parameter `μ` in the copy `ULift.{u} ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]` of the coefficient ring of
the universal level-three normal form in `Type u`. -/
noncomputable def parameterULift : ULift.{u} Ring :=
  .up parameter

/-- The primitive cube root of unity `ζ` in `ULift.{u} ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]`. -/
noncomputable def rootOfUnityULift : ULift.{u} Ring :=
  .up rootOfUnity

/-- The root of unity `ζ` of `ULift.{u} ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]` is a root of `ζ² + ζ + 1`. -/
theorem rootOfUnityULift_sq_add_rootOfUnityULift_add_one :
    rootOfUnityULift.{u} ^ 2 + rootOfUnityULift + 1 = 0 :=
  congrArg ULift.up rootOfUnity_sq_add_rootOfUnity_add_one

/-- The universal curve with a basis of its `3`-torsion over `ULift.{u} ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]`:
the level-three normal form `Y² + 3μXY + (μ³ - 1)Y = X³`. -/
noncomputable def curveULift : WeierstrassCurve (ULift.{u} Ring) :=
  levelThreeNormalForm parameterULift

/-- The universal curve over `ULift.{u} ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]` is the level-three normal form
with parameter `μ`. -/
theorem curveULift_eq_levelThreeNormalForm :
    curveULift.{u} = levelThreeNormalForm parameterULift :=
  (rfl)

/-- The universal curve over `ULift.{u} ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]` is the base change of the one
over `ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]` along the identification of the two rings. -/
theorem curveULift_eq :
    curveULift.{u} = curve.map (ULift.ringEquiv.symm : Ring ≃+* ULift.{u} Ring).toRingHom := by
  rw [curve_eq, map_levelThreeNormalForm]
  rfl

/-- The base change of the universal curve over `ULift.{u} ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]` along a ring
homomorphism `φ` is the level-three normal form with parameter the image of `μ`. -/
@[simp]
theorem map_curveULift {A : Type*} [CommRing A] (φ : ULift.{u} Ring →+* A) :
    curveULift.map φ = levelThreeNormalForm (φ parameterULift) :=
  map_levelThreeNormalForm _ φ

/-- The universal curve over `ULift.{u} ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]` is elliptic. -/
instance : curveULift.{u}.IsElliptic := by
  rw [curveULift_eq]
  infer_instance

/-- The point `(0, 0)` lies on the universal curve over `ULift.{u} ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]`. -/
theorem equation_curveULift_zero : curveULift.{u}.toAffine.Equation 0 0 := by
  rw [curveULift_eq_levelThreeNormalForm]
  exact equation_levelThreeNormalForm_zero _

/-- The point `(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` lies on the universal curve over
`ULift.{u} ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]`. -/
theorem equation_curveULift_basisPoint :
    curveULift.{u}.toAffine.Equation (-(parameterULift ^ 2 + parameterULift + 1))
      ((parameterULift ^ 2 + parameterULift + 1) * (parameterULift - rootOfUnityULift)) := by
  rw [curveULift_eq_levelThreeNormalForm]
  exact equation_levelThreeNormalForm_basisPoint _ rootOfUnityULift_sq_add_rootOfUnityULift_add_one

/-- The point `(0, 0)` of the universal curve, the first point of its basis of the `3`-torsion. -/
noncomputable def firstPoint : Spec (.of (ULift.{u} Ring)) ⟶ curveULift.{u}.projModel :=
  curveULift.projModelAffinePoint equation_curveULift_zero

/-- The point `(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` of the universal curve, the second point of its
basis of the `3`-torsion. -/
noncomputable def secondPoint : Spec (.of (ULift.{u} Ring)) ⟶ curveULift.{u}.projModel :=
  curveULift.projModelAffinePoint equation_curveULift_basisPoint

/-- The first basis point is the affine point `(0, 0)` of the projective model. -/
theorem firstPoint_def :
    firstPoint.{u} = curveULift.projModelAffinePoint equation_curveULift_zero :=
  (rfl)

/-- The second basis point is the affine point `(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` of the
projective model. -/
theorem secondPoint_def :
    secondPoint.{u} = curveULift.projModelAffinePoint equation_curveULift_basisPoint :=
  (rfl)

/-- The first basis point is a section of the projective model of the universal curve. -/
@[reassoc (attr := simp)]
theorem firstPoint_projModelOver : firstPoint.{u} ≫ curveULift.projModelOver = 𝟙 _ :=
  projModelAffinePoint_projModelOver _

/-- The second basis point is a section of the projective model of the universal curve. -/
@[reassoc (attr := simp)]
theorem secondPoint_projModelOver : secondPoint.{u} ≫ curveULift.projModelOver = 𝟙 _ :=
  projModelAffinePoint_projModelOver _

-- The universal basis satisfies the conditions of the level-three normal form: it is the image of
-- the basis of a level-three normal form under the identity.
private theorem basis_conditions :
    (∀ s, firstPoint.{u} s ≠ curveULift.projModelZero s) ∧
      (∀ s, secondPoint.{u} s ≠ curveULift.projModelZero s) ∧
      firstPoint.{u} ≫ curveULift.projModelMulBy 3 = curveULift.projModelZero ∧
      secondPoint.{u} ≫ curveULift.projModelMulBy 3 = curveULift.projModelZero ∧
      ∀ s, secondPoint.{u} s ≠ firstPoint.{u} s ∧
        secondPoint.{u} s ≠ (firstPoint.{u} ≫ curveULift.projModelNeg) s := by
  -- `curveULift` is opaque, so the identity of a level-three normal form is applied through its
  -- characterization `curveULift_eq_levelThreeNormalForm`
  have key {W : WeierstrassCurve (ULift.{u} Ring)} [W.IsElliptic]
      (hW : W = levelThreeNormalForm parameterULift) (h₁ : W.toAffine.Equation 0 0)
      (h₂ : W.toAffine.Equation (-(parameterULift ^ 2 + parameterULift + 1))
        ((parameterULift ^ 2 + parameterULift + 1) * (parameterULift - rootOfUnityULift))) :
      (∀ s, W.projModelAffinePoint h₁ s ≠ W.projModelZero s) ∧
        (∀ s, W.projModelAffinePoint h₂ s ≠ W.projModelZero s) ∧
        W.projModelAffinePoint h₁ ≫ W.projModelMulBy 3 = W.projModelZero ∧
        W.projModelAffinePoint h₂ ≫ W.projModelMulBy 3 = W.projModelZero ∧
        ∀ s, W.projModelAffinePoint h₂ s ≠ W.projModelAffinePoint h₁ s ∧
          W.projModelAffinePoint h₂ s ≠ (W.projModelAffinePoint h₁ ≫ W.projModelNeg) s := by
    subst hW
    exact (exists_iso_levelThreeNormalForm_iff (projModelAffinePoint_projModelOver _)
      (projModelAffinePoint_projModelOver _)).mp
      ⟨_, _, rootOfUnityULift_sq_add_rootOfUnityULift_add_one, Iso.refl _, by simp, by simp,
        by simp, by simp⟩
  exact key curveULift_eq_levelThreeNormalForm _ _

/-- The first basis point misses the zero section at every point of the base. -/
theorem firstPoint_ne_projModelZero (s) : firstPoint.{u} s ≠ curveULift.projModelZero s :=
  basis_conditions.1 s

/-- The second basis point misses the zero section at every point of the base. -/
theorem secondPoint_ne_projModelZero (s) : secondPoint.{u} s ≠ curveULift.projModelZero s :=
  basis_conditions.2.1 s

/-- The first basis point is killed by `3`. -/
@[reassoc (attr := simp)]
theorem firstPoint_projModelMulBy_three :
    firstPoint.{u} ≫ curveULift.projModelMulBy 3 = curveULift.projModelZero :=
  basis_conditions.2.2.1

/-- The second basis point is killed by `3`. -/
@[reassoc (attr := simp)]
theorem secondPoint_projModelMulBy_three :
    secondPoint.{u} ≫ curveULift.projModelMulBy 3 = curveULift.projModelZero :=
  basis_conditions.2.2.2.1

/-- The second basis point differs from the first at every point of the base. -/
theorem secondPoint_ne_firstPoint (s) : secondPoint.{u} s ≠ firstPoint.{u} s :=
  (basis_conditions.2.2.2.2 s).1

/-- The second basis point differs from the negative of the first at every point of the base. -/
theorem secondPoint_ne_firstPoint_projModelNeg (s) :
    secondPoint.{u} s ≠ (firstPoint.{u} ≫ curveULift.projModelNeg) s :=
  (basis_conditions.2.2.2.2 s).2

end WeierstrassCurve.UniversalLevelThree

namespace TauCeti.AlgebraicGeometry.UniversalLevelThree

open WeierstrassCurve MonoidalCategory

/-! ### The universal level-three normal form as an elliptic curve -/

/-- The universal level-three normal form `Y² + 3μXY + (μ³ - 1)Y = X³` as an elliptic curve over
`Spec ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]`, whose total space is the projective model of `curveULift`. -/
noncomputable abbrev curveGeom :
    EllipticCurveGeom (Spec (.of (ULift.{u} UniversalLevelThree.Ring))) :=
  toEllipticCurveGeom UniversalLevelThree.curveULift

/-- The point `(0, 0)` of the universal level-three normal form, as a point with values in the base
of the elliptic curve `curveGeom`. -/
noncomputable def firstPointHom : 𝟙_ (Over (Spec (.of (ULift.{u} UniversalLevelThree.Ring)))) ⟶
    Over.mk curveGeom.{u}.structureMap :=
  Over.homMk (UniversalLevelThree.firstPoint ≫
    (toEllipticCurveGeomIso UniversalLevelThree.curveULift).inv) <| by
      simp [← toEllipticCurveGeomIso_hom_projModelOver]

/-- The point `(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` of the universal level-three normal form, as a
point with values in the base of the elliptic curve `curveGeom`. -/
noncomputable def secondPointHom : 𝟙_ (Over (Spec (.of (ULift.{u} UniversalLevelThree.Ring)))) ⟶
    Over.mk curveGeom.{u}.structureMap :=
  Over.homMk (UniversalLevelThree.secondPoint ≫
    (toEllipticCurveGeomIso UniversalLevelThree.curveULift).inv) <| by
      simp [← toEllipticCurveGeomIso_hom_projModelOver]

/-- On the projective model, the point `(0, 0)` of `curveGeom` is `firstPoint`. -/
@[simp]
theorem firstPointHom_left :
    firstPointHom.{u}.left =
      UniversalLevelThree.firstPoint ≫
        (toEllipticCurveGeomIso UniversalLevelThree.curveULift).inv :=
  (rfl)

/-- On the projective model, the point `(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` of `curveGeom` is
`secondPoint`. -/
@[simp]
theorem secondPointHom_left :
    secondPointHom.{u}.left =
      UniversalLevelThree.secondPoint ≫
        (toEllipticCurveGeomIso UniversalLevelThree.curveULift).inv :=
  (rfl)

end TauCeti.AlgebraicGeometry.UniversalLevelThree

namespace TauCeti.AlgebraicGeometry

open WeierstrassCurve UniversalLevelThree

/-! ### Classifying pairs over an affine base -/

-- `(f, g)` classifies `(π, zero, P, Q)`: `g` exhibits `X` as the base change of the universal
-- level-three normal form along `f`, carrying `zero` to the zero section and `P` and `Q` to the
-- universal basis.
private def IsLevelThree {X T : Scheme.{u}} (π : X ⟶ T) (zero P Q : T ⟶ X)
    (f : T ⟶ Spec (.of (ULift.{u} UniversalLevelThree.Ring)))
    (g : X ⟶ curveULift.{u}.projModel) : Prop :=
  IsPullback g π curveULift.projModelOver f ∧ zero ≫ g = f ≫ curveULift.projModelZero ∧
    P ≫ g = f ≫ firstPoint ∧ Q ≫ g = f ≫ secondPoint

section Affine

variable {R : Type u} [CommRing R]

-- The image of the root of unity under a ring homomorphism is a root of `ζ² + ζ + 1`.
private theorem map_rootOfUnityULift_sq_add_add_one (φ : ULift.{u} UniversalLevelThree.Ring →+* R) :
    φ rootOfUnityULift ^ 2 + φ rootOfUnityULift + 1 = 0 := by
  simpa using congrArg φ rootOfUnityULift_sq_add_rootOfUnityULift_add_one

-- Two ring homomorphisms out of `ULift ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]` agreeing on `μ` and `ζ` are
-- equal.
private theorem ringHom_ext_ULift {φ φ' : ULift.{u} UniversalLevelThree.Ring →+* R}
    (hμ : φ parameterULift = φ' parameterULift) (hζ : φ rootOfUnityULift = φ' rootOfUnityULift) :
    φ = φ' := by
  have : φ.comp (ULift.ringEquiv.symm : UniversalLevelThree.Ring ≃+* ULift.{u} _).toRingHom =
      φ'.comp (ULift.ringEquiv.symm : UniversalLevelThree.Ring ≃+* ULift.{u} _).toRingHom :=
    UniversalLevelThree.Ring.ringHom_ext hμ hζ
  ext x
  exact congr($this x.down)

-- The classifying homomorphism `ULift ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)] →+* R` of an elliptic level-three
-- normal form with a root `ζ` of `ζ² + ζ + 1`.
private noncomputable def liftULift {μ ζ : R} (hΔ : IsUnit (levelThreeNormalForm μ).Δ)
    (hζ : ζ ^ 2 + ζ + 1 = 0) : ULift.{u} UniversalLevelThree.Ring →+* R :=
  (lift hΔ hζ).comp ULift.ringEquiv.toRingHom

private theorem liftULift_parameterULift {μ ζ : R} (hΔ : IsUnit (levelThreeNormalForm μ).Δ)
    (hζ : ζ ^ 2 + ζ + 1 = 0) : liftULift hΔ hζ parameterULift = μ :=
  lift_parameter hΔ hζ

private theorem liftULift_rootOfUnityULift {μ ζ : R} (hΔ : IsUnit (levelThreeNormalForm μ).Δ)
    (hζ : ζ ^ 2 + ζ + 1 = 0) : liftULift hΔ hζ rootOfUnityULift = ζ :=
  lift_rootOfUnity hΔ hζ

-- The base change morphism to the universal curve along `φ`, read on a curve `W'` equal to the base
-- change `curveULift.map φ`, is cartesian over `Spec φ`, pointed, and carries the points of `W'`
-- with the images of the coordinates of the universal basis to the universal basis.
private theorem isLevelThree_eqToHom_projModelBaseChange
    (φ : ULift.{u} UniversalLevelThree.Ring →+* R) {W' : WeierstrassCurve R}
    (hW' : curveULift.map φ = W') {x₁ y₁ x₂ y₂ : R} (h₁ : W'.toAffine.Equation x₁ y₁)
    (h₂ : W'.toAffine.Equation x₂ y₂) (hx₁ : x₁ = 0) (hy₁ : y₁ = 0)
    (hx₂ : x₂ = φ (-(parameterULift ^ 2 + parameterULift + 1)))
    (hy₂ : y₂ =
      φ ((parameterULift ^ 2 + parameterULift + 1) * (parameterULift - rootOfUnityULift))) :
    IsLevelThree W'.projModelOver W'.projModelZero (W'.projModelAffinePoint h₁)
      (W'.projModelAffinePoint h₂) (Spec.map (CommRingCat.ofHom φ))
      (eqToHom (congrArg projModel hW'.symm) ≫ curveULift.projModelBaseChange φ) := by
  subst hW'
  have e₁ : curveULift.{u}.toAffine.Equation 0 0 := equation_levelThreeNormalForm_zero _
  have e₂ : curveULift.{u}.toAffine.Equation (-(parameterULift ^ 2 + parameterULift + 1))
      ((parameterULift ^ 2 + parameterULift + 1) * (parameterULift - rootOfUnityULift)) :=
    equation_levelThreeNormalForm_basisPoint _ rootOfUnityULift_sq_add_rootOfUnityULift_add_one
  have h₁' : (curveULift.map φ).projModelAffinePoint h₁ =
      (curveULift.map φ).projModelAffinePoint (e₁.map φ) :=
    (projModelAffinePoint_inj h₁).mpr ⟨hx₁.trans (map_zero φ).symm, hy₁.trans (map_zero φ).symm⟩
  have h₂' : (curveULift.map φ).projModelAffinePoint h₂ =
      (curveULift.map φ).projModelAffinePoint (e₂.map φ) :=
    (projModelAffinePoint_inj h₂).mpr ⟨hx₂, hy₂⟩
  refine ⟨by simpa using curveULift.isPullback_projModelBaseChange φ, by simp, ?_, ?_⟩
  · rw [h₁', eqToHom_refl, Category.id_comp, projModelAffinePoint_projModelBaseChange]
    rfl
  · rw [h₂', eqToHom_refl, Category.id_comp, projModelAffinePoint_projModelBaseChange]
    rfl

variable {W : WeierstrassCurve R} {P Q : Spec (.of R) ⟶ W.projModel}

-- A level-three normal form pointed-isomorphic to the projective model of an elliptic curve is
-- elliptic.
private theorem isUnit_Δ_of_iso [W.IsElliptic] {μ : R}
    (e : (levelThreeNormalForm μ).projModel ≅ W.projModel)
    (he : e.hom ≫ W.projModelOver = (levelThreeNormalForm μ).projModelOver)
    (he₀ : (levelThreeNormalForm μ).projModelZero ≫ e.hom = W.projModelZero) :
    IsUnit (levelThreeNormalForm μ).Δ := by
  obtain ⟨C, ⟨hC, -⟩, -⟩ := existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom e he he₀
  rw [← hC]
  exact (C • W).isUnit_Δ

-- A classifying pair of `(W, P, Q)` over `Spec φ` is the base change morphism along `φ`, composed
-- with a pointed isomorphism from `projModel W` to the level-three normal form with the image of
-- `μ` as parameter, carrying `P` and `Q` to its basis with the image of `ζ` as root of unity.
private theorem exists_iso_of_isLevelThree (hP : P ≫ W.projModelOver = 𝟙 _)
    (hQ : Q ≫ W.projModelOver = 𝟙 _) {φ : ULift.{u} UniversalLevelThree.Ring →+* R}
    {g : W.projModel ⟶ curveULift.projModel}
    (hg : IsLevelThree W.projModelOver W.projModelZero P Q (Spec.map (CommRingCat.ofHom φ)) g) :
    ∃ e : (levelThreeNormalForm (φ parameterULift)).projModel ≅ W.projModel,
      e.hom ≫ W.projModelOver = (levelThreeNormalForm (φ parameterULift)).projModelOver ∧
        (levelThreeNormalForm (φ parameterULift)).projModelZero ≫ e.hom = W.projModelZero ∧
        (levelThreeNormalForm (φ parameterULift)).projModelAffinePoint
          (equation_levelThreeNormalForm_zero _) ≫ e.hom = P ∧
        (levelThreeNormalForm (φ parameterULift)).projModelAffinePoint
          (equation_levelThreeNormalForm_basisPoint _
            (map_rootOfUnityULift_sq_add_add_one φ)) ≫ e.hom = Q ∧
        g = e.inv ≫ eqToHom (congrArg projModel (map_curveULift φ).symm) ≫
          curveULift.projModelBaseChange φ := by
  -- `g` and the base change morphism are two pullbacks of the same cospan
  have hT := isLevelThree_eqToHom_projModelBaseChange φ (map_curveULift φ)
    (equation_levelThreeNormalForm_zero _)
    (equation_levelThreeNormalForm_basisPoint _ (map_rootOfUnityULift_sq_add_add_one φ))
    rfl rfl (by simp) (by simp)
  let e := hg.1.isoIsPullback _ _ hT.1
  have he : e.hom ≫ _ = g := hg.1.isoIsPullback_hom_fst _ _ hT.1
  have he' : e.hom ≫ _ = W.projModelOver := hg.1.isoIsPullback_hom_snd _ _ hT.1
  refine ⟨e.symm, by simp [← he'], ?_, ?_, ?_, by simp [← he]⟩
  · rw [Iso.symm_hom, Iso.comp_inv_eq]
    refine hT.1.hom_ext ?_ ?_
    · rw [Category.assoc, he, hg.2.1, hT.2.1]
    · simp [he']
  · rw [Iso.symm_hom, Iso.comp_inv_eq]
    refine hT.1.hom_ext ?_ ?_
    · rw [Category.assoc, he, hg.2.2.1, hT.2.2.1]
    · simp [he', hP]
  · rw [Iso.symm_hom, Iso.comp_inv_eq]
    refine hT.1.hom_ext ?_ ?_
    · rw [Category.assoc, he, hg.2.2.2, hT.2.2.2]
    · simp [he', hQ]

variable [W.IsElliptic] (hP : P ≫ W.projModelOver = 𝟙 _) (hQ : Q ≫ W.projModelOver = 𝟙 _)
  (hP₀ : ∀ s, P s ≠ W.projModelZero s) (hQ₀ : ∀ s, Q s ≠ W.projModelZero s)
  (hP₃ : P ≫ W.projModelMulBy 3 = W.projModelZero)
  (hQ₃ : Q ≫ W.projModelMulBy 3 = W.projModelZero)
  (hQP : ∀ s, Q s ≠ P s ∧ Q s ≠ (P ≫ W.projModelNeg) s)

include hP hQ hP₀ hQ₀ hP₃ hQ₃ hQP

-- Over an affine base, two sections satisfying the conditions of the level-three normal form have
-- a classifying pair.
private theorem exists_isLevelThree :
    ∃ f g, IsLevelThree W.projModelOver W.projModelZero P Q f g := by
  obtain ⟨⟨μ, ζ⟩, ⟨hζ, e, he, he₀, heP, heQ⟩, -⟩ :=
    W.existsUnique_levelThreeNormalForm hP hQ hP₀ hQ₀ hP₃ hQ₃ hQP
  have hΔ := isUnit_Δ_of_iso e he he₀
  have hT := isLevelThree_eqToHom_projModelBaseChange (liftULift hΔ hζ)
    (by rw [map_curveULift, liftULift_parameterULift]) (equation_levelThreeNormalForm_zero μ)
    (equation_levelThreeNormalForm_basisPoint μ hζ) rfl rfl
    (by simp [liftULift_parameterULift])
    (by simp [liftULift_parameterULift, liftULift_rootOfUnityULift])
  have he₀' : W.projModelZero ≫ e.inv = (levelThreeNormalForm μ).projModelZero :=
    (Iso.comp_inv_eq e).mpr he₀.symm
  have heP' : P ≫ e.inv = (levelThreeNormalForm μ).projModelAffinePoint
      (equation_levelThreeNormalForm_zero μ) := (Iso.comp_inv_eq e).mpr heP.symm
  have heQ' : Q ≫ e.inv = (levelThreeNormalForm μ).projModelAffinePoint
      (equation_levelThreeNormalForm_basisPoint μ hζ) := (Iso.comp_inv_eq e).mpr heQ.symm
  have hsq : IsPullback e.inv W.projModelOver (levelThreeNormalForm μ).projModelOver (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simp [← he]⟩
  exact ⟨_, _, by simpa using hsq.paste_horiz hT.1, by rw [reassoc_of% he₀', hT.2.1],
    by rw [reassoc_of% heP', hT.2.2.1], by rw [reassoc_of% heQ', hT.2.2.2]⟩

-- Over an affine base, the classifying pair of two sections satisfying the conditions of the
-- level-three normal form is unique.
private theorem existsUnique_isLevelThree :
    ∃! fg : (Spec (.of R) ⟶ Spec (.of (ULift.{u} UniversalLevelThree.Ring))) ×
      (W.projModel ⟶ curveULift.projModel),
      IsLevelThree W.projModelOver W.projModelZero P Q fg.1 fg.2 := by
  obtain ⟨f, g, hfg⟩ := exists_isLevelThree hP hQ hP₀ hQ₀ hP₃ hQ₃ hQP
  refine ⟨(f, g), hfg, fun ⟨f', g'⟩ hfg' ↦ ?_⟩
  obtain ⟨⟨φ⟩, rfl⟩ := Spec.map_surjective f
  obtain ⟨⟨φ'⟩, rfl⟩ := Spec.map_surjective f'
  obtain ⟨e, he, he₀, heP, heQ, rfl⟩ := exists_iso_of_isLevelThree hP hQ hfg
  obtain ⟨e', he', he₀', heP', heQ', rfl⟩ := exists_iso_of_isLevelThree hP hQ hfg'
  -- both level-three normal forms are the unique one for `(P, Q)`, so `φ` and `φ'` agree on `μ`
  -- and `ζ`
  have hμζ := (W.existsUnique_levelThreeNormalForm hP hQ hP₀ hQ₀ hP₃ hQ₃ hQP).unique
    (y₁ := (φ' parameterULift, φ' rootOfUnityULift)) (y₂ := (φ parameterULift, φ rootOfUnityULift))
    ⟨map_rootOfUnityULift_sq_add_add_one φ', e', he', he₀', heP', heQ'⟩
    ⟨map_rootOfUnityULift_sq_add_add_one φ, e, he, he₀, heP, heQ⟩
  obtain rfl : φ' = φ :=
    ringHom_ext_ULift (congrArg Prod.fst hμζ) (congrArg Prod.snd hμζ)
  rw [levelThreeNormalForm_iso_ext (map_rootOfUnityULift_sq_add_add_one φ') he' he₀' he he₀
    (heP'.trans heP.symm) (heQ'.trans heQ.symm)]

end Affine

/-! ### The universal property -/

namespace EllipticCurveGeom

variable {S : Scheme.{u}} {E : EllipticCurveGeom S} {P Q : S ⟶ E.carrier}
  (hP : P ≫ E.structureMap = 𝟙 S) (hQ : Q ≫ E.structureMap = 𝟙 S)

-- A section killed by `n` gives, on every chart, a model point killed by `n`.
private theorem modelPoint_projModelMulBy {n : ℤ} (hn : P ≫ (E.mulBy n).left = E.zero)
    (c : PointedWeierstrassChart E.structureMap E.zero) :
    c.modelPoint hP ≫ c.equation.projModelMulBy n = c.equation.projModelZero :=
  c.isPullback_modelIso_inv_toTotal.hom_ext
    (by rw [Category.assoc, c.equation.projModelMulBy_comp_of_isPullback
      c.isPullback_modelIso_inv_toTotal c.projModelZero_modelIso_inv_toTotal, ← Category.assoc,
      c.modelPoint_modelIso_inv_toTotal, Category.assoc, hn,
      c.projModelZero_modelIso_inv_toTotal])
    (by
      rw [Category.assoc, projModelMulBy_projModelOver, c.modelPoint_projModelOver,
        projModelZero_projModelOver]
      rfl)

variable (hP₀ : ∀ s, P s ≠ E.zero s) (hQ₀ : ∀ s, Q s ≠ E.zero s)
  (hP₃ : P ≫ (E.mulBy 3).left = E.zero) (hQ₃ : Q ≫ (E.mulBy 3).left = E.zero)
  (hQP : ∀ s, Q s ≠ P s ∧ Q s ≠ (P ≫ E.neg) s)

include hP hQ hP₀ hQ₀ hP₃ hQ₃ hQP in
variable (E) in
/-- **The universal level-three normal form.** Let `E` be an elliptic curve over a scheme `S` and
`P`, `Q` sections of `E` which meet the zero section over no point of `S`, are killed by
multiplication by `3`, and such that `Q` is neither `P` nor `-P` over any point of `S`. Then there
is a unique pair of a morphism `f : S ⟶ Spec ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]` and a morphism `g` from `E`
to the projective model of the universal level-three normal form `Y² + 3μXY + (μ³ - 1)Y = X³` such
that `g` exhibits `E` as the base change of the universal curve along `f`, carrying the zero section
of `E` to the zero section, `P` to the point `(0, 0)` and `Q` to the point
`(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))`. Conversely, such a pair exists only if `P` and `Q` satisfy
the conditions (`exists_levelThreeNormalForm_iff`). -/
theorem existsUnique_levelThreeNormalForm :
    ∃! fg : (S ⟶ Spec (.of (ULift.{u} UniversalLevelThree.Ring))) ×
      (E.carrier ⟶ curveULift.projModel),
      IsPullback fg.2 E.structureMap curveULift.projModelOver fg.1 ∧
        E.zero ≫ fg.2 = fg.1 ≫ curveULift.projModelZero ∧ P ≫ fg.2 = fg.1 ≫ firstPoint ∧
        Q ≫ fg.2 = fg.1 ≫ secondPoint := by
  have hσ : ∀ i, ![P, Q] i ≫ E.structureMap = 𝟙 S := Fin.forall_fin_two.mpr ⟨hP, hQ⟩
  -- on every chart, this is the affine case for the model points of `P` and `Q`
  refine (existsUnique_congr fun _ ↦ by rw [Fin.forall_fin_two]; exact Iff.rfl).mp
    (existsUnique_isPullback_of_forall_chart (t₀ := curveULift.projModelZero)
      (t := ![firstPoint, secondPoint]) hσ fun c ↦ ?_)
  refine (existsUnique_congr fun _ ↦ by rw [Fin.forall_fin_two]; exact Iff.rfl).mpr
    (existsUnique_isLevelThree (c.modelPoint_projModelOver hP) (c.modelPoint_projModelOver hQ)
      (c.modelPoint_apply_ne hP hP₀) (c.modelPoint_apply_ne hQ hQ₀)
      (modelPoint_projModelMulBy hP hP₃ c) (modelPoint_projModelMulBy hQ hQ₃ c) fun s ↦
        ⟨c.modelPoint_apply_ne_modelPoint hP hQ (fun s ↦ (hQP s).1) s, ?_⟩)
  rw [← modelPoint_neg c hP]
  exact c.modelPoint_apply_ne_modelPoint _ hQ (fun s ↦ (hQP s).2) s

include hP hQ in
variable (E) in
/-- **The conditions of the level-three normal form are necessary.** Two sections `P` and `Q` of
an elliptic curve `E` over `S` are the pullbacks of the points `(0, 0)` and
`(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` of the universal level-three normal form along a cartesian
morphism from `E` carrying the zero section to the zero section exactly when they meet the zero
section over no point of `S`, are killed by multiplication by `3`, and `Q` is neither `P` nor `-P`
over any point of `S`. -/
theorem exists_levelThreeNormalForm_iff :
    (∃ (f : S ⟶ Spec (.of (ULift.{u} UniversalLevelThree.Ring)))
      (g : E.carrier ⟶ curveULift.projModel),
      IsPullback g E.structureMap curveULift.projModelOver f ∧
        E.zero ≫ g = f ≫ curveULift.projModelZero ∧ P ≫ g = f ≫ firstPoint ∧
        Q ≫ g = f ≫ secondPoint) ↔
      (∀ s, P s ≠ E.zero s) ∧ (∀ s, Q s ≠ E.zero s) ∧ P ≫ (E.mulBy 3).left = E.zero ∧
        Q ≫ (E.mulBy 3).left = E.zero ∧ ∀ s, Q s ≠ P s ∧ Q s ≠ (P ≫ E.neg) s := by
  refine ⟨fun ⟨f, g, hg, h₀, hgP, hgQ⟩ ↦ ?_, fun ⟨hP₀, hQ₀, hP₃, hQ₃, hQP⟩ ↦
    let ⟨⟨f, g⟩, h, _⟩ := E.existsUnique_levelThreeNormalForm hP hQ hP₀ hQ₀ hP₃ hQ₃ hQP
    ⟨f, g, h⟩⟩
  -- `g` carries `P`, `Q`, `-P` and `3P`, `3Q` to the corresponding points of the universal curve,
  -- which satisfy the conditions
  have hne {R₁ R₂ : S ⟶ E.carrier} {pt₁ pt₂ : _ ⟶ curveULift.projModel} (h₁ : R₁ ≫ g = f ≫ pt₁)
      (h₂ : R₂ ≫ g = f ≫ pt₂) (hpt : ∀ s, pt₁ s ≠ pt₂ s) (s : S) : R₁ s ≠ R₂ s := fun hs ↦
    hpt (f s) (by simpa only [← Scheme.Hom.comp_apply, h₁, h₂] using congrArg g hs)
  have h₃ {R' : S ⟶ E.carrier} (hR' : R' ≫ E.structureMap = 𝟙 S) {pt : _ ⟶ curveULift.projModel}
      (hpt : R' ≫ g = f ≫ pt) (hpt₃ : pt ≫ curveULift.projModelMulBy 3 = curveULift.projModelZero) :
      R' ≫ (E.mulBy 3).left = E.zero :=
    hg.hom_ext (by rw [Category.assoc, ← curveULift.comp_projModelMulBy_of_isPullback hg h₀,
      reassoc_of% hpt, hpt₃, h₀]) (by simp [hR'])
  have hneg : E.neg ≫ g = g ≫ curveULift.projModelNeg := by
    -- `g` read into the elliptic curve `toEllipticCurveGeom curveULift` commutes with negation
    have hg' : IsPullback (g ≫ (toEllipticCurveGeomIso curveULift).inv) E.structureMap
        (toEllipticCurveGeom curveULift).structureMap f := by
      simpa using hg.paste_horiz (IsPullback.of_horiz_isIso
        (fst := (toEllipticCurveGeomIso curveULift).inv) (snd := curveULift.projModelOver)
        (f := (toEllipticCurveGeom curveULift).structureMap) (g := 𝟙 _)
        ⟨by simp [← toEllipticCurveGeomIso_hom_projModelOver]⟩)
    have := neg_comp_of_isPullback hg'
      (by simp [reassoc_of% h₀, ← zero_toEllipticCurveGeomIso_hom])
    simpa [neg_toEllipticCurveGeomIso_hom (W := curveULift)] using
      this =≫ (toEllipticCurveGeomIso curveULift).hom
  have hgP' : (P ≫ E.neg) ≫ g = f ≫ firstPoint ≫ curveULift.projModelNeg := by
    rw [Category.assoc, hneg, reassoc_of% hgP]
  exact ⟨hne hgP h₀ firstPoint_ne_projModelZero, hne hgQ h₀ secondPoint_ne_projModelZero,
    h₃ hP hgP firstPoint_projModelMulBy_three, h₃ hQ hgQ secondPoint_projModelMulBy_three,
    fun s ↦ ⟨hne hgQ hgP secondPoint_ne_firstPoint s,
      hne hgQ hgP' secondPoint_ne_firstPoint_projModelNeg s⟩⟩

/-! ### The universal level-three normal form as an elliptic curve -/

-- Reading the universal level-three normal form on its projective model through
-- `toEllipticCurveGeomIso` identifies classifying pairs into `curveGeom` with the classifying
-- pairs of `existsUnique_levelThreeNormalForm`.
private theorem isLevelThree_curveGeom_iff
    {f : S ⟶ Spec (.of (ULift.{u} UniversalLevelThree.Ring))}
    {g : E.carrier ⟶ curveGeom.{u}.carrier} :
    (IsPullback g E.structureMap curveGeom.structureMap f ∧ E.zero ≫ g = f ≫ curveGeom.zero ∧
      P ≫ g = f ≫ firstPointHom.left ∧ Q ≫ g = f ≫ secondPointHom.left) ↔
    (IsPullback (g ≫ (toEllipticCurveGeomIso curveULift).hom) E.structureMap
        curveULift.projModelOver f ∧
      E.zero ≫ g ≫ (toEllipticCurveGeomIso curveULift).hom = f ≫ curveULift.projModelZero ∧
      P ≫ g ≫ (toEllipticCurveGeomIso curveULift).hom = f ≫ firstPoint ∧
      Q ≫ g ≫ (toEllipticCurveGeomIso curveULift).hom = f ≫ secondPoint) := by
  have hiso : IsPullback (toEllipticCurveGeomIso curveULift.{u}).hom curveGeom.structureMap
      curveULift.projModelOver (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [toEllipticCurveGeomIso_hom_projModelOver, Category.comp_id]⟩
  refine and_congr ⟨fun hg ↦ by simpa using hg.paste_horiz hiso, fun hg ↦ ?_⟩ ?_
  · exact IsPullback.of_right (by simpa using hg) (by simpa using hg.w) hiso
  · refine and_congr ?_ (and_congr ?_ ?_) <;>
    · rw [← cancel_mono (toEllipticCurveGeomIso curveULift).hom]
      simp

include hP hQ hP₀ hQ₀ hP₃ hQ₃ hQP in
variable (E) in
/-- **The universal level-three normal form as an elliptic curve.** The universal property
`existsUnique_levelThreeNormalForm`, with the universal level-three normal form read as the
elliptic curve `curveGeom` and its basis of the `3`-torsion as `firstPointHom` and
`secondPointHom`: there is a unique pair of a morphism `f : S ⟶ Spec ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]` and
a morphism `g` from `E` to `curveGeom` exhibiting `E` as the pullback of `curveGeom` along `f`,
carrying the zero section to the zero section, `P` to `(0, 0)` and `Q` to
`(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))`. -/
theorem existsUnique_levelThreeNormalForm_curveGeom :
    ∃! fg : (S ⟶ Spec (.of (ULift.{u} UniversalLevelThree.Ring))) ×
      (E.carrier ⟶ curveGeom.{u}.carrier),
      IsPullback fg.2 E.structureMap curveGeom.structureMap fg.1 ∧
        E.zero ≫ fg.2 = fg.1 ≫ curveGeom.zero ∧ P ≫ fg.2 = fg.1 ≫ firstPointHom.left ∧
        Q ≫ fg.2 = fg.1 ≫ secondPointHom.left := by
  obtain ⟨⟨f, g⟩, hfg, huniq⟩ := E.existsUnique_levelThreeNormalForm hP hQ hP₀ hQ₀ hP₃ hQ₃ hQP
  refine ⟨(f, g ≫ (toEllipticCurveGeomIso curveULift).inv),
    isLevelThree_curveGeom_iff.mpr (by simpa using hfg), fun ⟨f', g'⟩ hfg' ↦ ?_⟩
  have := huniq (f', g' ≫ (toEllipticCurveGeomIso curveULift).hom)
    (isLevelThree_curveGeom_iff.mp hfg')
  simp only [Prod.mk.injEq] at this
  exact Prod.ext this.1 (by simp [← this.2])

end EllipticCurveGeom

namespace UniversalLevelThree

open MonoidalCategory

/-! ### The universal basis of the `3`-torsion -/

-- The universal basis satisfies the conditions of the level-three normal form, as the basis it is
-- carried to by the identity.
private theorem basisHom_conditions :
    (∀ s, firstPointHom.{u}.left s ≠ curveGeom.zero s) ∧
      (∀ s, secondPointHom.{u}.left s ≠ curveGeom.zero s) ∧
      firstPointHom.{u}.left ≫ (curveGeom.mulBy 3).left = curveGeom.zero ∧
      secondPointHom.{u}.left ≫ (curveGeom.mulBy 3).left = curveGeom.zero ∧
      ∀ s, secondPointHom.{u}.left s ≠ firstPointHom.left s ∧
        secondPointHom.{u}.left s ≠ (firstPointHom.left ≫ curveGeom.neg) s :=
  (curveGeom.exists_levelThreeNormalForm_iff (Over.w firstPointHom) (Over.w secondPointHom)).mp
    ⟨𝟙 _, (toEllipticCurveGeomIso curveULift).hom,
      IsPullback.of_horiz_isIso
        ⟨by rw [toEllipticCurveGeomIso_hom_projModelOver, Category.comp_id]⟩,
      by rw [zero_toEllipticCurveGeomIso_hom, Category.id_comp], by simp, by simp⟩

/-- The point `(0, 0)` of `curveGeom` misses the zero section at every point of the base. -/
theorem firstPointHom_left_ne_zero (s) : firstPointHom.{u}.left s ≠ curveGeom.zero s :=
  basisHom_conditions.1 s

/-- The point `(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` of `curveGeom` misses the zero section at
every point of the base. -/
theorem secondPointHom_left_ne_zero (s) : secondPointHom.{u}.left s ≠ curveGeom.zero s :=
  basisHom_conditions.2.1 s

/-- The point `(0, 0)` of `curveGeom` is killed by `3`. -/
@[reassoc]
theorem firstPointHom_left_comp_mulBy_three_left :
    firstPointHom.{u}.left ≫ (curveGeom.mulBy 3).left = curveGeom.zero :=
  basisHom_conditions.2.2.1

/-- The point `(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` of `curveGeom` is killed by `3`. -/
@[reassoc]
theorem secondPointHom_left_comp_mulBy_three_left :
    secondPointHom.{u}.left ≫ (curveGeom.mulBy 3).left = curveGeom.zero :=
  basisHom_conditions.2.2.2.1

/-- The two basis points of `curveGeom` differ at every point of the base. -/
theorem secondPointHom_left_ne_firstPointHom_left (s) :
    secondPointHom.{u}.left s ≠ firstPointHom.{u}.left s :=
  (basisHom_conditions.2.2.2.2 s).1

/-- The point `(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` of `curveGeom` differs from the negative of
`(0, 0)` at every point of the base. -/
theorem secondPointHom_left_ne_firstPointHom_left_neg (s) :
    secondPointHom.{u}.left s ≠ (firstPointHom.{u}.left ≫ curveGeom.neg) s :=
  (basisHom_conditions.2.2.2.2 s).2

end UniversalLevelThree

end TauCeti.AlgebraicGeometry
