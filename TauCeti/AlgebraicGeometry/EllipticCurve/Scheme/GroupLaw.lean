/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Grp
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.MonObj
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Points
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Neg
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Inverse

/-!
# The group law of the projective Weierstrass model

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`, let `E = projModel W` be its
projective model over `S = Spec R`, and regard `E` as the object `Over.mk W.projModelOver` of the
cartesian monoidal category `Over S`, whose tensor product is the fibre product over `S`. This
file makes `E` a commutative group object of `Over S`: a commutative group scheme over `S`. The
unit is the zero section `[0 : 1 : 0]` (`WeierstrassCurve.projModelZero`), the multiplication is
the Bosma–Lenstra addition morphism `E ×_S E ⟶ E` (`WeierstrassCurve.additionMorphism`), and the
inverse is the negation morphism `[X : Y : Z] ↦ [X : -Y - a₁X - a₃Z : Z]`
(`WeierstrassCurve.projModelNeg`).

The underlying commutative monoid object is `WeierstrassCurve.monObjProjModelOver`, whose axioms
are the unit laws, associativity and commutativity of the addition morphism. The inverse laws are
the right inverse law `WeierstrassCurve.additionMorphism_right_inv` and the left inverse law,
which follows from it by commutativity `WeierstrassCurve.additionMorphism_comm`.

Over a field `K`, the points of this group scheme with values in `Spec K` form the group
`W.toAffine.Point` of Mathlib: the dictionary `WeierstrassCurve.projModelPointsEquiv` between the
sections of `projModel W ⟶ Spec K` and `W.toAffine.Point` carries the addition morphism to the
addition of points (`WeierstrassCurve.projModelPointsEquiv_lift_additionMorphism`).

## Main definitions

* `WeierstrassCurve.grpObjProjModel`: the group-object structure on `Over.mk W.projModelOver`.
* `WeierstrassCurve.projModelPointsMulEquiv`: over a field `K`, the isomorphism between the group
  of points of `projModel W` with values in `Spec K` and the group `W.toAffine.Point`.

## Main results

* `WeierstrassCurve.inv_projModelOver_left`: the inverse is the negation morphism. The unit and
  multiplication are described by `WeierstrassCurve.one_projModelOver_left` and
  `WeierstrassCurve.mul_projModelOver_left`, and their commutativity is
  `WeierstrassCurve.isCommMonObj_projModelOver`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §2.1.
* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.
* AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), file
  `projects/ModularCurves/ModularCurves/EllipticCurve/GroupLawConstruction.lean` at commit
  `c3415f32a313e19ace43e05479aeaa0d56ca287a`, which states the group laws of the same projective
  model as equations of morphisms of `Over (Spec R)` for its multiplication `mulOver`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

universe u

namespace WeierstrassCurve

section CommRing

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]

-- Adding the negation on the left is the zero section.
private theorem additionMorphism_left_inv :
    pullback.lift (f := W.projModelOver) (g := W.projModelOver) W.projModelNeg (𝟙 W.projModel)
      (by simp) ≫ W.additionMorphism = W.projModelOver ≫ W.projModelZero := by
  have h : pullback.lift (f := W.projModelOver) (g := W.projModelOver) W.projModelNeg
      (𝟙 W.projModel) (by simp) =
        pullback.lift (𝟙 W.projModel) W.projModelNeg (by simp) ≫
          (pullbackSymmetry W.projModelOver W.projModelOver).hom := by
    apply pullback.hom_ext <;> simp
  rw [h, Category.assoc, additionMorphism_comm, additionMorphism_right_inv]

/-- **The group law of the projective Weierstrass model.** For an elliptic Weierstrass curve `W`
over a commutative ring `R`, the projective model `projModel W ⟶ Spec R`, as an object of the
cartesian monoidal category `Over (Spec R)`, is a group object: its unit is the zero section
`projModelZero`, its multiplication is the Bosma–Lenstra addition morphism `additionMorphism`, and
its inverse is the negation morphism `projModelNeg`. -/
noncomputable instance grpObjProjModel : GrpObj (Over.mk W.projModelOver) where
  toMonObj := W.monObjProjModelOver
  inv := Over.homMk W.projModelNeg (by simp)
  left_inv := by
    ext1
    simp [additionMorphism_left_inv]
  right_inv := by
    ext1
    simp

/-- The inverse of the group law of the projective Weierstrass model is the negation morphism. -/
@[simp]
theorem inv_projModelOver_left : ι[Over.mk W.projModelOver].left = W.projModelNeg :=
  (rfl)

end CommRing

/-! ### The group of points over a field -/

section Field

variable {K : Type u} [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- **The group of points of the projective model over a field.** For an elliptic Weierstrass
curve `W` over a field `K`, the points of the group scheme `projModel W` with values in the base
`Spec K`, with the group law of `grpObjProjModel`, form a group isomorphic to the group
`W.toAffine.Point` of Mathlib. The isomorphism is the dictionary `projModelPointsEquiv` between
sections of `projModel W ⟶ Spec K` and `W.toAffine.Point`, which is additive by
`projModelPointsEquiv_lift_additionMorphism`. -/
noncomputable def projModelPointsMulEquiv :
    (𝟙_ (Over (Spec (.of K))) ⟶ Over.mk W.projModelOver) ≃* Multiplicative W.toAffine.Point where
  toFun x := .ofAdd (W.projModelPointsEquiv ⟨x.left, by simpa using x.w⟩)
  invFun P := Over.homMk (W.projModelPointsEquiv.symm P.toAdd).1
    (by simpa using (W.projModelPointsEquiv.symm P.toAdd).2)
  left_inv x := by
    ext1
    simp
  right_inv P := by
    simp
  map_mul' x y := by
    rw [← ofAdd_add, ← projModelPointsEquiv_lift_additionMorphism]
    simp [Hom.mul_def]

/-- The point of `W` corresponding to a point `x` of the projective model over `Spec K` is the
point corresponding to the section `x.left` of `projModel W ⟶ Spec K` under
`projModelPointsEquiv`. -/
@[simp]
theorem toAdd_projModelPointsMulEquiv (x : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk W.projModelOver) :
    (W.projModelPointsMulEquiv x).toAdd =
      W.projModelPointsEquiv ⟨x.left, by simpa using x.w⟩ :=
  (rfl)

/-- The point of the projective model over `Spec K` corresponding to a point `P` of `W` is the
section of `projModel W ⟶ Spec K` corresponding to `P` under `projModelPointsEquiv`. -/
@[simp]
theorem projModelPointsMulEquiv_symm_apply_left (P : Multiplicative W.toAffine.Point) :
    (W.projModelPointsMulEquiv.symm P).left = (W.projModelPointsEquiv.symm P.toAdd).1 :=
  (rfl)

end Field

end WeierstrassCurve
