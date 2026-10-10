/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Grp
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Morphism
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Neg
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Assoc
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Comm
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Inverse
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Unit

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

The group axioms are the scheme-theoretic laws proved for these morphisms over an arbitrary base
ring: the right unit law `WeierstrassCurve.additionMorphism_right_unit`, associativity
`WeierstrassCurve.additionMorphism_assoc`, commutativity `WeierstrassCurve.additionMorphism_comm`
and the right inverse law `WeierstrassCurve.additionMorphism_right_inv`. The left unit and left
inverse laws follow from the right ones by commutativity.

## Main definitions

* `WeierstrassCurve.grpObjProjModel`: the group-object structure on `Over.mk W.projModelOver`.

## Main results

* `WeierstrassCurve.isCommMonObj_projModel`: the group law is commutative.
* `WeierstrassCurve.one_projModel_left`, `WeierstrassCurve.mul_projModel_left` and
  `WeierstrassCurve.inv_projModel_left`: the unit, multiplication and inverse are the zero
  section, the addition morphism and the negation morphism.

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

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]

-- Adding the zero section on the left is the identity.
private theorem additionMorphism_left_unit :
    pullback.lift (f := W.projModelOver) (g := W.projModelOver)
      (W.projModelOver ≫ W.projModelZero) (𝟙 W.projModel) (by simp) ≫ W.additionMorphism =
        𝟙 W.projModel := by
  have h : pullback.lift (f := W.projModelOver) (g := W.projModelOver)
      (W.projModelOver ≫ W.projModelZero) (𝟙 W.projModel) (by simp) =
        pullback.lift (𝟙 W.projModel) (W.projModelOver ≫ W.projModelZero) (by simp) ≫
          (pullbackSymmetry W.projModelOver W.projModelOver).hom := by
    apply pullback.hom_ext <;> simp
  rw [h, Category.assoc, additionMorphism_comm, additionMorphism_right_unit]

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
  one := Over.homMk W.projModelZero (by simp)
  mul := Over.homMk W.additionMorphism (by simp)
  inv := Over.homMk W.projModelNeg (by simp)
  one_mul := by
    -- `η ▷ E` pairs the zero section with a point, so this is the left unit law
    ext1
    simp only [Over.comp_left, Over.whiskerRight_left, Over.leftUnitor_hom_left, Over.mk_hom,
      Over.mk_left, Over.homMk_left, Over.tensorUnit_hom]
    conv_rhs => rw [← Category.comp_id (pullback.snd _ _), ← W.additionMorphism_left_unit]
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp [← pullback.condition_assoc]
  mul_one := by
    -- `E ◁ η` pairs a point with the zero section, so this is the right unit law
    ext1
    simp only [Over.comp_left, Over.whiskerLeft_left, Over.rightUnitor_hom_left, Over.mk_hom,
      Over.mk_left, Over.homMk_left, Over.tensorUnit_hom]
    conv_rhs => rw [← Category.comp_id (pullback.fst _ _), ← W.additionMorphism_right_unit]
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp [pullback.condition_assoc]
  mul_assoc := by
    -- the two sides add the three components of `(E ×_S E) ×_S E` as `(a + b) + c` and, through
    -- the associator, as `a + (b + c)`, which is `additionMorphism_assoc`
    ext1
    simp only [Over.comp_left, Over.whiskerRight_left, Over.whiskerLeft_left, Over.mk_hom,
      Over.mk_left, Over.homMk_left, Over.tensorObj_hom]
    rw [← Category.assoc]
    refine (congrArg (· ≫ W.additionMorphism) ?_).trans
      (W.additionMorphism_assoc.trans (congrArg (· ≫ W.additionMorphism) ?_))
    · -- `μ ▷ E` is `(a, b, c) ↦ (a + b, c)`
      apply pullback.hom_ext <;> simp
    · -- the associator followed by `E ◁ μ` is `(a, b, c) ↦ (a, b + c)`
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, Category.comp_id]
        exact (Over.associator_hom_left_fst (Over.mk W.projModelOver) (Over.mk W.projModelOver)
          (Over.mk W.projModelOver)).symm
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc]
        congr 1
        apply pullback.hom_ext
        · rw [pullback.lift_fst, Category.assoc]
          exact (Over.associator_hom_left_snd_fst (Over.mk W.projModelOver)
            (Over.mk W.projModelOver) (Over.mk W.projModelOver)).symm
        · rw [pullback.lift_snd, Category.assoc]
          exact (Over.associator_hom_left_snd_snd (Over.mk W.projModelOver)
            (Over.mk W.projModelOver) (Over.mk W.projModelOver)).symm
  left_inv := by
    ext1
    simp [additionMorphism_left_inv]
  right_inv := by
    ext1
    simp

/-- The unit of the group law of the projective Weierstrass model is the zero section. -/
@[simp]
theorem one_projModel_left : η[Over.mk W.projModelOver].left = W.projModelZero :=
  (rfl)

/-- The multiplication of the group law of the projective Weierstrass model is the Bosma–Lenstra
addition morphism. -/
@[simp]
theorem mul_projModel_left : μ[Over.mk W.projModelOver].left = W.additionMorphism :=
  (rfl)

/-- The inverse of the group law of the projective Weierstrass model is the negation morphism. -/
@[simp]
theorem inv_projModel_left : ι[Over.mk W.projModelOver].left = W.projModelNeg :=
  (rfl)

/-- **The group law of the projective Weierstrass model is commutative.** -/
instance isCommMonObj_projModel : IsCommMonObj (Over.mk W.projModelOver) where
  mul_comm := by
    ext1
    simp

end WeierstrassCurve
