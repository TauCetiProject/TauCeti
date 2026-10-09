/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Morphism
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Neg
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Point
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Comm
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Points
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Integral
import TauCeti.AlgebraicGeometry.EllipticCurve.Universal

/-!
# The negation morphism is an inverse for the Bosma–Lenstra addition morphism

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`, let `E = projModel W` be its
projective model over `S = Spec R`, with structure morphism `π : E ⟶ S`, zero section `0 : S ⟶ E`
and negation morphism `ν = projModelNeg W : E ⟶ E`, and let `E ×_S E ⟶ E` be the Bosma–Lenstra
addition morphism `WeierstrassCurve.additionMorphism`. This file shows that the negation morphism
is a left and a right inverse for the addition morphism: the morphisms `E ⟶ E ×_S E` with
components `(ν, 𝟙)` and `(𝟙, ν)`, followed by the addition morphism, are the composite `π ≫ 0`
of the structure morphism and the zero section.

These equations supply the left and right inverse axioms for the projective model as a group
object over `Spec R`. They hold over arbitrary commutative rings when the curve is elliptic.

## Main results

* `WeierstrassCurve.lift_projModelNeg_id_additionMorphism`: the negation morphism is a left
  inverse for the addition morphism of an elliptic Weierstrass curve over a commutative ring.
* `WeierstrassCurve.lift_id_projModelNeg_additionMorphism`: the negation morphism is a right
  inverse for the addition morphism of an elliptic Weierstrass curve over a commutative ring.

## References

* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.

## Provenance

`lift_projModelNeg_id_additionMorphism` and `lift_id_projModelNeg_additionMorphism` are adapted
from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/EllipticCurve/GroupLawAxioms.lean`, declarations
`invOver_mulOver_atlas`, the left inverse law over the universal base, and
`invOver_mulOver_of_map`, `invOver_mulOver_of_eq` and `invOver_mulOver`, its transport to every
elliptic Weierstrass curve, and file `ModelRecord.lean` of the same directory, the field
`right_inv` of the definition `modelGrpObj`, the right inverse law, deduced from the left one and
commutativity. The other files named below lie in that directory too.

The source states the left inverse law as an equation of morphisms of `Over (Spec R)`, for its
morphisms `invOver`, `oneOver` and `mulOver` (file `GroupLawConstruction.lean`), with the pairing
`lift` and the morphism `toUnit` to the unit of the cartesian monoidal structure:
`lift (invOver W) (𝟙 (modelOver W)) ≫ mulOver W = toUnit (modelOver W) ≫ oneOver W`. It does not
state the right inverse law as a theorem: it proves it only as the field `right_inv` of
`modelGrpObj`. Here the two laws are equations of morphisms of schemes `E ⟶ E`, for the morphisms
`E ⟶ E ×_S E` with components `(ν, 𝟙)` and `(𝟙, ν)`, built with `pullback.lift`. The source
obtains the same two equations from its laws in `Over (Spec R)`, by taking underlying morphisms,
inside the proofs of `EllipticCurveGeom.grpObj_left_inv` and `EllipticCurveGeom.grpObj_right_inv`
(file `GroupLawDescent.lean`).

The source proves the left inverse law over one ring, the copy `WeierstrassAtlasRingU` in `Type u`
of its universal ring (file `AdditionBaseChange.lean`), by its extensionality principle
`hom_ext_of_forall_specPoint` for field-valued points (file `PointsDictionary.lean`). It evaluates
the multiplication on a pair of points over a field with `mulModelHom_specPoints` (file
`AdditionSpecPoints.lean`) and the negation on a point over a field with `negModelHom_specPoints`
(file `GroupLawConstruction.lean`), and concludes from `neg_add_cancel` in
`WeierstrassCurve.Affine.Point` through its dictionary `projModelPointsEquiv`, which sends the
zero section to `0` (`projModelPointsEquiv_zero`, file `PointsDictionary.lean`). Here the same
argument is carried out for every curve whose projective model is reduced, in particular over
every integral domain, with Mathlib's `AlgebraicGeometry.ext_of_fromSpecResidueField_eq` in place
of `hom_ext_of_forall_specPoint`, on points given by homogeneous coordinates
(`WeierstrassCurve.exists_ringHom_eq_projModelPoint`,
`WeierstrassCurve.projModelPoint_projModelNeg`, `WeierstrassCurve.SpecMap_projModelZero` and
`WeierstrassCurve.lift_projModelPoint_additionMorphism_eq_add`), and concludes from
`WeierstrassCurve.Projective.neg_add_cancel_equiv`, the form for point representatives of
`neg_add_cancel` in Mathlib's `WeierstrassCurve.Projective.Point`. The transport to every curve
follows the source, with the reduction `WeierstrassCurve.exists_map_eq_of_isElliptic` in place of
the source's named universal curve `universalWeierstrassLocU` over `WeierstrassAtlasRingU`, and
with `WeierstrassCurve.projModelNeg_projModelBaseChange` and
`WeierstrassCurve.projModelZero_projModelBaseChange` in place of the source's
`negModelHom_baseChange` (file `NegModelBaseChange.lean`) and `projModelZero_baseChangeOf`. The
right inverse law is deduced from the left one and commutativity, as in the source, by comparing
the components of the two morphisms to `E ×_S E`, where the source uses Mathlib's
`CategoryTheory.CartesianMonoidalCategory.lift_braiding_hom`.
-/

public section

/-
Over an integral domain `R`, the scheme `E` is integral, hence reduced, and it is separated, so
two morphisms `E ⟶ E` are equal as soon as they agree on the points of `E` with values in its
residue fields. Such a point has homogeneous coordinates `P` over a field, the negation morphism
sends it to the point with homogeneous coordinates `neg P`, Mathlib's negation of `P`, and the
composite `π ≫ 0` sends it to the point with homogeneous coordinates `(0, 1, 0)` over the same
field. The addition morphism sends the pair of the points with homogeneous coordinates `neg P` and
`P` to the point with homogeneous coordinates the sum `add (neg P) P` of Mathlib's addition of
point representatives, and `add (neg P) P` and `(0, 1, 0)` represent the same point
(`WeierstrassCurve.Projective.neg_add_cancel_equiv`).

An elliptic Weierstrass curve over an arbitrary commutative ring is the base change of one over an
integral domain (`WeierstrassCurve.exists_map_eq_of_isElliptic`). The left inverse law passes to a
base change `W.map f`, because `projModel (W.map f)` is the base change of `projModel W`
(`WeierstrassCurve.isPullback_projModelBaseChange`), and the addition morphism, the negation
morphism and the zero section commute with base change
(`WeierstrassCurve.additionMorphism_projModelBaseChange`,
`WeierstrassCurve.projModelNeg_projModelBaseChange` and
`WeierstrassCurve.projModelZero_projModelBaseChange`). The right inverse law follows from the left
one, because the addition morphism is commutative (`WeierstrassCurve.additionMorphism_comm`).
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Field

variable [W.IsElliptic] {K : Type u} [Field K]

open Projective in
-- Over a field, the addition morphism sends the pair of the negation of the point with
-- homogeneous coordinates `P` and that point to the zero section.
private theorem lift_projModelNeg_projModelPoint_additionMorphism {g : R →+* K} {P : Fin 3 → K}
    {hP : (W.toProjective.map g).Equation P} {i : Fin 3} (hi : IsUnit (P i)) :
    pullback.lift (W.projModelPoint g hP hi ≫ W.projModelNeg) (W.projModelPoint g hP hi)
        (by rw [Category.assoc, projModelNeg_projModelOver]) ≫ W.additionMorphism =
      Spec.map (CommRingCat.ofHom g) ≫ W.projModelZero := by
  -- a solution with a nonzero coordinate on an elliptic curve over a field is nonsingular
  have hP' := (equation_iff_nonsingular_of_ne_zero (Function.ne_iff.mpr ⟨i, hi.ne_zero⟩)).mp hP
  -- the negation `neg P` and the sum `add (neg P) P` are nonsingular, so each of them has a
  -- nonzero coordinate
  have hN := nonsingular_neg hP'
  obtain ⟨j, hj⟩ := Function.ne_iff.mp (ne_zero_of_nonsingular hN)
  obtain ⟨m, hm⟩ := Function.ne_iff.mp (ne_zero_of_nonsingular (nonsingular_add hN hP'))
  -- the negation of the point is the point with homogeneous coordinates `neg P`, so the pair goes
  -- to the point with homogeneous coordinates `add (neg P) P`, a unit multiple of `(0, 1, 0)`,
  -- the homogeneous coordinates of the zero section
  obtain ⟨u, hu⟩ := neg_add_cancel_equiv hP'
  simp only [W.projModelPoint_projModelNeg hi hj.isUnit, SpecMap_projModelZero]
  rw [W.lift_projModelPoint_additionMorphism_eq_add hj.isUnit hi hm.isUnit,
    projModelPoint_eq_projModelPoint_iff]
  exact ⟨rfl, u, hu.symm⟩

-- The morphism `E ⟶ E ×_S E` with components `(ν, 𝟙)`, followed by the addition morphism, agrees
-- with `π ≫ 0` on every point of `E` with values in a field.
private theorem comp_lift_projModelNeg_id_additionMorphism (p : Spec (.of K) ⟶ W.projModel) :
    p ≫ pullback.lift W.projModelNeg (𝟙 W.projModel)
        (by rw [projModelNeg_projModelOver, Category.id_comp]) ≫ W.additionMorphism =
      p ≫ W.projModelOver ≫ W.projModelZero := by
  -- `p` is the point with homogeneous coordinates `P`, along a ring homomorphism `g`
  obtain ⟨g, P, hP, i, hi, rfl⟩ := W.exists_ringHom_eq_projModelPoint p
  rw [projModelPoint_projModelOver_assoc,
    ← W.lift_projModelNeg_projModelPoint_additionMorphism (hP := hP) hi, ← Category.assoc]
  -- and it goes to the pair of its negation and itself
  refine congrArg (· ≫ W.additionMorphism) (pullback.hom_ext ?_ ?_)
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]

end Field

-- The negation morphism is a left inverse for the addition morphism whenever `E` is reduced, as it
-- is over an integral domain: `E` is a separated scheme, so it suffices that the two sides agree
-- on the points of `E` with values in its residue fields.
private theorem lift_projModelNeg_id_additionMorphism_of_isReduced [W.IsElliptic]
    [IsReduced W.projModel] :
    pullback.lift W.projModelNeg (𝟙 W.projModel)
        (by rw [projModelNeg_projModelOver, Category.id_comp]) ≫ W.additionMorphism =
      W.projModelOver ≫ W.projModelZero :=
  ext_of_fromSpecResidueField_eq _ _ (terminal.from _) Set.univ dense_univ
    (fun x _ ↦ W.comp_lift_projModelNeg_id_additionMorphism (Scheme.fromSpecResidueField _ x))
    (terminal.hom_ext _ _)

variable {R' : Type u} [CommRing R'] (f : R →+* R')

-- If the negation morphism of `W` is a left inverse for its addition morphism, then so is the
-- negation morphism of the base change `W.map f`.
private theorem lift_projModelNeg_id_additionMorphism_map [W.IsElliptic]
    (h : pullback.lift W.projModelNeg (𝟙 W.projModel)
        (by rw [projModelNeg_projModelOver, Category.id_comp]) ≫ W.additionMorphism =
      W.projModelOver ≫ W.projModelZero) :
    pullback.lift (W.map f).projModelNeg (𝟙 (W.map f).projModel)
        (by rw [projModelNeg_projModelOver, Category.id_comp]) ≫ (W.map f).additionMorphism =
      (W.map f).projModelOver ≫ (W.map f).projModelZero := by
  -- a morphism to `projModel (W.map f)`, the base change of `projModel W` along `Spec f`, is
  -- determined by its composites with the base change morphism and with the structure morphism
  refine (W.isPullback_projModelBaseChange f).hom_ext ?_ ?_
  · rw [Category.assoc, additionMorphism_projModelBaseChange, ← Category.assoc]
    -- the base change morphism commutes with the zero sections, and the negation morphism of `W`
    -- is a left inverse
    conv_rhs =>
      rw [Category.assoc, projModelZero_projModelBaseChange,
        ← projModelBaseChange_projModelOver_assoc, ← h, ← Category.assoc]
    -- and the base change morphism commutes with the negation morphisms and with the identities
    refine congrArg (· ≫ W.additionMorphism) (pullback.hom_ext ?_ ?_)
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        projModelNeg_projModelBaseChange]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp,
        Category.comp_id]
  · -- both sides lie over `Spec R'`
    rw [Category.assoc, additionMorphism_projModelOver, pullback.lift_fst_assoc,
      projModelNeg_projModelOver, Category.assoc, projModelZero_projModelOver, Category.comp_id]

/-- **The negation morphism is a left inverse for the addition morphism.** Let `W` be an elliptic
Weierstrass curve over a commutative ring `R`, and write `E = projModel W` and `S = Spec R`, with
structure morphism `π : E ⟶ S`, zero section `0 : S ⟶ E` and negation morphism `ν : E ⟶ E`. The
morphism `E ⟶ E ×_S E` with components `ν` and the identity, followed by the Bosma–Lenstra
addition morphism `E ×_S E ⟶ E`, is `π ≫ 0`. This morphism `E ⟶ E ×_S E` is the underlying
morphism of the pair `CartesianMonoidalCategory.lift` of the corresponding morphisms of the
cartesian monoidal category `Over S` (`CategoryTheory.Over.lift_left`), and `π` is the underlying
morphism of `SemiCartesianMonoidalCategory.toUnit`, the morphism from `E` to the unit object of
`Over S` (`CategoryTheory.Over.toUnit_left`): the equation is that of
`CategoryTheory.GrpObj.left_inv`. -/
@[reassoc (attr := simp)]
theorem lift_projModelNeg_id_additionMorphism [W.IsElliptic] :
    pullback.lift W.projModelNeg (𝟙 W.projModel)
        (by rw [projModelNeg_projModelOver, Category.id_comp]) ≫ W.additionMorphism =
      W.projModelOver ≫ W.projModelZero := by
  -- `W` is the base change of an elliptic Weierstrass curve `W₀` over an integral domain, over
  -- which `E` is reduced
  obtain ⟨R₀, _, _, _, W₀, _, f, rfl⟩ := W.exists_map_eq_of_isElliptic
  exact W₀.lift_projModelNeg_id_additionMorphism_map f
    W₀.lift_projModelNeg_id_additionMorphism_of_isReduced

/-- **The negation morphism is a right inverse for the addition morphism.** Let `W` be an elliptic
Weierstrass curve over a commutative ring `R`, and write `E = projModel W` and `S = Spec R`, with
structure morphism `π : E ⟶ S`, zero section `0 : S ⟶ E` and negation morphism `ν : E ⟶ E`. The
morphism `E ⟶ E ×_S E` with components the identity and `ν`, followed by the Bosma–Lenstra
addition morphism `E ×_S E ⟶ E`, is `π ≫ 0`. This morphism `E ⟶ E ×_S E` is the underlying
morphism of the pair `CartesianMonoidalCategory.lift` of the corresponding morphisms of the
cartesian monoidal category `Over S` (`CategoryTheory.Over.lift_left`), and `π` is the underlying
morphism of `SemiCartesianMonoidalCategory.toUnit`, the morphism from `E` to the unit object of
`Over S` (`CategoryTheory.Over.toUnit_left`): the equation is that of
`CategoryTheory.GrpObj.right_inv`. -/
@[reassoc (attr := simp)]
theorem lift_id_projModelNeg_additionMorphism [W.IsElliptic] :
    pullback.lift (𝟙 W.projModel) W.projModelNeg
        (by rw [Category.id_comp, projModelNeg_projModelOver]) ≫ W.additionMorphism =
      W.projModelOver ≫ W.projModelZero := by
  -- the addition morphism is commutative, and the negation morphism is a left inverse
  rw [← W.additionMorphism_comm, ← Category.assoc]
  conv_rhs => rw [← W.lift_projModelNeg_id_additionMorphism]
  -- and the swap of the two factors exchanges the two components
  refine congrArg (· ≫ W.additionMorphism) (pullback.hom_ext ?_ ?_)
  · rw [Category.assoc, pullbackSymmetry_hom_comp_fst, pullback.lift_snd, pullback.lift_fst]
  · rw [Category.assoc, pullbackSymmetry_hom_comp_snd, pullback.lift_fst, pullback.lift_snd]

end WeierstrassCurve
