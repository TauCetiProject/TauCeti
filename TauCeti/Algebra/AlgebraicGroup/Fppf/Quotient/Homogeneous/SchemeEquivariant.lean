/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Equivariant
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Scheme

/-!
# Equivariant morphisms between represented homogeneous quotients

Let `X` and `Y` represent the fppf homogeneous quotients `G/P` and `G/Q` over a commutative
ring `R`. Evaluation at the base point identifies equivariant scheme morphisms `X ⟶ Y` with
the `R`-points of `Y` fixed by `P`. Equivariance and fixedness are tested on points with values
in every `R`-algebra, using the representing isomorphisms.

The equivalence is transported from `fppfHomogeneousQuotientEquivariantEquiv` by full
faithfulness of the fppf functor of points. Its evaluation formula is expressed using the
canonical scheme projection `representedQuotientProjection`.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

namespace CommHopfAlgCat

open TauCeti

universe u

variable {R : Type u} [CommRing R] {G : _root_.CommHopfAlgCat.{u} R}
  {P Q : HopfIdeal R G} {X Y : Over (Spec (CommRingCat.of R))}
  (eP : fppfHomogeneousQuotient G P ≅ CommAlgCat.pointsSheaf X)
  (eQ : fppfHomogeneousQuotient G Q ≅ CommAlgCat.pointsSheaf Y)

/-- **Evaluation at the base point for represented homogeneous quotients.** Equivariant scheme
morphisms `X ⟶ Y` correspond to `R`-points of `Y` fixed by `P`. The representing isomorphisms
transport the action and fixed-point condition from the fppf quotients; both conditions quantify
over points with values in every `R`-algebra. -/
noncomputable def representedQuotientEquivariantEquiv :
    {f : X ⟶ Y // IsFppfHomogeneousQuotientEquivariant
      (eP.hom ≫ (CommAlgCat.pointsSheafFunctor R).map f ≫ eQ.inv)} ≃
    {y : (Spec (CommRingCat.of R)).asOver (Spec (CommRingCat.of R)) ⟶ Y //
      eQ.inv.hom.app (op (op (CommAlgCat.of R R))) (ULift.up y) ∈
        fppfHomogeneousQuotientFixedPoints G P Q} := by
  let eHom := (CommAlgCat.fullyFaithfulPointsSheafFunctor R).homEquiv.trans
    (Iso.homCongr eP eQ).symm
  let ePoint :
      ((Spec (CommRingCat.of R)).asOver (Spec (CommRingCat.of R)) ⟶ Y) ≃
        (fppfHomogeneousQuotient G Q).obj.obj (op (op (CommAlgCat.of R R))) :=
    Equiv.ulift.symm.trans <| Iso.toEquiv
      (((sheafToPresheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).mapIso eQ.symm).app
        (op (op (CommAlgCat.of R R))))
  exact ((eHom.subtypeEquiv (fun _ ↦ Iff.rfl)).trans
    (fppfHomogeneousQuotientEquivariantEquiv P Q)).trans
      (ePoint.subtypeEquiv (fun _ ↦ Iff.rfl)).symm

/-- The represented-quotient equivalence evaluates a scheme morphism at the image of the
identity group point under the canonical quotient projection. -/
@[simp]
theorem representedQuotientEquivariantEquiv_apply
    (f : {f : X ⟶ Y // IsFppfHomogeneousQuotientEquivariant
      (eP.hom ≫ (CommAlgCat.pointsSheafFunctor R).map f ≫ eQ.inv)}) :
    (representedQuotientEquivariantEquiv eP eQ f).val =
      Spec.mapMulEquiv (1 : WithConv (G →ₐ[R] R)) ≫
        representedQuotientProjection G P eP ≫ f.val := by
  change (eQ.hom.hom.app (op (op (CommAlgCat.of R R)))
    ((fppfHomogeneousQuotientEquivariantEquiv P Q
      ⟨eP.hom ≫ (CommAlgCat.pointsSheafFunctor R).map f.val ≫ eQ.inv, f.property⟩).val)).down = _
  rw [fppfHomogeneousQuotientEquivariantEquiv_apply]
  change (((eP.hom ≫ (CommAlgCat.pointsSheafFunctor R).map f.val ≫ eQ.inv) ≫ eQ.hom).hom.app
    (op (op (CommAlgCat.of R R)))
    ((fppfHomogeneousQuotientProjection G P).app (op (op (CommAlgCat.of R R)))
      (ULift.up (1 : WithConv (G →ₐ[R] R))))).down = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hmap := congrArg ULift.down
    (CommAlgCat.pointsSheafFunctor_map_hom_app f.val (op (op (CommAlgCat.of R R)))
      (eP.hom.hom.app (op (op (CommAlgCat.of R R)))
        ((fppfHomogeneousQuotientProjection G P).app (op (op (CommAlgCat.of R R)))
          (ULift.up (1 : HopfAlgebra.points (R := R) (H := G) (CommAlgCat.of R R))))).down)
  exact hmap.trans <| (congrArg (fun y ↦ y ≫ f.val)
    (mapMulEquiv_comp_representedQuotientProjection G P eP
      (1 : HopfAlgebra.points (R := R) (H := G) (CommAlgCat.of R R)))).symm.trans
        (Category.assoc _ _ _)

end CommHopfAlgCat
