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

## Main results

* `CommHopfAlgCat.representedQuotientEquivariantEquiv`: evaluation at the base point identifies
  equivariant scheme morphisms with fixed points.
* `CommHopfAlgCat.representedQuotientProjection_mem_fixedPoints_iff`: the point `gQ` is fixed by
  `P` over every algebra exactly when `g⁻¹Pg ⊆ Q` as subgroup schemes.
* `CommHopfAlgCat.representedQuotientRightMul`: the scheme morphism `xP ↦ xgQ` associated to
  such an inclusion.
* `CommHopfAlgCat.representedQuotientEquivariant_iff_exists_eq_rightMul_of_surjective`: over a
  commutative ring, every equivariant scheme morphism has this form if all `R`-points of the
  target quotient lift to `G(R)`.
* `CommHopfAlgCat.representedQuotientEquivariant_iff_exists_eq_rightMul`: over an algebraically
  closed field, the lifting hypothesis holds, so every equivariant scheme morphism has this form.
* `CommHopfAlgCat.representedQuotientRightMul_eq_iff`: two representatives give the same scheme
  morphism exactly when they give the same point of `Y`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 5.22 (the quotient universal property).
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

/-- **Fixed cosets on a representing scheme.** The point `gQ` of `Y` is fixed by `P` on points
with values in every algebra exactly when `g⁻¹Pg ⊆ Q` as subgroup schemes. In the contravariant
order on defining Hopf ideals, the inclusion is `Q.conjugate g ≤ P`. -/
theorem representedQuotientProjection_mem_fixedPoints_iff
    (g : HopfAlgebra.points (R := R) (H := G) (CommAlgCat.of R R)) :
    eQ.inv.hom.app (op (op (CommAlgCat.of R R)))
        (ULift.up (Spec.mapMulEquiv g ≫ representedQuotientProjection G Q eQ)) ∈
      fppfHomogeneousQuotientFixedPoints G P Q ↔ Q.conjugate g ≤ P := by
  have hpoint : ULift.up (Spec.mapMulEquiv g ≫ representedQuotientProjection G Q eQ) =
      eQ.hom.hom.app (op (op (CommAlgCat.of R R)))
        ((fppfHomogeneousQuotientProjection G Q).app (op (op (CommAlgCat.of R R)))
          (ULift.up g)) :=
    ULift.ext (mapMulEquiv_comp_representedQuotientProjection G Q eQ g)
  have hvalue := congrArg (fun y ↦ eQ.inv.hom.app (op (op (CommAlgCat.of R R))) y) hpoint
  have hcancel : eQ.inv.hom.app (op (op (CommAlgCat.of R R)))
      (eQ.hom.hom.app (op (op (CommAlgCat.of R R)))
        ((fppfHomogeneousQuotientProjection G Q).app (op (op (CommAlgCat.of R R)))
          (ULift.up g))) =
      (fppfHomogeneousQuotientProjection G Q).app (op (op (CommAlgCat.of R R)))
        (ULift.up g) := by
    change ((eQ.hom ≫ eQ.inv).hom.app (op (op (CommAlgCat.of R R))) _) = _
    rw [eQ.hom_inv_id]
    rfl
  exact (Iff.of_eq (congrArg (fun y ↦ y ∈ fppfHomogeneousQuotientFixedPoints G P Q)
    (hvalue.trans hcancel))).trans (projection_mem_fppfHomogeneousQuotientFixedPoints_iff G g)

/-- The scheme morphism `xP ↦ xgQ` between represented homogeneous quotients. It is obtained
from the corresponding fppf sheaf morphism by full faithfulness of the functor of points. -/
noncomputable def representedQuotientRightMul
    (g : HopfAlgebra.points (R := R) (H := G) (CommAlgCat.of R R))
    (h : Q.conjugate g ≤ P) : X ⟶ Y :=
  ((CommAlgCat.fullyFaithfulPointsSheafFunctor R).homEquiv.trans
    (Iso.homCongr eP eQ).symm).symm (fppfHomogeneousQuotientRightMul G g h)

/-- A scheme morphism is `xP ↦ xgQ` exactly when its morphism of fppf quotient sheaves is the
corresponding right-multiplication morphism. -/
theorem eq_representedQuotientRightMul_iff
    (g : HopfAlgebra.points (R := R) (H := G) (CommAlgCat.of R R))
    (h : Q.conjugate g ≤ P) (f : X ⟶ Y) :
    f = representedQuotientRightMul eP eQ g h ↔
      eP.hom ≫ (CommAlgCat.pointsSheafFunctor R).map f ≫ eQ.inv =
        fppfHomogeneousQuotientRightMul G g h := by
  exact Equiv.eq_symm_apply
    ((CommAlgCat.fullyFaithfulPointsSheafFunctor R).homEquiv.trans
      (Iso.homCongr eP eQ).symm)

/-- **Independence of the representative.** Two morphisms `xP ↦ xgQ` between representing
schemes agree exactly when their representatives give the same scheme point `gQ` of `Y`. -/
theorem representedQuotientRightMul_eq_iff
    {g g' : HopfAlgebra.points (R := R) (H := G) (CommAlgCat.of R R)}
    (h : Q.conjugate g ≤ P) (h' : Q.conjugate g' ≤ P) :
    representedQuotientRightMul eP eQ g h = representedQuotientRightMul eP eQ g' h' ↔
      Spec.mapMulEquiv g ≫ representedQuotientProjection G Q eQ =
        Spec.mapMulEquiv g' ≫ representedQuotientProjection G Q eQ := by
  rw [eq_representedQuotientRightMul_iff eP eQ g' h']
  rw [(eq_representedQuotientRightMul_iff eP eQ g h _).mp rfl,
    fppfHomogeneousQuotientRightMul_eq_fppfHomogeneousQuotientRightMul_iff]
  exact (mapMulEquiv_comp_representedQuotientProjection_eq_iff G Q eQ g g').symm

/-- **Equivariant morphisms when rational quotient points lift.** If every `R`-point of the
fppf quotient `G/Q` lifts to `G(R)`, the equivariant scheme morphisms `G/P ⟶ G/Q` are exactly
the morphisms `xP ↦ xgQ` with `g⁻¹Pg ⊆ Q` as subgroup schemes. -/
theorem representedQuotientEquivariant_iff_exists_eq_rightMul_of_surjective
    (hs : Function.Surjective
      ((fppfHomogeneousQuotientProjection G Q).app (op (op (CommAlgCat.of R R)))))
    (f : X ⟶ Y) :
    IsFppfHomogeneousQuotientEquivariant
      (eP.hom ≫ (CommAlgCat.pointsSheafFunctor R).map f ≫ eQ.inv) ↔
    ∃ (g : HopfAlgebra.points (R := R) (H := G) (CommAlgCat.of R R))
      (h : Q.conjugate g ≤ P), f = representedQuotientRightMul eP eQ g h := by
  constructor
  · intro hf
    obtain ⟨⟨g⟩, hg⟩ := hs
      ((eP.hom ≫ (CommAlgCat.pointsSheafFunctor R).map f ≫ eQ.inv).hom.app
        (op (op (CommAlgCat.of R R)))
        ((fppfHomogeneousQuotientProjection G P).app (op (op (CommAlgCat.of R R)))
          (ULift.up (1 : HopfAlgebra.points (R := R) (H := G) (CommAlgCat.of R R)))))
    have h : Q.conjugate g ≤ P :=
      (projection_mem_fppfHomogeneousQuotientFixedPoints_iff G g).mp
        (hg ▸ hf.app_projection_one_mem)
    refine ⟨g, h, (eq_representedQuotientRightMul_iff eP eQ g h f).mpr ?_⟩
    exact hf.ext (isFppfHomogeneousQuotientEquivariant_rightMul G g h)
      (hg.symm.trans (fppfHomogeneousQuotientRightMul_app_projection_one G g h).symm)
  · rintro ⟨g, h, hfg⟩
    rw [(eq_representedQuotientRightMul_iff eP eQ g h f).mp hfg]
    exact isFppfHomogeneousQuotientEquivariant_rightMul G g h

section AlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k] {G : _root_.CommHopfAlgCat.{u} k}
  {P Q : HopfIdeal k G} {X Y : Over (Spec (CommRingCat.of k))}
  (eP : fppfHomogeneousQuotient G P ≅ CommAlgCat.pointsSheaf X)
  (eQ : fppfHomogeneousQuotient G Q ≅ CommAlgCat.pointsSheaf Y)

/-- **Equivariant morphisms between representing schemes over an algebraically closed field.**
Every equivariant scheme morphism `G/P ⟶ G/Q` is `xP ↦ xgQ` for a rational group point `g`
with `g⁻¹Pg ⊆ Q` as subgroup schemes, and every such morphism is equivariant. -/
theorem representedQuotientEquivariant_iff_exists_eq_rightMul (f : X ⟶ Y) :
    IsFppfHomogeneousQuotientEquivariant
      (eP.hom ≫ (CommAlgCat.pointsSheafFunctor k).map f ≫ eQ.inv) ↔
    ∃ (g : HopfAlgebra.points (R := k) (H := G) (CommAlgCat.of k k))
      (h : Q.conjugate g ≤ P), f = representedQuotientRightMul eP eQ g h :=
  representedQuotientEquivariant_iff_exists_eq_rightMul_of_surjective eP eQ
    (fppfHomogeneousQuotientProjection_app_surjective G Q) f

end AlgClosed

end CommHopfAlgCat
