/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.RationalPoints

/-!
# Left translation and the rational points of homogeneous quotients

Subgroup-induced projections of fppf homogeneous quotients commute with left translation
by ground-ring-valued points. Over an algebraically closed field, the identification of
rational points with left cosets intertwines these automorphisms with Mathlib's usual
left action on cosets. The comparison uses the actual sheaf automorphism, not a separate
action transported across a bijection.

The translation automorphisms are constructed in `Homogeneous.Basic` over every commutative
base ring, without normality or representability assumptions. Only translation by
ground-ring-valued points is used here, not an internal action morphism of sheaves.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5, homogeneous spaces and quotient sheaves.
-/

public section

open CategoryTheory Opposite

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

universe u

noncomputable section

variable {R : Type u} [CommRing R] (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H)

/-- Subgroup-induced maps of coset presheaves commute with left translation. -/
@[reassoc]
theorem homogeneousQuotientPresheafTranslation_hom_comp_map {J : HopfIdeal R H}
    (hJI : J ≤ I) (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (homogeneousQuotientPresheafTranslation H I g).hom ≫
        homogeneousQuotientPresheafMap H hJI =
      homogeneousQuotientPresheafMap H hJI ≫
        (homogeneousQuotientPresheafTranslation H J g).hom := by
  ext A q
  induction q using homogeneousQuotientPresheaf_induction_on H I with
  | h x => simp

/-- Subgroup-induced projections of fppf quotients commute with translation. -/
@[reassoc]
theorem fppfHomogeneousQuotientTranslation_hom_comp_map {J : HopfIdeal R H}
    (hJI : J ≤ I) (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (fppfHomogeneousQuotientTranslation H I g).hom ≫ fppfHomogeneousQuotientMap H hJI =
      fppfHomogeneousQuotientMap H hJI ≫ (fppfHomogeneousQuotientTranslation H J g).hom := by
  apply fppfHomogeneousQuotient_hom_ext
  ext A ⟨(x : HopfAlgebra.points (R := R) (H := H) A.unop.unop)⟩
  have hmap (y : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :=
    congrArg (fun f ↦ f.app A (ULift.up y))
      (fppfHomogeneousQuotientProjection_comp_map H hJI)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, TypeCat.Fun.toFun_apply] at hmap ⊢
  -- Compute on a projected point: translate, project to the larger subgroup, then translate.
  calc
    _ = (fppfHomogeneousQuotientMap H hJI).hom.app A
        ((fppfHomogeneousQuotientProjection H I).app A
          (ULift.up (HopfAlgebra.extendPoint H A.unop.unop g * x))) := by
      rw [fppfHomogeneousQuotientTranslation_hom_app_projection]
    _ = (fppfHomogeneousQuotientProjection H J).app A
        (ULift.up (HopfAlgebra.extendPoint H A.unop.unop g * x)) := hmap _
    _ = _ := by
      rw [hmap, fppfHomogeneousQuotientTranslation_hom_app_projection]

/-- Over an algebraically closed field, the rational-point/coset comparison intertwines
left translation on the fppf quotient with the usual left action on cosets. -/
theorem fppfHomogeneousQuotientTranslation_hom_app_rationalPointsEquiv
    {k : Type u} [Field k] [IsAlgClosed k] (H : _root_.CommHopfAlgCat.{u} k)
    (I : HopfIdeal k H)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    (q : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) ⧸
      quotientPointsSubgroup H I (CommAlgCat.of k k)) :
    (fppfHomogeneousQuotientTranslation H I g).hom.hom.app (op (op (CommAlgCat.of k k)))
        (fppfHomogeneousQuotientRationalPointsEquiv H I q) =
      fppfHomogeneousQuotientRationalPointsEquiv H I (g • q) := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [fppfHomogeneousQuotientRationalPointsEquiv_mk,
      fppfHomogeneousQuotientTranslation_hom_app_projection,
      MulAction.Quotient.smul_mk, smul_eq_mul,
      fppfHomogeneousQuotientRationalPointsEquiv_mk, HopfAlgebra.extendPoint_self]

end

end CommHopfAlgCat
