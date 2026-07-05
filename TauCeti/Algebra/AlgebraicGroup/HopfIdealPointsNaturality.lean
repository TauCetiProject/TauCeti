/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdealPoints

/-!
# Naturality of Hopf-ideal quotient points

For a Hopf ideal `I` in a commutative Hopf algebra `H`, the quotient Hopf algebra
`H ⧸ I` represents the closed subgroup whose `A`-points are the ambient `H`-points killing
`I`. This file records that this description is natural in the value algebra `A`.

The quotient-points inclusion commutes with post-composition along a morphism
`A ⟶ B` of commutative `R`-algebras. Consequently the subgroup of ambient points cut out by
`I` is preserved by the functor-of-points map, and the value-algebra map restricts to a
homomorphism between these subgroups.

This is a small Layer 3 prerequisite for the ReductiveGroups roadmap target "Hopf ideals ↔
closed subgroup schemes": the closed-subgroup functor represented by `H ⧸ I` must be a
subfunctor of the ambient points functor, not just a subgroup at each individual algebra.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u v w

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- Post-composition preserves the ambient-point subgroup cut out by a Hopf ideal. -/
lemma mapPoints_mem_quotientPointsSubgroup (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) {g : HopfAlgebra.points (R := R) (H := H) A}
    (hg : g ∈ quotientPointsSubgroup H I A) :
    HopfAlgebra.mapPoints (H := H) χ g ∈ quotientPointsSubgroup H I B := by
  rw [mem_quotientPointsSubgroup_iff] at hg
  rw [← quotientPointsHom_liftQuotientPoint H I A g hg]
  have hnat :
      HopfAlgebra.mapPoints (H := H) χ
          (quotientPointsHom H I A (liftQuotientPoint H I A g hg)) =
        quotientPointsHom H I B
          (HopfAlgebra.mapPoints (H := quotient H I) χ
            (liftQuotientPoint H I A g hg)) := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro h
    rw [quotientPointsHom_apply_apply]
    -- `mapPoints` is a bundled group hom, so expose its evaluation before rewriting
    -- `quotientPointsHom` under post-composition.
    change χ.hom
        ((quotientPointsHom H I A (liftQuotientPoint H I A g hg)).ofConv h) =
      χ.hom
        (((liftQuotientPoint H I A g hg).ofConv) (Ideal.Quotient.mkₐ R I.toIdeal h))
    rw [quotientPointsHom_apply_apply]
  rw [hnat]
  exact quotientPointsHom_mem_quotientPointsSubgroup H I B _

/-- The value-algebra functor of the point subgroups cut out by a Hopf ideal. -/
@[expose] noncomputable def quotientPointsSubgroupFunctor
    (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) :
    CommAlgCat.{w} R ⥤ GrpCat.{max v w} where
  obj A := GrpCat.of (quotientPointsSubgroup H I A)
  map {A B} χ := GrpCat.ofHom
    (((HopfAlgebra.mapPoints (H := H) χ).hom.restrict (quotientPointsSubgroup H I A)).codRestrict
      (quotientPointsSubgroup H I B)
      fun g => mapPoints_mem_quotientPointsSubgroup H I χ g.property)
  map_id A := by
    ext g h
    rfl
  map_comp {A B C} χ ψ := by
    ext g h
    rfl

/-- The subgroup functor includes naturally into the ambient functor of points. -/
noncomputable def quotientPointsSubgroupIncl (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) :
    quotientPointsSubgroupFunctor (R := R) H I ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := H) where
  app A := GrpCat.ofHom (quotientPointsSubgroup H I A).subtype
  naturality {A B} χ := by
    ext g
    rfl

/-- The functor-of-points map restricted to the subgroups cut out by a Hopf ideal. -/
noncomputable abbrev mapQuotientPointsSubgroup (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) :
    quotientPointsSubgroup H I A →* quotientPointsSubgroup H I B :=
  ((quotientPointsSubgroupFunctor H I).map χ).hom

/-- The restricted map on cut-out subgroups is induced by the ambient functor-of-points map. -/
@[simp]
lemma mapQuotientPointsSubgroup_apply (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) (g : quotientPointsSubgroup H I A) :
    mapQuotientPointsSubgroup H I χ g =
      ⟨HopfAlgebra.mapPoints (H := H) χ g,
        mapPoints_mem_quotientPointsSubgroup H I χ g.property⟩ :=
  rfl

/-- Coercing the restricted subgroup map gives the ambient functor-of-points map. -/
@[simp]
lemma coe_mapQuotientPointsSubgroup_apply (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) (g : quotientPointsSubgroup H I A) :
    (mapQuotientPointsSubgroup H I χ g :
      HopfAlgebra.points (R := R) (H := H) B) =
      HopfAlgebra.mapPoints (H := H) χ g :=
  rfl

/-- Pointwise form of the restricted subgroup map. -/
@[simp]
lemma mapQuotientPointsSubgroup_apply_apply (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) (g : quotientPointsSubgroup H I A) (h : H) :
    ((mapQuotientPointsSubgroup H I χ g :
      HopfAlgebra.points (R := R) (H := H) B).ofConv) h =
      χ.hom (g.val.ofConv h) :=
  rfl

/-- The restricted subgroup maps preserve identity morphisms of value algebras. -/
@[simp]
lemma mapQuotientPointsSubgroup_id (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (A : CommAlgCat.{w} R) :
    mapQuotientPointsSubgroup H I (𝟙 A) =
      MonoidHom.id (quotientPointsSubgroup H I A) := by
  exact congrArg GrpCat.Hom.hom ((quotientPointsSubgroupFunctor (R := R) H I).map_id A)

/-- The restricted subgroup maps preserve composition of value-algebra morphisms. -/
lemma mapQuotientPointsSubgroup_comp (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B C : CommAlgCat.{w} R} (χ : A ⟶ B) (ψ : B ⟶ C) :
    mapQuotientPointsSubgroup H I (χ ≫ ψ) =
      (mapQuotientPointsSubgroup H I ψ).comp
        (mapQuotientPointsSubgroup H I χ) := by
  exact congrArg GrpCat.Hom.hom ((quotientPointsSubgroupFunctor (R := R) H I).map_comp χ ψ)

/-- The image of a quotient point under the subgroup functor is its mapped quotient point,
viewed inside the cut-out subgroup. -/
lemma quotientPointsSubgroupFunctor_map_quotientPointsHom
    (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) (f : HopfAlgebra.points (R := R) (H := quotient H I) A) :
    mapQuotientPointsSubgroup H I χ
        ⟨quotientPointsHom H I A f, quotientPointsHom_mem_quotientPointsSubgroup H I A f⟩ =
      ⟨quotientPointsHom H I B (HopfAlgebra.mapPoints (H := quotient H I) χ f),
        quotientPointsHom_mem_quotientPointsSubgroup H I B _⟩ := by
  apply Subtype.ext
  rw [coe_mapQuotientPointsSubgroup_apply]
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro h
  rw [quotientPointsHom_apply_apply]
  -- `mapPoints` is a bundled group hom, so expose its evaluation before rewriting
  -- `quotientPointsHom` under post-composition.
  change χ.hom ((quotientPointsHom H I A f).ofConv h) =
    χ.hom (f.ofConv (Ideal.Quotient.mkₐ R I.toIdeal h))
  rw [quotientPointsHom_apply_apply]

/-- Factoring an ambient point through the quotient is natural in the value algebra. -/
lemma mapPoints_liftQuotientPoint (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) (g : HopfAlgebra.points (R := R) (H := H) A)
    (hg : ∀ h : H, h ∈ I → g.ofConv h = 0) :
    HopfAlgebra.mapPoints (H := quotient H I) χ
        (liftQuotientPoint H I A g hg) =
      liftQuotientPoint H I B (HopfAlgebra.mapPoints (H := H) χ g)
        (by
          intro h hh
          exact (mem_quotientPointsSubgroup_iff H I B _).mp
            (mapPoints_mem_quotientPointsSubgroup H I χ
              ((mem_quotientPointsSubgroup_iff H I A g).mpr hg)) h hh) := by
  apply quotientPointsHom_injective H I B
  have hnat :
      HopfAlgebra.mapPoints (H := H) χ
          (quotientPointsHom H I A (liftQuotientPoint H I A g hg)) =
        quotientPointsHom H I B
          (HopfAlgebra.mapPoints (H := quotient H I) χ
            (liftQuotientPoint H I A g hg)) := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro h
    rw [quotientPointsHom_apply_apply]
    -- `mapPoints` is a bundled group hom, so expose its evaluation before rewriting
    -- `quotientPointsHom` under post-composition.
    change χ.hom
        ((quotientPointsHom H I A (liftQuotientPoint H I A g hg)).ofConv h) =
      χ.hom
        (((liftQuotientPoint H I A g hg).ofConv) (Ideal.Quotient.mkₐ R I.toIdeal h))
    rw [quotientPointsHom_apply_apply]
  rw [← hnat, quotientPointsHom_liftQuotientPoint, quotientPointsHom_liftQuotientPoint]

end CommHopfAlgCat

end TauCeti
