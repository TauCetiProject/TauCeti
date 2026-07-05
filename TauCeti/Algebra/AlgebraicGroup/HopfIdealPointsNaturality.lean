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

/-- The quotient-points inclusion is natural in the value algebra. -/
@[simp]
lemma mapPoints_quotientPointsHom (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) (f : HopfAlgebra.points (R := R) (H := quotient H I) A) :
    HopfAlgebra.mapPoints (H := H) χ (quotientPointsHom H I A f) =
      quotientPointsHom H I B (HopfAlgebra.mapPoints (H := quotient H I) χ f) := by
  exact mapPointsFunctor_naturality_apply (R := R) (mkQuotient H I) χ f

/-- Post-composition preserves the ambient-point subgroup cut out by a Hopf ideal. -/
lemma mapPoints_mem_quotientPointsSubgroup (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) {g : HopfAlgebra.points (R := R) (H := H) A}
    (hg : g ∈ quotientPointsSubgroup H I A) :
    HopfAlgebra.mapPoints (H := H) χ g ∈ quotientPointsSubgroup H I B := by
  rw [mem_quotientPointsSubgroup_iff] at hg
  rw [← quotientPointsHom_liftQuotientPoint H I A g hg, mapPoints_quotientPointsHom]
  exact quotientPointsHom_mem_quotientPointsSubgroup H I B _

/-- The functor-of-points map restricted to the subgroups cut out by a Hopf ideal. -/
@[expose] noncomputable def mapQuotientPointsSubgroup (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) :
    quotientPointsSubgroup H I A →* quotientPointsSubgroup H I B :=
  (((HopfAlgebra.mapPoints (H := H) χ).hom.restrict (quotientPointsSubgroup H I A)).codRestrict
    (quotientPointsSubgroup H I B)
    fun g => mapPoints_mem_quotientPointsSubgroup H I χ g.property)

/-- The value-algebra functor of the point subgroups cut out by a Hopf ideal. -/
@[expose] noncomputable def quotientPointsSubgroupFunctor
    (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) :
    CommAlgCat.{w} R ⥤ GrpCat.{max v w} where
  obj A := GrpCat.of (quotientPointsSubgroup H I A)
  map {A B} χ := GrpCat.ofHom (mapQuotientPointsSubgroup H I χ)
  map_id A := by
    ext g h
    rfl
  map_comp {A B C} χ ψ := by
    ext g h
    rfl

/-- The subgroup functor includes naturally into the ambient functor of points. -/
@[expose] noncomputable def quotientPointsSubgroupIncl (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) :
    quotientPointsSubgroupFunctor (R := R) H I ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := H) where
  app A := GrpCat.ofHom (quotientPointsSubgroup H I A).subtype
  naturality {A B} χ := by
    ext g
    rfl

/-- The component of the subgroup inclusion is the subgroup subtype map. -/
@[simp]
lemma quotientPointsSubgroupIncl_app (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (A : CommAlgCat.{w} R) :
    (quotientPointsSubgroupIncl H I).app A =
      GrpCat.ofHom (quotientPointsSubgroup H I A).subtype :=
  rfl

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

/-- The inverse map from a cut-out subgroup point to the corresponding quotient point. -/
noncomputable def liftQuotientPointHom (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (A : CommAlgCat.{w} R) :
    quotientPointsSubgroup H I A →* HopfAlgebra.points (R := R) (H := quotient H I) A where
  toFun g := liftQuotientPoint H I A g
    ((mem_quotientPointsSubgroup_iff H I A g).mp g.property)
  map_one' := by
    apply quotientPointsHom_injective H I A
    rw [quotientPointsHom_liftQuotientPoint, map_one]
    rfl
  map_mul' := by
    intro g₁ g₂
    apply quotientPointsHom_injective H I A
    rw [quotientPointsHom_liftQuotientPoint, map_mul, quotientPointsHom_liftQuotientPoint,
      quotientPointsHom_liftQuotientPoint]
    rfl

private lemma liftQuotientPointHom_naturality (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B : CommAlgCat.{w} R} (χ : A ⟶ B)
    (g : quotientPointsSubgroup H I A) :
    HopfAlgebra.mapPoints (H := quotient H I) χ (liftQuotientPointHom H I A g) =
      liftQuotientPointHom H I B (mapQuotientPointsSubgroup H I χ g) := by
  apply quotientPointsHom_injective H I B
  rw [← mapPoints_quotientPointsHom H I χ]
  -- Expose the concrete lift maps after applying injectivity to the quotient-points inclusion.
  change HopfAlgebra.mapPoints (H := H) χ
      (quotientPointsHom H I A
        (liftQuotientPoint H I A g
          ((mem_quotientPointsSubgroup_iff H I A g).mp g.property))) =
    quotientPointsHom H I B
      (liftQuotientPoint H I B (mapQuotientPointsSubgroup H I χ g)
        ((mem_quotientPointsSubgroup_iff H I B (mapQuotientPointsSubgroup H I χ g)).mp
          (mapQuotientPointsSubgroup H I χ g).property))
  rw [quotientPointsHom_liftQuotientPoint, quotientPointsHom_liftQuotientPoint]
  rfl

/-- The component isomorphism between quotient points and the cut-out subgroup. -/
noncomputable def quotientPointsSubgroupIso (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (A : CommAlgCat.{w} R) :
    GrpCat.of (HopfAlgebra.points (R := R) (H := quotient H I) A) ≅
      GrpCat.of (quotientPointsSubgroup H I A) where
  hom := GrpCat.ofHom ((quotientPointsHom H I A).hom.codRestrict
    (quotientPointsSubgroup H I A)
    (quotientPointsHom_mem_quotientPointsSubgroup H I A))
  inv := GrpCat.ofHom (liftQuotientPointHom H I A)
  hom_inv_id := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    -- The component iso is bundled in `GrpCat`; expose the underlying quotient lift.
    change liftQuotientPoint H I A (quotientPointsHom H I A g)
        ((mem_quotientPointsSubgroup_iff H I A (quotientPointsHom H I A g)).mp
          (quotientPointsHom_mem_quotientPointsSubgroup H I A g)) =
      g
    apply quotientPointsHom_injective H I A
    rw [quotientPointsHom_liftQuotientPoint]
  inv_hom_id := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    -- The component iso is bundled in `GrpCat`; expose the underlying quotient inclusion.
    change (⟨quotientPointsHom H I A (liftQuotientPointHom H I A g),
        quotientPointsHom_mem_quotientPointsSubgroup H I A _⟩ :
        quotientPointsSubgroup H I A) = g
    exact Subtype.ext (quotientPointsHom_liftQuotientPoint H I A g
      ((mem_quotientPointsSubgroup_iff H I A g).mp g.property))

private lemma quotientPointsSubgroupFunctor_map_quotientPointsHom_aux
    (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) (f : HopfAlgebra.points (R := R) (H := quotient H I) A) :
    mapQuotientPointsSubgroup H I χ
        ⟨quotientPointsHom H I A f, quotientPointsHom_mem_quotientPointsSubgroup H I A f⟩ =
      ⟨quotientPointsHom H I B (HopfAlgebra.mapPoints (H := quotient H I) χ f),
        quotientPointsHom_mem_quotientPointsSubgroup H I B _⟩ := by
  apply Subtype.ext
  rw [coe_mapQuotientPointsSubgroup_apply, mapPoints_quotientPointsHom]

/-- The quotient Hopf algebra represents the subgroup functor cut out by the Hopf ideal. -/
noncomputable def quotientPointsSubgroupNatIso (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) :
    HopfAlgebra.pointsFunctor (R := R) (H := quotient H I) ≅
      quotientPointsSubgroupFunctor (R := R) H I :=
  NatIso.ofComponents
    (quotientPointsSubgroupIso H I)
    (by
      intro A B χ
      ext f
      exact (quotientPointsSubgroupFunctor_map_quotientPointsHom_aux H I χ f).symm)

/-- The image of a quotient point under the subgroup functor is its mapped quotient point,
viewed inside the cut-out subgroup. -/
lemma quotientPointsSubgroupFunctor_map_quotientPointsHom
    (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) (f : HopfAlgebra.points (R := R) (H := quotient H I) A) :
    mapQuotientPointsSubgroup H I χ
        ⟨quotientPointsHom H I A f, quotientPointsHom_mem_quotientPointsSubgroup H I A f⟩ =
      ⟨quotientPointsHom H I B (HopfAlgebra.mapPoints (H := quotient H I) χ f),
        quotientPointsHom_mem_quotientPointsSubgroup H I B _⟩ := by
  exact quotientPointsSubgroupFunctor_map_quotientPointsHom_aux H I χ f

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
  exact liftQuotientPointHom_naturality H I χ
    (⟨g, (mem_quotientPointsSubgroup_iff H I A g).mpr hg⟩ :
      quotientPointsSubgroup H I A)

end CommHopfAlgCat

end TauCeti
