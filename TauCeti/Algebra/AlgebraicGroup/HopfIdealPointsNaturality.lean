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

namespace HopfAlgebra

variable {R : Type u} [CommRing R] {H : Type v} [Semiring H] [_root_.HopfAlgebra R H]

/-- Pointwise form of the map on points induced by a morphism of value algebras. -/
@[simp]
lemma mapPoints_apply_apply {A B : CommAlgCat.{w} R} (χ : A ⟶ B)
    (f : points (R := R) (H := H) A) (h : H) :
    ((mapPoints (H := H) χ f).ofConv) h = χ.hom (f.ofConv h) :=
  rfl

end HopfAlgebra

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- The quotient-points inclusion is natural in the value algebra.

Post-composing a quotient point `H ⧸ I →ₐ[R] A` by `χ : A ⟶ B`, then including it as an
ambient point of `H`, gives the same ambient `B`-point as first including it and then
post-composing by `χ`. -/
lemma mapPoints_quotientPointsHom (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) (f : HopfAlgebra.points (R := R) (H := quotient H I) A) :
    HopfAlgebra.mapPoints (H := H) χ (quotientPointsHom H I A f) =
      quotientPointsHom H I B
        (HopfAlgebra.mapPoints (H := quotient H I) χ f) := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro h
  calc
    ((HopfAlgebra.mapPoints (H := H) χ (quotientPointsHom H I A f)).ofConv) h =
        χ.hom (((quotientPointsHom H I A f).ofConv) h) :=
      HopfAlgebra.mapPoints_apply_apply (H := H) χ (quotientPointsHom H I A f) h
    _ = χ.hom (f.ofConv (Ideal.Quotient.mkₐ R I.toIdeal h)) := by
      rw [quotientPointsHom_apply_apply]
    _ = ((quotientPointsHom H I B
          (HopfAlgebra.mapPoints (H := quotient H I) χ f)).ofConv) h := by
      rw [quotientPointsHom_apply_apply,
        HopfAlgebra.mapPoints_apply_apply (H := quotient H I)]

/-- Pointwise form of naturality of the quotient-points inclusion. -/
lemma mapPoints_quotientPointsHom_apply_apply (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) (f : HopfAlgebra.points (R := R) (H := quotient H I) A) (h : H) :
    ((HopfAlgebra.mapPoints (H := H) χ (quotientPointsHom H I A f)).ofConv) h =
      χ.hom (f.ofConv (Ideal.Quotient.mkₐ R I.toIdeal h)) := by
  rw [mapPoints_quotientPointsHom, quotientPointsHom_apply_apply]
  rfl

/-- The quotient-points inclusion commutes with the functor-of-points maps as a morphism
equality. -/
lemma quotientPointsHom_naturality (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) :
    quotientPointsHom H I A ≫ HopfAlgebra.mapPoints (H := H) χ =
      HopfAlgebra.mapPoints (H := quotient H I) χ ≫ quotientPointsHom H I B := by
  ext f h
  exact congrArg (fun g : HopfAlgebra.points (R := R) (H := H) B => g.ofConv h)
    (mapPoints_quotientPointsHom H I χ f)

/-- Post-composition preserves the ambient-point subgroup cut out by a Hopf ideal. -/
lemma mapPoints_mem_quotientPointsSubgroup (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) {g : HopfAlgebra.points (R := R) (H := H) A}
    (hg : g ∈ quotientPointsSubgroup H I A) :
    HopfAlgebra.mapPoints (H := H) χ g ∈ quotientPointsSubgroup H I B := by
  rw [mem_quotientPointsSubgroup_iff] at hg ⊢
  intro h hh
  rw [HopfAlgebra.mapPoints_apply_apply]
  rw [hg h hh, map_zero]

/-- The functor-of-points map restricted to the subgroups cut out by a Hopf ideal. -/
@[expose] noncomputable def mapQuotientPointsSubgroup (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) :
    quotientPointsSubgroup H I A →* quotientPointsSubgroup H I B where
  toFun g :=
    ⟨HopfAlgebra.mapPoints (H := H) χ g,
      mapPoints_mem_quotientPointsSubgroup H I χ g.property⟩
  map_one' := by
    ext h
    exact congrArg (fun f : HopfAlgebra.points (R := R) (H := H) B => f.ofConv h)
      (HopfAlgebra.mapPoints_one (H := H) χ)
  map_mul' g₁ g₂ := by
    ext h
    exact congrArg (fun f : HopfAlgebra.points (R := R) (H := H) B => f.ofConv h)
      (HopfAlgebra.mapPoints_mul (H := H) χ g₁ g₂)

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
  ext g h
  rfl

/-- The restricted subgroup maps preserve composition of value-algebra morphisms. -/
lemma mapQuotientPointsSubgroup_comp (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B C : CommAlgCat.{w} R} (χ : A ⟶ B) (ψ : B ⟶ C) :
    mapQuotientPointsSubgroup H I (χ ≫ ψ) =
      (mapQuotientPointsSubgroup H I ψ).comp
        (mapQuotientPointsSubgroup H I χ) := by
  ext g h
  rfl

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
          rw [HopfAlgebra.mapPoints_apply_apply]
          rw [hg h hh, map_zero]) := by
  apply quotientPointsHom_injective H I B
  rw [← mapPoints_quotientPointsHom, quotientPointsHom_liftQuotientPoint,
    quotientPointsHom_liftQuotientPoint]

end CommHopfAlgCat

end TauCeti
