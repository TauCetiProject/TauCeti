/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Map
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation

/-!
# Conjugation of fppf homogeneous quotients

Let `G` be an affine group over a commutative ring `R`, `N` a closed subgroup cut out by a Hopf
ideal `I`, and `g` an `R`-valued point of `G`. Conjugating `N` by `g` produces the closed subgroup
`g N g⁻¹`, cut out by `I.conjugate g`. Because `x N ↦ (g x g⁻¹) (g N g⁻¹)` is well defined on left
cosets and natural in the value algebra `A`, inner conjugation by `g` induces canonical
isomorphisms

* `CommHopfAlgCat.homogeneousQuotientPresheafConjugateIso` on coset presheaves, and
* `CommHopfAlgCat.fppfHomogeneousQuotientConjugateIso` on fppf homogeneous quotients.

Consequently, a scheme over `Spec R` represents `G / N` if and only if it represents
`G / (g N g⁻¹)`. Both isomorphisms commute with subgroup-inclusion projections `G / P ⟶ G / Q`,
and the fppf isomorphism carries left translation by `x` to left translation by `g x g⁻¹`. No
reducedness, smoothness, normality, or finite-type hypotheses are needed.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§3.5, 5.e.
-/

public section

open CategoryTheory Opposite

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

universe u

noncomputable section

variable {R : Type u} [CommRing R] (H : _root_.CommHopfAlgCat.{u} R)

/-- Conjugating a subgroup point by an extended ground-ring point lands in the conjugated subgroup
cut-out. -/
private theorem extendPoint_conj_mem_conjugate (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : CommAlgCat.{u} R) {x : HopfAlgebra.points (R := R) (H := H) A}
    (hx : x ∈ quotientPointsSubgroup H I A) :
    HopfAlgebra.extendPoint H A g * x * (HopfAlgebra.extendPoint H A g)⁻¹ ∈
      quotientPointsSubgroup H (I.conjugate g) A := by
  -- Destruct the bundled Hopf algebra so `H` matches `_root_.CommHopfAlgCat.of R H`.
  rcases H with ⟨H⟩
  rw [HopfAlgebra.extendPoint_eq_mapValue]
  exact (pointConjugation_mem_conjugate_iff (H := H) I g A x).mpr hx

/-- Inner conjugation on lifted group points as an endomorphism of `pointsPresheaf H ⋙ ulift`. -/
private def pointsPresheafConjugateHom
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ⟶
      HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} where
  app A := ↾fun (x : ULift.{u + 1, u} (HopfAlgebra.points (R := R) (H := H) A.unop.unop)) ↦
    ULift.up (HopfAlgebra.extendPoint H A.unop.unop g * x.down *
      (HopfAlgebra.extendPoint H A.unop.unop g)⁻¹)
  naturality {A B} χ := by
    ext ⟨(x : HopfAlgebra.points (R := R) (H := H) A.unop.unop)⟩
    -- `TypeCat.ofHom` (`↾...`) on the lifted points presheaf has no equation lemma for `rw`.
    change ULift.up (HopfAlgebra.extendPoint H B.unop.unop g *
        HopfAlgebra.mapPoints (H := H) χ.unop.unop x *
          (HopfAlgebra.extendPoint H B.unop.unop g)⁻¹) =
      ULift.up (HopfAlgebra.mapPoints (H := H) χ.unop.unop
        (HopfAlgebra.extendPoint H A.unop.unop g * x *
          (HopfAlgebra.extendPoint H A.unop.unop g)⁻¹))
    rw [map_mul, map_mul, map_inv, HopfAlgebra.mapPoints_extendPoint]

@[reassoc]
private theorem pointsPresheafConjugateHom_comp_inv
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    pointsPresheafConjugateHom H g ≫ pointsPresheafConjugateHom H g⁻¹ = 𝟙 _ := by
  ext A ⟨(x : HopfAlgebra.points (R := R) (H := H) A.unop.unop)⟩
  -- Unpack `TypeCat.ofHom` applications in `pointsPresheafConjugateHom`.
  change ULift.up (HopfAlgebra.extendPoint H A.unop.unop g⁻¹ *
      (HopfAlgebra.extendPoint H A.unop.unop g * x *
        (HopfAlgebra.extendPoint H A.unop.unop g)⁻¹) *
      (HopfAlgebra.extendPoint H A.unop.unop g⁻¹)⁻¹) = ULift.up x
  simp [mul_assoc]

@[reassoc]
private theorem pointsPresheafConjugateHom_inv_comp
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    pointsPresheafConjugateHom H g⁻¹ ≫ pointsPresheafConjugateHom H g = 𝟙 _ := by
  simpa only [inv_inv] using pointsPresheafConjugateHom_comp_inv H g⁻¹

/-- Inner conjugation on coset presheaves from `I` to any Hopf ideal `J` equal to
`I.conjugate g`. -/
private def homogeneousQuotientPresheafConjugateHomOfEq {I J : HopfIdeal R H}
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) (hIJ : I.conjugate g = J) :
    homogeneousQuotientPresheaf H I ⟶ homogeneousQuotientPresheaf H J :=
  homogeneousQuotientPresheafLift H I
    (pointsPresheafConjugateHom H g ≫ homogeneousQuotientPresheafProjection H J)
    fun A x n ↦ by
      simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
      symm
      refine (homogeneousQuotientPresheafProjection_eq_iff H J A _ _).mpr ?_
      subst hIJ
      convert extendPoint_conj_mem_conjugate H I g A.unop.unop n.property using 1
      group

/-- **Inner conjugation on coset presheaves.** Conjugating by a ground-ring point `g` identifies
the left-coset presheaf `G / N` with `G / (g N g⁻¹)` via `x N ↦ (g x g⁻¹) (g N g⁻¹)`. -/
def homogeneousQuotientPresheafConjugateIso (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    homogeneousQuotientPresheaf H I ≅ homogeneousQuotientPresheaf H (I.conjugate g) where
  hom := homogeneousQuotientPresheafConjugateHomOfEq H g rfl
  inv := homogeneousQuotientPresheafConjugateHomOfEq H g⁻¹ (HopfIdeal.conjugate_inv_conjugate I g)
  hom_inv_id := by
    apply homogeneousQuotientPresheaf_hom_ext
    simp [homogeneousQuotientPresheafConjugateHomOfEq, pointsPresheafConjugateHom_comp_inv_assoc]
  inv_hom_id := by
    apply homogeneousQuotientPresheaf_hom_ext
    simp [homogeneousQuotientPresheafConjugateHomOfEq, pointsPresheafConjugateHom_inv_comp_assoc]

/-- The forward conjugation isomorphism carries the coset of `x` to the coset of `g x g⁻¹`. -/
@[simp]
theorem homogeneousQuotientPresheafConjugateIso_hom_app_mk (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (x : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    (homogeneousQuotientPresheafConjugateIso H I g).hom.app A
        (homogeneousQuotientPresheafMk H I A x) =
      homogeneousQuotientPresheafMk H (I.conjugate g) A
        (HopfAlgebra.extendPoint H A.unop.unop g * x *
          (HopfAlgebra.extendPoint H A.unop.unop g)⁻¹) := by
  dsimp only [homogeneousQuotientPresheafConjugateIso]
  rw [homogeneousQuotientPresheafConjugateHomOfEq, homogeneousQuotientPresheafLift_app_mk]
  exact homogeneousQuotientPresheafProjection_app_apply H (I.conjugate g) A _

/-- The inverse conjugation isomorphism carries the coset of `x` to the coset of `g⁻¹ x g`. -/
@[simp]
theorem homogeneousQuotientPresheafConjugateIso_inv_app_mk (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (x : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    (homogeneousQuotientPresheafConjugateIso H I g).inv.app A
        (homogeneousQuotientPresheafMk H (I.conjugate g) A x) =
      homogeneousQuotientPresheafMk H I A
        (HopfAlgebra.extendPoint H A.unop.unop g⁻¹ * x *
          (HopfAlgebra.extendPoint H A.unop.unop g⁻¹)⁻¹) := by
  dsimp only [homogeneousQuotientPresheafConjugateIso]
  rw [homogeneousQuotientPresheafConjugateHomOfEq, homogeneousQuotientPresheafLift_app_mk]
  exact homogeneousQuotientPresheafProjection_app_apply H I A _

/-- Conjugation of coset presheaves commutes with subgroup-inclusion projections. -/
@[reassoc]
theorem homogeneousQuotientPresheafConjugateIso_hom_comp_map {I J : HopfIdeal R H} (hJI : J ≤ I)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (homogeneousQuotientPresheafConjugateIso H I g).hom ≫
        homogeneousQuotientPresheafMap H (HopfIdeal.conjugate_mono g hJI) =
      homogeneousQuotientPresheafMap H hJI ≫
        (homogeneousQuotientPresheafConjugateIso H J g).hom := by
  ext A q
  induction q using homogeneousQuotientPresheaf_induction_on H I with
  | h x => simp

/-- **Inner conjugation on fppf homogeneous quotients.** Conjugating by a ground-ring point `g`
identifies `G / N` with `G / (g N g⁻¹)` as fppf sheaves, obtained by sheafifying
`homogeneousQuotientPresheafConjugateIso`. -/
def fppfHomogeneousQuotientConjugateIso (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    fppfHomogeneousQuotient H I ≅ fppfHomogeneousQuotient H (I.conjugate g) :=
  eqToIso (fppfHomogeneousQuotient_eq H I) ≪≫
    (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).mapIso
      (homogeneousQuotientPresheafConjugateIso H I g) ≪≫
    eqToIso (fppfHomogeneousQuotient_eq H (I.conjugate g)).symm

@[reassoc]
private theorem fppfHomogeneousQuotientProjection_comp_sheafifyMap_conjugateHomOfEq
    {I J : HopfIdeal R H}
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) (hIJ : I.conjugate g = J) :
    fppfHomogeneousQuotientProjection H I ≫
        (eqToHom (fppfHomogeneousQuotient_eq H I) ≫
          (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).map
            (homogeneousQuotientPresheafConjugateHomOfEq H g hIJ) ≫
          eqToHom (fppfHomogeneousQuotient_eq H J).symm).hom =
      pointsPresheafConjugateHom H g ≫ fppfHomogeneousQuotientProjection H J := by
  have hnat : toSheafify (CommAlgCat.fppfTopology R) (homogeneousQuotientPresheaf H I) ≫
        ((presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).map
          (homogeneousQuotientPresheafConjugateHomOfEq H g hIJ)).hom =
      homogeneousQuotientPresheafConjugateHomOfEq H g hIJ ≫
        toSheafify (CommAlgCat.fppfTopology R) (homogeneousQuotientPresheaf H J) :=
    (toSheafify_naturality (CommAlgCat.fppfTopology R)
      (homogeneousQuotientPresheafConjugateHomOfEq H g hIJ)).symm
  simp only [fppfHomogeneousQuotientProjection_def, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.eqToHom_hom, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, reassoc_of% hnat]
  rw [homogeneousQuotientPresheafConjugateHomOfEq,
    homogeneousQuotientPresheafProjection_comp_lift_assoc, Category.assoc]

/-- On projected group points, forward conjugation on `G / N` conjugates the representative by the
extended point `g`. -/
@[simp]
theorem fppfHomogeneousQuotientConjugateIso_hom_app_projection (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (x : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    dsimp% (fppfHomogeneousQuotientConjugateIso H I g).hom.hom.app A
        ((fppfHomogeneousQuotientProjection H I).app A (ULift.up x)) =
      (fppfHomogeneousQuotientProjection H (I.conjugate g)).app A
        (ULift.up (HopfAlgebra.extendPoint H A.unop.unop g * x *
          (HopfAlgebra.extendPoint H A.unop.unop g)⁻¹)) := by
  have hcomp :
      fppfHomogeneousQuotientProjection H I ≫
          (fppfHomogeneousQuotientConjugateIso H I g).hom.hom =
        pointsPresheafConjugateHom H g ≫
          fppfHomogeneousQuotientProjection H (I.conjugate g) := by
    simpa only [fppfHomogeneousQuotientConjugateIso, homogeneousQuotientPresheafConjugateIso,
      Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom, Category.assoc] using
      fppfHomogeneousQuotientProjection_comp_sheafifyMap_conjugateHomOfEq H g rfl
  exact congrArg (fun f ↦ f.app A (ULift.up x)) hcomp

/-- On projected group points, inverse conjugation on `G / (g N g⁻¹)` conjugates the representative
by the extended inverse point `g⁻¹`. -/
@[simp]
theorem fppfHomogeneousQuotientConjugateIso_inv_app_projection (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (x : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    dsimp% (fppfHomogeneousQuotientConjugateIso H I g).inv.hom.app A
        ((fppfHomogeneousQuotientProjection H (I.conjugate g)).app A (ULift.up x)) =
      (fppfHomogeneousQuotientProjection H I).app A
        (ULift.up (HopfAlgebra.extendPoint H A.unop.unop g⁻¹ * x *
          (HopfAlgebra.extendPoint H A.unop.unop g⁻¹)⁻¹)) := by
  have hcomp :
      fppfHomogeneousQuotientProjection H (I.conjugate g) ≫
          (fppfHomogeneousQuotientConjugateIso H I g).inv.hom =
        pointsPresheafConjugateHom H g⁻¹ ≫ fppfHomogeneousQuotientProjection H I := by
    simpa only [fppfHomogeneousQuotientConjugateIso, homogeneousQuotientPresheafConjugateIso,
      Iso.trans_inv, eqToIso.inv, Functor.mapIso_inv, Category.assoc] using
      fppfHomogeneousQuotientProjection_comp_sheafifyMap_conjugateHomOfEq H g⁻¹
        (HopfIdeal.conjugate_inv_conjugate I g)
  exact congrArg (fun f ↦ f.app A (ULift.up x)) hcomp

/-- Conjugation of fppf homogeneous quotients commutes with subgroup-inclusion projections. -/
@[reassoc]
theorem fppfHomogeneousQuotientConjugateIso_hom_comp_map {I J : HopfIdeal R H} (hJI : J ≤ I)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (fppfHomogeneousQuotientConjugateIso H I g).hom ≫
        fppfHomogeneousQuotientMap H (HopfIdeal.conjugate_mono g hJI) =
      fppfHomogeneousQuotientMap H hJI ≫
        (fppfHomogeneousQuotientConjugateIso H J g).hom := by
  have hcomp (K : HopfIdeal R H) :
      fppfHomogeneousQuotientProjection H K ≫
          (fppfHomogeneousQuotientConjugateIso H K g).hom.hom =
        pointsPresheafConjugateHom H g ≫
          fppfHomogeneousQuotientProjection H (K.conjugate g) := by
    simpa only [fppfHomogeneousQuotientConjugateIso, homogeneousQuotientPresheafConjugateIso,
      Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom, Category.assoc] using
      fppfHomogeneousQuotientProjection_comp_sheafifyMap_conjugateHomOfEq H g rfl
  apply fppfHomogeneousQuotient_hom_ext
  simp [reassoc_of% (hcomp I), hcomp J]

/-- Conjugation intertwines left translation by `x` on `G / N` with left translation by `g x g⁻¹`
on `G / (g N g⁻¹)`. -/
@[reassoc]
theorem fppfHomogeneousQuotientTranslation_comp_conjugateIso (I : HopfIdeal R H)
    (g x : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (fppfHomogeneousQuotientTranslation H I x).hom ≫
        (fppfHomogeneousQuotientConjugateIso H I g).hom =
      (fppfHomogeneousQuotientConjugateIso H I g).hom ≫
        (fppfHomogeneousQuotientTranslation H (I.conjugate g) (g * x * g⁻¹)).hom := by
  apply fppfHomogeneousQuotient_hom_ext
  ext A ⟨(y : HopfAlgebra.points (R := R) (H := H) A.unop.unop)⟩
  simp [map_mul, map_inv, mul_assoc]

end

end CommHopfAlgCat
