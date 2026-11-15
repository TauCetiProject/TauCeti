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
`G / (g N g⁻¹)`. Both isomorphisms commute with subgroup-inclusion projections `G / P ⟶ G / Q` and
intertwine left translation by `x` with left translation by `g x g⁻¹`. No reducedness, smoothness,
normality, or finite-type hypotheses are needed.

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

/-- Extending a ground-ring point agrees with `AlgHom.mapValue` along the algebra structure map. -/
private theorem extendPoint_eq_mapValue (A : CommAlgCat.{u} R)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    HopfAlgebra.extendPoint H A g = AlgHom.mapValue (H := H) (Algebra.ofId R A) g :=
  (HopfAlgebra.extendPoint_apply H A g).trans (AlgHom.mapValue_apply (Algebra.ofId R A) g).symm

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
  rw [extendPoint_eq_mapValue]
  exact (pointConjugation_mem_conjugate_iff (H := H) I g A x).mpr hx

/-- Inverse-conjugating a point of the conjugated subgroup lands back in the original subgroup
cut-out. -/
private theorem extendPoint_inv_conj_mem_of_mem_conjugate (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : CommAlgCat.{u} R) {x : HopfAlgebra.points (R := R) (H := H) A}
    (hx : x ∈ quotientPointsSubgroup H (I.conjugate g) A) :
    HopfAlgebra.extendPoint H A g⁻¹ * x * (HopfAlgebra.extendPoint H A g⁻¹)⁻¹ ∈
      quotientPointsSubgroup H I A := by
  rcases H with ⟨H⟩
  apply (pointConjugation_mem_conjugate_iff (H := H) I g A _).mp
  rw [← extendPoint_eq_mapValue (_root_.CommHopfAlgCat.of R H), map_inv, inv_inv]
  simpa [mul_assoc] using hx

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

private def homogeneousQuotientPresheafConjugateHom (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    homogeneousQuotientPresheaf H I ⟶ homogeneousQuotientPresheaf H (I.conjugate g) :=
  homogeneousQuotientPresheafLift H I
    (pointsPresheafConjugateHom H g ≫ homogeneousQuotientPresheafProjection H (I.conjugate g))
    fun A x n ↦ by
      simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
      symm
      refine (homogeneousQuotientPresheafProjection_eq_iff H (I.conjugate g) A _ _).mpr ?_
      convert extendPoint_conj_mem_conjugate H I g A.unop.unop n.property using 1
      group

private def homogeneousQuotientPresheafConjugateInv (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    homogeneousQuotientPresheaf H (I.conjugate g) ⟶ homogeneousQuotientPresheaf H I :=
  homogeneousQuotientPresheafLift H (I.conjugate g)
    (pointsPresheafConjugateHom H g⁻¹ ≫ homogeneousQuotientPresheafProjection H I)
    fun A x n ↦ by
      simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
      symm
      refine (homogeneousQuotientPresheafProjection_eq_iff H I A _ _).mpr ?_
      convert extendPoint_inv_conj_mem_of_mem_conjugate H I g A.unop.unop n.property using 1
      group

/-- **Inner conjugation on coset presheaves.** Conjugating by a ground-ring point `g` identifies
the left-coset presheaf `G / N` with `G / (g N g⁻¹)` via `x N ↦ (g x g⁻¹) (g N g⁻¹)`. -/
def homogeneousQuotientPresheafConjugateIso (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    homogeneousQuotientPresheaf H I ≅ homogeneousQuotientPresheaf H (I.conjugate g) where
  hom := homogeneousQuotientPresheafConjugateHom H I g
  inv := homogeneousQuotientPresheafConjugateInv H I g
  hom_inv_id := by
    apply homogeneousQuotientPresheaf_hom_ext
    rw [homogeneousQuotientPresheafConjugateHom, homogeneousQuotientPresheafConjugateInv,
      homogeneousQuotientPresheafProjection_comp_lift_assoc, Category.assoc,
      homogeneousQuotientPresheafProjection_comp_lift,
      pointsPresheafConjugateHom_comp_inv_assoc, Category.comp_id]
  inv_hom_id := by
    apply homogeneousQuotientPresheaf_hom_ext
    rw [homogeneousQuotientPresheafConjugateHom, homogeneousQuotientPresheafConjugateInv,
      homogeneousQuotientPresheafProjection_comp_lift_assoc, Category.assoc,
      homogeneousQuotientPresheafProjection_comp_lift]
    have hinv := pointsPresheafConjugateHom_comp_inv H g⁻¹
    rw [inv_inv] at hinv
    rw [reassoc_of% hinv, Category.comp_id]

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
  rw [homogeneousQuotientPresheafConjugateHom, homogeneousQuotientPresheafLift_app_mk]
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
  rw [homogeneousQuotientPresheafConjugateInv, homogeneousQuotientPresheafLift_app_mk]
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

private def fppfHomogeneousQuotientConjugateHom (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    fppfHomogeneousQuotient H I ⟶ fppfHomogeneousQuotient H (I.conjugate g) :=
  (fppfHomogeneousQuotientHomEquiv H I (fppfHomogeneousQuotient H (I.conjugate g))).symm
    ⟨pointsPresheafConjugateHom H g ≫ fppfHomogeneousQuotientProjection H (I.conjugate g),
      fun A x n ↦ by
        have h := (fppfHomogeneousQuotientHomEquiv H (I.conjugate g)
          (fppfHomogeneousQuotient H (I.conjugate g)) (𝟙 _)).property A
          (HopfAlgebra.extendPoint H A.unop.unop g * x *
            (HopfAlgebra.extendPoint H A.unop.unop g)⁻¹)
          ⟨HopfAlgebra.extendPoint H A.unop.unop g * n.val *
            (HopfAlgebra.extendPoint H A.unop.unop g)⁻¹,
            extendPoint_conj_mem_conjugate H I g A.unop.unop n.property⟩
        simp only [fppfHomogeneousQuotientHomEquiv_apply, ObjectProperty.FullSubcategory.id_hom,
          Category.comp_id] at h
        have hm : HopfAlgebra.extendPoint H A.unop.unop g * (x * n.val) *
              (HopfAlgebra.extendPoint H A.unop.unop g)⁻¹ =
            HopfAlgebra.extendPoint H A.unop.unop g * x *
              (HopfAlgebra.extendPoint H A.unop.unop g)⁻¹ *
              (HopfAlgebra.extendPoint H A.unop.unop g * n.val *
                (HopfAlgebra.extendPoint H A.unop.unop g)⁻¹) := by
          simp [mul_assoc]
        exact (congrArg (fun z ↦
          (fppfHomogeneousQuotientProjection H (I.conjugate g)).app A (ULift.up z)) hm).trans h⟩

@[reassoc]
private theorem fppfHomogeneousQuotientProjection_comp_conjugateHom (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    fppfHomogeneousQuotientProjection H I ≫ (fppfHomogeneousQuotientConjugateHom H I g).hom =
      pointsPresheafConjugateHom H g ≫ fppfHomogeneousQuotientProjection H (I.conjugate g) :=
  fppfHomogeneousQuotientHomEquiv_symm_apply H I _ _ _

private def fppfHomogeneousQuotientConjugateInv (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    fppfHomogeneousQuotient H (I.conjugate g) ⟶ fppfHomogeneousQuotient H I :=
  (fppfHomogeneousQuotientHomEquiv H (I.conjugate g) (fppfHomogeneousQuotient H I)).symm
    ⟨pointsPresheafConjugateHom H g⁻¹ ≫ fppfHomogeneousQuotientProjection H I,
      fun A x n ↦ by
        have h := (fppfHomogeneousQuotientHomEquiv H I
          (fppfHomogeneousQuotient H I) (𝟙 _)).property A
          (HopfAlgebra.extendPoint H A.unop.unop g⁻¹ * x *
            (HopfAlgebra.extendPoint H A.unop.unop g⁻¹)⁻¹)
          ⟨HopfAlgebra.extendPoint H A.unop.unop g⁻¹ * n.val *
            (HopfAlgebra.extendPoint H A.unop.unop g⁻¹)⁻¹,
            extendPoint_inv_conj_mem_of_mem_conjugate H I g A.unop.unop n.property⟩
        simp only [fppfHomogeneousQuotientHomEquiv_apply, ObjectProperty.FullSubcategory.id_hom,
          Category.comp_id] at h
        have hm : HopfAlgebra.extendPoint H A.unop.unop g⁻¹ * (x * n.val) *
              (HopfAlgebra.extendPoint H A.unop.unop g⁻¹)⁻¹ =
            HopfAlgebra.extendPoint H A.unop.unop g⁻¹ * x *
              (HopfAlgebra.extendPoint H A.unop.unop g⁻¹)⁻¹ *
              (HopfAlgebra.extendPoint H A.unop.unop g⁻¹ * n.val *
                (HopfAlgebra.extendPoint H A.unop.unop g⁻¹)⁻¹) := by
          simp [mul_assoc]
        exact (congrArg (fun z ↦
          (fppfHomogeneousQuotientProjection H I).app A (ULift.up z)) hm).trans h⟩

@[reassoc]
private theorem fppfHomogeneousQuotientProjection_comp_conjugateInv (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    fppfHomogeneousQuotientProjection H (I.conjugate g) ≫
        (fppfHomogeneousQuotientConjugateInv H I g).hom =
      pointsPresheafConjugateHom H g⁻¹ ≫ fppfHomogeneousQuotientProjection H I :=
  fppfHomogeneousQuotientHomEquiv_symm_apply H (I.conjugate g) _ _ _

/-- **Inner conjugation on fppf homogeneous quotients.** Conjugating by a ground-ring point `g`
identifies `G / N` with `G / (g N g⁻¹)` as fppf sheaves. -/
def fppfHomogeneousQuotientConjugateIso (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    fppfHomogeneousQuotient H I ≅ fppfHomogeneousQuotient H (I.conjugate g) where
  hom := fppfHomogeneousQuotientConjugateHom H I g
  inv := fppfHomogeneousQuotientConjugateInv H I g
  hom_inv_id := by
    apply fppfHomogeneousQuotient_hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
      Category.comp_id]
    rw [fppfHomogeneousQuotientProjection_comp_conjugateHom_assoc,
      fppfHomogeneousQuotientProjection_comp_conjugateInv,
      pointsPresheafConjugateHom_comp_inv_assoc]
  inv_hom_id := by
    apply fppfHomogeneousQuotient_hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
      Category.comp_id]
    rw [fppfHomogeneousQuotientProjection_comp_conjugateInv_assoc,
      fppfHomogeneousQuotientProjection_comp_conjugateHom]
    have hinv := pointsPresheafConjugateHom_comp_inv H g⁻¹
    rw [inv_inv] at hinv
    rw [reassoc_of% hinv]

@[reassoc]
private theorem fppfHomogeneousQuotientProjection_comp_conjugateIso_hom (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    fppfHomogeneousQuotientProjection H I ≫
        (fppfHomogeneousQuotientConjugateIso H I g).hom.hom =
      pointsPresheafConjugateHom H g ≫ fppfHomogeneousQuotientProjection H (I.conjugate g) :=
  fppfHomogeneousQuotientProjection_comp_conjugateHom H I g

@[reassoc]
private theorem fppfHomogeneousQuotientProjection_comp_conjugateIso_inv (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    fppfHomogeneousQuotientProjection H (I.conjugate g) ≫
        (fppfHomogeneousQuotientConjugateIso H I g).inv.hom =
      pointsPresheafConjugateHom H g⁻¹ ≫ fppfHomogeneousQuotientProjection H I :=
  fppfHomogeneousQuotientProjection_comp_conjugateInv H I g

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
          (HopfAlgebra.extendPoint H A.unop.unop g)⁻¹)) :=
  congrArg (fun f ↦ f.app A (ULift.up x))
    (fppfHomogeneousQuotientProjection_comp_conjugateIso_hom H I g)

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
          (HopfAlgebra.extendPoint H A.unop.unop g⁻¹)⁻¹)) :=
  congrArg (fun f ↦ f.app A (ULift.up x))
    (fppfHomogeneousQuotientProjection_comp_conjugateIso_inv H I g)

/-- Conjugation of fppf homogeneous quotients commutes with subgroup-inclusion projections. -/
@[reassoc]
theorem fppfHomogeneousQuotientConjugateIso_hom_comp_map {I J : HopfIdeal R H} (hJI : J ≤ I)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (fppfHomogeneousQuotientConjugateIso H I g).hom ≫
        fppfHomogeneousQuotientMap H (HopfIdeal.conjugate_mono g hJI) =
      fppfHomogeneousQuotientMap H hJI ≫
        (fppfHomogeneousQuotientConjugateIso H J g).hom := by
  apply fppfHomogeneousQuotient_hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    fppfHomogeneousQuotientProjection_comp_conjugateIso_hom_assoc,
    fppfHomogeneousQuotientProjection_comp_map,
    fppfHomogeneousQuotientProjection_comp_map_assoc,
    fppfHomogeneousQuotientProjection_comp_conjugateIso_hom]

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
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, TypeCat.Fun.toFun_apply]
  have hm : HopfAlgebra.extendPoint H A.unop.unop g *
        (HopfAlgebra.extendPoint H A.unop.unop x * y) *
          (HopfAlgebra.extendPoint H A.unop.unop g)⁻¹ =
      HopfAlgebra.extendPoint H A.unop.unop (g * x * g⁻¹) *
        (HopfAlgebra.extendPoint H A.unop.unop g * y *
          (HopfAlgebra.extendPoint H A.unop.unop g)⁻¹) := by
    simp [map_mul, map_inv, mul_assoc]
  calc
    _ = (fppfHomogeneousQuotientConjugateIso H I g).hom.hom.app A
        ((fppfHomogeneousQuotientProjection H I).app A
          (ULift.up (HopfAlgebra.extendPoint H A.unop.unop x * y))) := by
      rw [fppfHomogeneousQuotientTranslation_hom_app_projection]
    _ = (fppfHomogeneousQuotientProjection H (I.conjugate g)).app A
        (ULift.up (HopfAlgebra.extendPoint H A.unop.unop g *
          (HopfAlgebra.extendPoint H A.unop.unop x * y) *
          (HopfAlgebra.extendPoint H A.unop.unop g)⁻¹)) := by
      rw [fppfHomogeneousQuotientConjugateIso_hom_app_projection]
    _ = (fppfHomogeneousQuotientProjection H (I.conjugate g)).app A
        (ULift.up (HopfAlgebra.extendPoint H A.unop.unop (g * x * g⁻¹) *
          (HopfAlgebra.extendPoint H A.unop.unop g * y *
            (HopfAlgebra.extendPoint H A.unop.unop g)⁻¹))) :=
      congrArg (fun z ↦ (fppfHomogeneousQuotientProjection H (I.conjugate g)).app A (ULift.up z)) hm
    _ = _ := by
      rw [fppfHomogeneousQuotientConjugateIso_hom_app_projection,
        fppfHomogeneousQuotientTranslation_hom_app_projection]

end

end CommHopfAlgCat
