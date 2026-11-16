/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.DerivedCategory.Basic
public import TauCeti.Algebra.Homology.CochainComplex.Double
public import TauCeti.Algebra.Homology.HomotopyCategory.Bounded.Double

/-!
# The distinguished triangle of a conflation

Let `S : X ↣ Y ↠ Z` be a conflation of an exact structure `E`. Its terms, placed in degree zero,
form a distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` of the bounded derived category `Dᵇ(E)`, and
its third morphism is natural in morphisms of conflations.

The two-term complex `D = (Y ⟶ Z)`, in degrees `0` and `1`, receives `X` in degree `0` with
acyclic mapping cone, so `X ≅ D` in `Dᵇ(E)`. Splitting off its top term is a degreewise split short
exact sequence `Z[-1] ⟶ D ⟶ Y`, hence a distinguished triangle of the homotopy category whose
third morphism `Y ⟶ Z[-1]⟦1⟧ ≅ Z` is `g`. Its rotation, transported along `X ≅ D`, is the
triangle of the conflation.

## Main definitions

* `TauCeti.ExactStructure.BoundedDerivedCategory.conflationδ`: the third morphism
  `Z ⟶ X⟦1⟧` of the triangle of a conflation.

## Main results

* `TauCeti.ExactStructure.acyclic_mappingCone_doubleι`: the chain map `X[0] ⟶ (Y ⟶ Z)` of a
  conflation has acyclic mapping cone.
* `TauCeti.ExactStructure.BoundedDerivedCategory.conflationTriangle_distinguished`: the triangle
  of a conflation is distinguished.
* `TauCeti.ExactStructure.BoundedDerivedCategory.conflationδ_naturality`: the third morphism is
  natural in morphisms of conflations.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  arXiv:0811.1480, Section 10.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject
open HomotopyCategory.Bounded (mkMap mkMap_comp singleFunctorObjIsoMk mkSingleIsoShift)

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

namespace ConflationTriangle

variable (S : ShortComplex C)

/-- The cycles of the mapping cone of `doubleι`: `X` in degree `0`, `Z` in degree `1`. -/
private noncomputable def coneB : ℤ → C
  | Int.ofNat 0 => S.X₁
  | Int.ofNat 1 => S.X₃
  | Int.ofNat (_ + 2) => 0
  | Int.negSucc _ => 0

private noncomputable def coneJ : ∀ m, coneB S m ⟶ S.double.X m
  | Int.ofNat 0 => S.f ≫ (HomologicalComplex.doubleXIso₀ S.g ComplexShape.up_rel_zero_one).inv
  | Int.ofNat 1 => (HomologicalComplex.doubleXIso₁ S.g ComplexShape.up_rel_zero_one (by simp)).inv
  | Int.ofNat (_ + 2) => 0
  | Int.negSucc _ => 0

private noncomputable def coneU : ∀ m, S.double.X m ⟶ coneB S (m + 1)
  | Int.ofNat 0 => (HomologicalComplex.doubleXIso₀ S.g ComplexShape.up_rel_zero_one).hom ≫ S.g
  | Int.ofNat (_ + 1) => 0
  | Int.negSucc _ => 0

private noncomputable def coneV :
    ∀ m, ((HomologicalComplex.single C (.up ℤ) 0).obj S.X₁).X m ⟶ coneB S m
  | Int.ofNat 0 => (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₁).hom
  | Int.ofNat (_ + 1) => 0
  | Int.negSucc _ => 0

private theorem coneJ_zero :
    coneJ S 0 = S.f ≫ (HomologicalComplex.doubleXIso₀ S.g ComplexShape.up_rel_zero_one).inv :=
  rfl

private theorem coneJ_one :
    coneJ S 1 = (HomologicalComplex.doubleXIso₁ S.g ComplexShape.up_rel_zero_one zero_ne_one).inv :=
  rfl

private theorem coneU_zero :
    coneU S 0 = (HomologicalComplex.doubleXIso₀ S.g ComplexShape.up_rel_zero_one).hom ≫ S.g :=
  rfl

private theorem coneV_zero : coneV S 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₁).hom :=
  rfl

private theorem coneV_one : coneV S 1 = 0 :=
  rfl

private theorem isZero_single_X {m : ℤ} (hm : m ≠ 0) :
    IsZero (((HomologicalComplex.single C (.up ℤ) 0).obj S.X₁).X m) :=
  HomologicalComplex.isZero_single_obj_X _ 0 _ m hm

private theorem isIso_coneJ {m : ℤ} (hm : m ≠ 0) : IsIso (coneJ S m) :=
  match m, hm with
  | Int.ofNat 0, hm => absurd rfl hm
  | Int.ofNat 1, _ =>
    inferInstanceAs
      (IsIso (HomologicalComplex.doubleXIso₁ S.g ComplexShape.up_rel_zero_one zero_ne_one).inv)
  | Int.ofNat (_ + 2), _ => isIso_of_source_target_iso_zero _ (isZero_zero C).isoZero
    (HomologicalComplex.isZero_double_X _ _ _ (by lia) (by lia)).isoZero
  | Int.negSucc _, _ => isIso_of_source_target_iso_zero _ (isZero_zero C).isoZero
    (HomologicalComplex.isZero_double_X _ _ _ (by lia) (by lia)).isoZero

private theorem isIso_coneV {m : ℤ} (hm : m ≠ 1) : IsIso (coneV S m) :=
  match m, hm with
  | Int.ofNat 0, _ => inferInstanceAs (IsIso (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₁).hom)
  | Int.ofNat 1, hm => absurd rfl hm
  | Int.ofNat (_ + 2), _ => isIso_of_source_target_iso_zero _
    (isZero_single_X S (by lia)).isoZero (isZero_zero C).isoZero
  | Int.negSucc _, _ => isIso_of_source_target_iso_zero _
    (isZero_single_X S (by lia)).isoZero (isZero_zero C).isoZero

private theorem coneU_eq_zero {m : ℤ} (hm : m ≠ 0) : coneU S m = 0 :=
  match m, hm with
  | Int.ofNat 0, hm => absurd rfl hm
  | Int.ofNat (_ + 1), _ => rfl
  | Int.negSucc _, _ => rfl

end ConflationTriangle

variable [HasBinaryBiproducts C] {E : ExactStructure C}

open ConflationTriangle in
/-- **`X` is resolved by `Y ⟶ Z`**: for a conflation `X ↣ Y ↠ Z`, the chain map
`X[0] ⟶ (Y ⟶ Z)` induced by `X ↣ Y` has acyclic mapping cone. -/
theorem acyclic_mappingCone_doubleι {S : ShortComplex C} (hS : E.Conflation S) :
    E.acyclic (CochainComplex.mappingCone S.doubleι) := by
  refine E.acyclic_mappingCone_of_isPushout _ (coneB S) (coneJ S) (fun _ ↦ 0) (coneU S)
    (coneV S) (fun m ↦ ?_) (fun m ↦ ?_) (fun m ↦ ?_) (fun m ↦ ?_) (fun _ ↦ by simp)
    (fun _ ↦ by simp)
  · by_cases hm : m = 0
    · subst hm
      rw [coneJ_zero]
      exact E.isInflation_comp _ _ (E.isInflation_f hS) (MorphismProperty.of_isIso _ _)
    · have := isIso_coneJ S hm
      exact MorphismProperty.of_isIso E.inflations _
  · by_cases hm : m = 0
    · subst hm
      let e := HomologicalComplex.doubleXIso₀ S.g ComplexShape.up_rel_zero_one
      have hS' : E.Conflation (ShortComplex.mk (S.f ≫ e.inv) (e.hom ≫ S.g) (by simp)) :=
        E.conflation_of_iso (S := S)
          (ShortComplex.isoMk (Iso.refl _) e.symm (Iso.refl _) (by simp) (by simp)) hS
      dsimp only [Int.reduceAdd]
      rw [coneJ_zero, coneU_zero, coneV_one]
      -- `exact`: the objects `coneB S 0` and `coneB S 1` are `S.X₁` and `S.X₃` by definition.
      exact (E.isKernelCokernelPair _ hS').isPushout_of_isZero (isZero_single_X S one_ne_zero)
    · have := isIso_coneJ S hm
      have := isIso_coneV S (m := m + 1) (by lia)
      exact IsPushout.of_horiz_isIso ⟨by simp [coneU_eq_zero S hm]⟩
  · by_cases hm : m = 0
    · subst hm
      dsimp only [Int.reduceAdd]
      rw [coneU_zero, coneJ_one, HomologicalComplex.double_d S.g _ zero_ne_one]
      -- `exact`: `coneB S 1` is `S.X₃` by definition, so `rw [Category.assoc]` cannot see it.
      exact Category.assoc _ _ _
    · rw [coneU_eq_zero S hm, zero_comp, HomologicalComplex.double_d_eq_zero₀ _ _ _ _ hm]
  · by_cases hm : m = 0
    · subst hm
      rw [coneV_zero, coneJ_zero]
      -- `exact`: `coneB S 0` is `S.X₁` by definition.
      exact S.doubleι_f_zero.symm
    · exact (isZero_single_X S hm).eq_of_src _ _

namespace ConflationTriangle

/-! ### The triangle in the bounded derived category -/

/-- The two-term complex `X₀ ⟶ X₁`, in degrees `0` and `1`, as an object of `Kᵇ(C)`. -/
private noncomputable abbrev bDouble {X₀ X₁ : C} (g : X₀ ⟶ X₁) : HomotopyCategory.Bounded C :=
  HomotopyCategory.Bounded.mk _ (CochainComplex.bounded_double g ComplexShape.up_rel_zero_one)

/-- An object in degree `n`, as the class in `Kᵇ(C)` of a complex. -/
private noncomputable abbrev bSingle (n : ℤ) (A : C) : HomotopyCategory.Bounded C :=
  HomotopyCategory.Bounded.mk _ (CochainComplex.bounded_single n A)

/-- The inclusion `X₁[-1] ⟶ (X₀ ⟶ X₁)`, in `Kᵇ(C)`. -/
private noncomputable abbrev bDoubleι₁ {X₀ X₁ : C} (g : X₀ ⟶ X₁) : bSingle 1 X₁ ⟶ bDouble g :=
  mkMap (HomologicalComplex.doubleι₁ g ComplexShape.up_rel_zero_one zero_ne_one)

variable {S : ShortComplex C}

private theorem isIso_Q_map_doubleι (hS : E.Conflation S) :
    IsIso ((BoundedDerivedCategory.Q E).map
      (mkMap S.doubleι : bSingle 0 S.X₁ ⟶ bDouble S.g)) :=
  Localization.inverts _ E.acyclicBounded.trW _
    (E.acyclicBounded_trW_homMk_quotient_map _ (acyclic_mappingCone_doubleι hS))

/-- The resolution `X ⟶ (Y ⟶ Z)`, as an isomorphism of `Dᵇ(E)`. -/
private noncomputable def doubleιIso (hS : E.Conflation S) :
    (BoundedDerivedCategory.Q E).obj (bSingle 0 S.X₁) ≅
      (BoundedDerivedCategory.Q E).obj (bDouble S.g) :=
  have := isIso_Q_map_doubleι hS
  asIso ((BoundedDerivedCategory.Q E).map (mkMap S.doubleι : bSingle 0 S.X₁ ⟶ bDouble S.g))

@[simp]
private theorem doubleιIso_hom (hS : E.Conflation S) :
    (doubleιIso hS).hom = (BoundedDerivedCategory.Q E).map (mkMap S.doubleι) :=
  rfl

/-- The object `A` in degree `0` is the shift of `A` in degree `1`, in `Dᵇ(E)`. -/
private noncomputable def shiftSingleIsoQ (A : C) :
    (BoundedDerivedCategory.Q E).obj (bSingle 0 A) ≅
      ((BoundedDerivedCategory.Q E).obj (bSingle 1 A))⟦(1 : ℤ)⟧ :=
  (BoundedDerivedCategory.Q E).mapIso (mkSingleIsoShift 1 0 1 (by simp) A) ≪≫
    ((BoundedDerivedCategory.Q E).commShiftIso (1 : ℤ)).app _

/-- The third morphism `Z ⟶ X⟦1⟧` of the triangle of a conflation, between the classes of the
complexes `Z[0]` and `X[0]`: minus the shifted inclusion `Z[-1] ⟶ (Y ⟶ Z)`, transported along
`Z[0] ≅ Z[-1]⟦1⟧` and `X ≅ (Y ⟶ Z)`. -/
private noncomputable def δ' (hS : E.Conflation S) :
    (BoundedDerivedCategory.Q E).obj (bSingle 0 S.X₃) ⟶
      ((BoundedDerivedCategory.Q E).obj (bSingle 0 S.X₁))⟦(1 : ℤ)⟧ :=
  (shiftSingleIsoQ S.X₃).hom ≫ (-((BoundedDerivedCategory.Q E).map (bDoubleι₁ S.g))⟦(1 : ℤ)⟧') ≫
    (doubleιIso hS).inv⟦(1 : ℤ)⟧'

/-- **The triangle of a conflation is distinguished**, for the classes of the complexes `X[0]`,
`Y[0]`, `Z[0]`: it is the rotation of the triangle of
`TauCeti.HomotopyCategory.Bounded.double_distinguished`, transported along
`X ≅ (Y ⟶ Z)` and `Z[0] ≅ Z[-1]⟦1⟧`. -/
private theorem distinguished' (hS : E.Conflation S) :
    Triangle.mk ((BoundedDerivedCategory.Q E).map
        (mkMap ((HomologicalComplex.single C (.up ℤ) 0).map S.f) :
          bSingle 0 S.X₁ ⟶ bSingle 0 S.X₂))
      ((BoundedDerivedCategory.Q E).map
        (mkMap ((HomologicalComplex.single C (.up ℤ) 0).map S.g) :
          bSingle 0 S.X₂ ⟶ bSingle 0 S.X₃)) (δ' hS) ∈ distTriang _ := by
  -- The rotation of the image of `double_distinguished S.g`, with its morphisms unfolded.
  have hR : Triangle.mk
      ((BoundedDerivedCategory.Q E).map
        (mkMap (HomologicalComplex.doubleπ₀ S.g ComplexShape.up_rel_zero_one zero_ne_one) :
          bDouble S.g ⟶ bSingle 0 S.X₂))
      ((BoundedDerivedCategory.Q E).map
        ((mkMap ((HomologicalComplex.single C (.up ℤ) 0).map S.g) :
          bSingle 0 S.X₂ ⟶ bSingle 0 S.X₃) ≫ (mkSingleIsoShift 1 0 1 (by simp) S.X₃).hom) ≫
        ((BoundedDerivedCategory.Q E).commShiftIso (1 : ℤ)).hom.app (bSingle 1 S.X₃))
      (-((BoundedDerivedCategory.Q E).map (bDoubleι₁ S.g))⟦(1 : ℤ)⟧') ∈ distTriang _ :=
    rot_of_distTriang _
      ((BoundedDerivedCategory.Q E).map_distinguished _
        (HomotopyCategory.Bounded.double_distinguished S.g))
  refine isomorphic_distinguished _ hR _
    (Triangle.isoMk _ _ (doubleιIso hS) (Iso.refl _) (shiftSingleIsoQ S.X₃) ?_ ?_ ?_)
  · simp only [Triangle.mk_mor₁, Iso.refl_hom, Category.comp_id, doubleιIso_hom]
    rw [← Functor.map_comp, ← mkMap_comp, S.doubleι_doubleπ]
  · simp only [Triangle.mk_mor₂, Iso.refl_hom, Category.id_comp, shiftSingleIsoQ, Iso.trans_hom,
      Functor.mapIso_hom, Iso.app_hom, Functor.map_comp, Category.assoc]
  · simp only [Triangle.mk_mor₃, δ', Category.assoc, Iso.inv_hom_id_map, Category.comp_id]

/-! ### Naturality -/

variable {S' : ShortComplex C} (φ : S ⟶ S')

/-- The map `(Y ⟶ Z) ⟶ (Y' ⟶ Z')` induced by a morphism of short complexes, in `Kᵇ(C)`. -/
private noncomputable abbrev bDoubleMap : bDouble S.g ⟶ bDouble S'.g :=
  mkMap (HomologicalComplex.doubleMap ComplexShape.up_rel_zero_one zero_ne_one φ.τ₂ φ.τ₃ φ.comm₂₃)

private theorem shiftSingleIsoQ_hom_naturality {A B : C} (a : A ⟶ B) :
    (BoundedDerivedCategory.Q E).map
      (mkMap ((HomologicalComplex.single C (.up ℤ) 0).map a) : bSingle 0 A ⟶ bSingle 0 B) ≫
      (shiftSingleIsoQ B).hom = (shiftSingleIsoQ A).hom ≫
        ((BoundedDerivedCategory.Q E).map (mkMap ((HomologicalComplex.single C (.up ℤ) 1).map a) :
          bSingle 1 A ⟶ bSingle 1 B))⟦(1 : ℤ)⟧' := by
  simp only [shiftSingleIsoQ, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [← Functor.map_comp_assoc,
    HomotopyCategory.Bounded.mkMap_single_comp_mkSingleIsoShift_hom 1 0 1 (by simp),
    Functor.map_comp_assoc,
    Functor.commShiftIso_hom_naturality]
  exact (Category.assoc _ _ _).symm

variable {φ} in
/-- **The third morphism of the triangle of a conflation is natural.** -/
private theorem δ'_naturality (hS : E.Conflation S) (hS' : E.Conflation S') :
    δ' hS ≫ ((BoundedDerivedCategory.Q E).map
      (mkMap ((HomologicalComplex.single C (.up ℤ) 0).map φ.τ₁) :
        bSingle 0 S.X₁ ⟶ bSingle 0 S'.X₁))⟦(1 : ℤ)⟧' =
      (BoundedDerivedCategory.Q E).map
        (mkMap ((HomologicalComplex.single C (.up ℤ) 0).map φ.τ₃) :
          bSingle 0 S.X₃ ⟶ bSingle 0 S'.X₃) ≫ δ' hS' := by
  have k₁ : (doubleιIso hS).inv ≫ (BoundedDerivedCategory.Q E).map
      (mkMap ((HomologicalComplex.single C (.up ℤ) 0).map φ.τ₁) :
        bSingle 0 S.X₁ ⟶ bSingle 0 S'.X₁) =
      (BoundedDerivedCategory.Q E).map (bDoubleMap φ) ≫ (doubleιIso hS').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, doubleιIso_hom, doubleιIso_hom,
      ← Functor.map_comp, ← Functor.map_comp, ← mkMap_comp, ← mkMap_comp,
      ShortComplex.doubleι_doubleMap]
  have k₂ : (-((BoundedDerivedCategory.Q E).map (bDoubleι₁ S.g))⟦(1 : ℤ)⟧') ≫
        ((BoundedDerivedCategory.Q E).map (bDoubleMap φ))⟦(1 : ℤ)⟧' =
      ((BoundedDerivedCategory.Q E).map
        (mkMap ((HomologicalComplex.single C (.up ℤ) 1).map φ.τ₃) :
          bSingle 1 S.X₃ ⟶ bSingle 1 S'.X₃))⟦(1 : ℤ)⟧' ≫
        (-((BoundedDerivedCategory.Q E).map (bDoubleι₁ S'.g))⟦(1 : ℤ)⟧') := by
    rw [Preadditive.neg_comp, Preadditive.comp_neg, ← Functor.map_comp, ← Functor.map_comp,
      ← Functor.map_comp, ← Functor.map_comp, ← mkMap_comp, ← mkMap_comp,
      HomologicalComplex.doubleι₁_doubleMap]
  simp only [δ', Category.assoc]
  rw [← Functor.map_comp, k₁, Functor.map_comp, reassoc_of% k₂,
    ← reassoc_of% (shiftSingleIsoQ_hom_naturality (E := E) φ.τ₃)]

end ConflationTriangle

namespace BoundedDerivedCategory

open ConflationTriangle

variable {S S' : ShortComplex C}

/-- An object placed in degree `0` of `Kᵇ(C)` is the class of the complex `X[0]`. -/
private noncomputable abbrev singleIso (A : C) :
    (HomotopyCategory.Bounded.singleFunctor C 0).obj A ≅ bSingle 0 A :=
  singleFunctorObjIsoMk 0 A

private theorem Q_map_singleIso_hom_naturality {A B : C} (a : A ⟶ B) :
    (Q E).map ((HomotopyCategory.Bounded.singleFunctor C 0).map a) ≫
      (Q E).map (singleIso B).hom = (Q E).map (singleIso A).hom ≫
        (Q E).map (mkMap ((HomologicalComplex.single C (.up ℤ) 0).map a) :
          bSingle 0 A ⟶ bSingle 0 B) := by
  rw [← Functor.map_comp, ← Functor.map_comp,
    HomotopyCategory.Bounded.singleFunctor_map_comp_singleFunctorObjIsoMk_hom]

/-- **The connecting morphism of a conflation** `X ↣ Y ↠ Z` in `Dᵇ(E)`: the third morphism
`Z ⟶ X⟦1⟧` of its distinguished triangle. -/
noncomputable def conflationδ (hS : E.Conflation S) :
    (Q E).obj ((HomotopyCategory.Bounded.singleFunctor C 0).obj S.X₃) ⟶
      ((Q E).obj ((HomotopyCategory.Bounded.singleFunctor C 0).obj S.X₁))⟦(1 : ℤ)⟧ :=
  (Q E).map (singleIso S.X₃).hom ≫ δ' hS ≫ ((Q E).map (singleIso S.X₁).inv)⟦(1 : ℤ)⟧'

/-- **The triangle of a conflation is distinguished**: a conflation `X ↣ Y ↠ Z` gives a
distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` in `Dᵇ(E)`. -/
theorem conflationTriangle_distinguished (hS : E.Conflation S) :
    Triangle.mk ((Q E).map ((HomotopyCategory.Bounded.singleFunctor C 0).map S.f))
      ((Q E).map ((HomotopyCategory.Bounded.singleFunctor C 0).map S.g))
        (conflationδ hS) ∈ distTriang _ :=
  isomorphic_distinguished _ (distinguished' hS) _ (Triangle.isoMk _ _
    ((Q E).mapIso (singleIso _)) ((Q E).mapIso (singleIso _)) ((Q E).mapIso (singleIso _))
      (Q_map_singleIso_hom_naturality S.f) (Q_map_singleIso_hom_naturality S.g)
      (by simp [conflationδ, ← Functor.map_comp]))

/-- **The connecting morphism of a conflation is natural** in morphisms of conflations. -/
theorem conflationδ_naturality (φ : S ⟶ S') (hS : E.Conflation S) (hS' : E.Conflation S') :
    conflationδ hS ≫ ((Q E).map ((HomotopyCategory.Bounded.singleFunctor C 0).map φ.τ₁))⟦(1 : ℤ)⟧' =
      (Q E).map ((HomotopyCategory.Bounded.singleFunctor C 0).map φ.τ₃) ≫ conflationδ hS' := by
  have k : (singleIso S.X₁).inv ≫ (HomotopyCategory.Bounded.singleFunctor C 0).map φ.τ₁ =
      mkMap ((HomologicalComplex.single C (.up ℤ) 0).map φ.τ₁) ≫ (singleIso S'.X₁).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact HomotopyCategory.Bounded.singleFunctor_map_comp_singleFunctorObjIsoMk_hom 0 φ.τ₁
  simp only [conflationδ, Category.assoc, ← Functor.map_comp, k]
  rw [Functor.map_comp, Functor.map_comp, reassoc_of% (δ'_naturality hS hS'),
    reassoc_of% (Q_map_singleIso_hom_naturality φ.τ₃)]

end BoundedDerivedCategory

end TauCeti.ExactStructure
