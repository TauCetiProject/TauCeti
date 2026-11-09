/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

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

* `TauCeti.ExactStructure.BoundedDerivedCategory.conflationTriangle_distinguished`: the triangle
  of a conflation is distinguished.
* `TauCeti.ExactStructure.BoundedDerivedCategory.conflationδ_naturality`: the third morphism is
  natural in morphisms of conflations.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject
open HomotopyCategory.Bounded (mkMap singleFunctorObjIsoMk)

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {E : ExactStructure C}

namespace ConflationTriangle

variable (S : ShortComplex C)

theorem rel₀₁ : (ComplexShape.up ℤ).Rel 0 1 := by simp

/-- The two-term complex `Y ⟶ Z` of a short complex, in degrees `0` and `1`. -/
noncomputable abbrev double : CochainComplex C ℤ := HomologicalComplex.double S.g rel₀₁

/-- The inclusion of `X` in degree `0` into the two-term complex `Y ⟶ Z`. -/
noncomputable def doubleι : (HomologicalComplex.single C (.up ℤ) 0).obj S.X₁ ⟶ double S :=
  HomologicalComplex.mkHomFromSingle (S.f ≫ (HomologicalComplex.doubleXIso₀ S.g rel₀₁).inv)
    (by
      rintro k (hk : 0 + 1 = k)
      obtain rfl : k = 1 := by lia
      rw [HomologicalComplex.double_d S.g rel₀₁ (by simp)]
      simp)

omit [HasBinaryBiproducts C] in
theorem doubleι_f_zero : (doubleι S).f 0 =
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₁).hom ≫ S.f ≫
      (HomologicalComplex.doubleXIso₀ S.g rel₀₁).inv :=
  HomologicalComplex.mkHomFromSingle_f _ _

/-- The cycles of the mapping cone of `doubleι`: `X` in degree `0`, `Z` in degree `1`. -/
private noncomputable def coneB : ℤ → C
  | Int.ofNat 0 => S.X₁
  | Int.ofNat 1 => S.X₃
  | Int.ofNat (_ + 2) => 0
  | Int.negSucc _ => 0

private noncomputable def coneJ : ∀ m, coneB S m ⟶ (double S).X m
  | Int.ofNat 0 => S.f ≫ (HomologicalComplex.doubleXIso₀ S.g rel₀₁).inv
  | Int.ofNat 1 => (HomologicalComplex.doubleXIso₁ S.g rel₀₁ (by simp)).inv
  | Int.ofNat (_ + 2) => 0
  | Int.negSucc _ => 0

private noncomputable def coneU : ∀ m, (double S).X m ⟶ coneB S (m + 1)
  | Int.ofNat 0 => (HomologicalComplex.doubleXIso₀ S.g rel₀₁).hom ≫ S.g
  | Int.ofNat (_ + 1) => 0
  | Int.negSucc _ => 0

private noncomputable def coneV :
    ∀ m, ((HomologicalComplex.single C (.up ℤ) 0).obj S.X₁).X m ⟶ coneB S m
  | Int.ofNat 0 => (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₁).hom
  | Int.ofNat (_ + 1) => 0
  | Int.negSucc _ => 0

omit [HasBinaryBiproducts C] in
private theorem isZero_single_X {m : ℤ} (hm : m ≠ 0) :
    IsZero (((HomologicalComplex.single C (.up ℤ) 0).obj S.X₁).X m) :=
  HomologicalComplex.isZero_single_obj_X _ 0 _ m hm

omit [HasBinaryBiproducts C] in
private theorem isZero_double_X {m : ℤ} (h₀ : m ≠ 0) (h₁ : m ≠ 1) : IsZero ((double S).X m) :=
  HomologicalComplex.isZero_double_X _ _ _ h₀ h₁

/-- The cokernel square of a conflation `W ↣ X ↠ Z`, against a zero object: a pushout. -/
private theorem isPushout_of_conflation_of_isZero {W X Y Z : C} {f : W ⟶ X} {h : X ⟶ Z}
    {w : f ≫ h = 0} (hS : E.Conflation (ShortComplex.mk f h w)) (hY : IsZero Y) :
    IsPushout f (0 : W ⟶ Y) h (0 : Y ⟶ Z) := by
  have hkc := E.isKernelCokernelPair _ hS
  have := hkc.epi_g
  refine IsPushout.of_isColimit' (⟨by simp [w]⟩ : CommSq f (0 : W ⟶ Y) h (0 : Y ⟶ Z))
    (PushoutCocone.IsColimit.mk _ (fun s ↦ hkc.desc s.inl (by simpa using s.condition))
      (fun s ↦ hkc.g_desc _ _) (fun s ↦ hY.eq_of_src _ _) (fun s m hm _ ↦ ?_))
  rw [← cancel_epi h]
  exact hm.trans (hkc.g_desc _ _).symm

variable {S}

/-- **`X` is resolved by `Y ⟶ Z`**: the mapping cone of `doubleι` is acyclic. -/
theorem acyclic_mappingCone_doubleι (hS : E.Conflation S) :
    E.acyclic (CochainComplex.mappingCone (doubleι S)) := by
  refine E.acyclic_mappingCone_of_isPushout _ (coneB S) (coneJ S) (fun _ ↦ 0) (coneU S)
    (coneV S) (fun m ↦ ?_) (fun m ↦ ?_) (fun m ↦ ?_) (fun m ↦ ?_) (fun m ↦ ?_) (fun m ↦ ?_)
  · have hiso {A B : C} (i : A ⟶ B) [IsIso i] : E.IsInflation i :=
      MorphismProperty.of_isIso E.inflations i
    match m with
    | Int.ofNat 0 => exact E.isInflation_comp _ _ (E.isInflation_f hS) (hiso _)
    | Int.ofNat 1 =>
      have : IsIso (coneJ S (Int.ofNat 1)) :=
        inferInstanceAs (IsIso (HomologicalComplex.doubleXIso₁ S.g rel₀₁ (by simp)).inv)
      exact hiso _
    | Int.ofNat (k + 2) =>
      have : IsIso (coneJ S (Int.ofNat (k + 2))) := isIso_of_source_target_iso_zero _
        (isZero_zero C).isoZero (isZero_double_X S (by lia) (by lia)).isoZero
      exact hiso _
    | Int.negSucc k =>
      have : IsIso (coneJ S (Int.negSucc k)) := isIso_of_source_target_iso_zero _
        (isZero_zero C).isoZero (isZero_double_X S (by lia) (by lia)).isoZero
      exact hiso _
  · match m with
    | Int.negSucc 0 =>
      have : IsIso (coneJ S (Int.negSucc 0)) := isIso_of_source_target_iso_zero _
        (isZero_zero C).isoZero (isZero_double_X S (by lia) (by lia)).isoZero
      have : IsIso (coneV S (Int.negSucc 0 + 1)) :=
        inferInstanceAs (IsIso (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₁).hom)
      exact IsPushout.of_horiz_isIso ⟨(isZero_zero C).eq_of_src _ _⟩
    | Int.negSucc (k + 1) =>
      have : IsIso (coneJ S (Int.negSucc (k + 1))) := isIso_of_source_target_iso_zero _
        (isZero_zero C).isoZero (isZero_double_X S (by lia) (by lia)).isoZero
      have : IsIso (coneV S (Int.negSucc (k + 1) + 1)) := isIso_of_source_target_iso_zero _
        (isZero_single_X S (by lia)).isoZero (isZero_zero C).isoZero
      exact IsPushout.of_horiz_isIso ⟨(isZero_zero C).eq_of_src _ _⟩
    | Int.ofNat 0 =>
      have hS' : E.Conflation (ShortComplex.mk (S.f ≫ (HomologicalComplex.doubleXIso₀ S.g
          rel₀₁).inv) ((HomologicalComplex.doubleXIso₀ S.g rel₀₁).hom ≫ S.g) (by simp)) :=
        E.conflation_of_iso (S := S) (ShortComplex.isoMk (Iso.refl _)
          (HomologicalComplex.doubleXIso₀ S.g rel₀₁).symm (Iso.refl _) (by simp) (by simp)) hS
      exact isPushout_of_conflation_of_isZero hS' (isZero_single_X S (by lia))
    | Int.ofNat 1 =>
      have : IsIso (coneJ S (Int.ofNat 1)) :=
        inferInstanceAs (IsIso (HomologicalComplex.doubleXIso₁ S.g rel₀₁ (by simp)).inv)
      have : IsIso (coneV S (Int.ofNat 1 + 1)) := isIso_of_source_target_iso_zero _
        (isZero_single_X S (by lia)).isoZero (isZero_zero C).isoZero
      exact IsPushout.of_horiz_isIso ⟨(isZero_zero C).eq_of_tgt _ _⟩
    | Int.ofNat (k + 2) =>
      have : IsIso (coneJ S (Int.ofNat (k + 2))) := isIso_of_source_target_iso_zero _
        (isZero_zero C).isoZero (isZero_double_X S (by lia) (by lia)).isoZero
      have : IsIso (coneV S (Int.ofNat (k + 2) + 1)) := isIso_of_source_target_iso_zero _
        (isZero_single_X S (by lia)).isoZero (isZero_zero C).isoZero
      exact IsPushout.of_horiz_isIso ⟨(isZero_zero C).eq_of_src _ _⟩
  · match m with
    | Int.ofNat 0 =>
      change ((HomologicalComplex.doubleXIso₀ S.g rel₀₁).hom ≫ S.g) ≫
        (HomologicalComplex.doubleXIso₁ S.g rel₀₁ (by simp)).inv = (double S).d 0 1
      rw [HomologicalComplex.double_d S.g rel₀₁ (by simp), Category.assoc]
    | Int.ofNat (k + 1) => exact (isZero_double_X S (by lia) (by lia)).eq_of_tgt _ _
    | Int.negSucc k => exact (isZero_double_X S (by lia) (by lia)).eq_of_src _ _
  · match m with
    | Int.ofNat 0 => exact (doubleι_f_zero S).symm
    | Int.ofNat (k + 1) => exact (isZero_single_X S (by lia)).eq_of_src _ _
    | Int.negSucc k => exact (isZero_single_X S (by lia)).eq_of_src _ _
  · simp
  · simp

variable (S)

/-- The inclusion of the top term `Z`, in degree `1`, into the two-term complex `Y ⟶ Z`. -/
noncomputable def doubleTopι : (HomologicalComplex.single C (.up ℤ) 1).obj S.X₃ ⟶ double S :=
  HomologicalComplex.mkHomFromSingle (HomologicalComplex.doubleXIso₁ S.g rel₀₁ (by simp)).inv
    (by
      rintro k (hk : 1 + 1 = k)
      exact (isZero_double_X S (by lia) (by lia)).eq_of_tgt _ _)

omit [HasBinaryBiproducts C] in
theorem doubleTopι_f_one : (doubleTopι S).f 1 =
    (HomologicalComplex.singleObjXSelf (.up ℤ) 1 S.X₃).hom ≫
      (HomologicalComplex.doubleXIso₁ S.g rel₀₁ (by simp)).inv :=
  HomologicalComplex.mkHomFromSingle_f _ _

/-- The projection of the two-term complex `Y ⟶ Z` onto `Y` in degree `0`. -/
noncomputable def doubleπ : double S ⟶ (HomologicalComplex.single C (.up ℤ) 0).obj S.X₂ :=
  HomologicalComplex.mkHomFromDouble rel₀₁ (by simp)
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₂).inv 0 (by simp) (by simp)

omit [HasBinaryBiproducts C] in
theorem doubleπ_f_zero : (doubleπ S).f 0 =
    (HomologicalComplex.doubleXIso₀ S.g rel₀₁).hom ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₂).inv :=
  HomologicalComplex.mkHomFromDouble_f₀ _ _ _ _ _ _

omit [HasBinaryBiproducts C] in
/-- The resolution `X ⟶ (Y ⟶ Z)` followed by the projection onto `Y` is `f`. -/
theorem doubleι_doubleπ :
    doubleι S ≫ doubleπ S = (HomologicalComplex.single C (.up ℤ) 0).map S.f := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, doubleι_f_zero, doubleπ_f_zero,
    HomologicalComplex.single_map_f_self]
  simp

instance : IsIso ((doubleTopι S).f 1) := by
  rw [doubleTopι_f_one]
  infer_instance

instance : IsIso ((doubleπ S).f 0) := by
  rw [doubleπ_f_zero]
  infer_instance

/-- The short complex `Z[-1] ⟶ (Y ⟶ Z) ⟶ Y` splitting off the top term. -/
noncomputable abbrev topShortComplex : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (doubleTopι S) (doubleπ S) (by
    refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
    by_cases hn : n = 1
    · subst hn
      exact (HomologicalComplex.isZero_single_obj_X _ 0 _ 1 (by simp)).eq_of_tgt _ _
    · exact (HomologicalComplex.isZero_single_obj_X _ 1 _ n hn).eq_of_src _ _)

/-- The short complex splitting off the top term is split in each degree. -/
noncomputable def topSplitting :
    ∀ n, ((topShortComplex S).map (HomologicalComplex.eval C _ n)).Splitting
  | Int.ofNat 0 => .ofIsZeroOfIsIso _
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 1 S.X₃ (Int.ofNat 0) (by simp))
      (inferInstanceAs (IsIso ((doubleπ S).f 0)))
  | Int.ofNat 1 => .ofIsIsoOfIsZero _ (inferInstanceAs (IsIso ((doubleTopι S).f 1)))
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 S.X₂ (Int.ofNat 1) (by simp))
  | Int.ofNat (k + 2) => .ofIsZeroOfIsIso _
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 1 S.X₃ (Int.ofNat (k + 2)) (by lia))
      (isIso_of_source_target_iso_zero _ (isZero_double_X S (by lia) (by lia)).isoZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 S.X₂ (Int.ofNat (k + 2))
          (by lia)).isoZero)
  | Int.negSucc k => .ofIsZeroOfIsIso _
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 1 S.X₃ (Int.negSucc k) (by lia))
      (isIso_of_source_target_iso_zero _ (isZero_double_X S (by lia) (by lia)).isoZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 S.X₂ (Int.negSucc k)
          (by lia)).isoZero)

omit [HasBinaryBiproducts C] in
/-- The connecting morphism of the split sequence `Z[-1] ⟶ (Y ⟶ Z) ⟶ Y` is `g`. -/
theorem homOfDegreewiseSplit_comp_shiftIso :
    CochainComplex.homOfDegreewiseSplit _ (topSplitting S) ≫
      ((CochainComplex.singleFunctors C).shiftIso 1 0 1 (by simp)).hom.app S.X₃ =
        (HomologicalComplex.single C (.up ℤ) 0).map S.g := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, CochainComplex.homOfDegreewiseSplit_f]
  have h : (CochainComplex.cocycleOfDegreewiseSplit _ (topSplitting S)).1.v 0 (0 + 1) rfl =
      inv ((doubleπ S).f 0) ≫ (double S).d 0 1 ≫ inv ((doubleTopι S).f 1) := rfl
  have h₁ : inv ((doubleπ S).f 0) = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₂).hom ≫
      (HomologicalComplex.doubleXIso₀ S.g rel₀₁).inv :=
    IsIso.inv_eq_of_hom_inv_id (by simp [doubleπ_f_zero])
  have h₂ : inv ((doubleTopι S).f 1) = (HomologicalComplex.doubleXIso₁ S.g rel₀₁ (by simp)).hom ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 1 S.X₃).inv :=
    IsIso.inv_eq_of_hom_inv_id (by simp [doubleTopι_f_one])
  rw [h, h₁, h₂, HomologicalComplex.double_d S.g rel₀₁ (by simp),
    HomologicalComplex.single_map_f_self]
  simp [CochainComplex.singleFunctors, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq]

/-! ### The triangle in the bounded derived category -/

omit [HasBinaryBiproducts C] in
private theorem bounded_double : CochainComplex.bounded C (double S) :=
  (CochainComplex.bounded_iff C _).2 ⟨0, 1,
    (CochainComplex.isStrictlyGE_iff _ _).2 fun _ hi ↦ isZero_double_X S (by lia) (by lia),
    (CochainComplex.isStrictlyLE_iff _ _).2 fun _ hi ↦ isZero_double_X S (by lia) (by lia)⟩

/-- The two-term complex `Y ⟶ Z`, as an object of `Kᵇ(C)`. -/
private noncomputable abbrev bDouble (S : ShortComplex C) : HomotopyCategory.Bounded C :=
  HomotopyCategory.Bounded.mk _ (bounded_double S)

/-- An object in degree `n`, as the class in `Kᵇ(C)` of a complex. -/
private noncomputable abbrev bSingle (n : ℤ) (A : C) : HomotopyCategory.Bounded C :=
  HomotopyCategory.Bounded.mk _ (CochainComplex.bounded_single n A)

/-- The object `A` in degree `0` is the shift of `A` in degree `1`, in `Kᵇ(C)`. -/
private noncomputable def shiftSingleIso (A : C) : bSingle 0 A ≅ (bSingle 1 A)⟦(1 : ℤ)⟧ :=
  (HomotopyCategory.Bounded.fullyFaithfulι C).preimageIso
    ((_root_.HomotopyCategory.quotient C (.up ℤ)).mapIso
      (((CochainComplex.singleFunctors C).shiftIso 1 0 1 (by simp)).app A).symm ≪≫
        ((_root_.HomotopyCategory.quotient C (.up ℤ)).commShiftIso (1 : ℤ)).app _ ≪≫
          ((HomotopyCategory.Bounded.ι C).commShiftIso (1 : ℤ)).symm.app (bSingle 1 A))

variable {S}

private theorem isIso_Q_map_doubleι (hS : E.Conflation S) :
    IsIso ((BoundedDerivedCategory.Q E).map
      (mkMap (doubleι S) : bSingle 0 S.X₁ ⟶ bDouble S)) :=
  Localization.inverts _ E.acyclicBounded.trW _
    (E.acyclicBounded_trW_mkMap _ _ _ (acyclic_mappingCone_doubleι hS))

/-- The resolution `X ⟶ (Y ⟶ Z)`, as an isomorphism of `Dᵇ(E)`. -/
private noncomputable def doubleιIso (hS : E.Conflation S) :
    (BoundedDerivedCategory.Q E).obj (bSingle 0 S.X₁) ≅
      (BoundedDerivedCategory.Q E).obj (bDouble S) :=
  @asIso _ _ _ _ ((BoundedDerivedCategory.Q E).map
    (mkMap (doubleι S) : bSingle 0 S.X₁ ⟶ bDouble S)) (isIso_Q_map_doubleι hS)

/-- The object `A` in degree `0` is the shift of `A` in degree `1`, in `Dᵇ(E)`. -/
private noncomputable def shiftSingleIsoQ (A : C) :
    (BoundedDerivedCategory.Q E).obj (bSingle 0 A) ≅
      ((BoundedDerivedCategory.Q E).obj (bSingle 1 A))⟦(1 : ℤ)⟧ :=
  (BoundedDerivedCategory.Q E).mapIso (shiftSingleIso A) ≪≫
    ((BoundedDerivedCategory.Q E).commShiftIso (1 : ℤ)).app _

/-- The third morphism `Z ⟶ X⟦1⟧` of the triangle of a conflation, between the classes of the
complexes `Z[0]` and `X[0]`: minus the shifted inclusion `Z[-1] ⟶ (Y ⟶ Z)`, transported along
`Z[0] ≅ Z[-1]⟦1⟧` and `X ≅ (Y ⟶ Z)`. -/
private noncomputable def δ' (hS : E.Conflation S) :
    (BoundedDerivedCategory.Q E).obj (bSingle 0 S.X₃) ⟶
      ((BoundedDerivedCategory.Q E).obj (bSingle 0 S.X₁))⟦(1 : ℤ)⟧ :=
  (shiftSingleIsoQ S.X₃).hom ≫
    (-((BoundedDerivedCategory.Q E).map
      (mkMap (doubleTopι S) : bSingle 1 S.X₃ ⟶ bDouble S))⟦(1 : ℤ)⟧') ≫
      (doubleιIso hS).inv⟦(1 : ℤ)⟧'

/-- **The triangle of a conflation is distinguished**, for the classes of the complexes `X[0]`,
`Y[0]`, `Z[0]`. -/
private theorem distinguished' (hS : E.Conflation S) :
    Triangle.mk ((BoundedDerivedCategory.Q E).map
        (mkMap ((HomologicalComplex.single C (.up ℤ) 0).map S.f) :
          bSingle 0 S.X₁ ⟶ bSingle 0 S.X₂))
      ((BoundedDerivedCategory.Q E).map
        (mkMap ((HomologicalComplex.single C (.up ℤ) 0).map S.g) :
          bSingle 0 S.X₂ ⟶ bSingle 0 S.X₃)) (δ' hS) ∈ distTriang _ := by
  let ι' : bSingle 1 S.X₃ ⟶ bDouble S := mkMap (doubleTopι S)
  obtain ⟨W, g', h', hT'⟩ := distinguished_cocone_triangle ι'
  let E₀ := isoTriangleOfIso₁₂ _ _ ((HomotopyCategory.Bounded.ι C).map_distinguished _ hT')
    (CochainComplex.trianglehOfDegreewiseSplit_distinguished _ (topSplitting S))
    (Iso.refl _) (Iso.refl _) ((Category.comp_id _).trans (Category.id_comp _).symm)
  let E₃ : W ≅ bSingle 0 S.X₂ :=
    (HomotopyCategory.Bounded.fullyFaithfulι C).preimageIso (Triangle.π₃.mapIso E₀)
  have hE₃ : (HomotopyCategory.Bounded.ι C).map E₃.inv = E₀.inv.hom₃ :=
    (HomotopyCategory.Bounded.fullyFaithfulι C).map_preimage _
  have hE₀₁ : E₀.hom.hom₁ = 𝟙 _ := rfl
  have hE₀₂ : E₀.hom.hom₂ = 𝟙 _ := rfl
  have hg' : (HomotopyCategory.Bounded.ι C).map g' =
      (_root_.HomotopyCategory.quotient C (.up ℤ)).map (doubleπ S) ≫ E₀.inv.hom₃ := by
    have h := E₀.hom.comm₂
    rw [hE₀₂] at h
    have hk : (HomotopyCategory.Bounded.ι C).map g' ≫ E₀.hom.hom₃ =
        (_root_.HomotopyCategory.quotient C (.up ℤ)).map (doubleπ S) :=
      h.trans (Category.id_comp _)
    exact ((Category.comp_id _).symm.trans (congrArg (fun x ↦ _ ≫ x)
      (Iso.hom_inv_id_triangle_hom₃ E₀).symm)).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ E₀.inv.hom₃) hk))
  have hh' : (HomotopyCategory.Bounded.ι C).map h' = E₀.hom.hom₃ ≫
      (_root_.HomotopyCategory.quotient C (.up ℤ)).map
        (CochainComplex.homOfDegreewiseSplit _ (topSplitting S)) ≫
      ((_root_.HomotopyCategory.quotient C (.up ℤ)).commShiftIso (1 : ℤ)).hom.app _ ≫
      ((HomotopyCategory.Bounded.ι C).commShiftIso (1 : ℤ)).inv.app (bSingle 1 S.X₃) := by
    have h := E₀.hom.comm₃
    rw [hE₀₁] at h
    have hk : (HomotopyCategory.Bounded.ι C).map h' ≫
        ((HomotopyCategory.Bounded.ι C).commShiftIso (1 : ℤ)).hom.app (bSingle 1 S.X₃) =
          E₀.hom.hom₃ ≫ (_root_.HomotopyCategory.quotient C (.up ℤ)).map
            (CochainComplex.homOfDegreewiseSplit _ (topSplitting S)) ≫
          ((_root_.HomotopyCategory.quotient C (.up ℤ)).commShiftIso (1 : ℤ)).hom.app _ :=
      (Category.comp_id _).symm.trans ((congrArg (fun x ↦ _ ≫ x)
        (CategoryTheory.Functor.map_id (shiftFunctor (_root_.HomotopyCategory C (.up ℤ)) (1 : ℤ))
          ((HomotopyCategory.Bounded.ι C).obj (bSingle 1 S.X₃))).symm).trans
            h)
    rw [← cancel_mono (((HomotopyCategory.Bounded.ι C).commShiftIso (1 : ℤ)).hom.app _), hk]
    simp
  have h₁ : (mkMap ((HomologicalComplex.single C (.up ℤ) 0).map S.f) :
      bSingle 0 S.X₁ ⟶ bSingle 0 S.X₂) ≫ E₃.inv = mkMap (doubleι S) ≫ g' := by
    apply (HomotopyCategory.Bounded.ι C).map_injective
    rw [Functor.map_comp, Functor.map_comp, hE₃, hg', ← doubleι_doubleπ]
    simp only [ObjectProperty.ι_map, ObjectProperty.homMk_hom, Functor.map_comp]
    exact Category.assoc _ _ _
  have hψ : (HomotopyCategory.Bounded.ι C).map (shiftSingleIso S.X₃).hom =
      (_root_.HomotopyCategory.quotient C (.up ℤ)).map
        (((CochainComplex.singleFunctors C).shiftIso 1 0 1 (by simp)).app S.X₃).inv ≫
      ((_root_.HomotopyCategory.quotient C (.up ℤ)).commShiftIso (1 : ℤ)).hom.app _ ≫
      ((HomotopyCategory.Bounded.ι C).commShiftIso (1 : ℤ)).inv.app (bSingle 1 S.X₃) :=
    (HomotopyCategory.Bounded.fullyFaithfulι C).map_preimage _
  have hs : (_root_.HomotopyCategory.quotient C (.up ℤ)).map
      (CochainComplex.homOfDegreewiseSplit _ (topSplitting S)) =
        (_root_.HomotopyCategory.quotient C (.up ℤ)).map
          ((HomologicalComplex.single C (.up ℤ) 0).map S.g) ≫
        (_root_.HomotopyCategory.quotient C (.up ℤ)).map
          (((CochainComplex.singleFunctors C).shiftIso 1 0 1 (by simp)).app S.X₃).inv := by
    rw [← Functor.map_comp, ← homOfDegreewiseSplit_comp_shiftIso S, Category.assoc]
    simp
  have h₂ : (mkMap ((HomologicalComplex.single C (.up ℤ) 0).map S.g) :
      bSingle 0 S.X₂ ⟶ bSingle 0 S.X₃) ≫ (shiftSingleIso S.X₃).hom = E₃.inv ≫ h' := by
    apply (HomotopyCategory.Bounded.ι C).map_injective
    rw [Functor.map_comp, Functor.map_comp, hE₃, hh', hψ]
    refine Eq.trans ?_ (Iso.inv_hom_id_triangle_hom₃_assoc E₀ _).symm
    refine Eq.trans ?_ (congrArg (· ≫ _) hs).symm
    exact (Category.assoc _ _ _).symm
  refine isomorphic_distinguished _ (rot_of_distTriang _
    ((BoundedDerivedCategory.Q E).map_distinguished _ hT')) _ (Triangle.isoMk _ _
      (doubleιIso hS) ((BoundedDerivedCategory.Q E).mapIso E₃.symm) (shiftSingleIsoQ S.X₃)
      ?_ ?_ ?_)
  · change (BoundedDerivedCategory.Q E).map _ ≫ (BoundedDerivedCategory.Q E).map E₃.inv =
      (BoundedDerivedCategory.Q E).map (mkMap (doubleι S)) ≫ (BoundedDerivedCategory.Q E).map g'
    rw [← Functor.map_comp, ← Functor.map_comp, h₁]
  · change (BoundedDerivedCategory.Q E).map _ ≫ (BoundedDerivedCategory.Q E).map
        (shiftSingleIso S.X₃).hom ≫ ((BoundedDerivedCategory.Q E).commShiftIso (1 : ℤ)).hom.app _ =
      (BoundedDerivedCategory.Q E).map E₃.inv ≫ (BoundedDerivedCategory.Q E).map h' ≫
        ((BoundedDerivedCategory.Q E).commShiftIso (1 : ℤ)).hom.app _
    rw [← Functor.map_comp_assoc, h₂, Functor.map_comp_assoc]
  · change (_ ≫ _ ≫ (doubleιIso hS).inv⟦(1 : ℤ)⟧') ≫ (doubleιIso hS).hom⟦(1 : ℤ)⟧' = _
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id_map, Category.comp_id]
    rfl

/-! ### Naturality -/

variable {S' : ShortComplex C} (φ : S ⟶ S')

/-- The map of two-term complexes induced by a morphism of short complexes. -/
noncomputable def doubleMap : double S ⟶ double S' :=
  HomologicalComplex.mkHomFromDouble rel₀₁ (by simp)
    (φ.τ₂ ≫ (HomologicalComplex.doubleXIso₀ S'.g rel₀₁).inv)
    (φ.τ₃ ≫ (HomologicalComplex.doubleXIso₁ S'.g rel₀₁ (by simp)).inv)
    (by rw [HomologicalComplex.double_d S'.g rel₀₁ (by simp)]; simp [φ.comm₂₃])
    (by
      rintro k (hk : 1 + 1 = k)
      exact (isZero_double_X S' (by lia) (by lia)).eq_of_tgt _ _)

omit [HasBinaryBiproducts C] in
theorem doubleι_doubleMap :
    doubleι S ≫ doubleMap φ = (HomologicalComplex.single C (.up ℤ) 0).map φ.τ₁ ≫ doubleι S' := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, doubleι_f_zero, doubleι_f_zero,
    HomologicalComplex.single_map_f_self, doubleMap, HomologicalComplex.mkHomFromDouble_f₀]
  simp [reassoc_of% φ.comm₁₂]

omit [HasBinaryBiproducts C] in
theorem doubleTopι_doubleMap : doubleTopι S ≫ doubleMap φ =
    (HomologicalComplex.single C (.up ℤ) 1).map φ.τ₃ ≫ doubleTopι S' := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, doubleTopι_f_one, doubleTopι_f_one,
    HomologicalComplex.single_map_f_self, doubleMap, HomologicalComplex.mkHomFromDouble_f₁]
  simp

omit [HasBinaryBiproducts C] in
private theorem shiftSingleIso_hom_naturality {A B : C} (a : A ⟶ B) :
    (mkMap ((HomologicalComplex.single C (.up ℤ) 0).map a) : bSingle 0 A ⟶ bSingle 0 B) ≫
      (shiftSingleIso B).hom = (shiftSingleIso A).hom ≫
        (mkMap ((HomologicalComplex.single C (.up ℤ) 1).map a) :
          bSingle 1 A ⟶ bSingle 1 B)⟦(1 : ℤ)⟧' := by
  apply (HomotopyCategory.Bounded.ι C).map_injective
  have hψ (X : C) : (HomotopyCategory.Bounded.ι C).map (shiftSingleIso X).hom =
      (_root_.HomotopyCategory.quotient C (.up ℤ)).map
        (((CochainComplex.singleFunctors C).shiftIso 1 0 1 (by simp)).app X).inv ≫
      ((_root_.HomotopyCategory.quotient C (.up ℤ)).commShiftIso (1 : ℤ)).hom.app _ ≫
      ((HomotopyCategory.Bounded.ι C).commShiftIso (1 : ℤ)).inv.app (bSingle 1 X) :=
    (HomotopyCategory.Bounded.fullyFaithfulι C).map_preimage _
  rw [Functor.map_comp, Functor.map_comp, hψ, hψ]
  simp only [Category.assoc]
  rw [← Functor.commShiftIso_inv_naturality]
  simp only [ObjectProperty.ι_map, ObjectProperty.homMk_hom]
  rw [← Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc]
  congr 2
  exact (((CochainComplex.singleFunctors C).shiftIso 1 0 1 (by simp)).inv.naturality a)

private theorem shiftSingleIsoQ_hom_naturality {A B : C} (a : A ⟶ B) :
    (BoundedDerivedCategory.Q E).map
      (mkMap ((HomologicalComplex.single C (.up ℤ) 0).map a) : bSingle 0 A ⟶ bSingle 0 B) ≫
      (shiftSingleIsoQ B).hom = (shiftSingleIsoQ A).hom ≫
        ((BoundedDerivedCategory.Q E).map (mkMap ((HomologicalComplex.single C (.up ℤ) 1).map a) :
          bSingle 1 A ⟶ bSingle 1 B))⟦(1 : ℤ)⟧' := by
  simp only [shiftSingleIsoQ, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [← Functor.map_comp_assoc, shiftSingleIso_hom_naturality, Functor.map_comp_assoc,
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
  let Dφ : bDouble S ⟶ bDouble S' := mkMap (doubleMap φ)
  have k₁ : (doubleιIso hS).inv ≫ (BoundedDerivedCategory.Q E).map
      (mkMap ((HomologicalComplex.single C (.up ℤ) 0).map φ.τ₁) :
        bSingle 0 S.X₁ ⟶ bSingle 0 S'.X₁) =
      (BoundedDerivedCategory.Q E).map Dφ ≫ (doubleιIso hS').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    change (BoundedDerivedCategory.Q E).map _ ≫ (BoundedDerivedCategory.Q E).map _ =
      (BoundedDerivedCategory.Q E).map _ ≫ (BoundedDerivedCategory.Q E).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    apply ObjectProperty.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      ← Functor.map_comp]
    rw [← doubleι_doubleMap, Functor.map_comp]
    rfl
  have k₂ : (BoundedDerivedCategory.Q E).map
      (mkMap (doubleTopι S) : bSingle 1 S.X₃ ⟶ bDouble S) ≫
        (BoundedDerivedCategory.Q E).map Dφ =
      (BoundedDerivedCategory.Q E).map
        (mkMap ((HomologicalComplex.single C (.up ℤ) 1).map φ.τ₃) :
          bSingle 1 S.X₃ ⟶ bSingle 1 S'.X₃) ≫ (BoundedDerivedCategory.Q E).map
            (mkMap (doubleTopι S') : bSingle 1 S'.X₃ ⟶ bDouble S') := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    apply ObjectProperty.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      ← Functor.map_comp]
    rw [← doubleTopι_doubleMap, Functor.map_comp]
    rfl
  have k₃ : (-(((BoundedDerivedCategory.Q E).map
      (mkMap (doubleTopι S) : bSingle 1 S.X₃ ⟶ bDouble S))⟦(1 : ℤ)⟧')) ≫
        ((BoundedDerivedCategory.Q E).map Dφ)⟦(1 : ℤ)⟧' =
      ((BoundedDerivedCategory.Q E).map
        (mkMap ((HomologicalComplex.single C (.up ℤ) 1).map φ.τ₃) :
          bSingle 1 S.X₃ ⟶ bSingle 1 S'.X₃))⟦(1 : ℤ)⟧' ≫ (-(((BoundedDerivedCategory.Q E).map
            (mkMap (doubleTopι S') : bSingle 1 S'.X₃ ⟶ bDouble S'))⟦(1 : ℤ)⟧')) := by
    rw [Preadditive.neg_comp, Preadditive.comp_neg,
      ← Functor.map_comp (shiftFunctor E.BoundedDerivedCategory (1 : ℤ)), k₂, Functor.map_comp]
  simp only [δ', Category.assoc]
  rw [← Functor.map_comp, k₁, Functor.map_comp, reassoc_of% k₃,
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
        (conflationδ hS) ∈ distTriang _ := by
  refine isomorphic_distinguished _ (distinguished' hS) _ (Triangle.isoMk _ _
    ((Q E).mapIso (singleIso _)) ((Q E).mapIso (singleIso _)) ((Q E).mapIso (singleIso _))
      (Q_map_singleIso_hom_naturality S.f) (Q_map_singleIso_hom_naturality S.g) ?_)
  change ((Q E).map (singleIso S.X₃).hom ≫ δ' hS ≫
    ((Q E).mapIso (singleIso S.X₁)).inv⟦(1 : ℤ)⟧') ≫
      ((Q E).mapIso (singleIso S.X₁)).hom⟦(1 : ℤ)⟧' = _
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_map, Category.comp_id]
  rfl

/-- **The connecting morphism of a conflation is natural** in morphisms of conflations. -/
theorem conflationδ_naturality (φ : S ⟶ S') (hS : E.Conflation S) (hS' : E.Conflation S') :
    conflationδ hS ≫ ((Q E).map ((HomotopyCategory.Bounded.singleFunctor C 0).map φ.τ₁))⟦(1 : ℤ)⟧' =
      (Q E).map ((HomotopyCategory.Bounded.singleFunctor C 0).map φ.τ₃) ≫ conflationδ hS' := by
  have h₁ : ((Q E).map (singleIso S.X₁).inv)⟦(1 : ℤ)⟧' ≫
      ((Q E).map ((HomotopyCategory.Bounded.singleFunctor C 0).map φ.τ₁))⟦(1 : ℤ)⟧' =
        ((Q E).map (mkMap ((HomologicalComplex.single C (.up ℤ) 0).map φ.τ₁) :
          bSingle 0 S.X₁ ⟶ bSingle 0 S'.X₁))⟦(1 : ℤ)⟧' ≫
            ((Q E).map (singleIso S'.X₁).inv)⟦(1 : ℤ)⟧' := by
    have k : (Q E).map (singleIso S.X₁).inv ≫
        (Q E).map ((HomotopyCategory.Bounded.singleFunctor C 0).map φ.τ₁) =
          (Q E).map (mkMap ((HomologicalComplex.single C (.up ℤ) 0).map φ.τ₁) :
            bSingle 0 S.X₁ ⟶ bSingle 0 S'.X₁) ≫ (Q E).map (singleIso S'.X₁).inv := by
      change ((Q E).mapIso (singleIso S.X₁)).inv ≫ _ = _ ≫ ((Q E).mapIso (singleIso S'.X₁)).inv
      rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
      exact Q_map_singleIso_hom_naturality φ.τ₁
    rw [← Functor.map_comp (shiftFunctor E.BoundedDerivedCategory (1 : ℤ)),
      ← Functor.map_comp (shiftFunctor E.BoundedDerivedCategory (1 : ℤ)), k]
  simp only [conflationδ, Category.assoc]
  rw [h₁, reassoc_of% (δ'_naturality hS hS'), reassoc_of% (Q_map_singleIso_hom_naturality φ.τ₃)]

end BoundedDerivedCategory

end TauCeti.ExactStructure
