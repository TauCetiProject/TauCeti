/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Buchweitz
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Equivalence
public import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.CategoryTheory.Exact.Stable.Functor.NatTrans
import TauCeti.CategoryTheory.Shift.CommShift

/-!
# Eisenbud's cokernel equivalence for maximal Cohen–Macaulay modules

For a nonzero element `w` in a regular local ring `S` with local quotient `R = S ⧸ (w)`,
reducing matrix factorizations modulo `w` and taking `coker d₀'` gives an essentially surjective
exact functor `quotientMaximalCohenMacaulayCokernel` into `MaximalCohenMacaulayModuleCat R`
(`TauCeti.MatrixFactorization.quotientMaximalCohenMacaulayCokernel`), descending to a
triangulated equivalence `HMF(S, w) ≌ stable(MCM-R)`
(`quotientMaximalCohenMacaulayStableCokernelEquivalence_isTriangulated`).

This combines `TauCeti.MatrixFactorization.Cokernel.Equivalence` with Buchweitz's hypersurface
comparison `TauCeti.MatrixFactorization.Cokernel.Buchweitz`.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Sections 5–6 and Corollary 6.3.
* R.-O. Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, AMS (2021), Section 4,
  Lemma 4.2.2.
* W. Bruns and J. Herzog, *Cohen–Macaulay Rings*, Section 3.3.
-/

public section

noncomputable section

universe u

open CategoryTheory

namespace TauCeti

namespace MatrixFactorization

variable {S : Type u} [CommRing S] [IsRegularLocalRing S] {w : S}
  [IsLocalRing (S ⧸ Ideal.span {w})]

/-- Over `S ⧸ (w)` (`w ≠ 0`), reduced cokernels of matrix factorizations of `w` are finite MCM. -/
theorem isFiniteMaximalCohenMacaulay_cokernelFunctor_obj_baseChangeFunctor_obj (hw : w ≠ 0)
    (X : MatrixFactorization S w) :
    IsFiniteMaximalCohenMacaulay.{u} (S ⧸ Ideal.span {w})
      (cokernelFunctor.obj
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj :=
  have := TauCeti.IsRegularLocalRing.isDomain (R := S)
  (isGorensteinProjective_quotient_iff_isFiniteMaximalCohenMacaulay hw _).1
    (isGorensteinProjective_cokernelFunctor_obj_baseChangeFunctor_obj
      (mem_nonZeroDivisors_of_ne_zero hw) X)

/-- **Eisenbud's cokernel functor** into `MaximalCohenMacaulayModuleCat (S ⧸ (w))`. -/
def quotientMaximalCohenMacaulayCokernel (hw : w ≠ 0) :
    MatrixFactorization S w ⥤ MaximalCohenMacaulayModuleCat.{u} (S ⧸ Ideal.span {w}) :=
  ObjectProperty.lift _ (baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w})) ⋙
      cokernelFunctor ⋙ forget₂ (FGModuleCat.{u} (S ⧸ Ideal.span {w})) (ModuleCat.{u} _))
    (isFiniteMaximalCohenMacaulay_cokernelFunctor_obj_baseChangeFunctor_obj hw)

/-- The underlying module of `quotientMaximalCohenMacaulayCokernel` is the reduced cokernel. -/
@[simp]
theorem quotientMaximalCohenMacaulayCokernel_obj_obj (hw : w ≠ 0) (X : MatrixFactorization S w) :
    ((quotientMaximalCohenMacaulayCokernel hw).obj X).obj =
      (cokernelFunctor.obj ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj :=
  (rfl)

/-- Composed with subcategory inclusion, `quotientMaximalCohenMacaulayCokernel` is `coker d₀'`. -/
theorem quotientMaximalCohenMacaulayCokernel_comp_ι (hw : w ≠ 0) :
    quotientMaximalCohenMacaulayCokernel hw ⋙ (IsFiniteMaximalCohenMacaulay.{u} _).ι =
      baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w})) ⋙ cokernelFunctor ⋙
        forget₂ (FGModuleCat.{u} (S ⧸ Ideal.span {w})) (ModuleCat.{u} _) := (rfl)

instance (hw : w ≠ 0) : (quotientMaximalCohenMacaulayCokernel hw).Additive := by
  unfold quotientMaximalCohenMacaulayCokernel; infer_instance

/-- Compatibility isomorphism with `quotientGorensteinProjectiveCokernel` (forward). -/
def quotientMaximalCohenMacaulayCokernelCompGorensteinProjectiveIso (hw : w ≠ 0) :
    quotientMaximalCohenMacaulayCokernel hw ⋙
        (MaximalCohenMacaulayModuleCat.gorensteinProjectiveEquivalence hw).functor ≅
      have := TauCeti.IsRegularLocalRing.isDomain (R := S)
      quotientGorensteinProjectiveCokernel (mem_nonZeroDivisors_of_ne_zero hw) :=
  have := TauCeti.IsRegularLocalRing.isDomain (R := S)
  ((IsGorensteinProjective (S ⧸ Ideal.span {w})).fullyFaithfulι.whiskeringRight _).preimageIso <|
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (eqToIso
      (MaximalCohenMacaulayModuleCat.gorensteinProjectiveEquivalence_functor_comp_ι hw)) ≪≫
    eqToIso ((quotientMaximalCohenMacaulayCokernel_comp_ι hw).trans
      (quotientGorensteinProjectiveCokernel_comp_ι (mem_nonZeroDivisors_of_ne_zero hw)).symm)

/-- Compatibility isomorphism with `quotientGorensteinProjectiveCokernel` (inverse). -/
def quotientGorensteinProjectiveCokernelCompInverseIso (hw : w ≠ 0) :
    have := TauCeti.IsRegularLocalRing.isDomain (R := S)
    quotientGorensteinProjectiveCokernel (mem_nonZeroDivisors_of_ne_zero hw) ⋙
        (MaximalCohenMacaulayModuleCat.gorensteinProjectiveEquivalence hw).inverse ≅
      quotientMaximalCohenMacaulayCokernel hw :=
  have := TauCeti.IsRegularLocalRing.isDomain (R := S)
  ((IsFiniteMaximalCohenMacaulay.{u} _).fullyFaithfulι.whiskeringRight _).preimageIso <|
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (eqToIso
      (MaximalCohenMacaulayModuleCat.gorensteinProjectiveEquivalence_inverse_comp_ι hw)) ≪≫
    eqToIso ((quotientGorensteinProjectiveCokernel_comp_ι (mem_nonZeroDivisors_of_ne_zero hw)).trans
      (quotientMaximalCohenMacaulayCokernel_comp_ι hw).symm)

/-- `quotientMaximalCohenMacaulayCokernel` preserves conflations and projective-injectives. -/
theorem stableConflationExact_quotientMaximalCohenMacaulayCokernel (hw : w ≠ 0) :
    StableConflationExact (splitExact S w)
      (MaximalCohenMacaulayModuleCat.exactStructure.{u} (S ⧸ Ideal.span {w}))
      (quotientMaximalCohenMacaulayCokernel hw) :=
  have := TauCeti.IsRegularLocalRing.isDomain (R := S)
  ((stableConflationExact_quotientGorensteinProjectiveCokernel
    (mem_nonZeroDivisors_of_ne_zero hw)).comp
    (MaximalCohenMacaulayModuleCat.stableConflationExact_gorensteinProjectiveEquivalence_inverse
      hw)).of_iso (quotientGorensteinProjectiveCokernelCompInverseIso hw)

/-- **Essential surjectivity before stabilization.** -/
theorem quotientMaximalCohenMacaulayCokernel_essSurj (hw : w ≠ 0) :
    (quotientMaximalCohenMacaulayCokernel hw).EssSurj := by
  have := TauCeti.IsRegularLocalRing.isDomain (R := S)
  have := quotientGorensteinProjectiveCokernel_essSurj (mem_nonZeroDivisors_of_ne_zero hw)
    (IsLocalRing.maximalIdeal S).spanFinrank (IsRegularLocalRing.hasProjectiveDimensionLE
      (_root_.IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)).ge)
  exact Functor.essSurj_of_iso (quotientGorensteinProjectiveCokernelCompInverseIso hw)

/-- Null-homotopic morphisms map into the projective stable ideal of MCM modules. -/
theorem quotientMaximalCohenMacaulayCokernel_map_mem_projectiveStableIdeal (hw : w ≠ 0)
    {X Y : MatrixFactorization S w} {g : X ⟶ Y}
    (hg : g ∈ (nullHomotopic (S := S) (w := w)).hom X Y) :
    (quotientMaximalCohenMacaulayCokernel hw).map g ∈
      (MaximalCohenMacaulayModuleCat.exactStructure
        (S ⧸ Ideal.span {w})).projectiveStableIdeal.hom _ _ := by
  have := TauCeti.IsRegularLocalRing.isDomain (R := S)
  rw [← MorphismIdeal.mem_comap_hom, ← MorphismIdeal.comap_eq_of_iso
    (MaximalCohenMacaulayModuleCat.exactStructure (S ⧸ Ideal.span {w})).projectiveStableIdeal
    (quotientGorensteinProjectiveCokernelCompInverseIso hw), MorphismIdeal.comap_comp,
    MorphismIdeal.mem_comap_hom]
  exact (MaximalCohenMacaulayModuleCat.stableConflationExact_gorensteinProjectiveEquivalence_inverse
    hw).projectiveStableIdeal_le_comap GorensteinProjectiveModuleCat.exactStructure_isFrobenius
    _ _ (quotientGorensteinProjectiveCokernel_map_mem_projectiveStableIdeal
      (mem_nonZeroDivisors_of_ne_zero hw) hg)

namespace HomotopyCategory

/-- **Eisenbud's stable cokernel functor** `HMF(S, w) ⥤ stable(MCM-(S ⧸ (w)))`. -/
def quotientMaximalCohenMacaulayStableCokernel (hw : w ≠ 0) :
    HomotopyCategory (S := S) (w := w) ⥤
      (MaximalCohenMacaulayModuleCat.exactStructure.{u}
        (S ⧸ Ideal.span {w})).ProjectiveStableCategory :=
  (nullHomotopic (S := S) (w := w)).lift
    (quotientMaximalCohenMacaulayCokernel hw ⋙
      (MaximalCohenMacaulayModuleCat.exactStructure (S ⧸ Ideal.span {w})).projectiveStableFunctor)
    fun _ _ _ hg ↦ by
      rw [Functor.mem_kerIdeal_hom, Functor.comp_map, MorphismIdeal.quotientFunctor_map_eq_zero_iff]
      exact quotientMaximalCohenMacaulayCokernel_map_mem_projectiveStableIdeal hw hg

instance (hw : w ≠ 0) : (quotientMaximalCohenMacaulayStableCokernel hw).Additive := by
  unfold quotientMaximalCohenMacaulayStableCokernel; infer_instance

/-- `quotientMaximalCohenMacaulayStableCokernel` descends `quotientMaximalCohenMacaulayCokernel`. -/
theorem quotientFunctor_comp_quotientMaximalCohenMacaulayStableCokernel (hw : w ≠ 0) :
    (nullHomotopic (S := S) (w := w)).quotientFunctor ⋙
        quotientMaximalCohenMacaulayStableCokernel hw =
      quotientMaximalCohenMacaulayCokernel hw ⋙
        (MaximalCohenMacaulayModuleCat.exactStructure
          (S ⧸ Ideal.span {w})).projectiveStableFunctor := by
  unfold quotientMaximalCohenMacaulayStableCokernel; exact CategoryTheory.Quotient.lift_spec _ _ _

/-- Compatibility isomorphism between the MCM and Gorenstein-projective stable cokernels. -/
def quotientMaximalCohenMacaulayStableCokernelCompGorensteinProjectiveStableIso (hw : w ≠ 0) :
    quotientMaximalCohenMacaulayStableCokernel hw ⋙
        (MaximalCohenMacaulayModuleCat.gorensteinProjectiveStableEquivalence hw).functor ≅
      have := TauCeti.IsRegularLocalRing.isDomain (R := S)
      quotientGorensteinProjectiveStableCokernel (mem_nonZeroDivisors_of_ne_zero hw) :=
  have := TauCeti.IsRegularLocalRing.isDomain (R := S)
  CategoryTheory.Quotient.natIsoLift (nullHomotopic (S := S) (w := w)).rel <|
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
      (eqToIso (quotientFunctor_comp_quotientMaximalCohenMacaulayStableCokernel hw)) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (eqToIso (by
      rw [MaximalCohenMacaulayModuleCat.gorensteinProjectiveStableEquivalence_functor,
        StableConflationExact.stableFunctor_eq_map, MorphismIdeal.quotientFunctor_comp_map])) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
      (quotientMaximalCohenMacaulayCokernelCompGorensteinProjectiveIso hw) _ ≪≫
    eqToIso (quotientFunctor_comp_quotientGorensteinProjectiveStableCokernel
      (mem_nonZeroDivisors_of_ne_zero hw)).symm

/-- Along `stableToHomotopy`, `quotientMaximalCohenMacaulayStableCokernel` is `stableFunctor`. -/
theorem stableToHomotopy_comp_quotientMaximalCohenMacaulayStableCokernel (hw : w ≠ 0) :
    stableToHomotopy S w ⋙ quotientMaximalCohenMacaulayStableCokernel hw =
      (stableConflationExact_quotientMaximalCohenMacaulayCokernel hw).stableFunctor
        (splitExact_isFrobenius S w) := by
  apply CategoryTheory.Quotient.lift_unique' (splitExact S w).projectiveStableIdeal.rel
  rw [StableConflationExact.stableFunctor_eq_map, MorphismIdeal.quotientFunctor_comp_map,
    ← Functor.assoc, projectiveStableFunctor_comp_stableToHomotopy,
    quotientFunctor_comp_quotientMaximalCohenMacaulayStableCokernel]

/-- Identifies `quotientMaximalCohenMacaulayStableCokernel` via `stableToHomotopy⁻¹`. -/
def stableToHomotopyInverseCompMaximalCohenMacaulayStableFunctorIso (hw : w ≠ 0) :
    (stableToHomotopy S w).asEquivalence.inverse ⋙
        (stableConflationExact_quotientMaximalCohenMacaulayCokernel hw).stableFunctor
          (splitExact_isFrobenius S w) ≅
      quotientMaximalCohenMacaulayStableCokernel hw :=
  Iso.inverseCompIso
    (eqToIso (stableToHomotopy_comp_quotientMaximalCohenMacaulayStableCokernel hw).symm)

/-- Shift compatibility of `quotientMaximalCohenMacaulayStableCokernel`. -/
@[instance_reducible]
def quotientMaximalCohenMacaulayStableCokernelCommShift (hw : w ≠ 0) :
    letI := (MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius hw).stableHasShift
    (quotientMaximalCohenMacaulayStableCokernel hw).CommShift ℤ :=
  have hE := splitExact_isFrobenius S w
  have hE' := MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius hw
  letI := hE.stableHasShift; letI := hE'.stableHasShift
  letI : (stableToHomotopy S w).asEquivalence.functor.CommShift ℤ := stableToHomotopyCommShift S w
  letI := (stableToHomotopy S w).asEquivalence.commShiftInverse ℤ
  letI := (stableConflationExact_quotientMaximalCohenMacaulayCokernel hw).stableFunctorCommShift
    hE hE'
  Functor.CommShift.ofIso (stableToHomotopyInverseCompMaximalCohenMacaulayStableFunctorIso hw) ℤ

/-- The shift compatibility of `quotientMaximalCohenMacaulayStableCokernel` is the one making
`stableToHomotopyInverseCompMaximalCohenMacaulayStableFunctorIso` commute with integral shifts. -/
theorem stableToHomotopyInverseCompMaximalCohenMacaulayStableFunctorIso_commShift (hw : w ≠ 0) :
    letI := (splitExact_isFrobenius S w).stableHasShift
    letI := (MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius hw).stableHasShift
    letI : (stableToHomotopy S w).asEquivalence.functor.CommShift ℤ := stableToHomotopyCommShift S w
    letI := (stableToHomotopy S w).asEquivalence.commShiftInverse ℤ
    letI := (stableConflationExact_quotientMaximalCohenMacaulayCokernel hw).stableFunctorCommShift
      (splitExact_isFrobenius S w) (MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius hw)
    letI := quotientMaximalCohenMacaulayStableCokernelCommShift hw
    NatTrans.CommShift
      (stableToHomotopyInverseCompMaximalCohenMacaulayStableFunctorIso hw).hom ℤ := by
  let := (splitExact_isFrobenius S w).stableHasShift
  let := (MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius hw).stableHasShift
  let : (stableToHomotopy S w).asEquivalence.functor.CommShift ℤ := stableToHomotopyCommShift S w
  let := (stableToHomotopy S w).asEquivalence.commShiftInverse ℤ
  let := (stableConflationExact_quotientMaximalCohenMacaulayCokernel hw).stableFunctorCommShift
    (splitExact_isFrobenius S w) (MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius hw)
  exact Functor.CommShift.ofIso_compatibility _ ℤ

private theorem eqToIso_stableFunctor_comp_commShift
    {C D K : Type*} [Category* C] [Preadditive C] [Limits.HasZeroObject C]
    [Limits.HasBinaryBiproducts C] [Category* D] [Preadditive D] [Limits.HasZeroObject D]
    [Limits.HasBinaryBiproducts D] [Category* K] [Preadditive K] [Limits.HasZeroObject K]
    [Limits.HasBinaryBiproducts K]
    {E : ExactStructure C} {E' : ExactStructure D} {E'' : ExactStructure K}
    {F : C ⥤ D} {G : D ⥤ K} [F.Additive] [G.Additive]
    (hF : StableConflationExact E E' F) (hG : StableConflationExact E' E'' G)
    (hE : E.IsFrobenius) (hE' : E'.IsFrobenius) (hE'' : E''.IsFrobenius) :
    letI := hE.stableHasShift; letI := hE'.stableHasShift; letI := hE''.stableHasShift
    letI := hF.stableFunctorCommShift hE hE'
    letI := hG.stableFunctorCommShift hE' hE''
    letI := (hF.comp hG).stableFunctorCommShift hE hE''
    NatTrans.CommShift (eqToIso (hF.stableFunctor_comp hG hE hE')).hom ℤ := by
  let := hE.stableHasShift; let := hE'.stableHasShift; let := hE''.stableHasShift
  let := hF.stableFunctorCommShift hE hE'
  let := hG.stableFunctorCommShift hE' hE''
  let := (hF.comp hG).stableFunctorCommShift hE hE''
  refine TauCeti.natTrans_commShift_iff_one.mpr ⟨?_⟩
  apply CategoryTheory.Quotient.natTrans_ext
  ext X
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj, Iso.trans_hom, eqToIso.hom]
  rw [Functor.commShiftIso_comp_hom_app,
    StableConflationExact.stableFunctorCommShift_iso_one (hF.comp hG) hE hE'',
    StableConflationExact.stableFunctorCommShift_iso_one hF hE hE',
    StableConflationExact.stableFunctorCommShift_iso_one hG hE' hE'']
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp,
    Category.assoc]
  have hnat := (eqToHom (hF.stableFunctor_comp hG hE hE')).naturality
    (hE.stableShiftFunctorOneIso.hom.app ((Quotient.functor _).obj X))
  dsimp only [Functor.comp_obj, Functor.comp_map] at hnat
  rw [← hE''.stableShiftFunctorOneIso.inv.naturality
      ((eqToHom (hF.stableFunctor_comp hG hE hE')).app ((Quotient.functor _).obj X)),
    ← reassoc_of% hnat]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  have hcanc :
      (hG.stableFunctor hE').map
          (hE'.stableShiftFunctorOneIso.inv.app
            ((hF.stableFunctor hE).obj ((Quotient.functor _).obj X))) ≫
        (hG.stableFunctor hE').map
          (hE'.stableShiftFunctorOneIso.hom.app
            ((hF.stableFunctor hE).obj ((Quotient.functor _).obj X))) =
        𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rw [reassoc_of% hcanc]
  congr 1
  simp only [← Category.assoc]
  congr 1
  simp only [eqToHom_app, eqToHom_map, Category.assoc]
  have hIsoG :
      (hG.stableSuspensionCompStableFunctorIso hE' hE'').hom.app
          ((hF.stableFunctor hE).obj ((Quotient.functor E.projectiveStableIdeal.rel).obj X)) =
        eqToHom (congrArg (hG.stableFunctor hE').obj (congrArg hE'.stableSuspension.obj
          (hF.stableFunctor_obj_projectiveStableFunctor_obj hE X))) ≫
          (hG.stableSuspensionCompStableFunctorIso hE' hE'').hom.app
            (E'.projectiveStableFunctor.obj (F.obj X)) ≫
          eqToHom (congrArg hE''.stableSuspension.obj (congrArg (hG.stableFunctor hE').obj
            (hF.stableFunctor_obj_projectiveStableFunctor_obj hE X).symm)) := by
    have hn := (hG.stableSuspensionCompStableFunctorIso hE' hE'').hom.naturality
      (eqToHom (hF.stableFunctor_obj_projectiveStableFunctor_obj hE X))
    dsimp only [Functor.comp_obj, Functor.comp_map] at hn
    simp only [eqToHom_map] at hn
    rw [← cancel_mono (eqToHom (congrArg hE''.stableSuspension.obj
      (congrArg (hG.stableFunctor hE').obj
        (hF.stableFunctor_obj_projectiveStableFunctor_obj hE X)))),
      Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    exact hn.symm
  rw [(hF.comp hG).stableSuspensionCompStableFunctorIso_hom_app hE hE'' X,
    hF.stableSuspensionCompStableFunctorIso_hom_app hE hE' X,
    hIsoG, hG.stableSuspensionCompStableFunctorIso_hom_app hE' hE'' (F.obj X)]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc]
  let P₁ := hF.mapSuspensionPresentation hE X
  let Q₁ := hE'.suspensionPresentation (F.obj X)
  let P₂ := hG.mapSuspensionPresentation hE' (F.obj X)
  let Q₂ := hE''.suspensionPresentation (G.obj (F.obj X))
  let P₁₂ := (hF.comp hG).mapSuspensionPresentation hE X
  have hp1K : P₁₂.K = G.obj P₁.K :=
    ((hF.comp hG).mapSuspensionPresentation_K hE X).trans
      (congrArg G.obj (hF.mapSuspensionPresentation_K hE X).symm)
  have hp1I : P₁₂.I = G.obj P₁.I :=
    ((hF.comp hG).mapSuspensionPresentation_I hE X).trans
      (congrArg G.obj (hF.mapSuspensionPresentation_I hE X).symm)
  have hp2K : P₂.K = G.obj Q₁.K := hG.mapSuspensionPresentation_K hE' (F.obj X)
  have hp2I : P₂.I = G.obj Q₁.I := hG.mapSuspensionPresentation_I hE' (F.obj X)
  let a : P₁₂.I ⟶ Q₂.I :=
    eqToHom hp1I ≫ G.map (P₁.middleMap Q₁ (𝟙 _)) ≫ eqToHom hp2I.symm ≫ P₂.middleMap Q₂ (𝟙 _)
  let g : P₁₂.K ⟶ Q₂.K :=
    eqToHom hp1K ≫ G.map (P₁.cokernelMap Q₁ (𝟙 _)) ≫ eqToHom hp2K.symm ≫ P₂.cokernelMap Q₂ (𝟙 _)
  have ha : P₁₂.i ≫ a = 𝟙 _ ≫ Q₂.i := by
    have h₁ : G.map P₁.i ≫ G.map (P₁.middleMap Q₁ (𝟙 _)) = G.map Q₁.i := by
      rw [← G.map_comp, P₁.i_comp_middleMap, Category.id_comp]
    have hP1i := (conj_eqToHom_iff_heq _ _ rfl
      ((hF.comp hG).mapSuspensionPresentation_I hE X)).2
      ((hF.comp hG).mapSuspensionPresentation_i hE X)
    have hP1i' := (conj_eqToHom_iff_heq _ _ rfl
      (hF.mapSuspensionPresentation_I hE X)).2
      (hF.mapSuspensionPresentation_i hE X)
    have hP2i := (conj_eqToHom_iff_heq _ _ rfl hp2I).2
      (hG.mapSuspensionPresentation_i hE' (F.obj X))
    dsimp only [a, P₁₂, P₁, P₂]
    rw [Category.id_comp]
    calc
      ((hF.comp hG).mapSuspensionPresentation hE X).i ≫
          eqToHom hp1I ≫ G.map (P₁.middleMap Q₁ (𝟙 _)) ≫ eqToHom hp2I.symm ≫
            P₂.middleMap Q₂ (𝟙 _)
        = G.map (hF.mapSuspensionPresentation hE X).i ≫ G.map (P₁.middleMap Q₁ (𝟙 _)) ≫
            eqToHom hp2I.symm ≫ P₂.middleMap Q₂ (𝟙 _) := by
          simp only [hP1i, hP1i', Functor.comp_map, G.map_comp, eqToHom_map, Category.assoc,
            eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      _ = G.map Q₁.i ≫ eqToHom hp2I.symm ≫ P₂.middleMap Q₂ (𝟙 _) := by
          rw [← Category.assoc, h₁]
      _ = P₂.i ≫ P₂.middleMap Q₂ (𝟙 _) := by
          rw [hP2i]
          simp only [Category.assoc, eqToHom_refl, Category.id_comp]
          rfl
      _ = Q₂.i := by rw [P₂.i_comp_middleMap, Category.id_comp]
  have hg : P₁₂.p ≫ g = a ≫ Q₂.p := by
    have h₁ : G.map P₁.p ≫ G.map (P₁.cokernelMap Q₁ (𝟙 _)) =
        G.map (P₁.middleMap Q₁ (𝟙 _)) ≫ G.map Q₁.p := by
      rw [← G.map_comp, P₁.p_comp_cokernelMap, G.map_comp]
    have hP12p := (conj_eqToHom_iff_heq _ _
      ((hF.comp hG).mapSuspensionPresentation_I hE X)
      ((hF.comp hG).mapSuspensionPresentation_K hE X)).2
      ((hF.comp hG).mapSuspensionPresentation_p hE X)
    have hP1p := (conj_eqToHom_iff_heq _ _
      (hF.mapSuspensionPresentation_I hE X)
      (hF.mapSuspensionPresentation_K hE X)).2
      (hF.mapSuspensionPresentation_p hE X)
    have hP2p := (conj_eqToHom_iff_heq _ _ hp2I hp2K).2
      (hG.mapSuspensionPresentation_p hE' (F.obj X))
    dsimp only [a, g]
    calc
      P₁₂.p ≫
          eqToHom hp1K ≫ G.map (P₁.cokernelMap Q₁ (𝟙 _)) ≫ eqToHom hp2K.symm ≫
            P₂.cokernelMap Q₂ (𝟙 _)
        = eqToHom hp1I ≫ G.map P₁.p ≫ G.map (P₁.cokernelMap Q₁ (𝟙 _)) ≫
            eqToHom hp2K.symm ≫ P₂.cokernelMap Q₂ (𝟙 _) := by
          rw [hP12p, hP1p]
          simp only [Functor.comp_map, G.map_comp, eqToHom_map, Category.assoc,
            eqToHom_trans_assoc]
      _ = eqToHom hp1I ≫ G.map (P₁.middleMap Q₁ (𝟙 _)) ≫ G.map Q₁.p ≫
            eqToHom hp2K.symm ≫ P₂.cokernelMap Q₂ (𝟙 _) := by
          rw [reassoc_of% h₁]
      _ = eqToHom hp1I ≫ G.map (P₁.middleMap Q₁ (𝟙 _)) ≫ eqToHom hp2I.symm ≫
            P₂.p ≫ P₂.cokernelMap Q₂ (𝟙 _) := by
          rw [hP2p]
          simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
          rfl
      _ = a ≫ Q₂.p := by
          simp only [a, Category.assoc, P₂.p_comp_cokernelMap]
  have hcmp := E''.projectiveStableFunctor_map_cokernelMap_eq P₁₂ Q₂
    (hE''.isProjective_I Q₂) (𝟙 _) a g ha hg
  have hP12 := hE''.projectiveStableIsoSuspensionObj_hom P₁₂
  dsimp only [Q₂, Functor.comp_obj] at hcmp
  dsimp only [Functor.comp_obj] at hP12
  rw [← hP12] at hcmp
  simp only [g, Functor.map_comp, eqToHom_map] at hcmp
  dsimp only [Q₂] at hcmp
  rw [← hE''.projectiveStableIsoSuspensionObj_hom P₂] at hcmp
  have hgmap := hG.stableFunctor_map_projectiveStableFunctor_map hE'
    (P₁.cokernelMap Q₁ (𝟙 _))
  have hgmap' :
      E''.projectiveStableFunctor.map (G.map (P₁.cokernelMap Q₁ (𝟙 _))) =
        eqToHom (hG.stableFunctor_obj_projectiveStableFunctor_obj hE' P₁.K).symm ≫
          (hG.stableFunctor hE').map
            ((hE'.projectiveStableIsoSuspensionObj P₁).hom) ≫
          eqToHom (hG.stableFunctor_obj_projectiveStableFunctor_obj hE'
            (hE'.suspensionObj (F.obj X))) := by
    rw [hE'.projectiveStableIsoSuspensionObj_hom P₁]
    apply (cancel_epi (eqToHom
      (hG.stableFunctor_obj_projectiveStableFunctor_obj hE' P₁.K))).1
    rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp, ← hgmap]
  rw [hgmap'] at hcmp
  dsimp only [P₁₂, P₁, P₂, Q₁] at hcmp
  rw [hcmp]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

omit [IsRegularLocalRing S] [IsLocalRing (S ⧸ Ideal.span {w})] in
private theorem eqToIso_stableToHomotopy_comp_commShift
    {D : Type*} [Category* D] [HasShift D ℤ]
    {F : HomotopyCategory (S := S) (w := w) ⥤ D}
    {G : (splitExact S w).ProjectiveStableCategory ⥤ D}
    [F.CommShift ℤ] (hFG : stableToHomotopy S w ⋙ F = G)
    (hG :
      letI := (splitExact_isFrobenius S w).stableHasShift
      G.CommShift ℤ)
    (hφ :
      letI := (splitExact_isFrobenius S w).stableHasShift
      letI : (stableToHomotopy S w).asEquivalence.functor.CommShift ℤ :=
        stableToHomotopyCommShift S w
      letI := (stableToHomotopy S w).asEquivalence.commShiftInverse ℤ
      NatTrans.CommShift
        (Iso.inverseCompIso (G := (stableToHomotopy S w).asEquivalence) (eqToIso hFG.symm)).hom
        ℤ) :
    letI := (splitExact_isFrobenius S w).stableHasShift
    letI : (stableToHomotopy S w).CommShift ℤ := stableToHomotopyCommShift S w
    NatTrans.CommShift (eqToIso hFG).hom ℤ := by
  let := (splitExact_isFrobenius S w).stableHasShift
  let e := (stableToHomotopy S w).asEquivalence
  let : (stableToHomotopy S w).CommShift ℤ := stableToHomotopyCommShift S w
  let : e.functor.CommShift ℤ := stableToHomotopyCommShift S w
  let := e.commShiftInverse ℤ
  let := e.commShift_of_functor ℤ
  have := hφ
  let φ := Iso.inverseCompIso (G := (stableToHomotopy S w).asEquivalence) (eqToIso hFG.symm)
  have hsymm :
      (eqToIso hFG.symm).hom =
        G.leftUnitor.inv ≫ Functor.whiskerRight e.unitIso.hom G ≫
          (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft e.functor φ.hom := by
    ext X
    simp only [NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp,
      Iso.inverseCompIso_hom_app, φ, eqToIso.hom, Functor.comp_obj]
    have hnat := (eqToIso hFG.symm).hom.naturality (e.unitIso.hom.app X)
    dsimp only [Functor.id_obj, Functor.comp_obj, eqToIso.hom] at hnat
    rw [reassoc_of% hnat, ← Functor.map_comp]
    have htri : (stableToHomotopy S w).map (e.unitIso.hom.app X) ≫
        (stableToHomotopy S w).asEquivalence.counitIso.hom.app (e.functor.obj X) =
        𝟙 ((stableToHomotopy S w).obj X) := e.functor_unitIso_comp X
    rw [htri, CategoryTheory.Functor.map_id, Category.comp_id]
  have : NatTrans.CommShift (eqToIso hFG.symm).hom ℤ := by rw [hsymm]; infer_instance
  have : (eqToIso hFG).hom = (eqToIso hFG.symm).inv := rfl
  rw [this]
  infer_instance

/-- `quotientMaximalCohenMacaulayStableCokernelCompGorensteinProjectiveStableIso` commutes with
integral shifts. -/
theorem quotientMaximalCohenMacaulayStableCokernelCompGorensteinProjectiveStableIso_commShift
    (hw : w ≠ 0) :
    letI := (MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius hw).stableHasShift
    letI := (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
      (A := S ⧸ Ideal.span {w})).stableHasShift
    letI := quotientMaximalCohenMacaulayStableCokernelCommShift hw
    letI := MaximalCohenMacaulayModuleCat.gorensteinProjectiveStableEquivalenceFunctorCommShift hw
    letI := quotientGorensteinProjectiveStableCokernelCommShift
      (have := TauCeti.IsRegularLocalRing.isDomain (R := S); mem_nonZeroDivisors_of_ne_zero hw)
    NatTrans.CommShift
      (quotientMaximalCohenMacaulayStableCokernelCompGorensteinProjectiveStableIso hw).hom ℤ := by
  have := TauCeti.IsRegularLocalRing.isDomain (R := S)
  have hE := splitExact_isFrobenius S w
  have hE' := MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius hw
  have hE'' := GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
    (A := S ⧸ Ideal.span {w})
  let := hE.stableHasShift; let := hE'.stableHasShift; let := hE''.stableHasShift
  let e := (stableToHomotopy S w).asEquivalence
  let : (stableToHomotopy S w).CommShift ℤ := stableToHomotopyCommShift S w
  let : e.functor.CommShift ℤ := stableToHomotopyCommShift S w
  let := e.commShiftInverse ℤ; let := e.commShift_of_functor ℤ
  let h₁ := stableConflationExact_quotientMaximalCohenMacaulayCokernel hw
  let h₂ :=
    MaximalCohenMacaulayModuleCat.stableConflationExact_gorensteinProjectiveEquivalence_functor hw
  let h₃ := stableConflationExact_quotientGorensteinProjectiveCokernel
    (mem_nonZeroDivisors_of_ne_zero hw)
  let := h₁.stableFunctorCommShift hE hE'
  let := h₂.stableFunctorCommShift hE' hE''
  let := (h₁.comp h₂).stableFunctorCommShift hE hE''
  let := h₃.stableFunctorCommShift hE hE''
  let := quotientMaximalCohenMacaulayStableCokernelCommShift hw
  let := MaximalCohenMacaulayModuleCat.gorensteinProjectiveStableEquivalenceFunctorCommShift hw
  let := quotientGorensteinProjectiveStableCokernelCommShift (mem_nonZeroDivisors_of_ne_zero hw)
  have := eqToIso_stableToHomotopy_comp_commShift
    (stableToHomotopy_comp_quotientMaximalCohenMacaulayStableCokernel hw) _
    (stableToHomotopyInverseCompMaximalCohenMacaulayStableFunctorIso_commShift hw)
  have := eqToIso_stableToHomotopy_comp_commShift
    (stableToHomotopy_comp_quotientGorensteinProjectiveStableCokernel
      (mem_nonZeroDivisors_of_ne_zero hw)) _
    (by
      rw [← congrArg Iso.hom
        (stableToHomotopyInverseCompStableFunctorIso_eq (mem_nonZeroDivisors_of_ne_zero hw))]
      exact stableToHomotopyInverseCompStableFunctorIso_commShift
        (mem_nonZeroDivisors_of_ne_zero hw))
  have := MaximalCohenMacaulayModuleCat.gorensteinProjectiveStableEquivalence_functor_commShift hw
  have := eqToIso_stableFunctor_comp_commShift h₁ h₂ hE hE' hE''
  have := StableConflationExact.stableNatTrans_commShift (h₁.comp h₂) h₃ hE hE''
    (quotientMaximalCohenMacaulayCokernelCompGorensteinProjectiveIso hw).hom
  let F₁ := quotientMaximalCohenMacaulayStableCokernel hw
  let F₂ := (MaximalCohenMacaulayModuleCat.gorensteinProjectiveStableEquivalence hw).functor
  let F₃ := quotientGorensteinProjectiveStableCokernel (mem_nonZeroDivisors_of_ne_zero hw)
  let α := (quotientMaximalCohenMacaulayStableCokernelCompGorensteinProjectiveStableIso hw).hom
  let αL : stableToHomotopy S w ⋙ (F₁ ⋙ F₂) ⟶ stableToHomotopy S w ⋙ F₃ :=
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (eqToIso (stableToHomotopy_comp_quotientMaximalCohenMacaulayStableCokernel hw)).hom F₂ ≫
    Functor.whiskerLeft (h₁.stableFunctor hE)
      (eqToIso (MaximalCohenMacaulayModuleCat.gorensteinProjectiveStableEquivalence_functor
        hw).symm).inv ≫
    (eqToIso (h₁.stableFunctor_comp h₂ hE hE')).inv ≫
    StableConflationExact.stableNatTrans (h₁.comp h₂) h₃ hE
      (quotientMaximalCohenMacaulayCokernelCompGorensteinProjectiveIso hw).hom ≫
    (eqToIso (stableToHomotopy_comp_quotientGorensteinProjectiveStableCokernel
      (mem_nonZeroDivisors_of_ne_zero hw))).inv
  have hwhisk : Functor.whiskerLeft e.functor α = αL := by
    apply CategoryTheory.Quotient.natTrans_ext
    ext X
    have hcomp :=
      Functor.congr_obj (projectiveStableFunctor_comp_stableToHomotopy S w) X
    dsimp only [Functor.comp_obj] at hcomp
    have hnat := α.naturality (eqToHom hcomp)
    dsimp only [Functor.comp_map] at hnat
    have hnat' :
        α.app (e.functor.obj ((splitExact S w).projectiveStableFunctor.obj X)) =
          F₂.map (F₁.map (eqToHom hcomp)) ≫
            α.app ((nullHomotopic (S := S) (w := w)).quotientFunctor.obj X) ≫
            F₃.map (eqToHom hcomp.symm) := by
      rw [← Category.assoc]
      dsimp only [e, F₁, F₂, F₃]
      rw [hnat, Category.assoc, ← CategoryTheory.Functor.map_comp, eqToHom_trans, eqToHom_refl,
        CategoryTheory.Functor.map_id, Category.comp_id]
      rfl
    dsimp only [Functor.whiskerLeft_app, Functor.comp_obj, αL, NatTrans.comp_app,
      Functor.associator_inv_app, Functor.whiskerRight_app, eqToIso.hom, eqToIso.inv,
      eqToHom_app, Category.id_comp]
    rw [hnat']
    have hnatTrans :=
      StableConflationExact.stableNatTrans_app_projectiveStableFunctor_obj
        (h₁.comp h₂) h₃ hE
        (quotientMaximalCohenMacaulayCokernelCompGorensteinProjectiveIso hw).hom X
    have hnatTrans' :
        (StableConflationExact.stableNatTrans (h₁.comp h₂) h₃ hE
            (quotientMaximalCohenMacaulayCokernelCompGorensteinProjectiveIso hw).hom).app
            ((splitExact S w).projectiveStableFunctor.obj X) =
          eqToHom ((h₁.comp h₂).stableFunctor_obj_projectiveStableFunctor_obj hE X) ≫
            (GorensteinProjectiveModuleCat.exactStructure
              (S ⧸ Ideal.span {w})).projectiveStableFunctor.map
              ((quotientMaximalCohenMacaulayCokernelCompGorensteinProjectiveIso hw).hom.app X) ≫
            eqToHom (h₃.stableFunctor_obj_projectiveStableFunctor_obj hE X).symm := by
      apply (cancel_epi (eqToHom
        ((h₁.comp h₂).stableFunctor_obj_projectiveStableFunctor_obj hE X).symm)).1
      apply (cancel_mono (eqToHom
        (h₃.stableFunctor_obj_projectiveStableFunctor_obj hE X))).1
      simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
        Category.id_comp, Category.comp_id] using hnatTrans
    rw [hnatTrans']
    simp only [α, quotientMaximalCohenMacaulayStableCokernelCompGorensteinProjectiveStableIso,
      CategoryTheory.Quotient.natIsoLift_hom, CategoryTheory.Quotient.natTransLift_app,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.associator_inv_app, Functor.associator_hom_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, eqToIso.hom, eqToHom_app, eqToHom_map,
      Category.assoc, eqToHom_trans_assoc, eqToHom_trans, Category.id_comp]
    -- `projectiveStableFunctor` is `MorphismIdeal.quotientFunctor` = `Quotient.functor` by defeq.
    erw [Category.id_comp]
  have : NatTrans.CommShift (Functor.whiskerLeft e.functor α) ℤ := by
    rw [hwhisk]
    infer_instance
  have hα :
      α = (F₁ ⋙ F₂).leftUnitor.inv ≫ Functor.whiskerRight e.counitIso.inv (F₁ ⋙ F₂) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft e.inverse (Functor.whiskerLeft e.functor α) ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight e.counitIso.hom F₃ ≫
        F₃.leftUnitor.hom := by
    ext Y
    simp only [NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
      Functor.leftUnitor_hom_app, Category.id_comp, Functor.id_obj]
    dsimp only [F₁, F₂, F₃]
    rw [← α.naturality_assoc, ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app]
    simp
  have : NatTrans.CommShift α ℤ := by rw [hα]; infer_instance
  exact this

/-- **The maximal Cohen–Macaulay stable cokernel functor is a triangle functor.** -/
theorem quotientMaximalCohenMacaulayStableCokernel_isTriangulated (hw : w ≠ 0) :
    letI := (MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius hw).stableHasShift
    letI := (MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius
      hw).stableShiftFunctor_additive
    letI := (MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius hw).stablePretriangulated
    letI := quotientMaximalCohenMacaulayStableCokernelCommShift hw
    (quotientMaximalCohenMacaulayStableCokernel hw).IsTriangulated := by
  have hE := splitExact_isFrobenius S w
  have hE' := MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius hw
  let := hE.stableHasShift; let := hE.stableShiftFunctor_additive; let := hE.stablePretriangulated
  let := hE'.stableHasShift; let := hE'.stableShiftFunctor_additive
  let := hE'.stablePretriangulated
  let e := (stableToHomotopy S w).asEquivalence
  let : e.functor.CommShift ℤ := stableToHomotopyCommShift S w
  let := e.commShiftInverse ℤ; let := e.commShift_of_functor ℤ
  let := (stableConflationExact_quotientMaximalCohenMacaulayCokernel hw).stableFunctorCommShift
    hE hE'
  let := quotientMaximalCohenMacaulayStableCokernelCommShift hw
  have : e.IsTriangulated := .mk' _ (stableToHomotopy_isTriangulated S w)
  have :=
    (stableConflationExact_quotientMaximalCohenMacaulayCokernel hw).stableFunctorIsTriangulated
      hE hE'
  have := stableToHomotopyInverseCompMaximalCohenMacaulayStableFunctorIso_commShift hw
  exact Functor.isTriangulated_of_iso
    (stableToHomotopyInverseCompMaximalCohenMacaulayStableFunctorIso hw)

/-- **Eisenbud's equivalence.** `quotientMaximalCohenMacaulayStableCokernel` is an equivalence. -/
theorem quotientMaximalCohenMacaulayStableCokernel_isEquivalence (hw : w ≠ 0) :
    (quotientMaximalCohenMacaulayStableCokernel hw).IsEquivalence := by
  have := TauCeti.IsRegularLocalRing.isDomain (R := S)
  have := quotientGorensteinProjectiveStableCokernel_isEquivalence_of_isRegularLocalRing
    (mem_nonZeroDivisors_of_ne_zero hw)
  have := Functor.isEquivalence_of_iso
    (quotientMaximalCohenMacaulayStableCokernelCompGorensteinProjectiveStableIso hw).symm
  exact Functor.isEquivalence_of_comp_right _
    (MaximalCohenMacaulayModuleCat.gorensteinProjectiveStableEquivalence hw).functor

/-- **Eisenbud's equivalence** `HMF(S, w) ≌ stable(MCM-(S ⧸ (w)))`. -/
def quotientMaximalCohenMacaulayStableCokernelEquivalence (hw : w ≠ 0) :
    HomotopyCategory (S := S) (w := w) ≌
      (MaximalCohenMacaulayModuleCat.exactStructure.{u}
        (S ⧸ Ideal.span {w})).ProjectiveStableCategory :=
  haveI := quotientMaximalCohenMacaulayStableCokernel_isEquivalence hw
  (quotientMaximalCohenMacaulayStableCokernel hw).asEquivalence

/-- The forward functor of `quotientMaximalCohenMacaulayStableCokernelEquivalence`. -/
@[simp]
theorem quotientMaximalCohenMacaulayStableCokernelEquivalence_functor (hw : w ≠ 0) :
    (quotientMaximalCohenMacaulayStableCokernelEquivalence hw).functor =
      quotientMaximalCohenMacaulayStableCokernel hw := (rfl)

/-- **Eisenbud's local hypersurface equivalence is triangulated.** -/
theorem quotientMaximalCohenMacaulayStableCokernelEquivalence_isTriangulated (hw : w ≠ 0) :
    letI := (MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius hw).stableHasShift
    letI := (MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius
      hw).stableShiftFunctor_additive
    letI := (MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius hw).stablePretriangulated
    letI := quotientMaximalCohenMacaulayStableCokernelCommShift hw
    letI : (quotientMaximalCohenMacaulayStableCokernelEquivalence hw).functor.CommShift ℤ :=
      Functor.CommShift.ofIso
        (eqToIso (quotientMaximalCohenMacaulayStableCokernelEquivalence_functor hw).symm) ℤ
    letI := (quotientMaximalCohenMacaulayStableCokernelEquivalence hw).commShiftInverse ℤ
    letI := (quotientMaximalCohenMacaulayStableCokernelEquivalence hw).commShift_of_functor ℤ
    (quotientMaximalCohenMacaulayStableCokernelEquivalence hw).IsTriangulated := by
  have hE' := MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius hw
  let := hE'.stableHasShift; let := hE'.stableShiftFunctor_additive
  let := hE'.stablePretriangulated; let := quotientMaximalCohenMacaulayStableCokernelCommShift hw
  let eqv := quotientMaximalCohenMacaulayStableCokernelEquivalence hw
  let e := eqToIso (quotientMaximalCohenMacaulayStableCokernelEquivalence_functor hw).symm
  let : eqv.functor.CommShift ℤ := Functor.CommShift.ofIso e ℤ
  let := eqv.commShiftInverse ℤ; let := eqv.commShift_of_functor ℤ
  have := Functor.CommShift.ofIso_compatibility e ℤ
  have := quotientMaximalCohenMacaulayStableCokernel_isTriangulated hw
  exact .mk' _ (Functor.isTriangulated_of_iso e)

end HomotopyCategory
end MatrixFactorization
end TauCeti
