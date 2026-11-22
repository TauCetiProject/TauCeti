/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GorensteinProjective.MaximalCohenMacaulay
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Equivalence
public import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.CategoryTheory.Exact.Stable.Functor.NatTrans
import TauCeti.CategoryTheory.Exact.Stable.Functor.Shift
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
comparison `TauCeti.Algebra.Homology.GorensteinProjective.MaximalCohenMacaulay`.

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
  have : NatTrans.CommShift
      (eqToIso (stableToHomotopy_comp_quotientMaximalCohenMacaulayStableCokernel hw).symm).hom
      ℤ :=
    TauCeti.natTrans_commShift_of_inverseCompIso e
      (eqToIso (stableToHomotopy_comp_quotientMaximalCohenMacaulayStableCokernel hw).symm)
      (stableToHomotopyInverseCompMaximalCohenMacaulayStableFunctorIso_commShift hw)
  have : NatTrans.CommShift
      (eqToIso (stableToHomotopy_comp_quotientMaximalCohenMacaulayStableCokernel hw)).hom ℤ :=
    inferInstanceAs (NatTrans.CommShift
      (eqToIso (stableToHomotopy_comp_quotientMaximalCohenMacaulayStableCokernel hw).symm).inv ℤ)
  have : NatTrans.CommShift
      (eqToIso (stableToHomotopy_comp_quotientGorensteinProjectiveStableCokernel
        (mem_nonZeroDivisors_of_ne_zero hw)).symm).hom ℤ :=
    TauCeti.natTrans_commShift_of_inverseCompIso e
      (eqToIso (stableToHomotopy_comp_quotientGorensteinProjectiveStableCokernel
        (mem_nonZeroDivisors_of_ne_zero hw)).symm)
      (by
        rw [← congrArg Iso.hom
          (stableToHomotopyInverseCompStableFunctorIso_eq (mem_nonZeroDivisors_of_ne_zero hw))]
        exact stableToHomotopyInverseCompStableFunctorIso_commShift
          (mem_nonZeroDivisors_of_ne_zero hw))
  have : NatTrans.CommShift
      (eqToIso (stableToHomotopy_comp_quotientGorensteinProjectiveStableCokernel
        (mem_nonZeroDivisors_of_ne_zero hw))).hom ℤ :=
    inferInstanceAs (NatTrans.CommShift
      (eqToIso (stableToHomotopy_comp_quotientGorensteinProjectiveStableCokernel
        (mem_nonZeroDivisors_of_ne_zero hw)).symm).inv ℤ)
  have := MaximalCohenMacaulayModuleCat.gorensteinProjectiveStableEquivalence_functor_commShift hw
  have := StableConflationExact.eqToIso_stableFunctor_comp_commShift h₁ h₂ hE hE' hE''
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
    have h12 :
        ((stableToHomotopy S w).associator F₁ F₂).inv.app
            ((Quotient.functor (splitExact S w).projectiveStableIdeal.rel).obj X) ≫
          (Functor.whiskerRight
            (eqToIso (stableToHomotopy_comp_quotientMaximalCohenMacaulayStableCokernel hw)).hom
            F₂).app ((Quotient.functor (splitExact S w).projectiveStableIdeal.rel).obj X) =
          eqToHom (congrArg F₂.obj (Functor.congr_obj
            (stableToHomotopy_comp_quotientMaximalCohenMacaulayStableCokernel hw)
            ((Quotient.functor (splitExact S w).projectiveStableIdeal.rel).obj X))) := by
      dsimp only [F₁]
      simp only [Functor.associator_inv_app, Functor.whiskerRight_app, eqToIso.hom, eqToHom_app,
        eqToHom_map, Category.id_comp]
    dsimp only [Functor.whiskerLeft_app, αL, NatTrans.comp_app]
    rw [hnat', reassoc_of% h12]
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
    dsimp only [F₁, F₂, F₃]
    simp only [α, quotientMaximalCohenMacaulayStableCokernelCompGorensteinProjectiveStableIso,
      CategoryTheory.Quotient.natIsoLift_hom, CategoryTheory.Quotient.natTransLift_app,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.associator_inv_app, Functor.associator_hom_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_map,
      Category.assoc, eqToHom_trans_assoc, eqToHom_trans, Category.id_comp]
  exact TauCeti.natTrans_commShift_of_whiskerLeft e (by rw [hwhisk]; infer_instance)

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
