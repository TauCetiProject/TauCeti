/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.Triangulated
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-!
# Acyclic periodic complexes

Cyclic homology is a homological functor on the periodic homotopy category. The objects
with zero homology in every residue form a triangulated subcategory, closed under retracts.
This is the kernel used in the Verdier construction of the periodic derived category.

The shift comparison follows Joël Riou's short-complex construction in
`Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence`. The homological-functor argument
follows `Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor`, using the
componentwise split conflations that define the periodic triangulation.

## References

* T. Stai, *The triangulated hull of periodic complexes*, Sections 3.1–3.2.
-/

public section

universe v u

namespace TauCeti.PeriodicComplex

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex
open scoped ZeroObject

variable (C : Type u) [Category.{v} C] (n : ℕ)

section Shift

variable [Preadditive C]

/-- The shift's two differential signs are absorbed into the outer components of the
three-term complex computing homology. -/
private noncomputable def shiftShortComplexIso (k : ℤ) (i : ZMod n) :
    CategoryTheory.shiftFunctor (CochainComplex C (ZMod n)) k ⋙
        shortComplexFunctor' C (ComplexShape.up (ZMod n)) (i - 1) i (i + 1) ≅
      shortComplexFunctor' C (ComplexShape.up (ZMod n))
        (i - 1 + k) (i + k) (i + 1 + k) :=
  NatIso.ofComponents (fun K ↦ ShortComplex.isoMk
    (k.negOnePow • Iso.refl (K.X (i - 1 + k)))
    (Iso.refl (K.X (i + k))) (k.negOnePow • Iso.refl (K.X (i + 1 + k)))
    (by simp [shortComplexFunctor', Linear.units_smul_comp])
    (by simp [shortComplexFunctor', Linear.comp_units_smul, smul_smul]))
    (fun f ↦ by ext <;> simp [shortComplexFunctor', ShortComplex.isoMk, Linear.comp_units_smul,
      Linear.units_smul_comp])

/-- Homology of a signed cyclic shift is homology in the shifted residue. -/
noncomputable def homologyShiftIso [CategoryWithHomology C] (k : ℤ) (i : ZMod n) :
    CategoryTheory.shiftFunctor (CochainComplex C (ZMod n)) k ⋙
        HomologicalComplex.homologyFunctor C (ComplexShape.up (ZMod n)) i ≅
      HomologicalComplex.homologyFunctor C (ComplexShape.up (ZMod n)) (i + k) :=
  Functor.isoWhiskerLeft _
      (homologyFunctorIso' C (ComplexShape.up (ZMod n)) (i - 1) i (i + 1)
        (by simp) (by simp)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (shiftShortComplexIso C n k i) _ ≪≫
    (homologyFunctorIso' C (ComplexShape.up (ZMod n))
      (i - 1 + k) (i + k) (i + 1 + k) (by simp; abel) (by simp; abel)).symm

variable [CategoryWithHomology C]

/-- Signed cyclic shifts preserve and reflect acyclicity. -/
@[simp]
theorem shift_acyclic_iff (K : CochainComplex C (ZMod n)) (k : ℤ) :
    (K⟦k⟧).Acyclic ↔ K.Acyclic := by
  simp only [acyclic_iff, exactAt_iff_isZero_homology]
  have hi (i : ZMod n) := ((homologyShiftIso C n k i).app K).isZero_iff
  simp only [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj] at hi
  simp only [hi]
  constructor
  · intro h i
    simpa using h (i - (k : ZMod n))
  · intro h i
    exact h _

end Shift

variable [Abelian C]

local notation "hE" => ExactStructure.homologicalComplex_split_isFrobenius
  (C := C) (c := ComplexShape.up (ZMod n))
  (fun j ↦ Exists.intro (j - 1) (by simp))
  (fun i ↦ Exists.intro (i + 1) (by simp))

/-- Homology in each cyclic degree sends distinguished triangles to exact sequences. -/
instance homologyFunctor_isHomological (i : ZMod n) :
    (HomotopyCategory.homologyFunctor C (ComplexShape.up (ZMod n)) i).IsHomological := by
  let := (hE).stableHasShift
  let := stableToHomotopyCommShift C n
  refine Functor.IsHomological.mk' _ (fun T hT ↦ ?_)
  obtain ⟨S, hS, ⟨e⟩⟩ := (homotopyCategory_mem_distTriang_iff C n T).mp hT
  have ht := (hE).stableConflationTriangle_eq_mk S hS
  erw [ht] at e
  refine ⟨_, e, ?_⟩
  have hSE : S.ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact S (fun j ↦
      (ExactStructure.split C).isKernelCokernelPair _
        ((ExactStructure.homologicalComplex_conflation_iff _ _ S).mp hS j) |>.shortExact)
  have hex := (ShortComplex.exact_iff_of_iso
    (S.mapNatIso (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up (ZMod n)) i))).2
      (hSE.homology_exact₂ i)
  let G := (ExactStructure.homologicalComplex (ExactStructure.split C)
    (ComplexShape.up (ZMod n))).projectiveStableFunctor ⋙
      ExactStructure.homologicalComplexSplitStableToHomotopy C
        (ComplexShape.up (ZMod n)) (fun i ↦ ⟨i + 1, rfl⟩)
  let H := HomotopyCategory.homologyFunctor C (ComplexShape.up (ZMod n)) i
  -- The first two triangle arrows give precisely this mapped short complex. Only the
  -- proof that they compose to zero differs; the connecting arrow does not enter it.
  change (S.map (G ⋙ H)).Exact
  exact (ShortComplex.exact_iff_of_iso (S.mapNatIso (Functor.isoWhiskerRight
    (eqToIso (ExactStructure.projectiveStableFunctor_comp_homologicalComplexSplitStableToHomotopy
      C (ComplexShape.up (ZMod n)) (fun i ↦ ⟨i + 1, rfl⟩))) H))).2 hex

/-- The acyclic objects of the cyclic homotopy category: homology vanishes in every residue. -/
def subcategoryAcyclic : ObjectProperty (HomotopyCategory C (ComplexShape.up (ZMod n))) :=
  fun K ↦ ∀ i, IsZero ((HomotopyCategory.homologyFunctor C (ComplexShape.up (ZMod n)) i).obj K)

/-- Membership in the acyclic subcategory is vanishing of every cyclic homology object. -/
theorem mem_subcategoryAcyclic_iff (K : HomotopyCategory C (ComplexShape.up (ZMod n))) :
    subcategoryAcyclic C n K ↔
      ∀ i, IsZero ((HomotopyCategory.homologyFunctor C (ComplexShape.up (ZMod n)) i).obj K) :=
  Iff.rfl

/-- A represented homotopy object is acyclic exactly when the original complex is acyclic. -/
@[simp]
theorem quotient_obj_mem_subcategoryAcyclic_iff (K : CochainComplex C (ZMod n)) :
    subcategoryAcyclic C n ((HomotopyCategory.quotient C _).obj K) ↔ K.Acyclic := by
  rw [mem_subcategoryAcyclic_iff, acyclic_iff]
  refine forall_congr' (fun i ↦ ?_)
  rw [exactAt_iff_isZero_homology]
  exact ((HomotopyCategory.homologyFunctorFactors C (ComplexShape.up (ZMod n)) i).app K).isZero_iff

instance : (subcategoryAcyclic C n).IsStableUnderRetracts where
  of_retract r h i := by
    let F := HomotopyCategory.homologyFunctor C (ComplexShape.up (ZMod n)) i
    apply (IsZero.iff_id_eq_zero _).mpr
    rw [← (r.map F).retract, (h i).eq_zero_of_src ((r.map F).r), comp_zero]

instance : (subcategoryAcyclic C n).IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, fun i ↦
    (HomotopyCategory.homologyFunctor C _ i).map_isZero (isZero_zero _)⟩
  toIsStableUnderShift := ⟨fun k ↦ ⟨fun K hK ↦ by
    obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    simp only [ObjectProperty.prop_shift_iff]
    rw [shift_quotient_obj, quotient_obj_mem_subcategoryAcyclic_iff, shift_acyclic_iff]
    exact (quotient_obj_mem_subcategoryAcyclic_iff C n X).mp hK⟩⟩
  toIsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ i ↦
    ((HomotopyCategory.homologyFunctor C _ i).map_distinguished_exact T hT).isZero_of_both_isZero
      (h₁ i) (h₃ i))

end TauCeti.PeriodicComplex
