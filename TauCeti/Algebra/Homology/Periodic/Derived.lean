/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.Acyclic
public import TauCeti.Algebra.Homology.Periodic.QuasiIso
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Localization.Triangulated

/-!
# The Verdier quotient of periodic complexes

The periodic derived category is the localization of the cyclic homotopy category at
morphisms whose cone has zero cyclic homology. Mathlib's Verdier localization supplies its
additive and triangulated structures, integral shifts, and localization universal property.
The functor from complexes factors through homotopy classes, and sends acyclic complexes
to zero. No finite-global-dimension hypothesis is needed for this construction.

The presentation here is the Verdier quotient. The mapping-cone characterization of periodic
quasi-isomorphisms identifies its weak equivalences with the homology-based quasi-isomorphisms.
Consequently the functor from periodic complexes is itself a localization at quasi-isomorphisms,
and the resulting comparison with Mathlib's constructed localization is an equivalence. A
positive period gives a finite cyclic grading; period zero is also supported.

The construction follows Joël Riou's localization instances in
`Mathlib.Algebra.Homology.DerivedCategory.Basic`, retaining the existing periodic shift.

## References

* T. Stai, *The triangulated hull of periodic complexes*, Sections 3.1–3.2.
-/

public section

universe v u

namespace TauCeti.PeriodicComplex

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex
open scoped ZeroObject

variable (C : Type u) [Category.{v} C] [Abelian C] (n : ℕ)

/-- Quasi-isomorphisms in the periodic homotopy category are exactly the morphisms whose
Verdier cone is acyclic. -/
theorem quasiIso_eq_trW_subcategoryAcyclic :
    HomotopyCategory.quasiIso C (ComplexShape.up (ZMod n)) =
      (subcategoryAcyclic C n).trW := by
  ext X Y f
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C
    (ComplexShape.up (ZMod n))).map_surjective f
  have htr :
      (subcategoryAcyclic C n).trW
          ((HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).map f) ↔
        subcategoryAcyclic C n
          ((HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).obj
            (homotopyCofiber f)) := by
    simpa only [mappingConeTriangle_mor₁, mappingConeTriangle_obj₃] using
      (subcategoryAcyclic C n).trW_iff_of_distinguished
        (mappingConeTriangle f) (mappingCone_mem_distTriang f)
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).trans
    ((quasiIso_iff_acyclic_homotopyCofiber f).trans
      ((quotient_obj_mem_subcategoryAcyclic_iff C n (homotopyCofiber f)).symm.trans htr.symm))

/-- The Verdier quotient of the cyclic homotopy category by the acyclic objects. -/
abbrev DerivedCategory := (subcategoryAcyclic C n).trW.Localization

namespace DerivedCategory

/-- The Verdier localization functor from cyclic homotopy classes. -/
noncomputable def Qh : HomotopyCategory C (ComplexShape.up (ZMod n)) ⥤ DerivedCategory C n :=
  (subcategoryAcyclic C n).trW.Q

instance : (Qh C n).IsLocalization (subcategoryAcyclic C n).trW := by
  dsimp [Qh]
  infer_instance

/-- The periodic Verdier functor is also a localization at the homology-based
quasi-isomorphisms of the periodic homotopy category. -/
instance : (Qh C n).IsLocalization
    (HomotopyCategory.quasiIso C (ComplexShape.up (ZMod n))) := by
  rw [quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

noncomputable instance : Preadditive (DerivedCategory C n) :=
  Localization.preadditive (Qh C n) (subcategoryAcyclic C n).trW

instance : (Qh C n).Additive :=
  Localization.functor_additive (Qh C n) (subcategoryAcyclic C n).trW

noncomputable instance : HasZeroObject (DerivedCategory C n) :=
  (Qh C n).hasZeroObject_of_additive

noncomputable instance : HasShift (DerivedCategory C n) ℤ :=
  HasShift.localized (Qh C n) (subcategoryAcyclic C n).trW ℤ

noncomputable instance : (Qh C n).CommShift ℤ :=
  Functor.CommShift.localized (Qh C n) (subcategoryAcyclic C n).trW ℤ

instance (k : ℤ) : (CategoryTheory.shiftFunctor (DerivedCategory C n) k).Additive := by
  rw [Localization.functor_additive_iff (Qh C n) (subcategoryAcyclic C n).trW]
  exact Functor.additive_of_iso ((Qh C n).commShiftIso k)

noncomputable instance : Pretriangulated (DerivedCategory C n) :=
  Triangulated.Localization.pretriangulated (Qh C n) (subcategoryAcyclic C n).trW

instance : (Qh C n).IsTriangulated :=
  Triangulated.Localization.isTriangulated_functor (Qh C n) (subcategoryAcyclic C n).trW

instance : IsTriangulated (DerivedCategory C n) :=
  Triangulated.Localization.isTriangulated (Qh C n) (subcategoryAcyclic C n).trW

/-- Passage from cyclic complexes to their derived classes, through the homotopy category. -/
noncomputable def Q : CochainComplex C (ZMod n) ⥤ DerivedCategory C n :=
  HomotopyCategory.quotient C (ComplexShape.up (ZMod n)) ⋙ Qh C n

/-- The functor from complexes factors through homotopy classes. -/
theorem quotient_comp_Qh : HomotopyCategory.quotient C (ComplexShape.up (ZMod n)) ⋙ Qh C n =
    Q C n := (rfl)

/-- Passage to the periodic derived category is a localization of periodic complexes at
quasi-isomorphisms. -/
instance : (Q C n).IsLocalization
    (HomologicalComplex.quasiIso C (ComplexShape.up (ZMod n))) := by
  dsimp only [Q]
  let _ : (HomotopyCategory.quotient C
      (ComplexShape.up (ZMod n))).IsLocalization
      (HomologicalComplex.homotopyEquivalences C (ComplexShape.up (ZMod n))) :=
    (ComplexShape.up (ZMod n)).quotient_isLocalization
      (fun j ↦ ⟨j - 1, by simp⟩) C
  refine Functor.IsLocalization.comp _ _
    (HomologicalComplex.homotopyEquivalences C (ComplexShape.up (ZMod n)))
    (HomotopyCategory.quasiIso C (ComplexShape.up (ZMod n)))
    (HomologicalComplex.quasiIso C (ComplexShape.up (ZMod n))) ?_ ?_ ?_
  · intro X Y f hf
    exact Localization.inverts (Qh C n)
      (HomotopyCategory.quasiIso C (ComplexShape.up (ZMod n))) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf)
  · exact homotopyEquivalences_le_quasiIso C (ComplexShape.up (ZMod n))
  · rw [HomotopyCategory.quasiIso_eq_quasiIso_map_quotient]

/-- A periodic quasi-isomorphism becomes an isomorphism in the periodic derived category. -/
instance {X Y : CochainComplex C (ZMod n)} (f : X ⟶ Y) [QuasiIso f] :
    IsIso ((Q C n).map f) :=
  Localization.inverts (Q C n)
    (HomologicalComplex.quasiIso C (ComplexShape.up (ZMod n))) f
      (inferInstanceAs (QuasiIso f))

/-- The equivalence from Mathlib's constructed localization at periodic quasi-isomorphisms to
the periodic Verdier quotient. -/
noncomputable def quasiIsoLocalizationEquivalence :
    (HomologicalComplex.quasiIso C
      (ComplexShape.up (ZMod n))).Localization ≌ DerivedCategory C n :=
  Localization.uniq
    (HomologicalComplex.quasiIso C (ComplexShape.up (ZMod n))).Q (Q C n)
      (HomologicalComplex.quasiIso C (ComplexShape.up (ZMod n)))

/-- The localization through `quasiIsoLocalizationEquivalence` agrees with the periodic Verdier
localization. -/
noncomputable def quasiIsoLocalizationCompEquivalenceFunctorIso :
    (HomologicalComplex.quasiIso C (ComplexShape.up (ZMod n))).Q ⋙
      (quasiIsoLocalizationEquivalence C n).functor ≅ Q C n :=
  Localization.compUniqFunctor
    (HomologicalComplex.quasiIso C (ComplexShape.up (ZMod n))).Q (Q C n)
      (HomologicalComplex.quasiIso C (ComplexShape.up (ZMod n)))

instance : (Q C n).Additive := by
  dsimp [Q]
  infer_instance

noncomputable instance : (Q C n).CommShift ℤ :=
  Functor.CommShift.ofIso (eqToIso (quotient_comp_Qh C n)) ℤ

instance : NatTrans.CommShift (eqToIso (quotient_comp_Qh C n)).hom ℤ :=
  Functor.CommShift.ofIso_compatibility (eqToIso (quotient_comp_Qh C n)) ℤ

/-- The Verdier localization kills every acyclic homotopy object. -/
theorem isZero_Qh_obj (K : HomotopyCategory C (ComplexShape.up (ZMod n)))
    (hK : subcategoryAcyclic C n K) : IsZero ((Qh C n).obj K) := by
  have hW := ObjectProperty.trW.mk' (subcategoryAcyclic C n) (contractible_distinguished K) hK
  have : IsIso (0 : (Qh C n).obj K ⟶
      (Qh C n).obj (0 : HomotopyCategory C (ComplexShape.up (ZMod n)))) := by
    simpa [contractibleTriangle] using
      Localization.inverts (Qh C n) (subcategoryAcyclic C n).trW _ hW
  exact IsZero.of_mono_eq_zero (0 : (Qh C n).obj K ⟶
    (Qh C n).obj (0 : HomotopyCategory C (ComplexShape.up (ZMod n)))) rfl

/-- An acyclic cyclic complex becomes zero in the periodic derived category. -/
theorem isZero_Q_obj (K : CochainComplex C (ZMod n)) (hK : K.Acyclic) :
    IsZero ((Q C n).obj K) := by
  exact isZero_Qh_obj C n _ ((quotient_obj_mem_subcategoryAcyclic_iff C n K).mpr hK)

end DerivedCategory

end TauCeti.PeriodicComplex
