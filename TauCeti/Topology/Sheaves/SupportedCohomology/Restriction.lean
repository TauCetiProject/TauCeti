/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.SupportedCohomology.Derived

/-!
# Restriction of derived supported sections

The comparison between right derived supported sections and the supported Ext groups
commutes with restriction to smaller opens. Thus these comparisons identify not only
the cohomology groups on individual opens, but also their restriction maps.

Restriction on the derived side is obtained by right deriving the actual restriction
of supported sections. On the Ext side it is the existing restriction in
`supportedModuleHPresheaf`. The compatibility follows from contravariant naturality
of the derived Hom-to-Ext comparison and the representing property of the relative
free module sheaves.

## References

* A. Grothendieck, *Local cohomology*, Lecture Notes in Mathematics 41, §1.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} {R : Type u} [CommRing R] (S : Closeds X)
  {W' W : Opens X}

noncomputable section

/-- The derived supported-section-to-Ext comparison commutes with restriction in every
cohomological degree, naturally in the coefficient sheaf. -/
@[reassoc]
lemma rightDerivedSupportedSubmoduleSectionsIso_hom_restrict (i : W' ⟶ W) (n : ℕ) :
    (supportedSubmoduleSectionsRestrict (R := R) S i).rightDerived n ≫
        (rightDerivedSupportedSubmoduleSectionsIso (R := R) S W' n).hom =
      (rightDerivedSupportedSubmoduleSectionsIso (R := R) S W n).hom ≫
        Functor.whiskerLeft (supportedModuleHPresheafFunctor S n)
          ((evaluation (Opens X)ᵒᵖ (ModuleCat.{u} R)).map i.op) := by
  have : IsIso ((supportedSubmoduleSectionsRepresentableIso (R := R) S W).hom.rightDerived n) := by
    rw [← NatIso.rightDerived_hom]
    infer_instance
  apply (cancel_epi
    ((supportedSubmoduleSectionsRepresentableIso (R := R) S W).hom.rightDerived n)).1
  rw [← Category.assoc, ← NatTrans.rightDerived_comp,
    ← supportedSubmoduleSectionsRepresentableIso_hom_restrict,
    NatTrans.rightDerived_comp, Category.assoc,
    rightDerivedSupportedSubmoduleSectionsIso_hom_comp,
    rightDerivedSupportedSubmoduleSectionsIso_hom_comp_assoc]
  exact rightDerivedLinearCoyonedaIsoExt_hom_naturality_left R _
    ((S.supportedFreeModuleSheafFunctor R).map i) n

end

end CategoryTheory.Sheaf
