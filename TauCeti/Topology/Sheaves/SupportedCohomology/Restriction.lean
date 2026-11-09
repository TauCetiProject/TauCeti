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

/-- Restriction of supported sections, natural in the coefficient sheaf. -/
def supportedSubmoduleSectionsRestrict (i : W' ⟶ W) :
    supportedSubmoduleSectionsFunctor (R := R) S W ⟶
      supportedSubmoduleSectionsFunctor S W' :=
  Functor.whiskerLeft (supportedSubmoduleFunctor S)
    ((sheafSections (Opens.grothendieckTopology X) (ModuleCat.{u} R)).map i.op)

/-- Restriction of supported sections leaves the usual restriction in the ambient sheaf. -/
-- Rewrite before evaluation simplifies the bundled section object.
@[simp↓]
lemma coe_supportedSubmoduleSectionsRestrict_app_apply (i : W' ⟶ W)
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (s : F.supportedSubmodule S W) :
    ((supportedSubmoduleSectionsRestrict (R := R) S i).app F s).val = F.obj.map i.op s :=
  (rfl)

/-- Restriction along an identity open inclusion is the identity transformation. -/
@[simp]
lemma supportedSubmoduleSectionsRestrict_id (W : Opens X) :
    supportedSubmoduleSectionsRestrict (R := R) S (𝟙 W) = 𝟙 _ := by
  ext F s
  apply Subtype.ext
  simp [supportedSubmoduleSectionsRestrict]

/-- Restricting through two open inclusions agrees with restriction along their composite. -/
@[reassoc (attr := simp)]
lemma supportedSubmoduleSectionsRestrict_comp {W'' : Opens X}
    (i : W'' ⟶ W') (j : W' ⟶ W) :
    supportedSubmoduleSectionsRestrict (R := R) S j ≫
        supportedSubmoduleSectionsRestrict S i =
      supportedSubmoduleSectionsRestrict S (i ≫ j) := by
  ext F s
  apply Subtype.ext
  simp [supportedSubmoduleSectionsRestrict, ← Functor.map_comp, ← op_comp]

/-- The representation of supported sections by `Q_S(W)` respects restriction of opens. -/
@[reassoc]
lemma supportedSubmoduleSectionsRepresentableIso_hom_restrict (i : W' ⟶ W) :
    (linearCoyoneda R _).map ((S.supportedFreeModuleSheafFunctor R).map i).op ≫
        (supportedSubmoduleSectionsRepresentableIso (R := R) S W').hom =
      (supportedSubmoduleSectionsRepresentableIso (R := R) S W).hom ≫
        supportedSubmoduleSectionsRestrict S i := by
  ext F g
  apply Subtype.ext
  -- Unbundle composition and the linear coyoneda action before using the opaque
  -- representing isomorphism's application lemmas.
  change (((supportedSubmoduleSectionsRepresentableIso (R := R) S W').hom.app F)
      ((S.supportedFreeModuleSheafFunctor R).map i ≫ g)).val =
    (((supportedSubmoduleSectionsRestrict (R := R) S i).app F)
      (((supportedSubmoduleSectionsRepresentableIso (R := R) S W).hom.app F) g)).val
  erw [supportedSubmoduleSectionsRepresentableIso_hom_app_apply,
    coe_supportedSubmoduleSectionsRestrict_app_apply,
    supportedSubmoduleSectionsRepresentableIso_hom_app_apply]
  exact S.coe_supportedFreeModuleSheafHomEquiv_map_comp R i F g

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
