/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.SupportedCohomology.Sections
import TauCeti.CategoryTheory.Sites.EpiMono

/-!
# Composition of supported-section functors

For closed subsets `Z ⊆ S`, taking sections supported in `S` and then in `Z`
is naturally isomorphic to taking sections supported in `Z` directly. The comparison
is induced by the inclusion of the supported-section sheaf into its ambient sheaf.
We construct it for sheaves of modules, retain its sectionwise formulas in both
directions, and prove compatibility with the inclusions and with forgetting scalars.

These comparisons identify the underived composite in the spectral sequence for
composed supported-section functors. No concentration or acyclicity assumption on
the coefficient sheaf is needed here.

## References

* A. Grothendieck, *Local cohomology*, Lecture Notes in Mathematics 41, §1.
* M. Kashiwara and P. Schapira, *Sheaves on Manifolds*, §2.6.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} {R : Type u} [CommRing R]
  (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
  {Z S : Closeds X}

noncomputable section

/-- If `Z ⊆ S`, the inclusion `Γ_S(F) ⟶ F` becomes an isomorphism after taking
sections supported in `Z`. -/
theorem isIso_supportedSubmoduleFunctor_map_ι (hZS : Z ≤ S) :
    IsIso ((supportedSubmoduleFunctor Z).map (F.supportedSubmoduleι S)) := by
  have (W : (Opens X)ᵒᵖ) :
      IsIso (((supportedSubmoduleFunctor Z).map (F.supportedSubmoduleι S)).hom.app W) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    refine ⟨?_, fun s ↦ ?_⟩
    · exact injective_app_of_mono ((supportedSubmoduleFunctor Z).map (F.supportedSubmoduleι S)) W
    · refine ⟨⟨⟨s.1, F.supportedSubmodule_mono hZS W.unop s.2⟩, ?_⟩, ?_⟩
      · exact (F.mem_supportedSubmodule_supportedSubmoduleSheaf_iff S Z W.unop _).2 s.2
      · exact Subtype.ext (F.coe_supportedSubmoduleFunctor_map_ι_hom_app_apply Z S W _)
  have : IsIso ((supportedSubmoduleFunctor Z).map (F.supportedSubmoduleι S)).hom :=
    NatIso.isIso_of_isIso_app _
  exact (ObjectProperty.isIso_hom_iff _).mp inferInstance

/-- For `Z ⊆ S`, taking supported sections twice gives the same sheaf as taking
sections supported in `Z` directly. -/
def supportedSubmoduleCompIso (hZS : Z ≤ S) :
    (F.supportedSubmoduleSheaf S).supportedSubmoduleSheaf Z ≅ F.supportedSubmoduleSheaf Z := by
  have := F.isIso_supportedSubmoduleFunctor_map_ι hZS
  exact asIso ((supportedSubmoduleFunctor Z).map (F.supportedSubmoduleι S))

lemma supportedSubmoduleCompIso_hom (hZS : Z ≤ S) :
    (F.supportedSubmoduleCompIso hZS).hom =
      (supportedSubmoduleFunctor Z).map (F.supportedSubmoduleι S) :=
  (rfl)

/-- For `Z ⊆ S`, the natural comparison `Γ_Z(Γ_S(F)) ≅ Γ_Z(F)`. -/
def supportedSubmoduleFunctorCompIso (hZS : Z ≤ S) :
    supportedSubmoduleFunctor (R := R) S ⋙ supportedSubmoduleFunctor Z ≅
      supportedSubmoduleFunctor Z :=
  NatIso.ofComponents (fun F ↦ F.supportedSubmoduleCompIso hZS)
    (fun {F G} f ↦ by
      rw [Functor.comp_map, supportedSubmoduleCompIso_hom, supportedSubmoduleCompIso_hom]
      rw [← Functor.map_comp, ← Functor.map_comp, supportedSubmoduleFunctor_map_ι])

@[simp]
lemma supportedSubmoduleFunctorCompIso_hom_app (hZS : Z ≤ S) :
    (supportedSubmoduleFunctorCompIso (R := R) hZS).hom.app F =
      (F.supportedSubmoduleCompIso hZS).hom :=
  (rfl)

@[simp]
lemma supportedSubmoduleFunctorCompIso_inv_app (hZS : Z ≤ S) :
    (supportedSubmoduleFunctorCompIso (R := R) hZS).inv.app F =
      (F.supportedSubmoduleCompIso hZS).inv :=
  (rfl)

/-- The comparison forgets the intermediate support condition, leaving the same section. -/
@[simp]
lemma coe_supportedSubmoduleCompIso_hom_hom_app_apply (hZS : Z ≤ S)
    (W : (Opens X)ᵒᵖ)
    (s : (F.supportedSubmoduleSheaf S).supportedSubmodule Z W.unop) :
    Subtype.val (α := F.obj.obj W) (p := (· ∈ F.supportedSubmodule Z W.unop))
      ((F.supportedSubmoduleCompIso hZS).hom.hom.app W s) = s.1.1 := by
  rw [supportedSubmoduleCompIso_hom]
  exact F.coe_supportedSubmoduleFunctor_map_ι_hom_app_apply Z S W s

/-- The composition comparison commutes with the inclusions into the ambient sheaf. -/
@[reassoc (attr := simp)]
lemma supportedSubmoduleCompIso_hom_ι (hZS : Z ≤ S) :
    (F.supportedSubmoduleCompIso hZS).hom ≫ F.supportedSubmoduleι Z =
      (F.supportedSubmoduleSheaf S).supportedSubmoduleι Z ≫ F.supportedSubmoduleι S := by
  rw [supportedSubmoduleCompIso_hom]
  exact supportedSubmoduleFunctor_map_ι Z (F.supportedSubmoduleι S)

/-- Reinserting the intermediate support and then including into `F` is the original
supported-section inclusion. -/
@[reassoc (attr := simp)]
lemma supportedSubmoduleCompIso_inv_ι (hZS : Z ≤ S) :
    (F.supportedSubmoduleCompIso hZS).inv ≫
        (F.supportedSubmoduleSheaf S).supportedSubmoduleι Z ≫ F.supportedSubmoduleι S =
      F.supportedSubmoduleι Z :=
  (Iso.inv_comp_eq _).2 (F.supportedSubmoduleCompIso_hom_ι hZS).symm

/-- The inverse comparison also leaves the ambient section unchanged. -/
@[simp]
lemma coe_coe_supportedSubmoduleCompIso_inv_hom_app_apply (hZS : Z ≤ S)
    (W : (Opens X)ᵒᵖ) (s : F.supportedSubmodule Z W.unop) :
    Subtype.val (α := F.obj.obj W) (p := (· ∈ F.supportedSubmodule S W.unop))
      (((F.supportedSubmoduleCompIso hZS).inv.hom.app W s).1) =
        s.1 := by
  have h := congr_arg (fun f ↦ (f.hom.app W).hom) (F.supportedSubmoduleCompIso hZS).inv_hom_id
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
    ModuleCat.hom_comp, ModuleCat.hom_id] at h
  exact (F.coe_supportedSubmoduleCompIso_hom_hom_app_apply hZS W _).symm.trans
    (congr_arg (fun t : F.supportedSubmodule Z W.unop ↦ t.1) (LinearMap.congr_fun h s))

/-- Forgetting scalars commutes with flattening iterated supported sections. This formulation
uses the canonical abelian inclusions, without choosing a second composition isomorphism. -/
@[reassoc]
lemma supportedSubmoduleCompIso_hom_forget_ι (hZS : Z ≤ S) :
    (sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).map
        (F.supportedSubmoduleCompIso hZS).hom ≫
        (F.supportedSubmoduleSheafForgetIso Z).hom ≫
        ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F).supportedSectionsι
          Z =
      ((F.supportedSubmoduleSheaf S).supportedSubmoduleSheafForgetIso Z).hom ≫
        ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj
          (F.supportedSubmoduleSheaf S)).supportedSectionsι Z ≫
        (F.supportedSubmoduleSheafForgetIso S).hom ≫
        ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F).supportedSectionsι
          S := by
  simp only [supportedSubmoduleSheafForgetIso_hom_ι,
    supportedSubmoduleSheafForgetIso_hom_ι_assoc, ← Functor.map_comp,
    supportedSubmoduleCompIso_hom_ι]

end

end CategoryTheory.Sheaf
