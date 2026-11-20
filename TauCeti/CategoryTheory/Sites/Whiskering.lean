/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# The functor induced on sheaves: additivity and global sections

An additive functor `F : A ⥤ B` between preadditive categories induces an additive functor
`sheafCompose J F : Sheaf J A ⥤ Sheaf J B` (`CategoryTheory.Sheaf.additive_sheafCompose`), since
morphisms of sheaves are added sectionwise. For instance, forgetting the module structure of a
sheaf of `R`-modules sectionwise is additive, so it acts on complexes of sheaves.

On a site with a terminal object, applying any functor `F` to global sections agrees with taking
global sections of the sheaf `sheafCompose J F` (`CategoryTheory.Sheaf.ΓCompIsoSheafComposeCompΓ`),
since both are the sections over the terminal object
(`CategoryTheory.Sheaf.ΓCompIsoSheafComposeCompΓ_hom_app`).
-/

public section

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) {A B : Type*} [Category* A]
  [Category* B]

section Additive

variable [Preadditive A] [Preadditive B] (F : A ⥤ B) [F.Additive] [J.HasSheafCompose F]

/-- The functor induced on sheaves by an additive functor is additive. -/
instance additive_sheafCompose : (sheafCompose J F).Additive := by
  unfold sheafCompose
  infer_instance

end Additive

variable (F : A ⥤ B) [J.HasSheafCompose F] [HasWeakSheafify J A] [HasWeakSheafify J B]
  [HasTerminal C] {T : C} (hT : IsTerminal T)

/-- On a site with a terminal object, applying a functor `F` to global sections agrees with taking
global sections of the sheaf obtained by applying `F` sectionwise. -/
noncomputable def ΓCompIsoSheafComposeCompΓ : Γ J A ⋙ F ≅ sheafCompose J F ⋙ Γ J B :=
  Functor.isoWhiskerRight (ΓNatIsoSheafSections J A hT) F ≪≫
    -- the sections over `T` of the sectionwise composite with `F` are `F` of the sections
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp) ≪≫
    Functor.isoWhiskerLeft (sheafCompose J F) (ΓNatIsoSheafSections J B hT).symm

/-- The comparison `ΓCompIsoSheafComposeCompΓ` is `F` applied to the identification of global
sections with sections over the terminal object `T`, followed by the inverse identification for
the sheaf `sheafCompose J F`. -/
lemma ΓCompIsoSheafComposeCompΓ_hom_app (G : Sheaf J A) :
    (ΓCompIsoSheafComposeCompΓ J F hT).hom.app G =
      F.map ((ΓNatIsoSheafSections J A hT).hom.app G) ≫
        (ΓNatIsoSheafSections J B hT).inv.app ((sheafCompose J F).obj G) := by
  dsimp only [ΓCompIsoSheafComposeCompΓ, Iso.trans_hom, NatTrans.comp_app]
  -- the middle comparison has identity components; its source and target functors agree with
  -- those of its neighbours only after unfolding, so its composite is split with `erw`
  erw [NatTrans.comp_app]
  simp only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    NatIso.ofComponents_hom_app, Iso.refl_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app]
  exact congrArg (F.map ((ΓNatIsoSheafSections J A hT).hom.app G) ≫ ·) (Category.id_comp _)

end CategoryTheory.Sheaf
