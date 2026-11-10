/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Global sections of the functor induced on sheaves

On a site with a terminal object, applying any functor `F` to global sections agrees with taking
global sections of the sheaf `sheafCompose J F` (`CategoryTheory.Sheaf.ΓCompIsoSheafComposeCompΓ`),
since both are the sections over the terminal object. For instance, the global sections of a sheaf
of `R`-modules with its module structure forgotten sectionwise are the underlying abelian group of
its global sections.
-/

public section

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) {A B : Type*} [Category* A]
  [Category* B]

variable (F : A ⥤ B) [J.HasSheafCompose F] [HasWeakSheafify J A] [HasWeakSheafify J B]
  [HasTerminal C] {T : C} (hT : IsTerminal T)

/-- On a site with a terminal object, applying a functor `F` to global sections agrees with taking
global sections of the sheaf obtained by applying `F` sectionwise. -/
noncomputable def ΓCompIsoSheafComposeCompΓ : Γ J A ⋙ F ≅ sheafCompose J F ⋙ Γ J B :=
  Functor.isoWhiskerRight (ΓNatIsoSheafSections J A hT) F ≪≫
    -- the sections over `T` of the sectionwise composite with `F` are `F` of the sections
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp) ≪≫
    Functor.isoWhiskerLeft (sheafCompose J F) (ΓNatIsoSheafSections J B hT).symm

end CategoryTheory.Sheaf
