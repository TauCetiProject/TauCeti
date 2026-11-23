/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Sheafified postcomposition commutes with sheaf pullback

Let `G : A ⥤ B` be a left adjoint, with right adjoint `R`, and let `Φ : C ⥤ D` be a continuous
functor from a site `(C, J)` to a site `(D, K)` whose sheaf pushforwards `Φ_*` admit left adjoints
`Φ^*` for both coefficient categories. The sheafified composite with `G`,
`Sheaf.composeAndSheafify J G`, commutes with the sheaf pullback `Φ^*`
(`CategoryTheory.Functor.composeAndSheafifyCompSheafPullbackIso`). Both composites are left
adjoint to the composite of `Φ_*` and `sheafCompose R`, which act by composition of presheaves on
different sides and so commute on the nose; the isomorphism is the uniqueness of left adjoints.
It is characterized by its compatibility with the units of the two adjunctions
(`CategoryTheory.Functor.unit_composeAndSheafifyCompSheafPullbackIso_hom_app`).
-/

public section

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] {J : GrothendieckTopology C}
  {K : GrothendieckTopology D} (Φ : C ⥤ D) [Φ.IsContinuous J K] {A B : Type*} [Category* A]
  [Category* B] {G : A ⥤ B} {R : B ⥤ A} (adj : G ⊣ R) [HasWeakSheafify J B]
  [HasWeakSheafify K B] [J.HasSheafCompose R] [K.HasSheafCompose R]
  [(Φ.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [(Φ.sheafPushforwardContinuous B J K).IsRightAdjoint]

/-- The sheafified composite with a left adjoint `G` commutes with the sheaf pullback along a
continuous functor `Φ`. Both composites are left adjoint to the composite of `sheafCompose R` and
the sheaf pushforward `Φ_*`, which act by composition of presheaves and so commute. -/
noncomputable def composeAndSheafifyCompSheafPullbackIso :
    Sheaf.composeAndSheafify J G ⋙ Φ.sheafPullback B J K ≅
      Φ.sheafPullback A J K ⋙ Sheaf.composeAndSheafify K G :=
  ((Sheaf.adjunction J adj).comp (Φ.sheafAdjunctionContinuous B J K)).leftAdjointUniq
    (((Φ.sheafAdjunctionContinuous A J K).comp (Sheaf.adjunction K adj)).ofNatIsoRight
      (Iso.refl _))

/-- `composeAndSheafifyCompSheafPullbackIso` is compatible with the units of the two adjunctions
`Φ^* ∘ G ⊣ R ∘ Φ_*` and `G ∘ Φ^* ⊣ Φ_* ∘ R`, whose right adjoints agree. -/
@[reassoc]
lemma unit_composeAndSheafifyCompSheafPullbackIso_hom_app (F : Sheaf J A) :
    ((Sheaf.adjunction J adj).comp (Φ.sheafAdjunctionContinuous B J K)).unit.app F ≫
        (Φ.sheafPushforwardContinuous B J K ⋙ sheafCompose J R).map
          ((Φ.composeAndSheafifyCompSheafPullbackIso adj).hom.app F) =
      ((Φ.sheafAdjunctionContinuous A J K).comp (Sheaf.adjunction K adj)).unit.app F := by
  rw [composeAndSheafifyCompSheafPullbackIso, Adjunction.unit_leftAdjointUniq_hom_app]
  exact Category.comp_id _

end CategoryTheory.Functor
