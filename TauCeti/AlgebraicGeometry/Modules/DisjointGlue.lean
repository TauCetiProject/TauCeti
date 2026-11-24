/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import TauCeti.AlgebraicGeometry.Modules.Products
import TauCeti.AlgebraicGeometry.Modules.Pushforward.Basic
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Restriction
import TauCeti.AlgebraicGeometry.Modules.Restriction.Basic

/-!
# Modules prescribed on pairwise disjoint opens

Let `U j` be opens of a scheme `X`, indexed by a possibly infinite type, and `F j` a module on
each `U j`. The product `∏ⱼ (ι_j)_* F j` of the pushforwards along the inclusions
`ι_j : U j → X` (`TauCeti.AlgebraicGeometry.Scheme.Modules.disjointGlue`) comes with projections
`TauCeti.AlgebraicGeometry.Scheme.Modules.disjointGlue.π`, a lift
`TauCeti.AlgebraicGeometry.Scheme.Modules.disjointGlue.lift` and the universal property
`TauCeti.AlgebraicGeometry.Scheme.Modules.disjointGlue.isLimit`. When the `U j` are pairwise
disjoint, it restricts to `F j` on each `U j`
(`TauCeti.AlgebraicGeometry.Scheme.Modules.restrictDisjointGlueIso`): over an open inside `U j`,
every other factor has only the zero section. When the `U j` moreover cover `X`, it is
quasicoherent as soon as every `F j` is
(`TauCeti.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_disjointGlue`).

This is meant for modules on a disjoint union `⨿ₙ Xₙ` prescribed componentwise, such as
`O(-n-1)` on `ℙⁿ`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped Function

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {J : Type u} (U : J → X.Opens) (F : ∀ j, (U j).toScheme.Modules)

/-- The product of the pushforwards of the `F j` along the inclusions `U j → X`. When the `U j` are
pairwise disjoint, it restricts to `F j` on each `U j` (`restrictDisjointGlueIso`). -/
def disjointGlue : X.Modules :=
  ∏ᶜ fun j ↦ (pushforward (U j).ι).obj (F j)

/-- Unfolding lemma for `disjointGlue`. -/
theorem disjointGlue_def :
    disjointGlue U F = ∏ᶜ fun j ↦ (pushforward (U j).ι).obj (F j) :=
  (rfl)

/-- The projection of `disjointGlue U F` to the pushforward of `F j`. -/
def disjointGlue.π (j : J) : disjointGlue U F ⟶ (pushforward (U j).ι).obj (F j) :=
  Pi.π (fun i ↦ (pushforward (U i).ι).obj (F i)) j

/-- The morphism into `disjointGlue U F` with prescribed projections. -/
def disjointGlue.lift {M : X.Modules} (g : ∀ j, M ⟶ (pushforward (U j).ι).obj (F j)) :
    M ⟶ disjointGlue U F :=
  Pi.lift g

/-- The lift into `disjointGlue U F` has the prescribed projections. -/
@[reassoc (attr := simp)]
theorem disjointGlue.lift_π {M : X.Modules} (g : ∀ j, M ⟶ (pushforward (U j).ι).obj (F j))
    (j : J) : disjointGlue.lift U F g ≫ disjointGlue.π U F j = g j :=
  Pi.lift_comp_π g j

/-- Morphisms into `disjointGlue U F` agreeing after every projection are equal. -/
@[ext]
theorem disjointGlue.hom_ext {M : X.Modules} {g h : M ⟶ disjointGlue U F}
    (w : ∀ j, g ≫ disjointGlue.π U F j = h ≫ disjointGlue.π U F j) : g = h :=
  Pi.hom_ext g h w

/-- `disjointGlue U F` with its projections is a product of the pushforwards of the `F j`. -/
def disjointGlue.isLimit : IsLimit (Fan.mk (disjointGlue U F) (disjointGlue.π U F)) :=
  productIsProduct fun j ↦ (pushforward (U j).ι).obj (F j)

variable {U}

/-- Over `U j`, the projection of `disjointGlue U F` to the pushforward of `F j` is an isomorphism:
every other factor has only the zero section over an open inside `U j`. -/
theorem isIso_restrictFunctor_map_π_disjointGlue (hdisj : Pairwise (Disjoint on U)) (j : J) :
    IsIso ((restrictFunctor (U j).ι).map (disjointGlue.π U F j)) := by
  refine isIso_restrictFunctor_map_of_isIso_app _ (U j) fun V hV ↦ ?_
  refine (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_app_π_of_subsingleton _ j V ?_)
  intro i hij
  exact subsingleton_sections_pushforward_of_disjoint _ ((hdisj hij).symm.mono_left hV)

/-- The restriction of `disjointGlue U F` to `U j` is `F j`. -/
def restrictDisjointGlueIso (hdisj : Pairwise (Disjoint on U)) (j : J) :
    (disjointGlue U F).restrict (U j).ι ≅ F j :=
  @asIso _ _ _ _ ((restrictFunctor (U j).ι).map (disjointGlue.π U F j))
      (isIso_restrictFunctor_map_π_disjointGlue F hdisj j) ≪≫
    asIso ((restrictAdjunction (U j).ι).counit.app (F j))

/-- The identification of the restriction of `disjointGlue U F` to `U j` with `F j` is the
restricted projection followed by the counit of the restriction adjunction. -/
@[simp]
theorem restrictDisjointGlueIso_hom (hdisj : Pairwise (Disjoint on U)) (j : J) :
    (restrictDisjointGlueIso F hdisj j).hom =
      (restrictFunctor (U j).ι).map (disjointGlue.π U F j) ≫
        (restrictAdjunction (U j).ι).counit.app (F j) := by
  simp [restrictDisjointGlueIso]

/-- When the pairwise disjoint opens `U j` cover `X` and every `F j` is quasicoherent,
`disjointGlue U F` is quasicoherent. -/
theorem isQuasicoherent_disjointGlue (hdisj : Pairwise (Disjoint on U)) (hcover : ⨆ j, U j = ⊤)
    [∀ j, (F j).IsQuasicoherent] : (disjointGlue U F).IsQuasicoherent :=
  ((disjointGlue U F).isQuasicoherent_iff_of_iSup_eq_top U hcover).2 fun j ↦
    (SheafOfModules.isQuasicoherent (U j).toScheme.ringCatSheaf).prop_of_iso
      (restrictDisjointGlueIso F hdisj j).symm inferInstance

end TauCeti.AlgebraicGeometry.Scheme.Modules
