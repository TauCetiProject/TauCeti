/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.AlgebraicGeometry.Cohomology.OpenImmersion
import TauCeti.AlgebraicGeometry.Modules.Products
import TauCeti.AlgebraicGeometry.Modules.Pushforward.Basic
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Restriction
import TauCeti.AlgebraicGeometry.Modules.Restriction.Basic

/-!
# Modules prescribed on pairwise disjoint opens

Let `U j` be pairwise disjoint opens of a scheme `X`, indexed by a possibly infinite type, and
`F j` a module on each `U j`. The product `∏ⱼ (ι_j)_* F j` of the pushforwards along the inclusions
`ι_j : U j → X` (`TauCeti.AlgebraicGeometry.Scheme.Modules.disjointGlue`) restricts to `F j` on each
`U j` (`TauCeti.AlgebraicGeometry.Scheme.Modules.restrictDisjointGlueIso`): over an open inside
`U j`, every other factor has only the zero section. When the `U j` cover `X`, it is
quasicoherent as soon as every `F j` is
(`TauCeti.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_disjointGlue`), and its cohomology on
`U j` is the cohomology of `F j`
(`TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyOnDisjointGlueIso`).

This builds, on the disjoint union `⨿ₙ Xₙ`, a module that is a prescribed module on each component,
such as `O(-n-1)` on `ℙⁿ`, whose higher direct images along `⨿ₙ ℙⁿ → ⨿ₙ Spec k` are nonzero in
every degree.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped Function

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {J : Type u} (U : J → X.Opens) (F : ∀ j, (U j).toScheme.Modules)

/-- The module on `X` that is `F j` on each of the pairwise disjoint opens `U j`: the product of
the pushforwards of the `F j` along the inclusions `U j → X`. -/
def disjointGlue : X.Modules :=
  ∏ᶜ fun j ↦ (pushforward (U j).ι).obj (F j)

/-- Unfolding lemma for `disjointGlue`. -/
theorem disjointGlue_def :
    disjointGlue U F = ∏ᶜ fun j ↦ (pushforward (U j).ι).obj (F j) :=
  (rfl)

variable {U}

/-- Over `U j`, the projection of `disjointGlue U F` to the pushforward of `F j` is an isomorphism:
every other factor has only the zero section over an open inside `U j`. -/
theorem isIso_restrictFunctor_map_π_disjointGlue (hdisj : Pairwise (Disjoint on U)) (j : J) :
    IsIso ((restrictFunctor (U j).ι).map
      (Pi.π (fun i ↦ (pushforward (U i).ι).obj (F i)) j)) := by
  refine isIso_restrictFunctor_map_of_isIso_app _ (U j) fun V hV ↦ ?_
  refine (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_app_π_of_subsingleton _ j V ?_)
  intro i hij
  exact subsingleton_sections_pushforward_of_disjoint _ ((hdisj hij).symm.mono_left hV)

/-- The restriction of `disjointGlue U F` to `U j` is `F j`. -/
def restrictDisjointGlueIso (hdisj : Pairwise (Disjoint on U)) (j : J) :
    (disjointGlue U F).restrict (U j).ι ≅ F j :=
  @asIso _ _ _ _ ((restrictFunctor (U j).ι).map (Pi.π (fun i ↦ (pushforward (U i).ι).obj (F i)) j))
      (isIso_restrictFunctor_map_π_disjointGlue F hdisj j) ≪≫
    asIso ((restrictAdjunction (U j).ι).counit.app (F j))

/-- When the pairwise disjoint opens `U j` cover `X` and every `F j` is quasicoherent,
`disjointGlue U F` is quasicoherent. -/
theorem isQuasicoherent_disjointGlue (hdisj : Pairwise (Disjoint on U)) (hcover : ⨆ j, U j = ⊤)
    [∀ j, (F j).IsQuasicoherent] : (disjointGlue U F).IsQuasicoherent :=
  ((disjointGlue U F).isQuasicoherent_iff_of_iSup_eq_top U hcover).2 fun j ↦
    (SheafOfModules.isQuasicoherent (U j).toScheme.ringCatSheaf).prop_of_iso
      (restrictDisjointGlueIso F hdisj j).symm inferInstance

/-- The cohomology of `disjointGlue U F` on `U j` is the cohomology of `F j`. -/
def cohomologyOnDisjointGlueIso (hdisj : Pairwise (Disjoint on U)) (j : J) (n : ℕ) :
    cohomologyOn (disjointGlue U F) n (U j) ≅ (cohomologyFunctor (U j).toScheme n).obj (F j) :=
  eqToIso (by rw [Scheme.Opens.opensRange_ι]) ≪≫
    cohomologyOnOpensRangeIso (U j).ι (disjointGlue U F) n ≪≫
      (cohomologyFunctor (U j).toScheme n).mapIso (restrictDisjointGlueIso F hdisj j)

end TauCeti.AlgebraicGeometry.Scheme.Modules
