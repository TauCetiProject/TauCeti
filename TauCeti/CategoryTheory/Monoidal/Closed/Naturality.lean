/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Closed.Functor
import TauCeti.CategoryTheory.Monoidal.Closed.Basic

/-!
# Naturality of internal-Hom comparisons in a monoidal functor

A natural transformation compatible with the tensor comparisons intertwines the canonical
internal-Hom comparisons, covariantly in the target and contravariantly in the source. For a
natural isomorphism, invertibility of either internal-Hom comparison therefore implies
invertibility of the other. Only the tensor compatibility at the source and its internal Hom
is needed; compatibility with the unit is unnecessary.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed

universe u₁ u₂ v₁ v₂

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- A natural transformation compatible with the tensor comparison intertwines the two
canonical internal-Hom comparisons. -/
theorem CategoryTheory.Functor.ihomComparison_app_comp_map
    (F G : C ⥤ D) [F.LaxMonoidal] [G.LaxMonoidal]
    (σ : F ⟶ G) (A B : C) [Closed A] [Closed (F.obj A)] [Closed (G.obj A)]
    (hμ : Functor.LaxMonoidal.μ F A ((ihom A).obj B) ≫
        σ.app (A ⊗ (ihom A).obj B) =
      (σ.app A ⊗ₘ σ.app ((ihom A).obj B)) ≫
        Functor.LaxMonoidal.μ G A ((ihom A).obj B)) :
    (F.ihomComparison A).app B ≫ (ihom (F.obj A)).map (σ.app B) =
      σ.app ((ihom A).obj B) ≫ (G.ihomComparison A).app B ≫
        (pre (σ.app A)).app (G.obj B) := by
  apply uncurry_injective
  rw [uncurry_natural_right, Functor.uncurry_ihomComparison,
    uncurry_natural_left, uncurry_pre_app, Functor.uncurry_ihomComparison,
    ← Category.assoc, ← tensorHom_def', ← reassoc_of% hμ, Category.assoc]
  exact congrArg (Functor.LaxMonoidal.μ F A ((ihom A).obj B) ≫ ·)
    (σ.naturality ((ihom.ev A).app B))

/-- A natural isomorphism preserving the relevant tensor comparison transports invertibility
of the canonical internal-Hom comparison. -/
theorem CategoryTheory.Functor.isIso_ihomComparison_app_iff_of_natIso
    (F G : C ⥤ D) [F.LaxMonoidal] [G.LaxMonoidal]
    (e : F ≅ G) (A B : C) [Closed A] [Closed (F.obj A)] [Closed (G.obj A)]
    (hμ : Functor.LaxMonoidal.μ F A ((ihom A).obj B) ≫
        e.hom.app (A ⊗ (ihom A).obj B) =
      (e.hom.app A ⊗ₘ e.hom.app ((ihom A).obj B)) ≫
        Functor.LaxMonoidal.μ G A ((ihom A).obj B)) :
    IsIso ((F.ihomComparison A).app B) ↔ IsIso ((G.ihomComparison A).app B) := by
  have hpre := pre_isIso (e.app A)
  have : IsIso ((pre (e.hom.app A)).app (G.obj B)) :=
    (NatTrans.isIso_iff_isIso_app _).mp hpre _
  have h := congrArg IsIso (F.ihomComparison_app_comp_map G e.hom A B hμ)
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using Iff.of_eq h

end
