/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import TauCeti.CategoryTheory.Sites.ConstantSheaf

/-!
# Global sections: additivity, linearity and the terminal restriction

Global sections are additive for abelian coefficients: constant sheaves are additive and
additivity passes to the right adjoint (`CategoryTheory.Sheaf.additive_Γ`). The canonical
identification with sections at a terminal object is the actual global-section restriction map,
with its inverse cancellation formula.

For a linear category `A` of coefficients, the category of `A`-valued sheaves on a site is linear,
as a full subcategory of the linear category of presheaves. On a site with a terminal object `T`,
the global sections functor `Sheaf.Γ` is isomorphic to evaluation at `T`
(`CategoryTheory.Sheaf.ΓNatIsoSheafSections`), so it is linear
(`CategoryTheory.Sheaf.linear_Γ`). For sheaves of `R`-modules this says that the `R`-module
structure on global sections is the one induced by the scalar endomorphisms of the sheaf, and it
makes the right derived functors of global sections `R`-linear.
-/

public noncomputable section

open CategoryTheory Limits Opposite

universe u v u' v'

namespace CategoryTheory.Sheaf
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v'} A]
/-- Global sections with abelian coefficients are additive by the constant-sheaf adjunction. -/
instance additive_Γ [Abelian A] [HasSheafify J A] [HasGlobalSectionsFunctor J A] :
    (Γ J A).Additive :=
  (constantSheafΓAdj J A).right_adjoint_additive
end CategoryTheory.Sheaf

namespace CategoryTheory.Sheaf
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v'} A] [HasWeakSheafify J A] [HasTerminal C]
/-- The global-sections identification is the native restriction to the terminal object. -/
@[simp]
lemma ΓNatIsoSheafSections_hom_app_eq_ΓRes {T : C} (hT : IsTerminal T) (F : Sheaf J A) :
    (Sheaf.ΓNatIsoSheafSections J A hT).hom.app F = F.ΓRes (op T) := by
  have h := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app
    (constantSheafΓAdj J A) (constantSheafAdj J A hT) F
  rw [Equiv.symm_apply_eq] at h
  refine h.trans ?_
  rw [constantSheafAdj_homEquiv_apply]
  -- The global-sections cone is the adjunction counit viewed as a presheaf map.
  change (((sheafificationAdjunction J A).homEquiv _ _)
    ((constantSheafΓAdj J A).counit.app F)).app (op T) =
    (((sheafificationAdjunction J A).homEquiv _ _)
      (((constantSheafΓAdj J A).homEquiv _ _).symm (𝟙 _))).app (op T)
  rw [Adjunction.homEquiv_counit, CategoryTheory.Functor.map_id, Category.id_comp]
  -- The identity functor on sheaves has object `F`.
  dsimp only [Functor.id_obj]
/-- Restriction to a terminal object is the canonical identification of global sections. -/
lemma natTransΓRes_eq_ΓNatIsoSheafSections_hom {T : C} (hT : IsTerminal T) :
    Sheaf.natTransΓRes J A (op T) = (Sheaf.ΓNatIsoSheafSections J A hT).hom := by
  apply NatTrans.ext
  funext F
  exact (ΓNatIsoSheafSections_hom_app_eq_ΓRes J A hT F).symm

/-- Terminal restriction followed by the inverse comparison is the identity. -/
@[reassoc (attr := simp)]
lemma ΓRes_ΓNatIsoSheafSections_inv_app {T : C} (hT : IsTerminal T) (F : Sheaf J A) :
    F.ΓRes (op T) ≫ (ΓNatIsoSheafSections J A hT).inv.app F = 𝟙 _ := by
  rw [← ΓNatIsoSheafSections_hom_app_eq_ΓRes J A hT F]
  exact (ΓNatIsoSheafSections J A hT).hom_inv_id_app F

/-- Restriction cancels the inverse terminal global-sections comparison. -/
@[reassoc (attr := simp)]
lemma ΓNatIsoSheafSections_inv_app_ΓRes {T : C} (hT : IsTerminal T) (F : Sheaf J A) :
    (ΓNatIsoSheafSections J A hT).inv.app F ≫ F.ΓRes (op T) = 𝟙 _ := by
  rw [← ΓNatIsoSheafSections_hom_app_eq_ΓRes J A hT F]
  exact (ΓNatIsoSheafSections J A hT).inv_hom_id_app F

end CategoryTheory.Sheaf

namespace CategoryTheory
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v'} A] [Preadditive A]
/-- Evaluation of sheaves is additive, by the underlying-presheaf and evaluation functors. -/
instance sheafSections_additive (T : Cᵒᵖ) : ((sheafSections J A).obj T).Additive :=
  inferInstanceAs (sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj T).Additive
end CategoryTheory

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) (R : Type*) [Semiring R]
  (A : Type*) [Category* A] [Preadditive A] [Linear R A] [HasWeakSheafify J A] [HasTerminal C]

/-- On a site with a terminal object, the global sections functor is linear. -/
instance linear_Γ : (Γ J A).Linear R where
  map_smul {F G} f a := by
    let e := ΓNatIsoSheafSections J A terminalIsTerminal
    -- scalar multiplication of sheaf morphisms is that of the underlying presheaf morphisms
    have h : (a • f).hom = a • f.hom :=
      (sheafToPresheaf J A).map_smul a f
    rw [← cancel_mono (e.hom.app G), e.hom.naturality, Linear.smul_comp, e.hom.naturality]
    simp [h, NatTrans.app_smul, Linear.comp_smul]

end CategoryTheory.Sheaf
