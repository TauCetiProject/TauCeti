/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Abelian.ShortExact

/-!
# Exactness of the forgetful functor to sheaves of `R`-modules on `Spec R`

For a commutative ring `R`, Mathlib's `AlgebraicGeometry.modulesSpecToSheaf` forgets the
`𝒪_{Spec R}`-module structure on an `𝒪_{Spec R}`-module to produce a sheaf of `R`-modules on
`Spec R`. Forgetting further down to sheaves of abelian groups recovers
`TauCeti.AlgebraicGeometry.Scheme.Modules.toSheaf (Spec R)`, which is additive and exact. Since the
forgetful functor from sheaves of `R`-modules to sheaves of abelian groups is faithful and reflects
short exact sequences, `modulesSpecToSheaf` is additive and exact as well.

## Main declarations

* `TauCeti.AlgebraicGeometry.modulesSpecToSheafCompForgetIso`: forgetting `R`-module structures
  after `modulesSpecToSheaf` recovers `Scheme.Modules.toSheaf`.
* `TauCeti.AlgebraicGeometry.additive_modulesSpecToSheaf`,
  `TauCeti.AlgebraicGeometry.shortExact_map_modulesSpecToSheaf`,
  `TauCeti.AlgebraicGeometry.preservesFiniteLimits_modulesSpecToSheaf`, and
  `TauCeti.AlgebraicGeometry.preservesFiniteColimits_modulesSpecToSheaf`: additivity and exactness
  of `modulesSpecToSheaf`.
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {R : CommRingCat.{u}}

/-- `modulesSpecToSheaf` is additive: addition of module-sheaf morphisms is sectionwise. -/
instance additive_modulesSpecToSheaf : (modulesSpecToSheaf (R := R)).Additive where
  map_add {_ _ _ _} := by
    ext
    rfl

/-- Forgetting `R`-module structures after `modulesSpecToSheaf` recovers
`Scheme.Modules.toSheaf`. -/
def modulesSpecToSheafCompForgetIso (R : CommRingCat.{u}) :
    modulesSpecToSheaf (R := R) ⋙
        sheafCompose (Opens.grothendieckTopology (Spec R))
          (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) ≅
      Scheme.Modules.toSheaf (Spec R) :=
  NatIso.ofComponents
    (fun _ ↦ ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl))
    fun _ ↦ by ext; rfl

/-- `modulesSpecToSheafCompForgetIso` is the identity on sections over each open set. -/
@[simp]
lemma modulesSpecToSheafCompForgetIso_hom_app_apply (N : (Spec R).Modules)
    (U : (TopologicalSpace.Opens (Spec R))ᵒᵖ)
    (x : ((modulesSpecToSheaf (R := R)).obj N).obj.obj U) :
    dsimp% only [sheafCompose_obj_obj, CategoryTheory.Functor.comp_obj, ModuleCat.forget₂_obj]
    (((modulesSpecToSheafCompForgetIso R).hom.app N).hom.app U x = x) :=
  (rfl)

/-- The inverse of `modulesSpecToSheafCompForgetIso` is the identity on sections over each open
set. -/
@[simp]
lemma modulesSpecToSheafCompForgetIso_inv_app_apply (N : (Spec R).Modules)
    (U : (TopologicalSpace.Opens (Spec R))ᵒᵖ)
    (x : ((Scheme.Modules.toSheaf (Spec R)).obj N).obj.obj U) :
    dsimp% only [sheafCompose_obj_obj, CategoryTheory.Functor.comp_obj, ModuleCat.forget₂_obj]
    (((modulesSpecToSheafCompForgetIso R).inv.app N).hom.app U x = x) :=
  (rfl)

/-- `modulesSpecToSheaf` preserves short exact sequences, checked on underlying abelian sheaves. -/
theorem shortExact_map_modulesSpecToSheaf {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact) :
    (S.map (modulesSpecToSheaf (R := R))).ShortExact := by
  apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful
    (sheafCompose (Opens.grothendieckTopology (Spec R))
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}))
  rw [← ShortComplex.map_comp]
  exact (ShortComplex.shortExact_iff_of_iso
    (S.mapNatIso (modulesSpecToSheafCompForgetIso R).symm)).2
      (Scheme.Modules.shortExact_map_toSheaf hS)

/-- `modulesSpecToSheaf` preserves finite limits. -/
instance preservesFiniteLimits_modulesSpecToSheaf :
    PreservesFiniteLimits (modulesSpecToSheaf (R := R)) := by
  rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  exact fun _ hS ↦ ⟨(shortExact_map_modulesSpecToSheaf hS).exact,
    (shortExact_map_modulesSpecToSheaf hS).mono_f⟩

/-- `modulesSpecToSheaf` preserves finite colimits. -/
instance preservesFiniteColimits_modulesSpecToSheaf :
    PreservesFiniteColimits (modulesSpecToSheaf (R := R)) := by
  rw [Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi]
  exact fun _ hS ↦ ⟨(shortExact_map_modulesSpecToSheaf hS).exact,
    (shortExact_map_modulesSpecToSheaf hS).epi_g⟩

end

end TauCeti.AlgebraicGeometry
