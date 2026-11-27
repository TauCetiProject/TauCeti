/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.Depth.Basic
public import TauCeti.AlgebraicGeometry.Modules.Stalk
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Stalk
import TauCeti.Algebra.Category.ModuleCat.Presheaf.Stalk
import TauCeti.RingTheory.Depth.Basic

/-!
# Depth of the stalk of a scheme module

`Scheme.Modules.stalkDepth` is the depth of a module stalk over the local ring at a point.
It expresses the depth hypothesis in coherent Hartogs extension.
For a quasi-coherent module, `Scheme.Modules.stalkDepth_eq_depth_localizedModule` reduces
this condition on an affine open to the depth of the localized module of sections.
The formula follows from `Scheme.Modules.isLocalizedModule_germₗ` and
`IsLocalRing.depth_eq_of_isLocalizedModule`.
`Scheme.Modules.stalkDepth_congr` uses `IsLocalRing.depth_eq_of_iso` to transport stalk depth
across module isomorphisms. `Scheme.Modules.stalkDepth_unit` identifies the structure sheaf's
stalk depth with the depth of the local ring, using preservation of filtered
colimits by the forgetful functor to abelian groups.
-/

public section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}}

/-- The depth of the stalk of a module at a point, over the local ring of the scheme. -/
noncomputable def stalkDepth (F : X.Modules) (x : X) : ℕ∞ :=
  depth (ModuleCat.of (X.presheaf.stalk x) (F.presheaf.stalk x))

/-- The defining equation for stalk depth over the local ring. It permits explicit rewriting
while keeping the definition opaque to users of the stalk depth API. -/
theorem stalkDepth_def (F : X.Modules) (x : X) :
    F.stalkDepth x = depth (ModuleCat.of (X.presheaf.stalk x) (F.presheaf.stalk x)) := (rfl)

/-- Isomorphic scheme modules have the same stalk depth at every point. -/
theorem stalkDepth_congr {F G : X.Modules} (e : F ≅ G) (x : X) :
    F.stalkDepth x = G.stalkDepth x := by
  rw [stalkDepth_def, stalkDepth_def]
  exact depth_eq_of_iso
    (PresheafOfModules.stalkLinearEquivCommRing x ((toPresheafOfModules X).mapIso e)).toModuleIso

/-- The stalk depth of the structure sheaf is the depth of the local ring at the point. -/
@[simp]
theorem stalkDepth_unit (x : X) :
    stalkDepth (SheafOfModules.unit X.ringCatSheaf) x =
      depth (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)) := by
  let F : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let forgetRing := forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}
  let diagram := (OpenNhds.inclusion x).op ⋙ X.presheaf
  let e : AddCommGrpCat.of (X.presheaf.stalk x) ≅ F.presheaf.stalk x :=
    preservesColimitIso forgetRing diagram
  have hgerm (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)) :
      e.hom (X.presheaf.germ U x hx r) = F.presheaf.germ U x hx r := by
    -- The unit module's underlying presheaf is the structure presheaf with scalars forgotten.
    exact ConcreteCategory.congr_hom
      (ι_preservesColimitIso_hom forgetRing diagram (op (⟨U, hx⟩ : OpenNhds x))) r
  have hsmul (a m : X.presheaf.stalk x) : e.hom (a • m) = a • e.hom m := by
    obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq a
    obtain ⟨V, hVU, hxV, s, rfl⟩ := X.presheaf.exists_le_germ_eq m hxU
    rw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV r, smul_eq_mul, ← map_mul, hgerm, hgerm]
    exact F.germ_smul x V hxV (X.presheaf.map (homOfLE hVU).op r) s
  let he := e.addCommGroupIsoToAddEquiv.toLinearEquiv hsmul
  exact (stalkDepth_def F x).trans (depth_eq_of_iso he.symm.toModuleIso)

/-- On an affine open, the stalk depth of a quasi-coherent module is the depth of the module of
sections localized at the prime corresponding to the point. -/
theorem stalkDepth_eq_depth_localizedModule (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens}
    (hV : IsAffineOpen V) (x : V) :
    F.stalkDepth x = depth (ModuleCat.of (Localization.AtPrime (hV.primeIdealOf x).asIdeal)
      (LocalizedModule (hV.primeIdealOf x).asIdeal.primeCompl Γ(F, V))) := by
  let := X.presheaf.algebra_section_stalk x
  let := F.moduleSectionStalk x
  let := F.isScalarTower_sectionStalk x
  have := hV.isLocalization_stalk x
  have := F.isLocalizedModule_germₗ x hV
  rw [stalkDepth_def]
  exact depth_eq_of_isLocalizedModule (hV.primeIdealOf x).asIdeal (X.presheaf.stalk x) (F.germₗ x)

end AlgebraicGeometry.Scheme.Modules
