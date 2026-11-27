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
import TauCeti.RingTheory.Depth.Basic

/-!
# Depth of the stalk of a scheme module

`Scheme.Modules.stalkDepth` is Mathlib's `IsLocalRing.depth` for a sheaf of modules at a point.
For a quasi-coherent module, `Scheme.Modules.stalkDepth_eq_depth_localizedModule` computes it on
an affine open, using `Scheme.Modules.isLocalizedModule_germₗ` and
`IsLocalRing.depth_eq_of_isLocalizedModule`.
-/

public section

open IsLocalRing

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}}

/-- The depth of the stalk of a module at a point, over the local ring of the scheme. -/
noncomputable def stalkDepth (F : X.Modules) (x : X) : ℕ∞ :=
  depth (ModuleCat.of (X.presheaf.stalk x) (F.presheaf.stalk x))

/-- The defining equation for stalk depth, expressed using the depth over the local ring. -/
@[simp]
theorem stalkDepth_def (F : X.Modules) (x : X) :
    F.stalkDepth x = depth (ModuleCat.of (X.presheaf.stalk x) (F.presheaf.stalk x)) := (rfl)

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
