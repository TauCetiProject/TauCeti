/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.ExteriorPower.Basic

/-!
# Pullback of exterior powers of free sheaves

The exterior power of a finite free sheaf is free on the subsets indexing its wedge basis.
Pullback preserves this description, providing the chart comparison for pullback compatibility
of exterior powers of finite locally free sheaves.
-/

public section

open CategoryTheory

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

universe u

open _root_.AlgebraicGeometry

variable {X Y : _root_.AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

/-- Pullback commutes with exterior powers of a finite free sheaf, by identifying both sides with
the free sheaf on subsets of the chosen basis. -/
noncomputable def pullbackExteriorPowerFreeIso (I : Type u) [Finite I] (n : ℕ) :
    (pullback f).obj ((exteriorPower Y n).obj (free Y I)) ≅
      (exteriorPower X n).obj ((pullback f).obj (free Y I)) := by
  classical
  let _ : LinearOrder I := linearOrderOfSTO WellOrderingRel
  exact ((pullback f).mapIso (exteriorPowerFreeIso Y I n) ≪≫
      pullbackFreeIso f (Set.powersetCard I n)) ≪≫
    ((exteriorPower X n).mapIso (pullbackFreeIso f I) ≪≫
      exteriorPowerFreeIso X I n).symm

/-- The forward map of the pullback comparison is the composite of the free-sheaf
identifications on both sides. -/
theorem pullbackExteriorPowerFreeIso_hom (I : Type u) [Finite I] (n : ℕ) :
    (pullbackExteriorPowerFreeIso f I n).hom =
      (let _ : LinearOrder I := by classical exact linearOrderOfSTO WellOrderingRel
       (((pullback f).mapIso (exteriorPowerFreeIso Y I n) ≪≫
           pullbackFreeIso f (Set.powersetCard I n)) ≪≫
         ((exteriorPower X n).mapIso (pullbackFreeIso f I) ≪≫
           exteriorPowerFreeIso X I n).symm).hom) := by
  classical
  rfl

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

end
