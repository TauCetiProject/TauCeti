/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Torsion
public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.EvenSublattice.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Bilinear
public import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Form
public import TauCeti.NumberTheory.IntegralLattice.Localization.Sublattice

/-!
# Localized discriminant form of the even sublattice

At an odd prime `p` and for a nondegenerate lattice `L`, the inclusion `L.evenSublattice ⊆ L` has
index dividing `2`, which is coprime to `p`, so it induces an isometry of `ℤ_p`-localizations and
hence an isometry between the `p`-primary discriminant bilinear modules of `L.evenSublattice` and
`L`.

## Main declarations

* `TauCeti.IntegralLattice.evenSublatticePrimaryBilinearIsometry`: at an odd prime `p`, for a
  nondegenerate lattice `L`, the `p`-primary component of the discriminant bilinear module of
  `L.evenSublattice` is isometric to that of `L`.
* `TauCeti.IntegralLattice.evenSublatticePrimaryBilinearIsometry_eq`: identification of
  `evenSublatticePrimaryBilinearIsometry` with `primaryDiscriminantBilinearIsometry` of the
  localized inclusion.
-/

public section

open AddCommGroup

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- At an odd prime `p`, for a nondegenerate lattice `L`, the `p`-primary component of the
discriminant bilinear module of `L.evenSublattice` is isometric to that of `L`. -/
noncomputable def evenSublatticePrimaryBilinearIsometry
    (L : IntegralLattice V) [L.IsNondegenerate] {p : ℕ} [Fact p.Prime] (hp : Odd p) :
    FiniteBilinearModule.Isometry
      (L.evenSublattice.discriminantBilinearModule.restrict
        (primaryComponent L.evenSublattice.discriminantBilinearModule p))
      (L.discriminantBilinearModule.restrict
        (primaryComponent L.discriminantBilinearModule p)) :=
  primaryDiscriminantBilinearIsometry
    (L.evenSublattice.localInclusionIsometryEquiv L p L.evenSublattice_form
      L.evenSublattice_carrier_le
      (L.not_dvd_relIndex_evenSublattice_of_odd hp (Fact.out : p.Prime).ne_one))

/-- `evenSublatticePrimaryBilinearIsometry` is `primaryDiscriminantBilinearIsometry` applied to the
localized inclusion `L.evenSublattice ⊆ L`. -/
theorem evenSublatticePrimaryBilinearIsometry_eq
    (L : IntegralLattice V) [L.IsNondegenerate] {p : ℕ} [Fact p.Prime] (hp : Odd p) :
    evenSublatticePrimaryBilinearIsometry L hp =
      primaryDiscriminantBilinearIsometry
        (L.evenSublattice.localInclusionIsometryEquiv L p L.evenSublattice_form
          L.evenSublattice_carrier_le
          (L.not_dvd_relIndex_evenSublattice_of_odd hp (Fact.out : p.Prime).ne_one)) := by
  rw [evenSublatticePrimaryBilinearIsometry]

end TauCeti.IntegralLattice
