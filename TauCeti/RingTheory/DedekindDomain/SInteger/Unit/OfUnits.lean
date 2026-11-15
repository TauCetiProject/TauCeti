/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.SInteger.Unit

/-!
# Units of a Dedekind domain as `S`-units

Let `R` be a Dedekind domain with fraction field `K`. Every unit of `R` is an `S`-unit, for any
set `S` of height-one primes of `R`. This module records the resulting canonical homomorphism
`TauCeti.SUnit.unitOfUnits S K : Rˣ →* S.unit K`, the composite of `Set.unitEmptyEquivUnits` with
the inclusion `Set.unit_mono` of the `∅`-units in the `S`-units.

For `R` the ring of integers of a number field, it is the inclusion used to compare Dirichlet's
logarithmic embedding of ordinary units with the logarithmic embedding of `S`-units.
-/

public noncomputable section

open IsDedekindDomain

namespace TauCeti.SUnit

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (S : Set (HeightOneSpectrum R)) (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The canonical homomorphism from the units of a Dedekind domain to the `S`-units of its
fraction field. -/
def unitOfUnits : Rˣ →* S.unit K :=
  (Subgroup.inclusion (Set.unit_mono K (Set.empty_subset S))).comp
    (Set.unitEmptyEquivUnits K).symm.toMonoidHom

/-- The underlying element of `K` of the `S`-unit attached to a unit `u` of `R` is the image of
`u` under the algebra map `R → K`. -/
theorem val_unitOfUnits (u : Rˣ) :
    (((unitOfUnits S K u : S.unit K) : Kˣ) : K) = algebraMap R K (u : R) := by
  rw [unitOfUnits, MonoidHom.comp_apply, Subgroup.coe_inclusion]
  simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using
    (Set.algebraMap_unitEmptyEquivUnits_apply K
      ((Set.unitEmptyEquivUnits K).symm u)).symm

/-- As a unit of `K`, the `S`-unit attached to a unit `u` of `R` is the image of `u` under the
map of unit groups induced by the algebra map `R → K`. -/
@[simp]
theorem coe_unitOfUnits (u : Rˣ) :
    ((unitOfUnits S K u : S.unit K) : Kˣ) = Units.map (algebraMap R K) u := by
  apply Units.ext
  exact val_unitOfUnits S K u

end TauCeti.SUnit
