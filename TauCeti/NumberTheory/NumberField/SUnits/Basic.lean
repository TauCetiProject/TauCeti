/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Units.SUnit

/-!
# Ordinary units as S-units

Every unit of the ring of integers of a number field is an `S`-unit, for any set `S` of finite
places. This module records the resulting canonical homomorphism. It is the inclusion used to
compare Dirichlet's logarithmic embedding of ordinary units with the logarithmic embedding of
`S`-units.
-/

public noncomputable section

open IsDedekindDomain NumberField

namespace TauCeti.NumberField.SUnit

variable {K : Type*} [Field K] [NumberField K]

/-- The canonical homomorphism from the units of the ring of integers to the `S`-units. -/
def unitOfUnits (S : Set (HeightOneSpectrum (𝓞 K))) : (𝓞 K)ˣ →* S.unit K :=
  (Subgroup.inclusion (Set.unit_mono K (Set.empty_subset S))).comp
    (Set.unitEmptyEquivUnits K).symm.toMonoidHom

theorem val_unitOfUnits (S : Set (HeightOneSpectrum (𝓞 K))) (u : (𝓞 K)ˣ) :
    (((unitOfUnits S u : S.unit K) : Kˣ) : K) = algebraMap (𝓞 K) K (u : 𝓞 K) := by
  rw [unitOfUnits, MonoidHom.comp_apply, Subgroup.coe_inclusion]
  simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using
    (Set.algebraMap_unitEmptyEquivUnits_apply K
      ((Set.unitEmptyEquivUnits K).symm u)).symm

@[simp]
theorem coe_unitOfUnits (S : Set (HeightOneSpectrum (𝓞 K))) (u : (𝓞 K)ˣ) :
    ((unitOfUnits S u : S.unit K) : Kˣ) = Units.map (algebraMap (𝓞 K) K) u := by
  apply Units.ext
  exact val_unitOfUnits S u

end TauCeti.NumberField.SUnit
