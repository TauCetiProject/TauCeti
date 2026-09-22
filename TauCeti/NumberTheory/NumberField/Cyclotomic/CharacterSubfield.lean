/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import TauCeti.NumberTheory.DirichletCharacter.Subgroup

/-!
# Conductors and cyclotomic character subfields

The Galois correspondence for a rational cyclotomic field identifies each intermediate field
with a subgroup of Dirichlet characters. This file packages the conductor criterion for comparing
such an intermediate field with a lower cyclotomic field: containment holds exactly when the
conductor of its character subgroup divides the lower level.

The result combines Mathlib's character-subgroup correspondence
`IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar` with its pointwise criterion
`IsCyclotomicExtension.Rat.mem_intermediateFieldEquivSubgroupChar_iff_conductor_dvd`.

## Main results

* `Subgroup.characterSubfield_le_iff_dirichletConductor_dvd`: the field cut out by a character
  subgroup lies in a lower cyclotomic field exactly when the subgroup conductor divides the lower
  level.
-/

public section

open DirichletCharacter IsCyclotomicExtension

namespace Subgroup

variable {n m : ℕ} [NeZero n] [NeZero m]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
  [IsAbelianGalois ℚ K]
variable {R : Type*} [CommRing R] [Finite (DirichletCharacter R n)]
  [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]

/-- A character subfield of the `n`-th cyclotomic field lies in its cyclotomic subfield of level
`m` exactly when every character in the group factors through level `m`, equivalently when the
group conductor divides `m`. -/
theorem characterSubfield_le_iff_dirichletConductor_dvd
    (Y : Subgroup (DirichletCharacter R n)) (F : IntermediateField ℚ K)
    [IsGalois ℚ F] [IsCyclotomicExtension {m} ℚ F] (hmn : m ∣ n) :
    (IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n K R).symm Y ≤ F ↔
      Y.dirichletConductor ∣ m := by
  rw [← (IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n K R).le_iff_le,
    (IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n K R).apply_symm_apply,
    dirichletConductor_dvd_iff]
  constructor
  · intro h χ hχ
    exact (IsCyclotomicExtension.Rat.mem_intermediateFieldEquivSubgroupChar_iff_conductor_dvd
      n K R F hmn χ).mp (h hχ)
  · intro h χ hχ
    exact (IsCyclotomicExtension.Rat.mem_intermediateFieldEquivSubgroupChar_iff_conductor_dvd
      n K R F hmn χ).mpr (h χ hχ)

end Subgroup
