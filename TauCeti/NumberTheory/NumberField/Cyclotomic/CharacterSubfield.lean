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

* `IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar_symm_apply`: the field cut out
  by a character subgroup is the fixed field of the automorphisms on which every character in the
  subgroup is trivial.
* `Subgroup.characterSubfield_le_iff_dirichletConductor_dvd`: the field cut out by a character
  subgroup lies in a lower cyclotomic field exactly when the subgroup conductor divides the lower
  level.
-/

public section

open DirichletCharacter IsCyclotomicExtension

variable {n m : ℕ} [NeZero n]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
  [IsAbelianGalois ℚ K]
variable {R : Type*} [CommRing R]
  [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]

namespace IsCyclotomicExtension.Rat

/-- The intermediate field attached to a subgroup `Y` of Dirichlet characters is the fixed field
of the automorphisms `σ` with `χ (galEquivZMod n K σ) = 1` for every `χ ∈ Y`; membership in that
subgroup is `mem_subgroupGalEquivSubgroupChar_symm_iff`. -/
theorem intermediateFieldEquivSubgroupChar_symm_apply (Y : Subgroup (DirichletCharacter R n)) :
    (intermediateFieldEquivSubgroupChar n K R).symm Y =
      IntermediateField.fixedField
        ((subgroupGalEquivSubgroupChar n K R).symm (OrderDual.toDual Y)) :=
  (rfl)

end IsCyclotomicExtension.Rat

namespace Subgroup

/-- A character subfield of the `n`-th cyclotomic field lies in its cyclotomic subfield of level
`m` exactly when every character in the group factors through level `m`, equivalently when the
group conductor divides `m`. -/
theorem characterSubfield_le_iff_dirichletConductor_dvd
    (Y : Subgroup (DirichletCharacter R n)) [Finite Y] (F : IntermediateField ℚ K)
    [IsGalois ℚ F] [IsCyclotomicExtension {m} ℚ F] (hmn : m ∣ n) :
    (IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar n K R).symm Y ≤ F ↔
      Y.dirichletConductor ∣ m := by
  let _ : NeZero m := ⟨fun h ↦ NeZero.ne n (Nat.eq_zero_of_zero_dvd (h ▸ hmn))⟩
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
