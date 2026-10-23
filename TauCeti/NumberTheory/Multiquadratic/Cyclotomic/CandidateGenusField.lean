/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Cyclotomic.FundamentalDiscriminant
public import TauCeti.NumberTheory.Multiquadratic.Cyclotomic.GenusCharGroup
public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Real.FixedField
public import TauCeti.NumberTheory.NumberField.Cyclotomic.MaximalRealSubfield

/-!
# The candidate genus field as a cyclotomic character subfield

For squarefree `d` with fundamental discriminant `D`, the candidate genus field of `ℚ(√d)` is the
compositum of the quadratic fields `ℚ(√P)` over the prime discriminants `P` dividing `D`. It lies
in every cyclotomic subfield `K ⊆ ℂ` of level `|D|`, and inside `K` the Galois correspondence
identifies it with the intermediate field attached to the genus characters, the Dirichlet
characters of level `|D|` that are products of the quadratic characters of the prime
discriminants dividing `D`. This is the explicit Kronecker–Weber description of the candidate
genus field: it is cut out of `ℚ(ζ_|D|)` by the genus character group. For imaginary `d` the
candidate genus field is the genus field of `ℚ(√d)` (`isGenusField_candidateGenusField`); for
real `d` it is the narrow genus field.

For real `d` the genus field of `ℚ(√d)` is instead the maximal real subfield
`candidateGenusFieldReal hd` of the candidate (`isGenusField_candidateGenusFieldReal`). Since the
maximal real subfield of `ℚ(ζ_|D|)` is cut out by the even characters, this real subfield is cut
out by the even genus characters, those with `χ (-1) = 1`.

## Main results

* `TauCeti.Multiquadratic.candidateGenusField_eq_map_characterSubfield_genusCharGroup`: the
  candidate genus field is the image in `ℂ` of the character subfield of the genus character
  group. The generators are the rescaled roots of
  `TauCeti.NumberTheory.Multiquadratic.Cyclotomic.FundamentalDiscriminant`.
* `TauCeti.Multiquadratic.map_candidateGenusFieldReal_eq_map_characterSubfield_inf_evenSubgroup`:
  the maximal real subfield of the candidate genus field is the image in `ℂ` of the character
  subfield of the even genus characters.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §6.A.
-/

public section

open IntermediateField IsCyclotomicExtension IsCyclotomicExtension.Rat

namespace TauCeti.Multiquadratic

variable {d : ℤ} (hd : Squarefree d) (K : IntermediateField ℚ ℂ) [NumberField K]
  [IsCyclotomicExtension {(∏ P ∈ genusPrimeDiscriminants hd, P).natAbs} ℚ K]

/-- **The candidate genus field is cut out of the cyclotomic field by the genus characters.** For
squarefree `d` with fundamental discriminant `D` and a cyclotomic subfield `K ⊆ ℂ` of level `|D|`,
the candidate genus field of `ℚ(√d)` is the image in `ℂ` of the intermediate field of `K` that the
character correspondence attaches to the genus character group of `D`. The correspondence is
taken for the abelian Galois structure of the cyclotomic extension. -/
theorem candidateGenusField_eq_map_characterSubfield_genusCharGroup
    (R : Type*) [CommRing R] [CharZero R]
    [HasEnoughRootsOfUnity R
      (Monoid.exponent (ZMod (∏ P ∈ genusPrimeDiscriminants hd, P).natAbs)ˣ)] :
    haveI := neZero_natAbs_prod_of_forall_isPrimeDiscriminant (genusPrimeDiscriminants_spec hd).1
    haveI := IsCyclotomicExtension.isAbelianGalois
      {(∏ P ∈ genusPrimeDiscriminants hd, P).natAbs} ℚ K
    candidateGenusField hd =
      ((intermediateFieldEquivSubgroupChar (∏ P ∈ genusPrimeDiscriminants hd, P).natAbs K R).symm
        ((genusCharGroup (genusPrimeDiscriminants hd) (genusPrimeDiscriminants_spec hd).1).map
          (MulChar.ringHomCompHom (Int.castRingHom R)))).map K.val := by
  have := neZero_natAbs_prod_of_forall_isPrimeDiscriminant (genusPrimeDiscriminants_spec hd).1
  have := IsCyclotomicExtension.isAbelianGalois
    {(∏ P ∈ genusPrimeDiscriminants hd, P).natAbs} ℚ K
  rw [characterSubfield_genusCharGroup_eq_adjoin_range _ _ R
    (genusFieldRootOfPrimeDiscriminant hd K) (genusFieldRootOfPrimeDiscriminant_sq hd K),
    map_adjoin_range_genusFieldRootOfPrimeDiscriminant]

/-- **The real genus field is cut out of the cyclotomic field by the even genus characters.** For
squarefree `d` with fundamental discriminant `D` and a cyclotomic subfield `K ⊆ ℂ` of level `|D|`,
the maximal real subfield of the candidate genus field of `ℚ(√d)` is the image in `ℂ` of the
intermediate field of `K` that the character correspondence attaches to the even genus characters
of `D`. For positive nonsquare `d` this real subfield is the genus field of `ℚ(√d)`
(`isGenusField_candidateGenusFieldReal`). -/
theorem map_candidateGenusFieldReal_eq_map_characterSubfield_inf_evenSubgroup
    (R : Type*) [CommRing R] [CharZero R]
    [HasEnoughRootsOfUnity R
      (Monoid.exponent (ZMod (∏ P ∈ genusPrimeDiscriminants hd, P).natAbs)ˣ)] :
    haveI := neZero_natAbs_prod_of_forall_isPrimeDiscriminant (genusPrimeDiscriminants_spec hd).1
    haveI := IsCyclotomicExtension.isAbelianGalois
      {(∏ P ∈ genusPrimeDiscriminants hd, P).natAbs} ℚ K
    (candidateGenusFieldReal hd).map (candidateGenusField hd).val =
      ((intermediateFieldEquivSubgroupChar (∏ P ∈ genusPrimeDiscriminants hd, P).natAbs K R).symm
        ((genusCharGroup (genusPrimeDiscriminants hd) (genusPrimeDiscriminants_spec hd).1).map
          (MulChar.ringHomCompHom (Int.castRingHom R)) ⊓
          DirichletCharacter.evenSubgroup R (∏ P ∈ genusPrimeDiscriminants hd, P).natAbs)).map
        K.val := by
  have := neZero_natAbs_prod_of_forall_isPrimeDiscriminant (genusPrimeDiscriminants_spec hd).1
  have := IsCyclotomicExtension.isAbelianGalois
    {(∏ P ∈ genusPrimeDiscriminants hd, P).natAbs} ℚ K
  set N := (∏ P ∈ genusPrimeDiscriminants hd, P).natAbs
  -- An element of `K` is cut out by the even characters exactly when it is real in `ℂ`.
  have heven (y : K) :
      y ∈ (intermediateFieldEquivSubgroupChar N K R).symm (DirichletCharacter.evenSubgroup R N) ↔
        star (y : ℂ) = y := by
    rw [← IntermediateField.mem_toSubfield,
      IsCyclotomicExtension.Rat.toSubfield_intermediateFieldEquivSubgroupChar_symm_evenSubgroup,
      IsCyclotomicExtension.Rat.mem_maximalRealSubfield_iff_star_eq N K.val.toRingHom,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, IntermediateField.coe_val]
  ext x
  rw [mem_map_candidateGenusFieldReal_iff,
    candidateGenusField_eq_map_characterSubfield_genusCharGroup hd K R, OrderIso.map_inf,
    IntermediateField.mem_map, IntermediateField.mem_map]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hstar⟩
    exact ⟨y, ⟨hy, (heven y).2 hstar⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hy'⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, (heven y).1 hy'⟩

end TauCeti.Multiquadratic
