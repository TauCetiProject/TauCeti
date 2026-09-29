/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Cyclotomic.FundamentalDiscriminant
public import TauCeti.NumberTheory.Multiquadratic.Cyclotomic.GenusCharGroup

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
real `d` it is the narrow candidate only.

## Main results

* `TauCeti.Multiquadratic.candidateGenusField_eq_map_characterSubfield_genusCharGroup`: the
  candidate genus field is the image in `ℂ` of the character subfield of the genus character
  group. The generators are the rescaled roots of
  `TauCeti.NumberTheory.Multiquadratic.Cyclotomic.FundamentalDiscriminant`.

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
    haveI := IsCyclotomicExtension.isAbelianGalois
      {(∏ P ∈ genusPrimeDiscriminants hd, P).natAbs} ℚ K
    candidateGenusField hd =
      ((intermediateFieldEquivSubgroupChar (∏ P ∈ genusPrimeDiscriminants hd, P).natAbs K R).symm
        ((genusCharGroup (genusPrimeDiscriminants hd) (genusPrimeDiscriminants_spec hd).1).map
          (MulChar.ringHomCompHom (Int.castRingHom R)))).map K.val := by
  have := IsCyclotomicExtension.isAbelianGalois
    {(∏ P ∈ genusPrimeDiscriminants hd, P).natAbs} ℚ K
  rw [characterSubfield_genusCharGroup_eq_adjoin_range _ _ R
    (genusFieldRootOfPrimeDiscriminant hd K) (genusFieldRootOfPrimeDiscriminant_sq hd K),
    map_adjoin_range_genusFieldRootOfPrimeDiscriminant]

end TauCeti.Multiquadratic
