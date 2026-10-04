/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.FiniteExtension
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Surjectivity
import TauCeti.NumberTheory.Cyclotomic.Irreducible

/-!
# Indices of cyclotomic images along finite extensions

For a finite extension `L/K` embedded in a separable closure of `K`, the cyclotomic image of
`G_L` is a subgroup of that of `G_K`, of relative index dividing `[L : K]`. In particular,
for a finite extension `L/ℚ_p`, the cyclotomic image has index dividing `[L : ℚ_p]` in `ℤ_pˣ`.
No valuation or topology on `L` is needed for this comparison.

These bounds constrain the possible cyclotomic orientations in local Galois presentations.
The arithmetic input over `ℚ_p` is irreducibility of the `p`-power cyclotomic polynomials;
the subgroup-index comparison uses the realization of `G_L` as an open subgroup of `G_K`.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §4.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I §5.
-/

public section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime]

section FiniteExtension

variable (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L]
  [FiniteDimensional K L] (σ : L →ₐ[K] SeparableClosure K)
include σ

/-- The cyclotomic image of a finite extension is the image of its absolute Galois subgroup
under the base field's cyclotomic character. -/
theorem range_localCyclotomicCharacter_eq_map :
    (localCyclotomicCharacter p L).range =
      (absoluteGaloisGroupExtend K L σ).range.map (localCyclotomicCharacter p K) := by
  rw [MonoidHom.map_range, localCyclotomicCharacter_comp_absoluteGaloisGroupExtend]

/-- The cyclotomic image of a finite extension is contained in that of the base field. -/
theorem range_localCyclotomicCharacter_le_of_finiteExtension :
    (localCyclotomicCharacter p L).range ≤ (localCyclotomicCharacter p K).range := by
  rw [range_localCyclotomicCharacter_eq_map p K L σ]
  exact Subgroup.map_le_range _ _

/-- The relative index of the cyclotomic image of a finite extension in that of its base field
divides the extension degree. This also applies when the base character is not surjective. -/
theorem relIndex_range_localCyclotomicCharacter_dvd_finrank :
    (localCyclotomicCharacter p L).range.relIndex (localCyclotomicCharacter p K).range ∣
      Module.finrank K L := by
  rw [range_localCyclotomicCharacter_eq_map p K L σ,
    ← Subgroup.map_top (localCyclotomicCharacter p K), Subgroup.relIndex_map_map]
  simpa only [top_sup_eq, Subgroup.relIndex_top_right,
    index_range_absoluteGaloisGroupExtend] using
    (Subgroup.index_dvd_of_le
      (le_sup_left : (absoluteGaloisGroupExtend K L σ).range ≤
        (absoluteGaloisGroupExtend K L σ).range ⊔ (localCyclotomicCharacter p K).ker))

end FiniteExtension

/-- The cyclotomic image of `G_{ℚ_p}` is all of `ℤ_pˣ`. -/
theorem range_localCyclotomicCharacter_ratPadic :
    (localCyclotomicCharacter p ℚ_[p]).range = ⊤ := by
  rw [MonoidHom.range_eq_top]
  exact localCyclotomicCharacter_surjective_of_irreducible
    (irreducible_cyclotomic_prime_pow_ratPadic p)

/-- The index of the cyclotomic image of a finite extension of `ℚ_p` divides its degree. -/
theorem index_range_localCyclotomicCharacter_dvd_finrank (K : Type*) [Field K]
    [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] :
    (localCyclotomicCharacter p K).range.index ∣ Module.finrank ℚ_[p] K := by
  have h := relIndex_range_localCyclotomicCharacter_dvd_finrank p ℚ_[p] K IsSepClosed.lift
  simpa only [range_localCyclotomicCharacter_ratPadic, Subgroup.relIndex_top_right] using h

end TauCeti
