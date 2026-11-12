/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Eisenstein.PowerBasis

/-!
# Valuation balls in Eisenstein power-basis coordinates

For an Eisenstein generator `ξ` of a finite extension `L/K` of degree `n`, the `i`-th
power-basis term has additive valuation `addVal (algebraMap (c i) * ξ ^ i) = n * addVal (c i) + i`,
so its additive valuation has residue `i` modulo `n`. Consequently, the coefficient
vectors whose power-basis linear combination lies in the valuation ball of radius `r` form a
box: the `i`-th coefficient belongs to the `ceil((r - i) / n)`-th power of the maximal ideal of
`O_K`. At radii divisible by `n`, this box is a cube. Both statements specialize the uniformizer
descriptions `TauCeti.le_addVal_sum_algebraMap_mul_pow_iff_of_irreducible` and
`TauCeti.ramificationIndex_mul_le_addVal_sum_algebraMap_mul_pow_iff_of_irreducible`, since an
Eisenstein generator is a uniformizer and `e(L/K) = n`.

These descriptions turn valuation-ball questions in a totally ramified extension into
coordinatewise ideal-membership questions over the base field. They are used in local change of
variables and root-counting arguments.

## Main results

* `Polynomial.le_addVal_sum_eisenstein_powerBasis_iff` identifies every valuation ball
  with its coordinate box.
* `Polynomial.natDegree_mul_le_addVal_sum_eisenstein_powerBasis_iff` gives the cube
  specialization at radii divisible by the degree.

## References

* J.-P. Serre, *Local Fields*, Chapter I, §6, Proposition 17.
-/

public section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField TauCeti
open scoped IntermediateField

namespace Polynomial

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- At an Eisenstein generator, the power-basis coefficient vectors representing elements of a
valuation ball form the box whose `i`-th factor is the `ceil((r - i) / deg f)`-th power of the
base maximal ideal. -/
theorem le_addVal_sum_eisenstein_powerBasis_iff
    (f : Polynomial 𝒪[K]) (hf : f.IsEisensteinAt 𝓂[K])
    (ξ : 𝒪[L]) (hroot : (f.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ)
    (hgen : K⟮(ξ : L)⟯ = ⊤) (c : Fin f.natDegree → 𝒪[K]) (r : ℕ) :
    (r : ℕ∞) ≤ IsDiscreteValuationRing.addVal 𝒪[L]
        (∑ i, algebraMap 𝒪[K] 𝒪[L] (c i) * ξ ^ (i : ℕ)) ↔
      ∀ i : Fin f.natDegree, c i ∈ 𝓂[K] ^ ((r - (i : ℕ)) ⌈/⌉ f.natDegree) := by
  rw [le_addVal_sum_algebraMap_mul_pow_iff_of_irreducible
      (irreducible_of_eisenstein_adjoin_eq_top f hf ξ hroot hgen)
      (ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top f hf ξ hroot hgen).ge c,
    ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top f hf ξ hroot hgen]

/-- At a radius divisible by the degree, the power-basis coordinate box is the cube in which
every coefficient belongs to the same power of the base maximal ideal. -/
theorem natDegree_mul_le_addVal_sum_eisenstein_powerBasis_iff
    (f : Polynomial 𝒪[K]) (hf : f.IsEisensteinAt 𝓂[K])
    (ξ : 𝒪[L]) (hroot : (f.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ)
    (hgen : K⟮(ξ : L)⟯ = ⊤) (c : Fin f.natDegree → 𝒪[K]) (ρ : ℕ) :
    (f.natDegree * ρ : ℕ) ≤ IsDiscreteValuationRing.addVal 𝒪[L]
        (∑ i, algebraMap 𝒪[K] 𝒪[L] (c i) * ξ ^ (i : ℕ)) ↔
      ∀ i : Fin f.natDegree, c i ∈ 𝓂[K] ^ ρ := by
  have he := ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top f hf ξ hroot hgen
  have h := ramificationIndex_mul_le_addVal_sum_algebraMap_mul_pow_iff_of_irreducible
    (irreducible_of_eisenstein_adjoin_eq_top f hf ξ hroot hgen) he.ge c ρ
  rwa [he] at h

end Polynomial
