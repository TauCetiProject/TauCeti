/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.GaussSum
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Decomposition

/-!
# Gauss sums and primary decomposition of finite quadratic modules

By primary decomposition (`TauCeti.FiniteQuadraticModule.primaryDecomposition`), the Gauss sum and
scaled Gauss sum factor over `p ∈ (#A).primeFactors`, and for nondegenerate `A` the `ZMod 8`-valued
`gaussSign` splits as the sum over `p ∈ (#A).primeFactors` (or any superset of primes).

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.11.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open AddCommGroup

namespace TauCeti.FiniteQuadraticModule

/-- **Primary factorization of the scaled Gauss sum.** The scaled Gauss sum of a finite quadratic
module is the product of the scaled Gauss sums of its prime-primary components. -/
theorem scaledGaussSum_eq_prod_primeFactors (A : FiniteQuadraticModule) (n : ℕ) :
    A.scaledGaussSum n =
      ∏ p ∈ (Nat.card A).primeFactors, (A.restrict (primaryComponent A p)).scaledGaussSum n := by
  rw [← A.primaryDecomposition.scaledGaussSum_eq, primaryComponents_eq_pi, scaledGaussSum_pi]
  exact Finset.prod_coe_sort _ (fun p ↦ (A.restrict (primaryComponent A p)).scaledGaussSum n)

/-- **Primary factorization of the Gauss sum.** The Gauss sum of a finite quadratic module is the
product of the Gauss sums of its prime-primary components. -/
theorem gaussSum_eq_prod_primeFactors (A : FiniteQuadraticModule) :
    A.gaussSum = ∏ p ∈ (Nat.card A).primeFactors, (A.restrict (primaryComponent A p)).gaussSum := by
  simpa only [scaledGaussSum_one] using A.scaledGaussSum_eq_prod_primeFactors 1

/-- **Primary decomposition of the Gauss-sum invariant.** The Gauss-sum invariant of a
nondegenerate finite quadratic module is the sum of the Gauss-sum invariants of its prime-primary
components. -/
theorem gaussSign_eq_sum_primeFactors {A : FiniteQuadraticModule} (hA : A.IsNondegenerate) :
    A.gaussSign =
      ∑ p ∈ (Nat.card A).primeFactors, (A.restrict (primaryComponent A p)).gaussSign := by
  rw [← A.primaryDecomposition.gaussSign_eq, primaryComponents_eq_pi, gaussSign_pi _ fun p ↦
    A.isNondegenerate_restrict_primaryComponent hA (Nat.prime_of_mem_primeFactors p.property)]
  exact Finset.sum_coe_sort _ (fun p ↦ (A.restrict (primaryComponent A p)).gaussSign)

/-- For any finite set `S` of primes containing the prime factors of `#A`, the Gauss-sum invariant
of a nondegenerate finite quadratic module `A` is the sum over `p ∈ S` of the Gauss-sum invariants
of its `p`-primary components. -/
theorem gaussSign_eq_sum_of_primeFactors_subset {A : FiniteQuadraticModule}
    (hA : A.IsNondegenerate) {S : Finset ℕ} (hS_prime : ∀ p ∈ S, p.Prime)
    (hS : (Nat.card A).primeFactors ⊆ S) :
    A.gaussSign = ∑ p ∈ S, (A.restrict (primaryComponent A p)).gaussSign := by
  rw [gaussSign_eq_sum_primeFactors hA]
  refine Finset.sum_subset hS fun p hpS hpnot ↦ ?_
  have hp := hS_prime p hpS
  have : Subsingleton (A.restrict (primaryComponent A p)) := Finite.card_le_one_iff_subsingleton.mp
    (by rw [A.natCard_restrict, TauCeti.AddCommGroup.natCard_primaryComponent A hp,
      Nat.factorization_eq_zero_of_not_dvd fun h ↦ hpnot (hp.mem_primeFactors h Nat.card_pos.ne'),
      pow_zero])
  exact gaussSign_eq_zero_of_subsingleton _

end TauCeti.FiniteQuadraticModule
