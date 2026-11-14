/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.GaussSum
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Decomposition
import TauCeti.LinearAlgebra.FiniteBilinearModule.Pi

/-!
# Gauss sums and primary decomposition of finite quadratic modules

Because a finite quadratic module is canonically isometric to the orthogonal product of its
prime-primary components (`TauCeti.FiniteQuadraticModule.primaryDecomposition`), its Gauss sum
factors as the product of the Gauss sums of its prime-primary restrictions, and — when it is
nondegenerate — its `ZMod 8`-valued Gauss-sum invariant `gaussSign` splits as the sum of their
`gaussSign` invariants. Primes not dividing `#A` contribute trivial primary components whose
`gaussSign` is zero, so the sum may be indexed by any finite set of primes containing the prime
factors of `#A`.

## Main results

* `TauCeti.FiniteQuadraticModule.gaussSum_eq_prod_primeFactors`: the Gauss sum of `A` is the
  product over `p ∈ (#A).primeFactors` of the Gauss sums of `A[p^∞]`.
* `TauCeti.FiniteQuadraticModule.gaussSign_eq_sum_primeFactors`: for nondegenerate `A`,
  `A.gaussSign` is the sum over `p ∈ (#A).primeFactors` of the `gaussSign` invariants of `A[p^∞]`.
* `TauCeti.FiniteQuadraticModule.gaussSign_eq_sum_of_primeFactors_subset`: the same sum over any
  finite set of primes containing `(#A).primeFactors`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.11.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open AddCommGroup

namespace TauCeti.FiniteQuadraticModule

/-- `primaryComponents` has the same carrier and quadratic map as the orthogonal sum `pi` of the
prime-primary restrictions. -/
private noncomputable def primaryComponentsIsometryPi (A : FiniteQuadraticModule) :
    Isometry A.primaryComponents
      (pi fun p : (Nat.card A).primeFactors ↦ A.restrict (primaryComponent A p.1)) where
  toLinearEquiv := LinearEquiv.refl ℤ _
  map_app' x := by
    rw [primaryComponents_quadratic, pi_quadratic]
    rfl

/-- **Primary factorization of the Gauss sum.** The Gauss sum of a finite quadratic module is the
product of the Gauss sums of its prime-primary components. -/
theorem gaussSum_eq_prod_primeFactors (A : FiniteQuadraticModule) :
    A.gaussSum =
      ∏ p ∈ (Nat.card A).primeFactors, (A.restrict (primaryComponent A p)).gaussSum := by
  rw [← A.primaryDecomposition.gaussSum_eq, (primaryComponentsIsometryPi A).gaussSum_eq,
    gaussSum_pi]
  exact Finset.prod_coe_sort (Nat.card A).primeFactors
    (fun p ↦ (A.restrict (primaryComponent A p)).gaussSum)

/-- **Primary decomposition of the Gauss-sum invariant.** The Gauss-sum invariant of a
nondegenerate finite quadratic module is the sum of the Gauss-sum invariants of its prime-primary
components. -/
theorem gaussSign_eq_sum_primeFactors {A : FiniteQuadraticModule} (hA : A.IsNondegenerate) :
    A.gaussSign =
      ∑ p ∈ (Nat.card A).primeFactors, (A.restrict (primaryComponent A p)).gaussSign := by
  rw [← A.primaryDecomposition.gaussSign_eq, (primaryComponentsIsometryPi A).gaussSign_eq,
    gaussSign_pi _ fun p ↦
      A.isNondegenerate_restrict_primaryComponent hA (Nat.prime_of_mem_primeFactors p.2)]
  exact Finset.sum_coe_sort (Nat.card A).primeFactors
    (fun p ↦ (A.restrict (primaryComponent A p)).gaussSign)

/-- For any finite set `S` of primes containing the prime factors of `#A`, the Gauss-sum invariant
of a nondegenerate finite quadratic module `A` is the sum over `p ∈ S` of the Gauss-sum invariants
of its `p`-primary components. -/
theorem gaussSign_eq_sum_of_primeFactors_subset {A : FiniteQuadraticModule}
    (hA : A.IsNondegenerate) {S : Finset ℕ} (hS_prime : ∀ p ∈ S, p.Prime)
    (hS : (Nat.card A).primeFactors ⊆ S) :
    A.gaussSign = ∑ p ∈ S, (A.restrict (primaryComponent A p)).gaussSign := by
  rw [gaussSign_eq_sum_primeFactors hA]
  refine Finset.sum_subset hS fun p hpS hpnot ↦ ?_
  have hp : p.Prime := hS_prime p hpS
  have hndvd : ¬ p ∣ Nat.card A := fun hdvd ↦
    hpnot (hp.mem_primeFactors hdvd Nat.card_pos.ne')
  have hcard1 : Nat.card (A.restrict (primaryComponent A p)) = 1 := by
    -- The carrier of `A.restrict P` is definitionally `P`.
    change Nat.card (primaryComponent A p) = 1
    rw [TauCeti.AddCommGroup.natCard_primaryComponent A hp,
      Nat.factorization_eq_zero_of_not_dvd hndvd, pow_zero]
  have : Subsingleton (A.restrict (primaryComponent A p)) :=
    Finite.card_le_one_iff_subsingleton.mp hcard1.le
  exact gaussSign_eq_zero_of_subsingleton _

end TauCeti.FiniteQuadraticModule
