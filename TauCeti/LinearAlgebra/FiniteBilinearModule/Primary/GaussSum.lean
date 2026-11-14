/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.GaussSum
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Decomposition

/-!
# Primary decomposition of the Gauss-sum invariant

For a nondegenerate finite quadratic module `A`, the canonical primary decomposition
`TauCeti.FiniteQuadraticModule.primaryDecomposition` identifies `A` isometrically with the
orthogonal product of its prime-primary components. Since `FiniteQuadraticModule.gaussSign` is
additive over orthogonal sums of nondegenerate modules
(`TauCeti.FiniteQuadraticModule.gaussSign_pi`) and vanishes on trivial modules, `A.gaussSign` is
the sum of the `p`-primary Gauss-sum invariants over `(Nat.card A).primeFactors`, and more
generally over any finite set of primes containing all prime factors of `Nat.card A`.

## Main declarations

* `TauCeti.FiniteQuadraticModule.piPrimaryComponentsIsometry`: canonical quadratic isometry between
  `FiniteQuadraticModule.pi` of the prime-primary restrictions and `A.primaryComponents`.
* `TauCeti.FiniteQuadraticModule.gaussSign_primaryComponents`: `A.primaryComponents.gaussSign` is
  the sum of the prime-primary Gauss-sum invariants.
* `TauCeti.FiniteQuadraticModule.gaussSign_eq_sum_primaryComponents`: `A.gaussSign` is the sum of
  the prime-primary Gauss-sum invariants over `(Nat.card A).primeFactors`.
* `TauCeti.FiniteQuadraticModule.gaussSign_eq_sum_primaryComponent`: `A.gaussSign` is the sum of
  the `p`-primary Gauss-sum invariants over any finite set of primes containing
  `(Nat.card A).primeFactors`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.11.2.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Appendix 4.
-/

public noncomputable section

open AddCommGroup

namespace TauCeti.FiniteQuadraticModule

variable (A : FiniteQuadraticModule)

/-- Canonical quadratic isometry identifying the orthogonal family product
`FiniteQuadraticModule.pi` of the prime-primary restrictions of `A` with `A.primaryComponents`. -/
def piPrimaryComponentsIsometry :
    Isometry
      (pi fun p : (Nat.card A).primeFactors ↦ A.restrict (primaryComponent A p.1))
      A.primaryComponents where
  toLinearEquiv :=
    { toFun := fun x p ↦ ⟨(x p).1, (x p).2⟩
      invFun := fun y p ↦ ⟨(y p).1, (y p).2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  map_app' x :=
    (A.primaryComponents_quadratic (fun p ↦ ⟨(x p).1, (x p).2⟩)).trans <|
      (Finset.sum_congr rfl fun p _ ↦
        (A.restrict_quadratic (primaryComponent A p.1) ⟨(x p).1, (x p).2⟩).symm).trans
        (pi_quadratic _ x).symm

/-- `piPrimaryComponentsIsometry` evaluates coordinatewise on each prime factor. -/
@[simp]
theorem piPrimaryComponentsIsometry_apply
    (x : pi fun p : (Nat.card A).primeFactors ↦ A.restrict (primaryComponent A p.1))
    (p : (Nat.card A).primeFactors) :
    (A.piPrimaryComponentsIsometry x p).1 = (x p).1 := by
  rfl

/-- The Gauss-sum invariant of `A.primaryComponents` is the sum of the Gauss-sum invariants of the
prime-primary restrictions of `A`. -/
theorem gaussSign_primaryComponents (hA : A.IsNondegenerate) :
    A.primaryComponents.gaussSign =
      ∑ p : (Nat.card A).primeFactors, (A.restrict (primaryComponent A p.1)).gaussSign := by
  classical
  rw [← A.piPrimaryComponentsIsometry.gaussSign_eq]
  exact gaussSign_pi _ fun p ↦
    A.isNondegenerate_restrict_primaryComponent hA (Nat.prime_of_mem_primeFactors p.2)

/-- **Primary decomposition of `gaussSign`.** The Gauss-sum invariant of a nondegenerate finite
quadratic module is the sum of the Gauss-sum invariants of its prime-primary components over the
prime factors of its order. -/
theorem gaussSign_eq_sum_primaryComponents (hA : A.IsNondegenerate) :
    A.gaussSign =
      ∑ p : (Nat.card A).primeFactors, (A.restrict (primaryComponent A p.1)).gaussSign := by
  rw [← A.primaryDecomposition.gaussSign_eq, A.gaussSign_primaryComponents hA]

/-- **Primary decomposition of `gaussSign` over any prime superset.** The Gauss-sum invariant of a
nondegenerate finite quadratic module is the sum of the Gauss-sum invariants of its `p`-primary
components over any finite set of primes `S` containing `(Nat.card A).primeFactors`; primes in `S`
not dividing `Nat.card A` have trivial `p`-primary component and contribute `0`. -/
theorem gaussSign_eq_sum_primaryComponent (hA : A.IsNondegenerate) (S : Finset ℕ)
    (hS_prime : ∀ p ∈ S, p.Prime) (hS_factors : (Nat.card A).primeFactors ⊆ S) :
    A.gaussSign = ∑ p ∈ S, (A.restrict (primaryComponent A p)).gaussSign := by
  classical
  rw [A.gaussSign_eq_sum_primaryComponents hA, Finset.univ_eq_attach,
    Finset.sum_attach (Nat.card A).primeFactors
      (fun p ↦ (A.restrict (primaryComponent A p)).gaussSign)]
  refine Finset.sum_subset hS_factors fun p hpS hnp ↦ ?_
  have hp : p.Prime := hS_prime p hpS
  have hfact : (Nat.card A).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun hdvd ↦
      hnp (Nat.mem_primeFactors.mpr ⟨hp, hdvd, Nat.card_pos.ne'⟩)
  have hcard : Nat.card (A.restrict (primaryComponent A p)) = 1 := by
    rw [A.natCard_restrict, TauCeti.AddCommGroup.natCard_primaryComponent _ hp, hfact, pow_zero]
  have : Subsingleton (A.restrict (primaryComponent A p)) :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  exact gaussSign_eq_zero_of_subsingleton _

end TauCeti.FiniteQuadraticModule
