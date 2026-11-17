/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing

import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Prime
import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.RingTheory.MvPolynomial.Discriminant.Generic
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import TauCeti.RingTheory.Polynomial.Resultant.RootCoordinates

/-!
# The generic depressed polynomial and its discriminant

Let `R` be a commutative ring. A monic depressed polynomial of degree `m` over `R` has `m - 1`
free lower coefficients, represented universally by
`TauCeti.genericDepressed R m = X ^ m + a₂ X ^ (m - 2) + ⋯ + aₘ` over
`MvPolynomial (Fin (m - 1)) R`. Under uniform scaling `rᵢ ↦ t rᵢ` of the roots, `aₖ` acquires
weight `k`, and over any commutative ring `R` and degree `m` the generic depressed discriminant
`TauCeti.depressedDiscr R m` is weighted homogeneous of weight `m * (m - 1)` for
`TauCeti.depressedWeight m` (`TauCeti.depressedDiscr_mem`).

Over a unique factorization domain `R` with `(2 : R) ≠ 0`, `TauCeti.depressedDiscr R m` is prime
whenever either `2 ≤ m` and `IsUnit (m : R)` (in particular over any field `K` with `(2 : K) ≠ 0`
and `(m : K) ≠ 0`, such as any field of characteristic zero) or `3 ≤ m` and `(m : R) ≠ 0`. Under
these hypotheses, the repeated-root locus where the generic depressed discriminant vanishes is an
irreducible weighted-homogeneous hypersurface of weight `m * (m - 1)`, so inverting the
discriminant determines the homogeneous units on the locus of squarefree depressed polynomials.
Likewise, on short Weierstrass cubics `y² = x³ + a x + b`, the coordinate scaling
`(x, y) ↦ (t² x, t³ y)` assigns `(a, b)` weights `(4, 6)` — twice `TauCeti.depressedWeight 3` —
and makes the discriminant factor `4 a³ + 27 b²` weighted homogeneous of weight `12` over any
commutative ring, and prime over any unique factorization domain `R` with `(2 : R) ≠ 0` and
`(3 : R) ≠ 0`.

1. **Generic depressed polynomial and weighted homogeneity.** `TauCeti.genericDepressed R m`
   satisfies the universal property for monic depressed polynomials
   (`TauCeti.map_aeval_coeff_genericDepressed`), and specializing
   `Polynomial.Monic.isWeightedHomogeneous_discr` proves that `TauCeti.depressedDiscr R m` has
   weight `m * (m - 1)` for `TauCeti.depressedWeight m` (`TauCeti.depressedDiscr_mem`).

2. **Tschirnhaus equivalence and primality.** When `(m : R)` is a unit, translating the variable
   by the root barycenter `- m⁻¹ * X (m - 1)` identifies `MvPolynomial (Fin m) R` as an
   `R`-algebra with `Polynomial (MvPolynomial (Fin (m - 1)) R)` (`TauCeti.tschirnhausAlgEquiv`),
   carrying `(Polynomial.freeMonic R m).discr` to `Polynomial.C (TauCeti.depressedDiscr R m)` by
   translation invariance of the discriminant. Primality of `TauCeti.depressedDiscr R m` follows
   for `2 ≤ m` over any unique factorization domain in which `(2 : R) ≠ 0` and `(m : R)` is
   invertible (`TauCeti.prime_depressedDiscr_of_isUnit`). For `3 ≤ m`, specializing to `X ^ m - 1`
   and `X ^ m - X` shows that `TauCeti.depressedDiscr R m` has unit content, so `(m : R) ≠ 0`
   (with `(2 : R) ≠ 0`) suffices over any unique factorization domain
   (`TauCeti.prime_depressedDiscr_of_three_le`), and in particular `TauCeti.depressedDiscr K m` is
   prime for every `2 ≤ m` over any field of characteristic zero (`TauCeti.prime_depressedDiscr`).

3. **Low degrees and sharpness.** Explicit formulas are given in degrees `0` through `4`,
   including weighted homogeneity and primality of the Weierstrass cubic discriminant factor
   `4 X₀³ + 27 X₁²` of weight `12` for weights `(4, 6)`, together with counterexamples showing
   that `(2 : R) ≠ 0` in degree `2`, `(3 : R) ≠ 0` in degree `3`, and `IsUnit (2 : R)` over `ℤ`
   in degree `2` are all necessary.

## Main definitions

* `TauCeti.genericDepressed R m`: the generic monic depressed polynomial
  `X ^ m + ∑ i : Fin (m - 1), C (MvPolynomial.X i) * X ^ (m - (i + 2))`.
* `TauCeti.depressedWeight m`: the weight assignment `i ↦ (i : ℤ) + 2` on `Fin (m - 1)`.
* `TauCeti.depressedDiscr R m`: the discriminant `(genericDepressed R m).discr`.
* `TauCeti.tschirnhausAlgEquiv`: for `IsUnit (m : R)`, the Tschirnhaus `R`-algebra equivalence
  `MvPolynomial (Fin m) R ≃ₐ[R] Polynomial (MvPolynomial (Fin (m - 1)) R)`.

## Main results

* `TauCeti.depressedDiscr_mem`, `TauCeti.isWeightedHomogeneous_depressedDiscr`,
  `TauCeti.isWeightedHomogeneous_smul_depressedDiscr`: weighted homogeneity of
  `depressedDiscr R m` of weight `m * (m - 1)`.
* `TauCeti.tschirnhausAlgEquiv_discr_freeMonic`,
  `TauCeti.prime_depressedDiscr_iff_prime_discr_freeMonic_of_isUnit`: identification of generic
  monic and depressed discriminants when `m` is invertible.
* `TauCeti.prime_depressedDiscr_of_isUnit`, `TauCeti.prime_depressedDiscr_of_three_le`,
  `TauCeti.prime_depressedDiscr_of_ne_zero`, `TauCeti.prime_depressedDiscr`: primality of
  `depressedDiscr`.
* `TauCeti.depressedDiscr_two`, `TauCeti.depressedDiscr_three`, `TauCeti.depressedDiscr_four`,
  `TauCeti.isWeightedHomogeneous_four_mul_X_zero_pow_three_add_twentySeven_mul_X_one_pow_two`,
  `TauCeti.prime_four_mul_X_zero_pow_three_add_twentySeven_mul_X_one_pow_two`: explicit low-degree
  discriminants and weighted homogeneity and primality of the Weierstrass cubic discriminant
  factor.

## References

* S. Lang, *Algebra*, Revised Third Edition, GTM 211, Springer (2002), Chapter IV, §8.
* I. M. Gelfand, M. M. Kapranov, A. V. Zelevinsky, *Discriminants, Resultants, and
  Multidimensional Determinants*, Birkhäuser (1994), Chapter 12, §1.B.
-/

public section

open Finset MvPolynomial Polynomial

/-! ### The generic depressed polynomial and its discriminant -/

namespace TauCeti

section GenericDepressed

/-- The **generic monic depressed polynomial** of degree `m` over `R`:
`X ^ m + a₂ X ^ (m - 2) + ⋯ + aₘ`, viewed in `(MvPolynomial (Fin (m - 1)) R)[X]` with `X i`
representing `a_{i + 2}`. For `m = 0` this is `1`, and for `m = 1` it is `X`. -/
noncomputable def genericDepressed (R : Type*) [CommSemiring R] (m : ℕ) :
    (MvPolynomial (Fin (m - 1)) R)[X] :=
  Polynomial.X ^ m +
    ∑ i : Fin (m - 1), Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ (m - ((i : ℕ) + 2))

/-- Explicit sum formula for `TauCeti.genericDepressed R m`. -/
theorem genericDepressed_def (R : Type*) [CommSemiring R] (m : ℕ) :
    genericDepressed R m =
      Polynomial.X ^ m +
        ∑ i : Fin (m - 1),
          Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ (m - ((i : ℕ) + 2)) :=
  (rfl)

/-- The coefficients of `TauCeti.genericDepressed R m`: in degree `k < m - 1` the coefficient is
`X ⟨m - 2 - k, _⟩`, in degree `m - 1` (when `m ≥ 1`) it vanishes, in degree `m` it is `1`, and
above `m` it vanishes. -/
@[grind =]
theorem coeff_genericDepressed (R : Type*) [CommSemiring R] (m k : ℕ) :
    (genericDepressed R m).coeff k =
      if hk : k < m - 1 then MvPolynomial.X ⟨m - 2 - k, by omega⟩
      else if k = m then 1 else 0 := by
  simp only [genericDepressed_def, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    finsetSum_coeff, Polynomial.coeff_C_mul, mul_ite, mul_one, mul_zero]
  by_cases hk : k < m - 1
  · have hkm : k ≠ m := by omega
    rw [ite_eq_right hkm, zero_add, dite_eq_left hk]
    rw [Finset.sum_eq_single (⟨m - 2 - k, by omega⟩ : Fin (m - 1))]
    · dsimp only
      rw [ite_eq_left (by omega)]
    · intro j _ hj
      rw [ite_eq_right]
      intro hjk
      apply hj
      ext
      dsimp only
      have := j.2
      omega
    · intro h
      exact absurd (mem_univ _) h
  · rw [dite_eq_right hk, Finset.sum_eq_zero fun j _ ↦ ?_, add_zero]
    have := j.2
    exact ite_eq_right (by omega)

/-- The coefficient of `X ^ m` in `TauCeti.genericDepressed R m` is `1`. -/
@[simp]
theorem coeff_genericDepressed_self (R : Type*) [CommSemiring R] (m : ℕ) :
    (genericDepressed R m).coeff m = 1 := by
  rw [coeff_genericDepressed, dite_eq_right (by omega), ite_eq_left rfl]

/-- For `i : Fin (m - 1)`, the coefficient of `X ^ (m - (i + 2))` in `TauCeti.genericDepressed R m`
is the indeterminate `MvPolynomial.X i`. -/
theorem coeff_genericDepressed_sub (R : Type*) [CommSemiring R] (m : ℕ) (i : Fin (m - 1)) :
    (genericDepressed R m).coeff (m - ((i : ℕ) + 2)) = MvPolynomial.X i := by
  have hi := i.2
  rw [coeff_genericDepressed, dite_eq_left (by omega)]
  congr 1
  ext
  dsimp only
  omega

/-- Mapping the base ring commutes with forming `TauCeti.genericDepressed`. -/
@[simp]
theorem map_map_genericDepressed {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (m : ℕ) :
    (genericDepressed R m).map (MvPolynomial.map φ) = genericDepressed S m := by
  simp [genericDepressed_def, Polynomial.map_sum]

/-- `TauCeti.genericDepressed R m` is monic for every `m`. -/
@[simp]
theorem monic_genericDepressed (R : Type*) [CommSemiring R] (m : ℕ) :
    (genericDepressed R m).Monic := by
  refine monic_of_natDegree_le_of_coeff_eq_one m ?_ (coeff_genericDepressed_self R m)
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_genericDepressed, dite_eq_right (by omega), ite_eq_right (by omega)]

/-- Over a nontrivial coefficient semiring, `TauCeti.genericDepressed R m` has degree `m`. -/
@[simp]
theorem degree_genericDepressed (R : Type*) [CommSemiring R] [Nontrivial R] (m : ℕ) :
    (genericDepressed R m).degree = m := by
  refine degree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · rw [degree_le_iff_coeff_zero]
    intro k hk
    have hmk : m < k := WithBot.coe_lt_coe.mp hk
    rw [coeff_genericDepressed, dite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [coeff_genericDepressed_self]
    exact one_ne_zero

/-- Over a nontrivial coefficient semiring, `TauCeti.genericDepressed R m` has `natDegree` `m`. -/
@[simp]
theorem natDegree_genericDepressed (R : Type*) [CommSemiring R] [Nontrivial R] (m : ℕ) :
    (genericDepressed R m).natDegree = m :=
  natDegree_eq_of_degree_eq_some (degree_genericDepressed R m)

/-- The subleading coefficient of `TauCeti.genericDepressed R m` vanishes for every `m`. -/
@[simp]
theorem nextCoeff_genericDepressed (R : Type*) [CommSemiring R] (m : ℕ) :
    (genericDepressed R m).nextCoeff = 0 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  rcases m with _ | m
  · rw [nextCoeff, ite_eq_left (natDegree_genericDepressed R 0)]
  · have hpos : 0 < (genericDepressed R (m + 1)).natDegree := by
      rw [natDegree_genericDepressed]
      omega
    rw [nextCoeff_of_natDegree_pos hpos]
    have hdeg := natDegree_genericDepressed R (m + 1)
    have hsub : (genericDepressed R (m + 1)).natDegree - 1 = m := by omega
    rw [hsub, coeff_genericDepressed, dite_eq_right (by omega), ite_eq_right (by omega)]

/-- **Universal specialization of `TauCeti.genericDepressed`.** Every monic depressed polynomial
`f : S[X]` of `natDegree` `m` over an `R`-algebra `S` is obtained from `genericDepressed R m` by
evaluating `X i` at `f.coeff (m - (i + 2))`. -/
theorem map_aeval_coeff_genericDepressed (R : Type*) [CommSemiring R] {S : Type*}
    [CommSemiring S] [Algebra R S] {f : S[X]} {m : ℕ} (hf : f.Monic) (hdeg : f.natDegree = m)
    (hnext : f.nextCoeff = 0) :
    (genericDepressed R m).map
        (MvPolynomial.aeval (R := R) fun i : Fin (m - 1) ↦
          f.coeff (m - ((i : ℕ) + 2))).toRingHom = f := by
  refine AddMonoidAlgebra.ext (DFunLike.ext _ _ fun k ↦ ?_)
  rw [Polynomial.coeff_map, coeff_genericDepressed]
  split_ifs with hk hkm
  · have hk_eq : m - ((m - 2 - k) + 2) = k := by omega
    simp [hk_eq]
  · rw [hkm, map_one, ← hdeg]
    exact hf.leadingCoeff.symm
  · simp only [AlgHom.toRingHom_eq_coe, map_zero]
    rcases eq_or_ne k (m - 1) with rfl | hkne
    · have hm1 : 1 ≤ m := by omega
      have hpos : 0 < f.natDegree := by omega
      have hsub : m - 1 = f.natDegree - 1 := by omega
      rw [hsub, ← nextCoeff_of_natDegree_pos hpos, hnext]
    · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-- For `m = 0`, `TauCeti.genericDepressed R 0` is the constant polynomial `1`. -/
@[simp]
theorem genericDepressed_zero (R : Type*) [CommSemiring R] :
    genericDepressed R 0 = 1 := by
  simp [genericDepressed_def]

/-- For `m = 1`, `TauCeti.genericDepressed R 1` is `X`. -/
@[simp]
theorem genericDepressed_one (R : Type*) [CommSemiring R] :
    genericDepressed R 1 = Polynomial.X := by
  simp [genericDepressed_def]

/-- For `m = 2`, `TauCeti.genericDepressed R 2` is `X ^ 2 + C (X 0)`. -/
theorem genericDepressed_two (R : Type*) [CommSemiring R] :
    genericDepressed R 2 = Polynomial.X ^ 2 + Polynomial.C (MvPolynomial.X 0) := by
  simp [genericDepressed_def]

/-- For `m = 3`, `TauCeti.genericDepressed R 3` is `X ^ 3 + C (X 0) * X + C (X 1)`. -/
theorem genericDepressed_three (R : Type*) [CommSemiring R] :
    genericDepressed R 3 =
      Polynomial.X ^ 3 + Polynomial.C (MvPolynomial.X 0) * Polynomial.X +
        Polynomial.C (MvPolynomial.X 1) := by
  rw [genericDepressed_def, Fin.sum_univ_two]
  simp [add_assoc]

/-- For `m = 4`, `TauCeti.genericDepressed R 4` is
`X ^ 4 + C (X 0) * X ^ 2 + C (X 1) * X + C (X 2)`. -/
theorem genericDepressed_four (R : Type*) [CommSemiring R] :
    genericDepressed R 4 =
      Polynomial.X ^ 4 + Polynomial.C (MvPolynomial.X 0) * Polynomial.X ^ 2 +
        Polynomial.C (MvPolynomial.X 1) * Polynomial.X +
        Polynomial.C (MvPolynomial.X 2) := by
  rw [genericDepressed_def, Fin.sum_univ_three]
  simp [add_assoc]

end GenericDepressed

/-! ### Weights and weighted homogeneity of the generic depressed discriminant -/

section DepressedDiscr

/-- The weight assignment `i ↦ i + 2` on `Fin (m - 1)`, giving the coefficient `aₖ` of
`X ^ (m - k)` in `TauCeti.genericDepressed` weight `k`. -/
def depressedWeight (m : ℕ) : Fin (m - 1) → ℤ :=
  fun i ↦ (i : ℤ) + 2

/-- Explicit formula for `TauCeti.depressedWeight m`. -/
theorem depressedWeight_def (m : ℕ) :
    depressedWeight m = fun i : Fin (m - 1) ↦ (i : ℤ) + 2 :=
  (rfl)

/-- Evaluation of `TauCeti.depressedWeight m` at `i : Fin (m - 1)`. -/
@[simp, grind =]
theorem depressedWeight_apply (m : ℕ) (i : Fin (m - 1)) :
    depressedWeight m i = (i : ℤ) + 2 := by
  rw [depressedWeight_def]

/-- The discriminant of `TauCeti.genericDepressed R m`, as an element of
`MvPolynomial (Fin (m - 1)) R`. -/
noncomputable def depressedDiscr (R : Type*) [CommRing R] (m : ℕ) :
    MvPolynomial (Fin (m - 1)) R :=
  (genericDepressed R m).discr

/-- Unfolding lemma for `TauCeti.depressedDiscr R m` as `(genericDepressed R m).discr`. -/
theorem depressedDiscr_def (R : Type*) [CommRing R] (m : ℕ) :
    depressedDiscr R m = (genericDepressed R m).discr :=
  (rfl)

/-- Mapping the base ring commutes with forming `TauCeti.depressedDiscr`. -/
@[simp]
theorem map_depressedDiscr {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (m : ℕ) :
    MvPolynomial.map φ (depressedDiscr R m) = depressedDiscr S m := by
  rw [depressedDiscr_def, ← (monic_genericDepressed R m).discr_map (MvPolynomial.map φ),
    map_map_genericDepressed, depressedDiscr_def]

/-- Evaluating `TauCeti.depressedDiscr R m` at `a : Fin (m - 1) → S` computes the discriminant of
the specialized depressed polynomial `(genericDepressed R m).map (aeval a)`. -/
theorem aeval_depressedDiscr {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {m : ℕ}
    (a : Fin (m - 1) → S) :
    MvPolynomial.aeval a (depressedDiscr R m) =
      ((genericDepressed R m).map (MvPolynomial.aeval a).toRingHom).discr := by
  rw [depressedDiscr_def, (monic_genericDepressed R m).discr_map]
  rfl

/-- **Universal specialization of `TauCeti.depressedDiscr`.** For any monic depressed polynomial
`f : S[X]` of `natDegree` `m` over an `R`-algebra `S`, evaluating `depressedDiscr R m` at the lower
coefficients `f.coeff (m - (i + 2))` recovers `f.discr`. -/
theorem aeval_coeff_depressedDiscr (R : Type*) [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    {f : S[X]} {m : ℕ} (hf : f.Monic) (hdeg : f.natDegree = m) (hnext : f.nextCoeff = 0) :
    MvPolynomial.aeval (R := R) (fun i : Fin (m - 1) ↦ f.coeff (m - ((i : ℕ) + 2)))
        (depressedDiscr R m) = f.discr := by
  rw [aeval_depressedDiscr, map_aeval_coeff_genericDepressed R hf hdeg hnext]

/-- For any element `u` of an additive commutative monoid `M`, `TauCeti.depressedDiscr R m` is
weighted homogeneous of weight `(m * (m - 1)) • u` when `X i` is given weight `(i + 2) • u`. -/
theorem isWeightedHomogeneous_smul_depressedDiscr (R : Type*) [CommRing R] {M : Type*}
    [AddCommMonoid M] (u : M) (m : ℕ) :
    (depressedDiscr R m).IsWeightedHomogeneous (fun i : Fin (m - 1) ↦ ((i : ℕ) + 2) • u)
      ((m * (m - 1)) • u) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim (depressedDiscr R m) 0]
    exact isWeightedHomogeneous_zero R _ _
  have h := (monic_genericDepressed R m).isWeightedHomogeneous_discr
    (fun i : Fin (m - 1) ↦ ((i : ℕ) + 2) • u) u fun k hk ↦ ?_
  · simpa [depressedDiscr_def, natDegree_genericDepressed] using h
  · rw [natDegree_genericDepressed] at hk ⊢
    rw [coeff_genericDepressed]
    split_ifs with hk' hkm
    · convert isWeightedHomogeneous_X R (fun i : Fin (m - 1) ↦ ((i : ℕ) + 2) • u)
        ⟨m - 2 - k, by omega⟩ using 1
      dsimp only
      congr 1
      omega
    · omega
    · exact isWeightedHomogeneous_zero R _ _

/-- `TauCeti.depressedDiscr R m` is weighted homogeneous of natural-number weight `m * (m - 1)`
with respect to `i ↦ i + 2`. -/
theorem isWeightedHomogeneous_nat_depressedDiscr (R : Type*) [CommRing R] (m : ℕ) :
    (depressedDiscr R m).IsWeightedHomogeneous (fun i : Fin (m - 1) ↦ (i : ℕ) + 2)
      (m * (m - 1)) := by
  simpa using isWeightedHomogeneous_smul_depressedDiscr R (1 : ℕ) m

/-- `TauCeti.depressedDiscr R m` is weighted homogeneous of integer weight `m * (m - 1)` for
`TauCeti.depressedWeight m`. -/
theorem isWeightedHomogeneous_depressedDiscr (R : Type*) [CommRing R] (m : ℕ) :
    (depressedDiscr R m).IsWeightedHomogeneous (depressedWeight m) ((m : ℤ) * (m - 1)) := by
  have h := isWeightedHomogeneous_smul_depressedDiscr R (1 : ℤ) m
  have hw : (fun i : Fin (m - 1) ↦ ((i : ℕ) + 2) • (1 : ℤ)) = depressedWeight m := by
    ext i
    simp [depressedWeight_apply]
  have hd : ((m * (m - 1)) • (1 : ℤ)) = (m : ℤ) * (m - 1) := by
    rcases m with _ | m <;> simp
  rwa [hw, hd] at h

/-- `TauCeti.depressedDiscr R m` belongs to the submodule of weighted homogeneous polynomials of
weight `m * (m - 1)` with respect to `TauCeti.depressedWeight m`. -/
theorem depressedDiscr_mem (R : Type*) [CommRing R] (m : ℕ) :
    depressedDiscr R m ∈
      weightedHomogeneousSubmodule R (depressedWeight m) ((m : ℤ) * (m - 1)) :=
  isWeightedHomogeneous_depressedDiscr R m

end DepressedDiscr

/-! ### Tschirnhaus equivalence between generic monic and depressed discriminants -/

section Tschirnhaus

/-- The `R`-algebra map from the universal monic coefficient ring `MvPolynomial (Fin m) R` to
`(MvPolynomial (Fin (m - 1)) R)[X]`, classifying the shifted generic depressed polynomial
`((genericDepressed R m).map C).comp (X + C X)`. -/
private noncomputable def tschirnhausToDepressed (R : Type*) [CommRing R] (m : ℕ) :
    MvPolynomial (Fin m) R →ₐ[R] (MvPolynomial (Fin (m - 1)) R)[X] :=
  MvPolynomial.aeval fun k : Fin m ↦
    (((genericDepressed R m).map Polynomial.C).comp
      (Polynomial.X + Polynomial.C Polynomial.X)).coeff k

/-- Mapping `Polynomial.freeMonic R m` along `tschirnhausToDepressed` produces the generic
depressed polynomial translated by the indeterminate `Polynomial.X`. -/
private theorem map_tschirnhausToDepressed_freeMonic (R : Type*) [CommRing R] (m : ℕ) :
    (freeMonic R m).map (tschirnhausToDepressed R m).toRingHom =
      ((genericDepressed R m).map Polynomial.C).comp
        (Polynomial.X + Polynomial.C Polynomial.X) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  let Q : (MvPolynomial (Fin (m - 1)) R)[X][X] :=
    ((genericDepressed R m).map Polynomial.C).comp (Polynomial.X + Polynomial.C Polynomial.X)
  have hQ_eq : Q = taylor Polynomial.X ((genericDepressed R m).map Polynomial.C) := by
    rw [taylor_apply]
  have hQmon : Q.Monic := by
    rw [hQ_eq, Monic.def, leadingCoeff_taylor]
    exact ((monic_genericDepressed R m).map Polynomial.C).leadingCoeff
  have hQdeg : Q.natDegree = m := by
    rw [hQ_eq, natDegree_taylor, (monic_genericDepressed R m).natDegree_map,
      natDegree_genericDepressed]
  exact congrArg Subtype.val
    ((MvPolynomial.mapEquivMonic R _ m).apply_symm_apply (.mk Q hQmon hQdeg))

/-- The normalized subleading coefficient `m⁻¹ • X ⟨m - 1, _⟩` (negated root barycenter) of
`Polynomial.freeMonic R m` when `IsUnit (m : R)` (and `0` in the subsingleton case `m = 0`). -/
private noncomputable def tschirnhausNegBarycenter {R : Type*} [CommRing R] {m : ℕ}
    (hmu : IsUnit (m : R)) : MvPolynomial (Fin m) R :=
  if hm : m - 1 < m then (↑hmu.unit⁻¹ : R) • MvPolynomial.X ⟨m - 1, hm⟩ else 0

/-- Centering `Polynomial.freeMonic R m` by `- tschirnhausNegBarycenter hmu` to annihilate its
subleading coefficient. -/
private noncomputable def tschirnhausCentered {R : Type*} [CommRing R] {m : ℕ}
    (hmu : IsUnit (m : R)) : (MvPolynomial (Fin m) R)[X] :=
  (freeMonic R m).comp (Polynomial.X - Polynomial.C (tschirnhausNegBarycenter hmu))

/-- The inverse `R`-algebra map `(MvPolynomial (Fin (m - 1)) R)[X] →ₐ[R] MvPolynomial (Fin m) R`
of `tschirnhausToDepressed`, sending `C (X i)` to the `(m - (i + 2))`-nd coefficient of
`tschirnhausCentered hmu` and `Polynomial.X` to `tschirnhausNegBarycenter hmu`. -/
private noncomputable def tschirnhausFromDepressed {R : Type*} [CommRing R] {m : ℕ}
    (hmu : IsUnit (m : R)) :
    (MvPolynomial (Fin (m - 1)) R)[X] →ₐ[R] MvPolynomial (Fin m) R :=
  Polynomial.aevalTower
    (MvPolynomial.aeval fun i : Fin (m - 1) ↦
      (tschirnhausCentered hmu).coeff (m - ((i : ℕ) + 2)))
    (tschirnhausNegBarycenter hmu)

private theorem tschirnhausToDepressed_X_sub_one {R : Type*} [CommRing R] {m : ℕ}
    (hm : m - 1 < m) :
    tschirnhausToDepressed R m (MvPolynomial.X ⟨m - 1, hm⟩) =
      (m : (MvPolynomial (Fin (m - 1)) R)[X]) * Polynomial.X := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  let G : (MvPolynomial (Fin (m - 1)) R)[X][X] := (genericDepressed R m).map Polynomial.C
  have hGmon : G.Monic := (monic_genericDepressed R m).map Polynomial.C
  have hGdeg : G.natDegree = m := by
    rw [(monic_genericDepressed R m).natDegree_map Polynomial.C, natDegree_genericDepressed]
  have hGpos : 0 < G.natDegree := by omega
  have hGnext : G.nextCoeff = 0 := by
    rw [nextCoeff_of_natDegree_pos hGpos, hGdeg, Polynomial.coeff_map, coeff_genericDepressed,
      dite_eq_right (by omega), ite_eq_right (by omega), map_zero]
  have htaylor : (taylor Polynomial.X G).coeff (m - 1) =
      (m : (MvPolynomial (Fin (m - 1)) R)[X]) * Polynomial.X := by
    have htdeg : (taylor Polynomial.X G).natDegree = m := by rw [natDegree_taylor, hGdeg]
    have htpos : 0 < (taylor Polynomial.X G).natDegree := by omega
    have htnext := nextCoeff_of_natDegree_pos htpos
    rw [htdeg] at htnext
    rw [← htnext, nextCoeff_taylor, hGnext, hGdeg, hGmon.leadingCoeff, zero_add, mul_one]
  simpa [tschirnhausToDepressed, G, ← taylor_apply] using htaylor

private theorem tschirnhausToDepressed_tschirnhausNegBarycenter {R : Type*} [CommRing R] {m : ℕ}
    (hmu : IsUnit (m : R)) :
    tschirnhausToDepressed R m (tschirnhausNegBarycenter hmu) = Polynomial.X := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  have hm : m - 1 < m := by
    rcases m with _ | n
    · rw [Nat.cast_zero] at hmu
      exact absurd hmu not_isUnit_zero
    · omega
  rw [tschirnhausNegBarycenter, dite_eq_left hm, map_smul, tschirnhausToDepressed_X_sub_one hm,
    ← smul_mul_assoc]
  have hum : (↑hmu.unit⁻¹ : R) • (m : (MvPolynomial (Fin (m - 1)) R)[X]) = 1 := by
    have h1 := congrArg (algebraMap R (MvPolynomial (Fin (m - 1)) R)[X]) hmu.val_inv_mul
    rwa [map_mul, map_natCast, map_one, ← Algebra.smul_def] at h1
  rw [hum, one_mul]

private theorem map_tschirnhausFromDepressed_comp_C_genericDepressed {R : Type*} [CommRing R]
    {m : ℕ} (hmu : IsUnit (m : R)) :
    (genericDepressed R m).map ((tschirnhausFromDepressed hmu).toRingHom.comp Polynomial.C) =
      tschirnhausCentered hmu := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  have hm : m - 1 < m := by
    rcases m with _ | n
    · rw [Nat.cast_zero] at hmu
      exact absurd hmu not_isUnit_zero
    · omega
  have hP₀_eq : tschirnhausCentered hmu =
      taylor (-tschirnhausNegBarycenter hmu) (freeMonic R m) := by
    simp [tschirnhausCentered, taylor_apply, sub_eq_add_neg]
  have hP₀_mon : (tschirnhausCentered hmu).Monic := by
    rw [hP₀_eq, Monic.def, leadingCoeff_taylor, (monic_freeMonic R m).leadingCoeff]
  have hP₀_deg : (tschirnhausCentered hmu).natDegree = m := by
    rw [hP₀_eq, natDegree_taylor, natDegree_freeMonic]
  have hP₀_next : (tschirnhausCentered hmu).nextCoeff = 0 := by
    have hfpos : 0 < (freeMonic R m).natDegree := by rw [natDegree_freeMonic]; omega
    rw [hP₀_eq, nextCoeff_taylor, nextCoeff_of_natDegree_pos hfpos, natDegree_freeMonic,
      (monic_freeMonic R m).leadingCoeff, mul_one, coeff_freeMonic, dite_eq_left hm,
      tschirnhausNegBarycenter, dite_eq_left hm, Algebra.smul_def, MvPolynomial.algebraMap_eq]
    calc MvPolynomial.X ⟨m - 1, hm⟩ +
          (m : MvPolynomial (Fin m) R) * -(MvPolynomial.C (↑hmu.unit⁻¹ : R) *
            MvPolynomial.X ⟨m - 1, hm⟩)
      _ = (1 - MvPolynomial.C ((m : R) * (↑hmu.unit⁻¹ : R))) * MvPolynomial.X ⟨m - 1, hm⟩ := by
          simp only [map_mul, map_natCast]
          ring
      _ = 0 := by simp [hmu.mul_val_inv]
  have hbase : (tschirnhausFromDepressed hmu).toRingHom.comp Polynomial.C =
      (MvPolynomial.aeval (R := R) fun i : Fin (m - 1) ↦
        (tschirnhausCentered hmu).coeff (m - ((i : ℕ) + 2))).toRingHom :=
    RingHom.ext (Polynomial.aevalTower_C _ _)
  rw [hbase]
  exact map_aeval_coeff_genericDepressed R hP₀_mon hP₀_deg hP₀_next

private theorem tschirnhausToDepressed_comp_tschirnhausFromDepressed {R : Type*} [CommRing R]
    {m : ℕ} (hmu : IsUnit (m : R)) :
    (tschirnhausToDepressed R m).comp (tschirnhausFromDepressed hmu) = AlgHom.id R _ := by
  apply Polynomial.algHom_ext'
  · refine MvPolynomial.algHom_ext fun i ↦ ?_
    have hcomp : (tschirnhausCentered hmu).map (tschirnhausToDepressed R m).toRingHom =
        (genericDepressed R m).map Polynomial.C := by
      rw [tschirnhausCentered, Polynomial.map_comp, map_tschirnhausToDepressed_freeMonic]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, tschirnhausToDepressed_tschirnhausNegBarycenter hmu, comp_assoc]
      have hcancel : (Polynomial.X + Polynomial.C Polynomial.X :
            (MvPolynomial (Fin (m - 1)) R)[X][X]).comp
          (Polynomial.X - Polynomial.C Polynomial.X) = Polynomial.X := by
        simp
      rw [hcancel, comp_X]
    have hcoeff := congrArg (fun p : (MvPolynomial (Fin (m - 1)) R)[X][X] ↦
      p.coeff (m - ((i : ℕ) + 2))) hcomp
    rw [Polynomial.coeff_map, Polynomial.coeff_map, coeff_genericDepressed_sub] at hcoeff
    simpa [tschirnhausFromDepressed, Polynomial.aevalTower_C] using hcoeff
  · simpa [tschirnhausFromDepressed] using tschirnhausToDepressed_tschirnhausNegBarycenter hmu

private theorem tschirnhausFromDepressed_comp_tschirnhausToDepressed {R : Type*} [CommRing R]
    {m : ℕ} (hmu : IsUnit (m : R)) :
    (tschirnhausFromDepressed hmu).comp (tschirnhausToDepressed R m) = AlgHom.id R _ := by
  refine MvPolynomial.algHom_ext fun k ↦ ?_
  have hcomp : ((freeMonic R m).map (tschirnhausToDepressed R m).toRingHom).map
      (tschirnhausFromDepressed hmu).toRingHom = freeMonic R m := by
    rw [map_tschirnhausToDepressed_freeMonic, Polynomial.map_comp, Polynomial.map_map,
      map_tschirnhausFromDepressed_comp_C_genericDepressed]
    have hX_inv : tschirnhausFromDepressed hmu Polynomial.X = tschirnhausNegBarycenter hmu := by
      simp [tschirnhausFromDepressed]
    simp only [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, hX_inv, tschirnhausCentered, comp_assoc]
    have hcancel : (Polynomial.X - Polynomial.C (tschirnhausNegBarycenter hmu)).comp
        (Polynomial.X + Polynomial.C (tschirnhausNegBarycenter hmu)) = Polynomial.X := by
      simp
    rw [hcancel, comp_X]
  have hcoeff := congrArg (fun p : (MvPolynomial (Fin m) R)[X] ↦ p.coeff k) hcomp
  rw [Polynomial.map_map, Polynomial.coeff_map, coeff_freeMonic, dite_eq_left k.2] at hcoeff
  simpa using hcoeff

/-- When `(m : R)` is invertible, centering `Polynomial.freeMonic R m` by its root barycenter
`- m⁻¹ * X (m - 1)` and recording the negated root barycenter (normalized subleading coefficient)
`m⁻¹ * X (m - 1)` in `Polynomial.X` gives an `R`-algebra equivalence
`MvPolynomial (Fin m) R ≃ₐ[R] (MvPolynomial (Fin (m - 1)) R)[X]`. -/
noncomputable def tschirnhausAlgEquiv {R : Type*} [CommRing R] {m : ℕ} (hmu : IsUnit (m : R)) :
    MvPolynomial (Fin m) R ≃ₐ[R] (MvPolynomial (Fin (m - 1)) R)[X] :=
  AlgEquiv.ofAlgHom (tschirnhausToDepressed R m) (tschirnhausFromDepressed hmu)
    (tschirnhausToDepressed_comp_tschirnhausFromDepressed hmu)
    (tschirnhausFromDepressed_comp_tschirnhausToDepressed hmu)

/-- Mapping `Polynomial.freeMonic R m` along `TauCeti.tschirnhausAlgEquiv` produces the generic
depressed polynomial translated by `Polynomial.X`. -/
theorem map_tschirnhausAlgEquiv_freeMonic {R : Type*} [CommRing R] {m : ℕ}
    (hmu : IsUnit (m : R)) :
    (freeMonic R m).map (tschirnhausAlgEquiv hmu).toRingHom =
      ((genericDepressed R m).map Polynomial.C).comp
        (Polynomial.X + Polynomial.C Polynomial.X) :=
  map_tschirnhausToDepressed_freeMonic R m

/-- `TauCeti.tschirnhausAlgEquiv` maps `X k` to the `k`-th coefficient of the shifted generic
depressed polynomial `((genericDepressed R m).map C).comp (X + C X)`. -/
theorem tschirnhausAlgEquiv_X {R : Type*} [CommRing R] {m : ℕ} (hmu : IsUnit (m : R))
    (k : Fin m) :
    tschirnhausAlgEquiv hmu (MvPolynomial.X k) =
      (((genericDepressed R m).map Polynomial.C).comp
        (Polynomial.X + Polynomial.C Polynomial.X)).coeff k := by
  have h := congrArg (fun p : (MvPolynomial (Fin (m - 1)) R)[X][X] ↦ p.coeff k)
    (map_tschirnhausAlgEquiv_freeMonic hmu)
  rw [Polynomial.coeff_map, coeff_freeMonic, dite_eq_left k.2] at h
  exact h

/-- `TauCeti.tschirnhausAlgEquiv` maps the subleading coefficient variable `X ⟨m - 1, hm⟩` to
`m * Polynomial.X`. -/
theorem tschirnhausAlgEquiv_X_sub_one {R : Type*} [CommRing R] {m : ℕ} (hmu : IsUnit (m : R))
    (hm : m - 1 < m) :
    tschirnhausAlgEquiv hmu (MvPolynomial.X ⟨m - 1, hm⟩) =
      (m : (MvPolynomial (Fin (m - 1)) R)[X]) * Polynomial.X :=
  tschirnhausToDepressed_X_sub_one hm

/-- The inverse of `TauCeti.tschirnhausAlgEquiv` maps `Polynomial.X` to the normalized subleading
coefficient `(↑hmu.unit⁻¹ : R) • X ⟨m - 1, hm⟩` (the negated root barycenter). -/
theorem tschirnhausAlgEquiv_symm_X {R : Type*} [CommRing R] {m : ℕ} (hmu : IsUnit (m : R))
    (hm : m - 1 < m) :
    (tschirnhausAlgEquiv hmu).symm Polynomial.X =
      (↑hmu.unit⁻¹ : R) • MvPolynomial.X ⟨m - 1, hm⟩ := by
  rw [tschirnhausAlgEquiv, AlgEquiv.ofAlgHom_symm_apply, tschirnhausFromDepressed,
    Polynomial.aevalTower_X, tschirnhausNegBarycenter, dite_eq_left hm]

/-- Mapping `TauCeti.genericDepressed R m` along `(tschirnhausAlgEquiv hmu).symm` composed with
`Polynomial.C` centers `Polynomial.freeMonic R m` at
`Polynomial.X - C ((tschirnhausAlgEquiv hmu).symm X)`. -/
theorem map_tschirnhausAlgEquiv_symm_comp_C_genericDepressed {R : Type*} [CommRing R] {m : ℕ}
    (hmu : IsUnit (m : R)) :
    (genericDepressed R m).map ((tschirnhausAlgEquiv hmu).symm.toRingHom.comp Polynomial.C) =
      (freeMonic R m).comp
        (Polynomial.X - Polynomial.C ((tschirnhausAlgEquiv hmu).symm Polynomial.X)) := by
  have hX : (tschirnhausAlgEquiv hmu).symm Polynomial.X = tschirnhausNegBarycenter hmu := by
    rw [tschirnhausAlgEquiv, AlgEquiv.ofAlgHom_symm_apply, tschirnhausFromDepressed,
      Polynomial.aevalTower_X]
  rw [hX]
  exact map_tschirnhausFromDepressed_comp_C_genericDepressed hmu

/-- The inverse of `TauCeti.tschirnhausAlgEquiv` maps `Polynomial.C (MvPolynomial.X i)` to the
`(m - (i + 2))`-nd coefficient of `Polynomial.freeMonic R m` centered at
`Polynomial.X - C ((tschirnhausAlgEquiv hmu).symm X)`. -/
theorem tschirnhausAlgEquiv_symm_C_X {R : Type*} [CommRing R] {m : ℕ} (hmu : IsUnit (m : R))
    (i : Fin (m - 1)) :
    (tschirnhausAlgEquiv hmu).symm (Polynomial.C (MvPolynomial.X i)) =
      ((freeMonic R m).comp
        (Polynomial.X - Polynomial.C ((tschirnhausAlgEquiv hmu).symm Polynomial.X))).coeff
        (m - ((i : ℕ) + 2)) := by
  have h := congrArg (fun p : (MvPolynomial (Fin m) R)[X] ↦ p.coeff (m - ((i : ℕ) + 2)))
    (map_tschirnhausAlgEquiv_symm_comp_C_genericDepressed hmu)
  simpa [Polynomial.coeff_map, coeff_genericDepressed_sub] using h

/-- **Tschirnhaus invariance of the universal discriminant.** When `(m : R)` is invertible,
`TauCeti.tschirnhausAlgEquiv` carries `(Polynomial.freeMonic R m).discr` to the constant
polynomial `Polynomial.C (depressedDiscr R m)`. -/
@[simp]
theorem tschirnhausAlgEquiv_discr_freeMonic {R : Type*} [CommRing R] {m : ℕ}
    (hmu : IsUnit (m : R)) :
    tschirnhausAlgEquiv hmu (freeMonic R m).discr = Polynomial.C (depressedDiscr R m) := by
  have h := congrArg Polynomial.discr (map_tschirnhausAlgEquiv_freeMonic hmu)
  rw [(monic_freeMonic R m).discr_map, discr_comp_X_add_C,
    (monic_genericDepressed R m).discr_map] at h
  exact h

/-- The inverse of `TauCeti.tschirnhausAlgEquiv` carries `Polynomial.C (depressedDiscr R m)` back
to `(Polynomial.freeMonic R m).discr`. -/
@[simp]
theorem tschirnhausAlgEquiv_symm_C_depressedDiscr {R : Type*} [CommRing R] {m : ℕ}
    (hmu : IsUnit (m : R)) :
    (tschirnhausAlgEquiv hmu).symm (Polynomial.C (depressedDiscr R m)) =
      (freeMonic R m).discr :=
  (tschirnhausAlgEquiv hmu).symm_apply_eq.mpr (tschirnhausAlgEquiv_discr_freeMonic hmu).symm

/-- When `(m : R)` is a unit, `TauCeti.depressedDiscr R m` is prime in
`MvPolynomial (Fin (m - 1)) R` if and only if `(Polynomial.freeMonic R m).discr` is prime in
`MvPolynomial (Fin m) R`. -/
theorem prime_depressedDiscr_iff_prime_discr_freeMonic_of_isUnit {R : Type*} [CommRing R] {m : ℕ}
    (hmu : IsUnit (m : R)) :
    Prime (depressedDiscr R m) ↔ Prime (freeMonic R m).discr := by
  rw [← Polynomial.prime_C_iff, ← tschirnhausAlgEquiv_discr_freeMonic hmu,
    MulEquiv.prime_iff (tschirnhausAlgEquiv hmu)]

/-- Over a unique factorization domain `R` with `2 ≤ m` and `IsUnit (m : R)`, the generic
depressed discriminant is prime if and only if `(2 : R) ≠ 0`. -/
theorem prime_depressedDiscr_iff_of_isUnit {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {m : ℕ} (hm : 2 ≤ m) (hmu : IsUnit (m : R)) :
    Prime (depressedDiscr R m) ↔ (2 : R) ≠ 0 :=
  (prime_depressedDiscr_iff_prime_discr_freeMonic_of_isUnit hmu).trans
    (prime_discr_freeMonic_iff hm)

/-- **Primality of the generic depressed discriminant over a UFD (invertible degree).** If `R` is a
unique factorization domain in which `2 ≠ 0` and `(m : R)` is a unit, then
`TauCeti.depressedDiscr R m` is prime in `MvPolynomial (Fin (m - 1)) R` for every `m ≥ 2`. -/
theorem prime_depressedDiscr_of_isUnit {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (h2 : (2 : R) ≠ 0) {m : ℕ} (hm : 2 ≤ m)
    (hmu : IsUnit (m : R)) : Prime (depressedDiscr R m) :=
  (prime_depressedDiscr_iff_of_isUnit hm hmu).mpr h2

/-- Over a field `K` of characteristic different from `2` in which `(m : K) ≠ 0`,
`TauCeti.depressedDiscr K m` is prime in `MvPolynomial (Fin (m - 1)) K` for every `m ≥ 2`. -/
theorem prime_depressedDiscr_of_ne_zero {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {m : ℕ}
    (hm : 2 ≤ m) (hm0 : (m : K) ≠ 0) : Prime (depressedDiscr K m) :=
  prime_depressedDiscr_of_isUnit h2 hm (IsUnit.mk0 _ hm0)

/-- Specializing `depressedDiscr R m` (`2 ≤ m`) to the depressed binomial `X ^ m - 1` shows that
any constant divisor `r` of `depressedDiscr R m` divides `m ^ m`. -/
private theorem dvd_pow_of_C_dvd_depressedDiscr_of_two_le {R : Type*} [CommRing R] [Nontrivial R]
    {m : ℕ} (hm : 2 ≤ m) {r : R} (hr : MvPolynomial.C r ∣ depressedDiscr R m) :
    r ∣ (m : R) ^ m := by
  let f : R[X] := Polynomial.X ^ m - Polynomial.C 1
  have hf_mon : f.Monic := monic_X_pow_sub_C 1 (by omega)
  have hf_deg : f.natDegree = m := natDegree_X_pow_sub_C (1 : R)
  have hm1_ne_m : m - 1 ≠ m := by omega
  have hm1_ne_zero : m - 1 ≠ 0 := by omega
  have hf_next : f.nextCoeff = 0 := by
    rw [nextCoeff_of_natDegree_pos (by omega), hf_deg, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, Polynomial.coeff_C, ite_eq_right hm1_ne_m,
      ite_eq_right hm1_ne_zero, sub_zero]
  have hdvd : r ∣ f.discr := by
    have hmap := _root_.map_dvd (MvPolynomial.aeval (R := R) fun i : Fin (m - 1) ↦
      f.coeff (m - ((i : ℕ) + 2))) hr
    simpa [aeval_coeff_depressedDiscr R hf_mon hf_deg hf_next] using hmap
  dsimp only [f] at hdvd
  rw [discr_X_pow_sub_C] at hdvd
  exact (isUnit_neg_one.pow _).dvd_mul_left.mp ((isUnit_neg_one.pow _).dvd_mul_right.mp hdvd)

/-- Specializing `depressedDiscr R m` (`3 ≤ m`) to the depressed polynomial
`X * (X ^ (m - 1) - 1) = X ^ m - X` shows that any constant divisor `r` of `depressedDiscr R m`
divides `(m - 1) ^ (m - 1)`. -/
private theorem dvd_sub_one_pow_of_C_dvd_depressedDiscr_of_three_le {R : Type*} [CommRing R]
    [Nontrivial R] {m : ℕ} (hm : 3 ≤ m) {r : R} (hr : MvPolynomial.C r ∣ depressedDiscr R m) :
    r ∣ ((m - 1 : ℕ) : R) ^ (m - 1) := by
  let g : R[X] := Polynomial.X ^ (m - 1) - Polynomial.C 1
  let f : R[X] := Polynomial.X * g
  have hg_mon : g.Monic := monic_X_pow_sub_C 1 (by omega)
  have hg_deg : g.natDegree = m - 1 := natDegree_X_pow_sub_C (1 : R)
  have hf_mon : f.Monic := monic_X.mul hg_mon
  have hf_deg : f.natDegree = m := by
    rw [monic_X.natDegree_mul hg_mon, natDegree_X, hg_deg]
    omega
  have hm_add : m - 1 + 1 = m := by omega
  have hf_eq : f = Polynomial.X ^ m - Polynomial.X := by
    dsimp only [f, g]
    rw [mul_sub, ← pow_succ', Polynomial.C_1, mul_one, hm_add]
  have hm1_ne_m : m - 1 ≠ m := by omega
  have hone_ne_m1 : 1 ≠ m - 1 := by omega
  have hf_next : f.nextCoeff = 0 := by
    rw [nextCoeff_of_natDegree_pos (by omega), hf_deg, hf_eq, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, ite_eq_right hm1_ne_m,
      ite_eq_right hone_ne_m1, sub_zero]
  have hdvd : r ∣ f.discr := by
    have hmap := _root_.map_dvd (MvPolynomial.aeval (R := R) fun i : Fin (m - 1) ↦
      f.coeff (m - ((i : ℕ) + 2))) hr
    simpa [aeval_coeff_depressedDiscr R hf_mon hf_deg hf_next] using hmap
  have hX_discr : (Polynomial.X : R[X]).discr = 1 := by
    simpa using discr_X_pow_sub_C (0 : R) 1
  have hm1_ne_zero : m - 1 ≠ 0 := by omega
  have hres : Polynomial.X.resultant g = -1 := by
    have hX1 := resultant_X_pow_left g 1 g.natDegree le_rfl
    rw [pow_one, pow_one, ← natDegree_X (R := R)] at hX1
    rw [hX1, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C,
      ite_eq_right hm1_ne_zero.symm, ite_eq_left rfl, zero_sub]
  rw [monic_X.discr_mul hg_mon, hX_discr, hres, neg_one_sq, one_mul, mul_one] at hdvd
  dsimp only [g] at hdvd
  rw [discr_X_pow_sub_C] at hdvd
  exact (isUnit_neg_one.pow _).dvd_mul_left.mp ((isUnit_neg_one.pow _).dvd_mul_right.mp hdvd)

/-- For `3 ≤ m` over any commutative ring `R`, `TauCeti.depressedDiscr R m` has unit content:
specializing to `X ^ m - 1` and `X * (X ^ (m - 1) - 1)` produces coprime powers of `m` and
`m - 1`. -/
private theorem isUnit_of_C_dvd_depressedDiscr_of_three_le {R : Type*} [CommRing R] {m : ℕ}
    (hm : 3 ≤ m) {r : R} (hr : MvPolynomial.C r ∣ depressedDiscr R m) : IsUnit r := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim r 1 ▸ isUnit_one
  have hdvd_m := dvd_pow_of_C_dvd_depressedDiscr_of_two_le (by omega) hr
  have hdvd_m1 := dvd_sub_one_pow_of_C_dvd_depressedDiscr_of_three_le hm hr
  have hm_add : m - 1 + 1 = m := by omega
  have hcop : IsCoprime ((m : R) ^ m) (((m - 1 : ℕ) : R) ^ (m - 1)) := by
    refine IsCoprime.pow ⟨1, -1, ?_⟩
    have hm_eq : (m : R) = ((m - 1 : ℕ) : R) + 1 := by
      conv_lhs => rw [← hm_add]
      push_cast
      rfl
    rw [hm_eq]
    ring
  exact hcop.isUnit_of_dvd' hdvd_m hdvd_m1

/-- **Primality of the generic depressed discriminant over a UFD for `3 ≤ m`.** Unlike degree
`m = 2` (where `depressedDiscr ℤ 2 = -4 X 0` is divisible by `2`), for every `m ≥ 3` over a unique
factorization domain `R` with `(2 : R) ≠ 0` and `(m : R) ≠ 0`, `TauCeti.depressedDiscr R m` has
unit content and is prime in `MvPolynomial (Fin (m - 1)) R`. -/
theorem prime_depressedDiscr_of_three_le {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (h2 : (2 : R) ≠ 0) {m : ℕ} (hm : 3 ≤ m)
    (hm0 : (m : R) ≠ 0) : Prime (depressedDiscr R m) := by
  rw [← UniqueFactorizationMonoid.irreducible_iff_prime]
  let K := FractionRing R
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have h2K : (2 : K) ≠ 0 := by
    rw [← map_ofNat (algebraMap R K) 2]
    exact fun h ↦ h2 (hinj (h.trans (map_zero _).symm))
  have hmK : (m : K) ≠ 0 := by
    rw [← map_natCast (algebraMap R K) m]
    exact fun h ↦ hm0 (hinj (h.trans (map_zero _).symm))
  have hirrK : Irreducible (depressedDiscr K m) :=
    (prime_depressedDiscr_of_ne_zero h2K (by omega) hmK).irreducible
  have hunit_of_map : ∀ {p : MvPolynomial (Fin (m - 1)) R},
      p ∣ depressedDiscr R m → IsUnit (MvPolynomial.map (algebraMap R K) p) → IsUnit p := by
    intro p hp hu
    obtain ⟨q, -, hq⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
    have hpC : p = MvPolynomial.C (p.coeff 0) := by
      ext d
      have hd := congrArg (fun g ↦ g.coeff d) hq
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C] at hd
      rw [MvPolynomial.coeff_C]
      split_ifs at hd ⊢ with hd0
      · subst hd0; rfl
      · exact hinj (hd.trans (map_zero _).symm)
    rw [hpC]
    exact (isUnit_of_C_dvd_depressedDiscr_of_three_le hm (hpC ▸ hp)).map MvPolynomial.C
  refine ⟨fun hu ↦ hirrK.not_isUnit ?_, fun f g hfg ↦ ?_⟩
  · rw [← map_depressedDiscr (algebraMap R K) m]
    exact hu.map (MvPolynomial.map (algebraMap R K))
  · have hfgK : depressedDiscr K m =
        MvPolynomial.map (algebraMap R K) f * MvPolynomial.map (algebraMap R K) g := by
      rw [← map_depressedDiscr (algebraMap R K) m, hfg, map_mul]
    rcases hirrK.isUnit_or_isUnit hfgK with hf | hg
    · exact Or.inl (hunit_of_map ⟨g, hfg⟩ hf)
    · exact Or.inr (hunit_of_map ⟨f, by rw [mul_comm, ← hfg]⟩ hg)

/-- Over a field `K` of characteristic zero, `TauCeti.depressedDiscr K m` is prime in
`MvPolynomial (Fin (m - 1)) K` for every `m ≥ 2`. -/
theorem prime_depressedDiscr (K : Type*) [Field K] [CharZero K] (m : ℕ) (hm : 2 ≤ m) :
    Prime (depressedDiscr K m) :=
  prime_depressedDiscr_of_ne_zero two_ne_zero hm (Nat.cast_ne_zero.mpr (by omega))

end Tschirnhaus

/-! ### Explicit low-degree formulas, Weierstrass discriminant, and sharpness -/

section LowDegree

/-- For `m = 0`, `TauCeti.depressedDiscr R 0` is `1`. -/
@[simp]
theorem depressedDiscr_zero (R : Type*) [CommRing R] :
    depressedDiscr R 0 = 1 := by
  rw [depressedDiscr_def, genericDepressed_zero]
  simpa only [Polynomial.C_1] using Polynomial.discr_C (1 : MvPolynomial (Fin 0) R)

/-- For `m = 1`, `TauCeti.depressedDiscr R 1` is `1`. -/
@[simp]
theorem depressedDiscr_one (R : Type*) [CommRing R] :
    depressedDiscr R 1 = 1 := by
  rw [depressedDiscr_def, genericDepressed_one]
  simpa using discr_X_pow_sub_C (0 : MvPolynomial (Fin 0) R) 1

/-- For `m = 2`, the discriminant of `X ^ 2 + a₂` is `-4 a₂`. -/
theorem depressedDiscr_two (R : Type*) [CommRing R] :
    depressedDiscr R 2 = -4 * MvPolynomial.X 0 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  rw [depressedDiscr_def, discr_of_degree_eq_two (degree_genericDepressed R 2)]
  have hc0 : (genericDepressed R 2).coeff 0 = MvPolynomial.X 0 := by
    simpa using coeff_genericDepressed_sub R 2 0
  have hc1 : (genericDepressed R 2).coeff 1 = 0 := by
    rw [coeff_genericDepressed, dite_eq_right (by omega), ite_eq_right (by omega)]
  rw [hc0, hc1, coeff_genericDepressed_self]
  ring

/-- For `m = 3`, the discriminant of `X ^ 3 + a₂ X + a₃` is `-4 a₂ ^ 3 - 27 a₃ ^ 2`. -/
theorem depressedDiscr_three (R : Type*) [CommRing R] :
    depressedDiscr R 3 = -4 * MvPolynomial.X 0 ^ 3 - 27 * MvPolynomial.X 1 ^ 2 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  rw [depressedDiscr_def, discr_of_degree_eq_three (degree_genericDepressed R 3)]
  have hc0 : (genericDepressed R 3).coeff 0 = MvPolynomial.X 1 := by
    simpa using coeff_genericDepressed_sub R 3 1
  have hc1 : (genericDepressed R 3).coeff 1 = MvPolynomial.X 0 := by
    simpa using coeff_genericDepressed_sub R 3 0
  have hc2 : (genericDepressed R 3).coeff 2 = 0 := by
    rw [coeff_genericDepressed, dite_eq_right (by omega), ite_eq_right (by omega)]
  rw [hc0, hc1, hc2, coeff_genericDepressed_self]
  ring

/-- For `m = 4`, the discriminant of `X ^ 4 + a₂ X ^ 2 + a₃ X + a₄`. -/
theorem depressedDiscr_four (R : Type*) [CommRing R] :
    depressedDiscr R 4 =
      256 * MvPolynomial.X 2 ^ 3 - 128 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2 ^ 2 +
        144 * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 -
        27 * MvPolynomial.X 1 ^ 4 + 16 * MvPolynomial.X 0 ^ 4 * MvPolynomial.X 2 -
        4 * MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 2 := by
  rw [depressedDiscr_def, genericDepressed_four, discr_depressedQuartic]

/-- In characteristic `2`, `depressedDiscr R 2` vanishes identically. -/
theorem depressedDiscr_two_of_charTwo (R : Type*) [CommRing R] [CharP R 2] :
    depressedDiscr R 2 = 0 := by
  rw [depressedDiscr_two]
  have h2 : (2 : MvPolynomial (Fin 1) R) = 0 := CharP.ofNat_eq_zero (MvPolynomial (Fin 1) R) 2
  linear_combination -2 * MvPolynomial.X 0 * h2

/-- In characteristic `2`, `depressedDiscr R 2` is not prime. -/
theorem not_prime_depressedDiscr_two_of_charTwo (R : Type*) [CommRing R] [CharP R 2] :
    ¬ Prime (depressedDiscr R 2) := by
  rw [depressedDiscr_two_of_charTwo]
  exact not_prime_zero

/-- In characteristic `3`, `depressedDiscr R 3` collapses to `-X 0 ^ 3`. -/
theorem depressedDiscr_three_of_charThree (R : Type*) [CommRing R] [CharP R 3] :
    depressedDiscr R 3 = -MvPolynomial.X 0 ^ 3 := by
  rw [depressedDiscr_three]
  have h3 : (3 : MvPolynomial (Fin 2) R) = 0 := CharP.ofNat_eq_zero (MvPolynomial (Fin 2) R) 3
  linear_combination (-MvPolynomial.X 0 ^ 3 - 9 * MvPolynomial.X 1 ^ 2) * h3

/-- In characteristic `3`, `depressedDiscr R 3` is not prime. -/
theorem not_prime_depressedDiscr_three_of_charThree (R : Type*) [CommRing R] [CharP R 3] :
    ¬ Prime (depressedDiscr R 3) := by
  have := CharP.nontrivial_of_char_ne_one (R := R) (by decide : 3 ≠ 1)
  rw [depressedDiscr_three_of_charThree]
  intro hp
  have hp' : Prime (MvPolynomial.X 0 ^ 3 : MvPolynomial (Fin 2) R) := by
    simpa using hp.neg
  obtain ⟨q, hq⟩ := hp'.dvd_of_dvd_pow
    (dvd_rfl : (MvPolynomial.X 0 : MvPolynomial (Fin 2) R) ^ 3 ∣ _)
  let ev : MvPolynomial (Fin 2) R →+* R[X] :=
    MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 0]
  have hev := congrArg ev hq
  simp only [ev, map_mul, map_pow, eval₂Hom_X', Matrix.cons_val_zero] at hev
  have hevq0 : ev q ≠ 0 := fun h0 ↦ by
    rw [h0, mul_zero] at hev
    exact X_ne_zero hev
  have hdeg3 : (Polynomial.X ^ 3 * ev q : R[X]).natDegree = 3 + (ev q).natDegree := by
    rw [(monic_X_pow 3).natDegree_mul' hevq0, natDegree_X_pow]
  rw [← hev, natDegree_X] at hdeg3
  omega

/-- Over `ℤ`, `depressedDiscr ℤ 2 = -4 X₀` is not prime because `2` is not a unit in `ℤ`
(witnessing that in degree `m = 2`, unlike `3 ≤ m` in `TauCeti.prime_depressedDiscr_of_three_le`,
`IsUnit (2 : R)` cannot be weakened to `(2 : R) ≠ 0` in
`TauCeti.prime_depressedDiscr_of_isUnit`). -/
theorem not_prime_depressedDiscr_int_two : ¬ Prime (depressedDiscr ℤ 2) := by
  rw [depressedDiscr_two]
  intro hp
  have hdvd : (-4 : MvPolynomial (Fin 1) ℤ) * MvPolynomial.X 0 ∣
      (-2 : MvPolynomial (Fin 1) ℤ) * (2 * MvPolynomial.X 0) :=
    ⟨1, by ring⟩
  rcases hp.dvd_or_dvd hdvd with ⟨q, hq⟩ | ⟨q, hq⟩ <;>
  · have hev := congrArg (MvPolynomial.eval (fun _ ↦ (1 : ℤ))) hq
    simp only [map_mul, map_neg, map_ofNat, MvPolynomial.eval_X, mul_one] at hev
    omega

/-- The **Weierstrass cubic discriminant factor** `4 X₀³ + 27 X₁² = -depressedDiscr R 3` is
weighted homogeneous of weight `12` when `X₀` and `X₁` are given integer weights `4` and `6`. -/
theorem isWeightedHomogeneous_four_mul_X_zero_pow_three_add_twentySeven_mul_X_one_pow_two
    (R : Type*) [CommRing R] :
    (4 * MvPolynomial.X 0 ^ 3 + 27 * MvPolynomial.X 1 ^ 2 :
      MvPolynomial (Fin 2) R).IsWeightedHomogeneous ![(4 : ℤ), 6] 12 := by
  have hw : (![(4 : ℤ), 6] : Fin 2 → ℤ) = fun i : Fin 2 ↦ ((i : ℕ) + 2) • (2 : ℤ) :=
    funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩)
  have hneg : (4 * MvPolynomial.X 0 ^ 3 + 27 * MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) R) =
      -depressedDiscr R 3 := by
    rw [depressedDiscr_three]
    ring
  rw [hneg, hw]
  exact (isWeightedHomogeneous_smul_depressedDiscr R (2 : ℤ) 3).neg

/-- Over a unique factorization domain `R` with `(2 : R) ≠ 0` and `(3 : R) ≠ 0` (including `ℤ`,
any field `k` of characteristic neither `2` nor `3`, and `k[t]` for such a field `k`), the
Weierstrass cubic discriminant factor `4 X₀³ + 27 X₁²` is prime in `MvPolynomial (Fin 2) R`. -/
theorem prime_four_mul_X_zero_pow_three_add_twentySeven_mul_X_one_pow_two {R : Type*}
    [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] (h2 : (2 : R) ≠ 0)
    (h3 : (3 : R) ≠ 0) :
    Prime (4 * MvPolynomial.X 0 ^ 3 + 27 * MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) R) := by
  have hneg : (4 * MvPolynomial.X 0 ^ 3 + 27 * MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) R) =
      -depressedDiscr R 3 := by
    rw [depressedDiscr_three]
    ring
  rw [hneg]
  exact Prime.neg (prime_depressedDiscr_of_three_le h2 (by omega) (by simpa using h3))

end LowDegree

end TauCeti
