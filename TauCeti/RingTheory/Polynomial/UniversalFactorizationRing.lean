/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing

/-!
# Universal factorization ring and free polynomial

Let `R` be a commutative semiring. Alongside Mathlib's `Polynomial.freeMonic` (the universal monic
polynomial of degree `n`), `Polynomial.freePoly R n` is the universal polynomial of degree at most
`n` with free coefficients over `MvPolynomial (Fin (n + 1)) R`.

## Main definitions

* `Polynomial.freePoly`: the universal polynomial `∑ i : Fin (n + 1), C (X i) * X ^ i` of degree
  at most `n` with free coefficients.

## Main results

* `Polynomial.coeff_freePoly`, `Polynomial.natDegree_freePoly`, `Polynomial.degree_freePoly`,
  `Polynomial.map_map_freePoly`, `Polynomial.map_aeval_coeff_freePoly`: coefficient, degree,
  base-change, and coefficient-specialization lemmas for `Polynomial.freePoly`.
* `Polynomial.UniversalCoprimeFactorizationRing.homEquiv_mkₐ_comp_fst` and
  `Polynomial.UniversalCoprimeFactorizationRing.homEquiv_mkₐ_comp_snd`: composing a point of the
  universal coprime factorization ring with values in `R` with the reduction `R → R ⧸ I` reduces
  both factors modulo `I`.
-/

public section

open Polynomial

namespace Polynomial

section FreePoly

variable (R : Type*) [CommSemiring R] (n : ℕ)

/-- The universal polynomial `∑ i : Fin (n + 1), C (X i) * X ^ i` of degree at most `n` with free
coefficients over `MvPolynomial (Fin (n + 1)) R`, the nonmonic counterpart of
`Polynomial.freeMonic`. -/
noncomputable def freePoly : (MvPolynomial (Fin (n + 1)) R)[X] :=
  ∑ i : Fin (n + 1), C (MvPolynomial.X i) * X ^ (i : ℕ)

variable {R n}

/-- The `k`-th coefficient of `Polynomial.freePoly R n` is `MvPolynomial.X k` for `k ≤ n` and `0`
otherwise. -/
theorem coeff_freePoly (k : ℕ) :
    (freePoly R n).coeff k =
      if hk : k ≤ n then MvPolynomial.X ⟨k, Nat.lt_succ_of_le hk⟩ else 0 := by
  simp only [freePoly, finsetSum_coeff, coeff_C_mul_X_pow]
  split_ifs with hk
  · rw [Finset.sum_eq_single_of_mem (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (n + 1)) (Finset.mem_univ _)
      fun i _ hi ↦ ite_eq_right fun h : k = ↑i ↦ hi (Fin.ext h.symm)]
    exact ite_eq_left rfl
  · exact Finset.sum_eq_zero fun i _ ↦
      ite_eq_right fun h : k = ↑i ↦ hk (h ▸ Nat.le_of_lt_succ i.isLt)

/-- Over a nontrivial ring, `Polynomial.freePoly R n` has `natDegree` equal to `n`. -/
theorem natDegree_freePoly [Nontrivial R] : (freePoly R n).natDegree = n := by
  refine le_antisymm ?_ ?_
  · refine natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ ?_
    rw [coeff_freePoly, dite_eq_right (not_le.mpr hk)]
  · refine le_natDegree_of_ne_zero ?_
    rw [coeff_freePoly, dite_eq_left le_rfl]
    exact MvPolynomial.X_ne_zero _

/-- Over a nontrivial ring, `Polynomial.freePoly R n` has degree `n`. -/
theorem degree_freePoly [Nontrivial R] : (freePoly R n).degree = n := by
  rw [degree_eq_natDegree (fun h ↦ by
    have hc := congrArg (fun p : (MvPolynomial (Fin (n + 1)) R)[X] ↦ p.coeff n) h
    rw [coeff_freePoly, dite_eq_left le_rfl, coeff_zero] at hc
    exact MvPolynomial.X_ne_zero _ hc), natDegree_freePoly]

/-- Mapping the base ring commutes with forming `Polynomial.freePoly`. -/
theorem map_map_freePoly {S : Type*} [CommSemiring S] (φ : R →+* S) (n : ℕ) :
    (freePoly R n).map (MvPolynomial.map φ) = freePoly S n := by
  simp [freePoly, Polynomial.map_sum]

/-- Specializing `Polynomial.freePoly R n` at the coefficients of a polynomial `p : S[X]` with
`p.natDegree ≤ n` over an `R`-algebra `S` recovers `p`. -/
theorem map_aeval_coeff_freePoly {S : Type*} [CommSemiring S] [Algebra R S]
    {p : S[X]} {n : ℕ} (hn : p.natDegree ≤ n) :
    (freePoly R n).map
        (MvPolynomial.aeval (R := R) fun i : Fin (n + 1) ↦ p.coeff i).toRingHom =
      p := by
  ext k
  rw [coeff_map, coeff_freePoly]
  split_ifs with hk
  · simp
  · rw [map_zero, eq_comm]
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hn (not_le.mp hk))

end FreePoly

end Polynomial

namespace Polynomial.UniversalCoprimeFactorizationRing

variable {R : Type*} [CommRing R] (I : Ideal R) {n : ℕ} (m k : ℕ) (hn : n = m + k)
  (P : MonicDegreeEq R n) (φ : UniversalCoprimeFactorizationRing m k hn P →ₐ[R] R)

/-- Composing a point of the universal coprime factorization ring with values in `R` with the
reduction `R → R ⧸ I` reduces its first factor modulo `I`. -/
lemma homEquiv_mkₐ_comp_fst :
    (homEquiv (R ⧸ I) m k hn P ((Ideal.Quotient.mkₐ R I).comp φ)).val.1.val =
      (homEquiv R m k hn P φ).val.1.val.map (Ideal.Quotient.mk I) := by
  rw [homEquiv_comp_fst, ← AlgHom.toRingHom_eq_coe, Ideal.Quotient.mkₐ_toRingHom]
  simp

/-- Composing a point of the universal coprime factorization ring with values in `R` with the
reduction `R → R ⧸ I` reduces its second factor modulo `I`. -/
lemma homEquiv_mkₐ_comp_snd :
    (homEquiv (R ⧸ I) m k hn P ((Ideal.Quotient.mkₐ R I).comp φ)).val.2.val =
      (homEquiv R m k hn P φ).val.2.val.map (Ideal.Quotient.mk I) := by
  rw [homEquiv_comp_snd, ← AlgHom.toRingHom_eq_coe, Ideal.Quotient.mkₐ_toRingHom]
  simp

end Polynomial.UniversalCoprimeFactorizationRing
