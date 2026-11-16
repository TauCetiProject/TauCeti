/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.Multiplicity
public import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished

import Mathlib.Algebra.Polynomial.Derivative

/-!
# The polynomial `(1 + X) ^ n - 1`

The polynomial `(1 + X) ^ n - 1` over a ring `R` is monic of degree `n` for `n ≠ 0`,
with constant coefficient `0` and, for `0 < k`, `k`-th coefficient the binomial coefficient
`n.choose k`. Over a commutative ring, when `n = p ^ m` is a power of a prime `p`, every
binomial coefficient `(p ^ m).choose k` with `0 < k < p ^ m` is divisible by `p`, so the
polynomial is *distinguished* at every ideal `I` containing `p`: monic with all non-leading
coefficients in `I`. Over the `p`-adic integers, or any complete local ring of residue
characteristic `p`, this is the shape of divisor for which Mathlib's Weierstrass division is
available.

This is the polynomial cutting out the finite levels of the power-series coordinate on the
completed group algebra `ℤ_p[[Γ]]` of a procyclic pro-`p` group `Γ`: at a level `Γ ⧸ U` of order
`p ^ m`, the class of the topological generator satisfies `σ ^ (p ^ m) = 1`, so
`(1 + X) ^ (p ^ m) - 1` vanishes at `X = σ - 1`.

For a general polynomial `F` distinguished at an ideal `I` with `I ^ e ⊆ (p)`, every root `t` of
`F` in an `O`-algebra satisfies `t ^ deg F ∈ I`, hence `p ∣ t ^ (deg F * e)`. Distinguished
polynomials at `I` are closed under finite products, including the empty product `1`.

## Main results

* `TauCeti.Polynomial.monic_one_add_X_pow_sub_one`: `(1 + X) ^ n - 1` is monic for `n ≠ 0`.
* `TauCeti.Polynomial.natDegree_one_add_X_pow_sub_one`: `(1 + X) ^ n - 1` has `natDegree` equal
  to `n` (at `n = 0` the polynomial is `0`, whose `natDegree` is `0` by convention).
* `TauCeti.Polynomial.isDistinguishedAt_one_add_X_pow_sub_one`: `(1 + X) ^ (p ^ m) - 1` is
  distinguished at every ideal containing `p`.
* `TauCeti.Polynomial.squarefree_one_add_X_pow_sub_one`: over a domain in which `(m : R) ≠ 0`,
  `(1 + X) ^ m - 1` is squarefree.
* `Polynomial.IsDistinguishedAt.natCast_dvd_pow_of_aeval_eq_zero`: a root `t` of a polynomial `F`
  distinguished at `I`, with `I ^ e ⊆ (p)`, satisfies `p ∣ t ^ (deg F * e)`.
* `Polynomial.isDistinguishedAt_one`, `Polynomial.IsDistinguishedAt.pow`,
  `Polynomial.isDistinguishedAt_prod`: `1`, powers and finite products of distinguished
  polynomials are distinguished.
-/

public section

namespace TauCeti

open Polynomial

namespace Polynomial

variable {R : Type*}

section Ring

variable [Ring R]

/-- The polynomial `(1 + X) ^ n - 1` has `natDegree` equal to `n`. For `n ≠ 0` this is its
degree; at `n = 0` the polynomial is `0`, whose `natDegree` is `0` by convention. -/
@[simp]
theorem natDegree_one_add_X_pow_sub_one [Nontrivial R] (n : ℕ) :
    ((1 + X) ^ n - 1 : R[X]).natDegree = n := by
  simpa [add_comm] using
    (natDegree_sub_C (p := (X + C (1 : R)) ^ n) (a := 1)).trans
      (natDegree_pow_X_add_C n 1)

/-- The polynomial `(1 + X) ^ n - 1` is monic for `n ≠ 0`. -/
theorem monic_one_add_X_pow_sub_one {n : ℕ} (hn : n ≠ 0) : ((1 + X) ^ n - 1 : R[X]).Monic := by
  nontriviality R
  rw [Monic, leadingCoeff, natDegree_one_add_X_pow_sub_one]
  simp [coeff_one_add_X_pow, coeff_one, hn]

end Ring

variable [CommRing R]

/-- **`(1 + X) ^ (p ^ m) - 1` is a distinguished polynomial at every ideal containing `p`**, for a
prime `p`: it is monic, its constant coefficient is `0`, and its other non-leading coefficients are
the binomial coefficients `(p ^ m).choose k` with `0 < k < p ^ m`, which `p` divides. -/
theorem isDistinguishedAt_one_add_X_pow_sub_one {p : ℕ} (hp : p.Prime) {I : Ideal R}
    (hI : (p : R) ∈ I) (m : ℕ) : ((1 + X) ^ p ^ m - 1 : R[X]).IsDistinguishedAt I := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨⟨fun hk ↦ by simp [natDegree_of_subsingleton] at hk⟩, monic_of_subsingleton _⟩
  refine ⟨⟨fun {k} hk ↦ ?_⟩, monic_one_add_X_pow_sub_one (pow_ne_zero m hp.ne_zero)⟩
  rw [natDegree_one_add_X_pow_sub_one] at hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp [coeff_one_add_X_pow]
  · rw [coeff_sub, coeff_one_add_X_pow, coeff_one, ite_eq_right hk0.ne', sub_zero]
    exact I.mem_of_dvd (Nat.cast_dvd_cast (hp.dvd_choose_pow hk0.ne' hk.ne)) hI

/-- Over an integral domain `R`, if `(m : R) ≠ 0`, then `(1 + X) ^ m - 1` is squarefree:
`(1 + X) * ω' - m * ω = m` forces any repeated factor to be a constant dividing the leading
coefficient `1` of the monic polynomial `ω`. -/
theorem squarefree_one_add_X_pow_sub_one [IsDomain R] {m : ℕ} (hm : (m : R) ≠ 0) :
    Squarefree ((1 + X) ^ m - 1 : R[X]) := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
  intro F hF
  set ω : R[X] := (1 + X) ^ m - 1
  obtain ⟨Q, hQ⟩ := hF
  -- `(1 + X) · ω' - m · ω = m`, and `F` divides both `ω` and `ω'`.
  have hderiv_ω : derivative ω = C (m : R) * (1 + X) ^ (m - 1) := by
    simp [ω, derivative_pow]
  have hid : (1 + X) * derivative ω - C (m : R) * ω = C (m : R) := by
    rw [hderiv_ω]
    have hpow : (1 + X : R[X]) * (1 + X) ^ (m - 1) = (1 + X) ^ m := mul_pow_sub_one hm0 _
    calc (1 + X) * (C (m : R) * (1 + X) ^ (m - 1)) - C (m : R) * ω
        = C (m : R) * ((1 + X) * (1 + X) ^ (m - 1)) - C (m : R) * ω := by ring
      _ = C (m : R) * (1 + X) ^ m - C (m : R) * ((1 + X) ^ m - 1) := by rw [hpow]
      _ = C (m : R) := by ring
  have hFdvd_ω : F ∣ ω := ⟨F * Q, by rw [hQ, mul_assoc]⟩
  have hFdvd_dω : F ∣ derivative ω := by
    refine ⟨2 * derivative F * Q + F * derivative Q, ?_⟩
    rw [hQ, derivative_mul, derivative_mul]
    ring
  have hFdvd_C : F ∣ C (m : R) :=
    hid ▸ dvd_sub (dvd_mul_of_dvd_right hFdvd_dω _) (dvd_mul_of_dvd_right hFdvd_ω _)
  have hdeg0 : F.natDegree = 0 :=
    Nat.eq_zero_of_le_zero ((natDegree_le_of_dvd hFdvd_C (C_ne_zero.mpr hm)).trans (by simp))
  have hFC : F = C (F.coeff 0) := eq_C_of_natDegree_eq_zero hdeg0
  obtain ⟨S, hS⟩ := hFdvd_ω
  have hlc : F.coeff 0 * S.coeff m = 1 := by
    have hcoeff := congrArg (fun P : R[X] ↦ P.coeff m) hS
    rw [hFC, coeff_C_mul] at hcoeff
    have hmon : ω.coeff m = 1 := by
      rw [← natDegree_one_add_X_pow_sub_one (R := R) m]
      exact (monic_one_add_X_pow_sub_one hm0).leadingCoeff
    exact hcoeff.symm.trans hmon
  exact hFC ▸ (IsUnit.of_mul_eq_one (S.coeff m) hlc).map C

end Polynomial

end TauCeti

namespace Polynomial

variable {R : Type*} [CommRing R] {I : Ideal R}

/-- The constant polynomial `1` is distinguished at every ideal. -/
theorem isDistinguishedAt_one : (1 : R[X]).IsDistinguishedAt I :=
  ⟨⟨fun hn ↦ by simp at hn⟩, monic_one⟩

/-- A power of a distinguished polynomial is distinguished. -/
theorem IsDistinguishedAt.pow {f : R[X]} (hf : f.IsDistinguishedAt I) (n : ℕ) :
    (f ^ n).IsDistinguishedAt I := by
  induction n with
  | zero => exact pow_zero f ▸ isDistinguishedAt_one
  | succ n ih => exact pow_succ f n ▸ ih.mul hf

/-- A finite product of distinguished polynomials is distinguished. -/
theorem isDistinguishedAt_prod {ι : Type*} {s : Finset ι} {f : ι → R[X]}
    (hf : ∀ i ∈ s, (f i).IsDistinguishedAt I) : (∏ i ∈ s, f i).IsDistinguishedAt I :=
  Finset.prod_induction f (·.IsDistinguishedAt I) (fun _ _ ↦ IsDistinguishedAt.mul)
    isDistinguishedAt_one hf

end Polynomial

namespace Polynomial.IsDistinguishedAt

variable {O : Type*} [CommRing O] {I : Ideal O} {F : O[X]} {p e : ℕ}

/-- If `F` is distinguished at `I` and `I ^ e ⊆ (p)`, then every root `t` of `F` in an `O`-algebra
satisfies `p ∣ t ^ (deg F * e)`. -/
theorem natCast_dvd_pow_of_aeval_eq_zero (hF : F.IsDistinguishedAt I)
    (hI : I ^ e ≤ Ideal.span {(p : O)}) {S : Type*} [CommRing S] [Algebra O S] {t : S}
    (ht : aeval t F = 0) : (p : S) ∣ t ^ (F.natDegree * e) := by
  have h := hF.toIsWeaklyEisensteinAt.pow_natDegree_le_of_aeval_zero_of_monic_mem_map ht
    hF.monic F.natDegree natDegree_map_le
  have h' : t ^ (F.natDegree * e) ∈ (Ideal.span {(p : O)}).map (algebraMap O S) := by
    rw [pow_mul]
    exact Ideal.map_mono hI (Ideal.map_pow (algebraMap O S) I e ▸ Ideal.pow_mem_pow h e)
  rwa [Ideal.map_span, Set.image_singleton, map_natCast, Ideal.mem_span_singleton] at h'

end Polynomial.IsDistinguishedAt
