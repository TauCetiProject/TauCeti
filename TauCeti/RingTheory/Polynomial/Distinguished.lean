/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Multiplicity
public import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished

import Mathlib.RingTheory.IntegralClosure.GoingDown

/-!
# The polynomial `(1 + X) ^ n - 1` and distinguished polynomials

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
polynomials at `I` are closed under finite products, including the empty product `1`, and under
monic divisors when `I` is radical (via Mathlib's `Polynomial.coeff_mem_radical_span_coeff_of_dvd`).

## Main results

* `TauCeti.Polynomial.monic_one_add_X_pow_sub_one`: `(1 + X) ^ n - 1` is monic for `n ≠ 0`.
* `TauCeti.Polynomial.natDegree_one_add_X_pow_sub_one`: `(1 + X) ^ n - 1` has `natDegree` equal
  to `n` (at `n = 0` the polynomial is `0`, whose `natDegree` is `0` by convention).
* `TauCeti.Polynomial.isDistinguishedAt_one_add_X_pow_sub_one`: `(1 + X) ^ (p ^ m) - 1` is
  distinguished at every ideal containing `p`.
* `Polynomial.IsDistinguishedAt.natCast_dvd_pow_of_aeval_eq_zero`: a root `t` of a polynomial `F`
  distinguished at `I`, with `I ^ e ⊆ (p)`, satisfies `p ∣ t ^ (deg F * e)`.
* `Polynomial.isDistinguishedAt_one`, `Polynomial.IsDistinguishedAt.pow`,
  `Polynomial.isDistinguishedAt_prod`: `1`, powers and finite products of distinguished
  polynomials are distinguished.
* `Polynomial.IsDistinguishedAt.isDistinguishedAt_radical_of_dvd`,
  `Polynomial.IsDistinguishedAt.of_dvd`: monic divisors of a polynomial distinguished at `I` are
  distinguished at `I.radical`, hence at `I` when `I` is radical.
* `Polynomial.IsDistinguishedAt.exists_C_mul_isDistinguishedAt_of_dvd`: over a ring without zero
  divisors, any divisor of a polynomial distinguished at a radical ideal is a unit-constant
  multiple of a distinguished polynomial.
* `Polynomial.IsDistinguishedAt.isUnit_iff_coeff_zero_notMem`: a polynomial distinguished at a
  proper ideal `I` is a unit if and only if its constant term lies outside `I`.
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

/-- Every monic divisor of a polynomial distinguished at an ideal `I` is distinguished at the
radical `I.radical`. -/
theorem IsDistinguishedAt.isDistinguishedAt_radical_of_dvd {f p : R[X]}
    (hf : f.IsDistinguishedAt I) (hp : p.Monic) (hpf : p ∣ f) :
    p.IsDistinguishedAt I.radical :=
  ⟨⟨fun {i} hi ↦ Ideal.radical_mono
      (Ideal.span_le.2 (by rintro _ ⟨k, hk, rfl⟩; exact hf.mem hk))
      (coeff_mem_radical_span_coeff_of_dvd f p hf.monic hp hpf i hi.ne)⟩, hp⟩

/-- Every monic divisor of a polynomial distinguished at a radical ideal `I` is distinguished at
`I`. -/
theorem IsDistinguishedAt.of_dvd {f p : R[X]} (hf : f.IsDistinguishedAt I)
    (hI : I.IsRadical) (hp : p.Monic) (hpf : p ∣ f) : p.IsDistinguishedAt I :=
  hI.radical ▸ hf.isDistinguishedAt_radical_of_dvd hp hpf

/-- Over a ring without zero divisors, every divisor of a polynomial distinguished at a radical
ideal `I` is a unit-constant multiple of a polynomial distinguished at `I`. -/
theorem IsDistinguishedAt.exists_C_mul_isDistinguishedAt_of_dvd [NoZeroDivisors R] {f d : R[X]}
    (hf : f.IsDistinguishedAt I) (hI : I.IsRadical) (hdf : d ∣ f) :
    ∃ (u : Rˣ) (p : R[X]), p.IsDistinguishedAt I ∧ d = C (u : R) * p := by
  obtain ⟨q, hfq⟩ := hdf
  obtain ⟨u, hu_eq⟩ := IsUnit.of_mul_eq_one q.leadingCoeff (by
    rw [← leadingCoeff_mul, ← hfq, hf.monic.leadingCoeff])
  refine ⟨u, C ((u⁻¹ : Rˣ) : R) * d, hf.of_dvd hI ?_ ?_, by
    rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]⟩
  · rw [Monic, leadingCoeff_mul, leadingCoeff_C, ← hu_eq, Units.inv_mul]
  · exact ⟨C (u : R) * q, by rw [hfq, ← mul_assoc, mul_right_comm (C ((u⁻¹ : Rˣ) : R)), ← map_mul,
      Units.inv_mul, map_one, one_mul]⟩

/-- A polynomial distinguished at a proper ideal `I` is a unit if and only if its constant term
lies outside `I`. -/
theorem IsDistinguishedAt.isUnit_iff_coeff_zero_notMem {f : R[X]} (hf : f.IsDistinguishedAt I)
    (hI : I ≠ ⊤) : IsUnit f ↔ f.coeff 0 ∉ I := by
  refine ⟨fun hu h0 ↦ hI ?_, fun h0 ↦ ?_⟩
  · rw [hf.monic.isUnit_iff.1 hu] at h0
    exact Ideal.eq_top_of_isUnit_mem I (by simpa using h0) isUnit_one
  · rw [hf.monic.isUnit_iff]
    refine eq_one_of_monic_natDegree_zero hf.monic ?_
    by_contra hdeg
    exact h0 (hf.mem (Nat.pos_of_ne_zero hdeg))

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
