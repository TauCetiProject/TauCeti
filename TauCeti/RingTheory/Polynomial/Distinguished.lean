/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Multiplicity
public import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished

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
polynomials at `I` are monotone in `I` and closed under finite products, including the empty
product `1`. Every monic divisor of a polynomial distinguished at `I` is distinguished at
`I.radical`; in particular, distinguished polynomials at `I` are closed under taking monic factors
if and only if `I` is radical.

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
* `Polynomial.IsWeaklyEisensteinAt.mono`, `Polynomial.IsDistinguishedAt.mono`: weak Eisensteinness
  and distinguishedness are monotone in the ideal.
* `Polynomial.IsDistinguishedAt.of_dvd_radical`, `Polynomial.IsDistinguishedAt.of_dvd`,
  `Polynomial.Monic.isDistinguishedAt_mul_iff`: monic factors of polynomials distinguished at `I`
  are distinguished at `I.radical`, hence at `I` when `I` is radical.
* `Ideal.isRadical_iff_forall_isDistinguishedAt_of_dvd`: an ideal `I` is radical if and only if
  distinguishedness at `I` is closed under monic divisors.
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

namespace Polynomial

section CommSemiring

variable {R : Type*} [CommSemiring R] {I J : Ideal R} {f : R[X]}

/-- Weak Eisensteinness at an ideal is monotone in the ideal. -/
theorem IsWeaklyEisensteinAt.mono (hf : f.IsWeaklyEisensteinAt I) (hIJ : I ≤ J) :
    f.IsWeaklyEisensteinAt J :=
  ⟨fun hn ↦ hIJ (hf.mem hn)⟩

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] {I J : Ideal R}

/-- Distinguishedness at an ideal is monotone in the ideal. -/
theorem IsDistinguishedAt.mono {f : R[X]} (hf : f.IsDistinguishedAt I) (hIJ : I ≤ J) :
    f.IsDistinguishedAt J :=
  ⟨hf.toIsWeaklyEisensteinAt.mono hIJ, hf.monic⟩

/-- Over a prime ideal `P`, every monic divisor of a polynomial distinguished at `P` is
distinguished at `P`: modulo `P` it is a monic divisor of `X ^ n` over an integral domain, hence
a power of `X`. -/
private theorem IsDistinguishedAt.of_dvd_of_isPrime {w p : R[X]} {P : Ideal R} [P.IsPrime]
    (hw : w.IsDistinguishedAt P) (hp : p.Monic) (hpw : p ∣ w) : p.IsDistinguishedAt P := by
  have := Ideal.Quotient.isDomain P
  have hdvd : p.map (Ideal.Quotient.mk P) ∣ X ^ w.natDegree :=
    hw.map_eq_X_pow ▸ Polynomial.map_dvd (Ideal.Quotient.mk P) hpw
  obtain ⟨k, -, hk⟩ := (dvd_prime_pow Polynomial.prime_X w.natDegree).1 hdvd
  have hpmap : p.map (Ideal.Quotient.mk P) = X ^ k :=
    eq_of_monic_of_associated (hp.map _) (monic_X_pow k) hk
  have hk_eq : k = p.natDegree := by
    simpa [hp.natDegree_map] using congrArg natDegree hpmap.symm
  refine ⟨⟨fun {n} hn ↦ Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩, hp⟩
  have hcoeff := congrArg (fun q ↦ q.coeff n) (hk_eq ▸ hpmap)
  simpa [coeff_X_pow, hn.ne] using hcoeff

/-- Every monic divisor of a polynomial distinguished at `I` is distinguished at `I.radical`. -/
theorem IsDistinguishedAt.of_dvd_radical {w p : R[X]} (hw : w.IsDistinguishedAt I)
    (hp : p.Monic) (hpw : p ∣ w) : p.IsDistinguishedAt I.radical := by
  refine ⟨⟨fun {n} hn ↦ ?_⟩, hp⟩
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro P ⟨hIP, hP⟩
  exact ((hw.mono hIP).of_dvd_of_isPrime hp hpw).mem hn

/-- Over a radical ideal `I`, every monic divisor of a polynomial distinguished at `I` is
distinguished at `I`. -/
theorem IsDistinguishedAt.of_dvd {w p : R[X]} (hw : w.IsDistinguishedAt I) (hI : I.IsRadical)
    (hp : p.Monic) (hpw : p ∣ w) : p.IsDistinguishedAt I :=
  hI.radical ▸ hw.of_dvd_radical hp hpw

/-- Over a radical ideal `I`, a product of two monic polynomials is distinguished at `I` if and
only if each factor is distinguished at `I`. -/
theorem Monic.isDistinguishedAt_mul_iff {f g : R[X]} (hf : f.Monic) (hg : g.Monic)
    (hI : I.IsRadical) :
    (f * g).IsDistinguishedAt I ↔ f.IsDistinguishedAt I ∧ g.IsDistinguishedAt I :=
  ⟨fun h ↦ ⟨h.of_dvd hI hf (dvd_mul_right f g), h.of_dvd hI hg (dvd_mul_left g f)⟩,
    fun ⟨h₁, h₂⟩ ↦ h₁.mul h₂⟩

end CommRing

end Polynomial

namespace Ideal

open scoped Polynomial

variable {R : Type*} [CommRing R]

/-- **An ideal is radical if and only if distinguishedness at it is closed under monic divisors.**
When `a ^ n ∈ I` with `n ≠ 0`, `X - C a` is a monic divisor of the distinguished polynomial
`X ^ n - C (a ^ n)`. -/
theorem isRadical_iff_forall_isDistinguishedAt_of_dvd (I : Ideal R) :
    I.IsRadical ↔ ∀ ⦃w p : R[X]⦄, w.IsDistinguishedAt I → p.Monic → p ∣ w →
      p.IsDistinguishedAt I := by
  refine ⟨fun hI _ _ hw hp hpw ↦ hw.of_dvd hI hp hpw, fun h a ⟨n, han⟩ ↦ ?_⟩
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Subsingleton.elim a 0 ▸ I.zero_mem
  rcases eq_or_ne n 0 with rfl | hn
  · exact I.eq_top_iff_one.2 (pow_zero a ▸ han) ▸ Submodule.mem_top
  have hw : (Polynomial.X ^ n - Polynomial.C (a ^ n)).IsDistinguishedAt I := by
    refine ⟨⟨fun {k} hk ↦ ?_⟩, Polynomial.monic_X_pow_sub_C (a ^ n) hn⟩
    rw [Polynomial.natDegree_X_pow_sub_C] at hk
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, ite_eq_right hk.ne, zero_sub,
      Polynomial.coeff_C]
    rcases eq_or_ne k 0 with rfl | hk0
    · simpa using I.neg_mem han
    · simp [hk0]
  have hp := h hw (Polynomial.monic_X_sub_C a)
    (map_pow Polynomial.C a n ▸ sub_dvd_pow_sub_pow Polynomial.X (Polynomial.C a) n)
  have h0 := hp.mem (n := 0) (by simp)
  exact I.neg_mem_iff.1 (by simpa using h0)

end Ideal

end
