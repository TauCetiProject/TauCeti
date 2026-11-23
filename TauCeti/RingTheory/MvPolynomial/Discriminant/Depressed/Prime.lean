/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Discriminant.Depressed.Basic

import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Prime
import TauCeti.RingTheory.MvPolynomial.Discriminant.Generic
import TauCeti.RingTheory.Polynomial.Resultant.RootCoordinates

/-!
# Primality and Tschirnhaus transport of the generic depressed discriminant

When `(m : R)` is invertible, the Tschirnhaus `R`-algebra equivalence
`TauCeti.tschirnhausAlgEquiv : MvPolynomial (Fin m) R ≃ₐ[R] (MvPolynomial (Fin (m - 1)) R)[X]`
carries `(Polynomial.freeMonic R m).discr` to `Polynomial.C (TauCeti.depressedDiscr R m)` by
translation invariance of the discriminant (`TauCeti.tschirnhausAlgEquiv_discr_freeMonic`). Over any
integral domain `R` with `(2 : R) ≠ 0` and `IsUnit (m : R)`, this gives primality of
`TauCeti.depressedDiscr R m` for every `m ≥ 2` (`TauCeti.prime_depressedDiscr_of_isUnit`).

For `3 ≤ m` over any integral domain `R` with `(2 : R) ≠ 0` and `(m : R) ≠ 0`, specializing to
`X ^ m - 1` and `X ^ m - X` shows that `TauCeti.depressedDiscr R m` has unit content
(`TauCeti.isUnit_of_C_dvd_depressedDiscr_of_three_le`). Localizing away from `m` gives primality
over `Rₘ`, and specializing `X ^ m + a_{m-1} X` modulo `m` exhibits a unit coefficient `±1` in
`depressedDiscr (R ⧸ Ideal.span {(m : R)}) m`, which by McCoy's regularity lemma makes the
discriminant ideal saturated with respect to `m`. Hence `TauCeti.depressedDiscr R m` is prime
over any integral domain `R` with `(2 : R) ≠ 0` and `(m : R) ≠ 0` (`3 ≤ m`), without requiring
unique factorization (`TauCeti.prime_depressedDiscr_of_three_le`).

For `m = 2`, `TauCeti.depressedDiscr R 2 = -4 X₀` is prime over an integral domain `R` if and only
if `IsUnit (2 : R)` (`TauCeti.prime_depressedDiscr_two_iff`), and counterexamples in
characteristics `2`, `3`, and over `ℤ` show sharpness.

## Main results

* `TauCeti.tschirnhausAlgEquiv_discr_freeMonic`,
  `TauCeti.prime_depressedDiscr_iff_prime_discr_freeMonic_of_isUnit`: identification of generic
  monic and depressed discriminants when `m` is invertible.
* `TauCeti.isUnit_of_C_dvd_depressedDiscr_of_three_le`, `TauCeti.prime_depressedDiscr_of_isUnit`,
  `TauCeti.prime_depressedDiscr_of_three_le`, `TauCeti.prime_depressedDiscr_of_ne_zero`,
  `TauCeti.depressedDiscr_prime`: unit content for `3 ≤ m` and integral-domain primality of
  `depressedDiscr`.
* `TauCeti.prime_depressedDiscr_two_iff`, `TauCeti.not_prime_depressedDiscr_two_of_charTwo`,
  `TauCeti.not_prime_depressedDiscr_three_of_charThree`,
  `TauCeti.not_prime_depressedDiscr_int_two`: degree-`2` criterion and sharpness counterexamples.

## References

* S. Lang, *Algebra*, Revised Third Edition, GTM 211, Springer (2002), Chapter IV, §8.
* I. M. Gelfand, M. M. Kapranov, A. V. Zelevinsky, *Discriminants, Resultants, and
  Multidimensional Determinants*, Birkhäuser (1994), Chapter 12, §1.B.
-/

public section

open Finset MvPolynomial Polynomial

namespace TauCeti

section Tschirnhaus

/-- **Tschirnhaus invariance of the universal discriminant.** When `(m : R)` is invertible,
`TauCeti.tschirnhausAlgEquiv` carries `(Polynomial.freeMonic R m).discr` to the constant
polynomial `Polynomial.C (depressedDiscr R m)`. -/
@[simp]
theorem tschirnhausAlgEquiv_discr_freeMonic {R : Type*} [CommRing R] {m : ℕ}
    (hmu : IsUnit (m : R)) :
    tschirnhausAlgEquiv hmu (freeMonic R m).discr = Polynomial.C (depressedDiscr R m) := by
  have h := congrArg Polynomial.discr (map_tschirnhausAlgEquiv_freeMonic hmu)
  rw [(monic_freeMonic R m).discr_map, discr_comp_X_add_C,
    (monic_genericDepressed (R := R) (m := m)).discr_map, discr_genericDepressed] at h
  simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_toRingEquiv] using h

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

/-- Over an integral domain `R` with `2 ≤ m` and `IsUnit (m : R)`, the generic depressed
discriminant is prime if and only if `(2 : R) ≠ 0`. -/
theorem prime_depressedDiscr_iff_of_isUnit {R : Type*} [CommRing R] [IsDomain R]
    {m : ℕ} (hm : 2 ≤ m) (hmu : IsUnit (m : R)) :
    Prime (depressedDiscr R m) ↔ (2 : R) ≠ 0 :=
  (prime_depressedDiscr_iff_prime_discr_freeMonic_of_isUnit hmu).trans
    (prime_discr_freeMonic_iff hm)

/-- **Primality of the generic depressed discriminant over a domain (invertible degree).** If `R` is
an integral domain in which `2 ≠ 0` and `(m : R)` is a unit, then `TauCeti.depressedDiscr R m` is
prime in `MvPolynomial (Fin (m - 1)) R` for every `m ≥ 2`. -/
theorem prime_depressedDiscr_of_isUnit {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} (hm : 2 ≤ m) (hmu : IsUnit (m : R)) :
    Prime (depressedDiscr R m) :=
  (prime_depressedDiscr_iff_of_isUnit hm hmu).mpr h2

/-- Over a field `K` of characteristic different from `2` in which `(m : K) ≠ 0`,
`TauCeti.depressedDiscr K m` is prime in `MvPolynomial (Fin (m - 1)) K` for every `m ≥ 2`. -/
theorem prime_depressedDiscr_of_ne_zero {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {m : ℕ}
    (hm : 2 ≤ m) (hm0 : (m : K) ≠ 0) : Prime (depressedDiscr K m) :=
  prime_depressedDiscr_of_isUnit h2 hm (IsUnit.mk0 _ hm0)

/-- A constant divisor of `depressedDiscr R m` divides the discriminant of any monic depressed
polynomial of degree `m`. -/
private theorem dvd_discr_of_C_dvd_depressedDiscr {R : Type*} [CommRing R] {m : ℕ} {r : R}
    (hr : MvPolynomial.C r ∣ depressedDiscr R m) {f : R[X]} (hf_mon : f.Monic)
    (hf_deg : f.natDegree = m) (hf_next : f.nextCoeff = 0) : r ∣ f.discr := by
  have hmap := _root_.map_dvd (MvPolynomial.aeval (R := R) fun i : Fin (m - 1) ↦
    f.coeff (m - 2 - (i : ℕ))) hr
  simpa [← hf_mon.discr_eq_aeval_depressedDiscr hf_deg hf_next] using hmap

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
  have hdvd : r ∣ f.discr := dvd_discr_of_C_dvd_depressedDiscr hr hf_mon hf_deg hf_next
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
  have hdvd : r ∣ f.discr := dvd_discr_of_C_dvd_depressedDiscr hr hf_mon hf_deg hf_next
  rw [hf_eq, discr_X_pow_sub_X (by omega)] at hdvd
  exact (isUnit_neg_one.pow _).dvd_mul_left.mp hdvd

/-- For `3 ≤ m` over any commutative ring `R`, `TauCeti.depressedDiscr R m` has unit content:
specializing to `X ^ m - 1` and `X ^ m - X` produces coprime powers of `m` and `m - 1`. -/
theorem isUnit_of_C_dvd_depressedDiscr_of_three_le {R : Type*} [CommRing R] {m : ℕ}
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

/-- A univariate polynomial over a commutative ring that has a regular coefficient is itself
regular (McCoy). -/
private theorem isRegular_polynomial_of_exists_isRegular_coeff {A : Type*} [CommRing A]
    {p : A[X]} (hp : ∃ k : ℕ, IsRegular (p.coeff k)) : IsRegular p := by
  suffices hleft : ∀ g : A[X], p * g = 0 → g = 0 by
    exact ⟨fun a b h ↦ by
      dsimp only at h
      exact sub_eq_zero.mp (hleft _ (by rw [mul_sub, h, sub_self])),
      fun a b h ↦ by
      dsimp only at h
      exact sub_eq_zero.mp (hleft _ (by rw [mul_comm, sub_mul, h, sub_self]))⟩
  have hbound : ∀ d : ℕ, ∀ g : A[X], g.natDegree ≤ d → p * g = 0 → g = 0 := by
    classical
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro g hgd hpg
      by_contra hg0
      have hkill : ∀ r : A, r * g.leadingCoeff = 0 → Polynomial.C r * g = 0 := by
        intro r hr
        rcases Nat.eq_zero_or_pos g.natDegree with hg0d | _hgpos
        · rw [eq_C_of_natDegree_eq_zero hg0d, ← Polynomial.C_mul]
          simp only [leadingCoeff, hg0d] at hr
          rw [hr, map_zero]
        · by_contra hcr0
          have hdeg_lt : (Polynomial.C r * g).degree < (g.natDegree : WithBot ℕ) := by
            rw [Polynomial.degree_lt_iff_coeff_zero]
            intro n hn
            rw [Polynomial.coeff_C_mul]
            rcases eq_or_lt_of_le hn with rfl | hlt
            · exact hr
            · rw [coeff_eq_zero_of_natDegree_lt hlt, mul_zero]
          have hlt : (Polynomial.C r * g).natDegree < g.natDegree :=
            (Polynomial.natDegree_lt_iff_degree_lt hcr0).mpr hdeg_lt
          exact hcr0 (ih (Polynomial.C r * g).natDegree (lt_of_lt_of_le hlt hgd)
            (Polynomial.C r * g) le_rfl (by rw [mul_left_comm, hpg, mul_zero]))
      have hlead : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg0
      obtain ⟨k, hk⟩ := hp
      have hk_ne : p.coeff k * g.leadingCoeff ≠ 0 := by
        intro h0
        exact hlead (hk.left (by simpa only [mul_zero] using h0))
      have hk_pk : p.coeff k ≠ 0 := fun h0 ↦ hk_ne (by rw [h0, zero_mul])
      have hk_le : k ≤ p.natDegree := Polynomial.le_natDegree_of_ne_zero hk_pk
      let S : Finset ℕ :=
        (Finset.range (p.natDegree + 1)).filter fun i ↦ Polynomial.C (p.coeff i) * g ≠ 0
      have hkS : k ∈ S := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hk_le), fun h0 ↦ ?_⟩
        have hc := congrArg (fun q : A[X] ↦ q.coeff g.natDegree) h0
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_zero] at hc
        exact hk_ne hc
      let i : ℕ := S.max' ⟨k, hkS⟩
      have hiS : i ∈ S := S.max'_mem ⟨k, hkS⟩
      have hgt : ∀ j : ℕ, i < j → Polynomial.C (p.coeff j) * g = 0 := by
        intro j hij
        by_cases hj : j ≤ p.natDegree
        · by_contra hne
          have hjS : j ∈ S := Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hj), hne⟩
          exact absurd (S.le_max' j hjS) (not_le_of_gt hij)
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hj), map_zero, zero_mul]
      have hcoeff0 : (p * g).coeff (i + g.natDegree) = 0 := by rw [hpg, Polynomial.coeff_zero]
      have hcoeff_eq : (p * g).coeff (i + g.natDegree) = p.coeff i * g.leadingCoeff := by
        conv_lhs => rw [p.as_sum_range_C_mul_X_pow]
        rw [Finset.sum_mul, Polynomial.finsetSum_coeff]
        have hi_mem : i ∈ Finset.range (p.natDegree + 1) := (Finset.mem_filter.mp hiS).1
        rw [Finset.sum_eq_single i]
        · rw [mul_assoc, mul_comm (Polynomial.X ^ i) g, ← mul_assoc, add_comm i g.natDegree,
            Polynomial.coeff_mul_X_pow, Polynomial.coeff_C_mul]
          rfl
        · intro j _hj hji
          rcases lt_or_gt_of_ne hji with hlt | hgt_j
          · rw [mul_assoc, mul_comm (Polynomial.X ^ j) g, ← mul_assoc,
              Polynomial.coeff_mul_X_pow', ite_eq_left (by omega), Polynomial.coeff_C_mul,
              Polynomial.coeff_eq_zero_of_natDegree_lt (p := g) (by omega), mul_zero]
          · rw [mul_assoc, mul_comm (Polynomial.X ^ j) g, ← mul_assoc, hgt j hgt_j, zero_mul,
              Polynomial.coeff_zero]
        · intro hi_nmem; exact absurd hi_mem hi_nmem
      have hi_lead : p.coeff i * g.leadingCoeff = 0 := hcoeff_eq.symm.trans hcoeff0
      exact (Finset.mem_filter.mp hiS).2 (hkill (p.coeff i) hi_lead)
  exact fun g hpg ↦ hbound g.natDegree g le_rfl hpg

/-- A multivariate polynomial over `Fin n` with a regular coefficient is regular. -/
private theorem isRegular_mvPolynomial_fin_of_exists_isRegular_coeff {A : Type*} [CommRing A] :
    ∀ {n : ℕ} {P : MvPolynomial (Fin n) A}, (∃ d : Fin n →₀ ℕ, IsRegular (P.coeff d)) →
      IsRegular P
  | 0, P, ⟨d, hd⟩ => by
    have hd0 : d = 0 := Subsingleton.elim d 0
    have hP : P = MvPolynomial.C (P.coeff 0) := by
      ext e
      rw [Subsingleton.elim e 0, MvPolynomial.coeff_C, ite_eq_left rfl]
    rw [hd0] at hd
    rw [hP]
    refine ⟨fun x y h ↦ ?_, fun x y h ↦ ?_⟩
    · ext e
      have he0 : e = 0 := Subsingleton.elim e 0
      subst he0
      have hc := congrArg (fun q : MvPolynomial (Fin 0) A ↦ q.coeff 0) h
      simp only [MvPolynomial.coeff_C_mul] at hc
      exact hd.left hc
    · ext e
      have he0 : e = 0 := Subsingleton.elim e 0
      subst he0
      have hc := congrArg (fun q : MvPolynomial (Fin 0) A ↦ q.coeff 0) h
      simp only [mul_comm _ (MvPolynomial.C _), MvPolynomial.coeff_C_mul] at hc
      exact hd.left hc
  | n + 1, P, ⟨d, hd⟩ => by
    let e := MvPolynomial.finSuccEquiv A n
    let d' : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j ↦ d j.succ
    have hcons : d'.cons (d 0) = d := by
      ext k
      refine Fin.cases rfl (fun j ↦ ?_) k
      simp [d', Finsupp.cons_succ]
    have hcoeff : ((e P).coeff (d 0)).coeff d' = P.coeff d := by
      rw [MvPolynomial.finSuccEquiv_coeff_coeff, hcons]
    have hreg_coeff : IsRegular ((e P).coeff (d 0)) :=
      isRegular_mvPolynomial_fin_of_exists_isRegular_coeff ⟨d', hcoeff.symm ▸ hd⟩
    have hreg_eP : IsRegular (e P) :=
      isRegular_polynomial_of_exists_isRegular_coeff ⟨d 0, hreg_coeff⟩
    refine ⟨fun x y h ↦ e.injective (hreg_eP.left ?_), fun x y h ↦ e.injective (hreg_eP.right ?_)⟩
    · dsimp only at h ⊢; rw [← map_mul, h, map_mul]
    · dsimp only at h ⊢; rw [← map_mul, h, map_mul]

/-- Over a quotient `R₀ = R ⧸ Ideal.span {(m : R)}` with `3 ≤ m`, `depressedDiscr R₀ m` has a
unit coefficient and is therefore regular in `MvPolynomial (Fin (m - 1)) R₀`. -/
private theorem isRegular_depressedDiscr_quotient {R : Type*} [CommRing R] {m : ℕ} (hm : 3 ≤ m) :
    IsRegular (depressedDiscr (R ⧸ Ideal.span {(m : R)}) m) := by
  let I : Ideal R := Ideal.span {(m : R)}
  let R₀ := R ⧸ I
  have hm0 : (m : R₀) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I) m]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hm1 : ((m - 1 : ℕ) : R₀) = -1 := by
    have hm_add : m - 1 + 1 = m := by omega
    have hm_eq : (m : R₀) = ((m - 1 : ℕ) : R₀) + 1 := by
      conv_lhs => rw [← hm_add]
      push_cast
      rfl
    have hsum : ((m - 1 : ℕ) : R₀) + 1 = 0 := hm_eq.symm.trans hm0
    exact eq_neg_of_add_eq_zero_left hsum
  let j₀ : Fin (m - 1) := ⟨m - 3, by omega⟩
  let φ : MvPolynomial (Fin (m - 1)) R₀ →ₐ[R₀] R₀[X] :=
    MvPolynomial.aeval fun j : Fin (m - 1) ↦ if j = j₀ then Polynomial.X else 0
  have hgen : (genericDepressed R₀ m).map φ.toRingHom =
      Polynomial.X ^ m - Polynomial.C (-Polynomial.X : R₀[X]) * Polynomial.X := by
    have hrhs : Polynomial.X ^ m - Polynomial.C (-Polynomial.X : R₀[X]) * Polynomial.X =
        Polynomial.X ^ m + Polynomial.C (Polynomial.X : R₀[X]) * Polynomial.X := by
      rw [map_neg]; ring
    rw [hrhs]
    rw [AddMonoidAlgebra.ext_iff, DFunLike.ext_iff]
    intro k
    rw [Polynomial.coeff_map, coeff_genericDepressed, Polynomial.coeff_add, Polynomial.coeff_X_pow]
    split_ifs with hkm hk
    · subst hkm
      rw [map_one, Polynomial.coeff_C_mul_X, ite_eq_right (by omega), add_zero]
    · have hk1 : (⟨m - 2 - k, by omega⟩ : Fin (m - 1)) = j₀ ↔ k = 1 := by
        simp [Fin.ext_iff, j₀]; omega
      rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.aeval_X,
        zero_add, Polynomial.coeff_C_mul_X]
      rcases eq_or_ne k 1 with rfl | hk_ne
      · simp [hk1.mpr rfl]
      · have hne : (⟨m - 2 - k, by omega⟩ : Fin (m - 1)) ≠ j₀ :=
          fun h ↦ hk_ne (hk1.mp h)
        simp [hne, hk_ne]
    · rw [map_zero, zero_add, Polynomial.coeff_C_mul_X, ite_eq_right (by omega)]
  let u : R₀ˣ := (-1) ^ ((m - 1) * (m - 2) / 2 + (m - 1))
  have hdiscr_val : φ (depressedDiscr R₀ m) = Polynomial.monomial m (u : R₀) := by
    rw [aeval_depressedDiscr, hgen, Polynomial.discr_X_pow_sub_C_mul_X (-Polynomial.X) (by omega)]
    have hm1_cast : ((m - 1 : ℕ) : R₀[X]) = -1 := by
      rw [← map_natCast (Polynomial.C : R₀ →+* R₀[X]), hm1, map_neg, map_one]
    rw [hm1_cast, neg_neg]
    calc (-1 : R₀[X]) ^ ((m - 1) * (m - 2) / 2) * (-1) ^ (m - 1) * Polynomial.X ^ m
        = Polynomial.C ((-1 : R₀) ^ ((m - 1) * (m - 2) / 2) * (-1) ^ (m - 1)) *
            Polynomial.X ^ m := by simp
      _ = Polynomial.monomial m (u : R₀) := by
          rw [Polynomial.C_mul_X_pow_eq_monomial]
          congr 1
          simp [u, pow_add]
  have hcoeff_m : (φ (depressedDiscr R₀ m)).coeff m = (u : R₀) := by
    rw [hdiscr_val, Polynomial.coeff_monomial_same]
  have hterm : ∀ d : Fin (m - 1) →₀ ℕ,
      (φ (MvPolynomial.monomial d ((depressedDiscr R₀ m).coeff d))).coeff m =
        if d = Finsupp.single j₀ m then (depressedDiscr R₀ m).coeff d else 0 := by
    intro d
    rw [MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq, Finsupp.prod]
    by_cases hother : ∃ j ∈ d.support, j ≠ j₀
    · obtain ⟨j, hj_supp, hj_ne⟩ := hother
      have hj0 : (if j = j₀ then Polynomial.X else (0 : R₀[X])) ^ d j = 0 := by
        rw [ite_eq_right hj_ne, zero_pow (Finsupp.mem_support_iff.mp hj_supp)]
      have hprod0 : (∏ x ∈ d.support, (if x = j₀ then Polynomial.X else (0 : R₀[X])) ^ d x) =
          0 := Finset.prod_eq_zero hj_supp hj0
      have hd_ne : d ≠ Finsupp.single j₀ m := by
        intro h
        subst h
        exact hj_ne (Finset.mem_singleton.mp (Finsupp.support_single_subset hj_supp))
      rw [hprod0, mul_zero, Polynomial.coeff_zero, ite_eq_right hd_ne]
    · push Not at hother
      have hd_eq : d = Finsupp.single j₀ (d j₀) := by
        ext j
        by_cases hj : j = j₀
        · subst hj; simp
        · rw [Finsupp.single_eq_of_ne hj]
          by_contra hj0
          exact hj (hother j (Finsupp.mem_support_iff.mpr hj0))
      have hprod : (∏ x ∈ d.support, (if x = j₀ then Polynomial.X else (0 : R₀[X])) ^ d x) =
          Polynomial.X ^ d j₀ := by
        by_cases hj_mem : j₀ ∈ d.support
        · rw [Finset.prod_eq_single j₀]
          · simp
          · intro x hx hne
            exact absurd (hother x hx) hne
          · intro h; exact absurd hj_mem h
        · have hd0 : d j₀ = 0 := Finsupp.notMem_support_iff.mp hj_mem
          have hsupp : d.support = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro x hx
            exact hj_mem (hother x hx ▸ hx)
          rw [hsupp, Finset.prod_empty, hd0, pow_zero]
      rw [hprod, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases hdm : d j₀ = m
      · have hd_eq' : d = Finsupp.single j₀ m := by rw [hd_eq, hdm]
        simp [hd_eq']
      · have hd_ne : d ≠ Finsupp.single j₀ m := fun h ↦ hdm (by rw [h, Finsupp.single_eq_same])
        simp [Ne.symm hdm, hd_ne]
  have hsum_coeff : (φ (depressedDiscr R₀ m)).coeff m =
      (depressedDiscr R₀ m).coeff (Finsupp.single j₀ m) := by
    conv_lhs => rw [MvPolynomial.as_sum (p := depressedDiscr R₀ m), map_sum,
      Polynomial.finsetSum_coeff]
    simp_rw [hterm]
    by_cases hm_mem : Finsupp.single j₀ m ∈ (depressedDiscr R₀ m).support
    · rw [Finset.sum_eq_single (Finsupp.single j₀ m)]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd hm_mem h
    · rw [Finset.sum_eq_zero (fun b hb ↦ ite_eq_right fun heq : b = Finsupp.single j₀ m ↦
        absurd (heq ▸ hb) hm_mem), Finsupp.notMem_support_iff.mp hm_mem]
  have hunit : IsUnit ((depressedDiscr R₀ m).coeff (Finsupp.single j₀ m)) := by
    rw [← hsum_coeff, hcoeff_m]
    exact u.isUnit
  exact isRegular_mvPolynomial_fin_of_exists_isRegular_coeff ⟨Finsupp.single j₀ m, hunit.isRegular⟩

/-- **Primality of the generic depressed discriminant over an integral domain for `3 ≤ m`.**
Unlike degree `m = 2` (where `depressedDiscr ℤ 2 = -4 X 0` is divisible by `2`), for every `m ≥ 3`
over any integral domain `R` with `(2 : R) ≠ 0` and `(m : R) ≠ 0`, `TauCeti.depressedDiscr R m`
is prime in `MvPolynomial (Fin (m - 1)) R`. -/
theorem prime_depressedDiscr_of_three_le {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} (hm : 3 ≤ m) (hm0 : (m : R) ≠ 0) :
    Prime (depressedDiscr R m) := by
  let D := depressedDiscr R m
  let K := FractionRing R
  have hinjK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have h2K : (2 : K) ≠ 0 := by
    rw [← map_ofNat (algebraMap R K) 2]
    exact fun h ↦ h2 (hinjK (h.trans (map_zero _).symm))
  have hmK : (m : K) ≠ 0 := by
    rw [← map_natCast (algebraMap R K) m]
    exact fun h ↦ hm0 (hinjK (h.trans (map_zero _).symm))
  have hprimeK : Prime (depressedDiscr K m) := prime_depressedDiscr_of_ne_zero h2K (by omega) hmK
  have hD0 : D ≠ 0 := fun h0 ↦ by
    apply hprimeK.ne_zero
    rw [← map_depressedDiscr (algebraMap R K) m]
    change (MvPolynomial.map (algebraMap R K)) D = 0
    rw [h0, map_zero]
  have hDnu : ¬ IsUnit D := fun hu ↦ by
    apply hprimeK.not_isUnit
    rw [← map_depressedDiscr (algebraMap R K) m]
    exact hu.map (MvPolynomial.map (algebraMap R K))
  let Rₘ := Localization.Away (m : R)
  have hM : Submonoid.powers (m : R) ≤ nonZeroDivisors R := by
    rintro _ ⟨k, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero k hm0)
  have : IsDomain Rₘ := IsLocalization.isDomain_localization hM
  have hinjM : Function.Injective (algebraMap R Rₘ) := IsLocalization.injective Rₘ hM
  have h2M : (2 : Rₘ) ≠ 0 := by
    rw [← map_ofNat (algebraMap R Rₘ) 2]
    exact fun h ↦ h2 (hinjM (h.trans (map_zero _).symm))
  have hmM : IsUnit (m : Rₘ) := by
    rw [← map_natCast (algebraMap R Rₘ) m]
    exact IsLocalization.Away.algebraMap_isUnit (m : R)
  have hprimeM : Prime (depressedDiscr Rₘ m) :=
    prime_depressedDiscr_of_isUnit h2M (by omega) hmM
  have hsat1 : ∀ h₀ : MvPolynomial (Fin (m - 1)) R,
      D ∣ MvPolynomial.C (m : R) * h₀ → D ∣ h₀ := by
    intro h₀ ⟨h, hh⟩
    let I : Ideal R := Ideal.span {(m : R)}
    let mk := Ideal.Quotient.mk I
    have hmap0 : depressedDiscr (R ⧸ I) m * MvPolynomial.map mk h = 0 := by
      have h1 := congrArg (MvPolynomial.map mk) hh
      have hmk_m : mk (m : R) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
      rw [map_mul, MvPolynomial.map_C, hmk_m, map_zero, zero_mul, map_mul,
        map_depressedDiscr] at h1
      exact h1.symm
    have hmh0 : MvPolynomial.map mk h = 0 :=
      (isRegular_depressedDiscr_quotient hm).left (by simpa using hmap0)
    have hdvd_coeff : ∀ d : Fin (m - 1) →₀ ℕ, (m : R) ∣ h.coeff d := by
      intro d
      have hc : mk (h.coeff d) = 0 := by
        have h0' := congrArg (fun p : MvPolynomial (Fin (m - 1)) (R ⧸ I) ↦ p.coeff d) hmh0
        simpa [MvPolynomial.coeff_map] using h0'
      exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hc)
    choose c hc using hdvd_coeff
    let h₁ : MvPolynomial (Fin (m - 1)) R :=
      ∑ d ∈ h.support, MvPolynomial.monomial d (c d)
    have hh₁ : h = MvPolynomial.C (m : R) * h₁ := by
      ext d
      rw [MvPolynomial.coeff_C_mul]
      simp only [h₁, MvPolynomial.coeff_sum]
      by_cases hd : d ∈ h.support
      · rw [Finset.sum_eq_single d]
        · rw [MvPolynomial.coeff_monomial, ite_eq_left rfl]; exact hc d
        · intro b _ hbd; rw [MvPolynomial.coeff_monomial, ite_eq_right hbd]
        · intro h'; exact absurd hd h'
      · rw [Finset.sum_eq_zero (fun b hb ↦ by
          rw [MvPolynomial.coeff_monomial, ite_eq_right fun hbd : b = d ↦ hd (hbd ▸ hb)]),
          mul_zero]
        exact Finsupp.notMem_support_iff.mp hd
    have hCm0 : (MvPolynomial.C (m : R) : MvPolynomial (Fin (m - 1)) R) ≠ 0 :=
      (MvPolynomial.C_ne_zero (σ := Fin (m - 1))).mpr hm0
    refine ⟨h₁, mul_left_cancel₀ hCm0 ?_⟩
    rw [hh, hh₁]; ring
  have hsat_pow : ∀ k : ℕ, ∀ f : MvPolynomial (Fin (m - 1)) R,
      D ∣ MvPolynomial.C ((m : R) ^ k) * f → D ∣ f := by
    intro k
    induction k with
    | zero => intro f hf; simpa using hf
    | succ k ih =>
      intro f hf
      refine ih f (hsat1 _ ?_)
      rwa [pow_succ', map_mul, mul_assoc] at hf
  have hdvd_of_map : ∀ f : MvPolynomial (Fin (m - 1)) R,
      MvPolynomial.map (algebraMap R Rₘ) D ∣ MvPolynomial.map (algebraMap R Rₘ) f → D ∣ f := by
    intro f ⟨q, hq⟩
    let deg : (Fin (m - 1) →₀ ℕ) → ℕ := fun d ↦ (IsLocalization.Away.sec (m : R) (q.coeff d)).2
    let k : ℕ := q.support.sup deg
    have hsec : ∀ d ∈ q.support,
        ∃ a : R, q.coeff d * algebraMap R Rₘ ((m : R) ^ k) = algebraMap R Rₘ a := by
      intro d hd
      have hle : deg d ≤ k := Finset.le_sup hd
      refine ⟨(IsLocalization.Away.sec (m : R) (q.coeff d)).1 * (m : R) ^ (k - deg d), ?_⟩
      rw [map_mul, map_pow, ← IsLocalization.Away.sec_spec (x := (m : R)) (s := q.coeff d),
        mul_assoc, ← map_pow, ← map_mul, ← pow_add, Nat.add_sub_of_le hle, map_pow]
    choose a ha using fun d (hd : d ∈ q.support) ↦ hsec d hd
    let q₀ : MvPolynomial (Fin (m - 1)) R :=
      ∑ d ∈ q.support, MvPolynomial.monomial d (if hd : d ∈ q.support then a d hd else 0)
    have hq₀ : MvPolynomial.map (algebraMap R Rₘ) q₀ =
        q * MvPolynomial.C (algebraMap R Rₘ ((m : R) ^ k)) := by
      ext d
      rw [MvPolynomial.coeff_map, mul_comm, MvPolynomial.coeff_C_mul]
      simp only [q₀, MvPolynomial.coeff_sum]
      by_cases hd : d ∈ q.support
      · rw [Finset.sum_eq_single d]
        · rw [MvPolynomial.coeff_monomial, ite_eq_left rfl, mul_comm]
          split_ifs
          exact (ha d hd).symm
        · intro b _ hbd; rw [MvPolynomial.coeff_monomial, ite_eq_right hbd]
        · intro h'; exact absurd hd h'
      · rw [Finset.sum_eq_zero (fun b hb ↦ by
          rw [MvPolynomial.coeff_monomial, ite_eq_right fun hbd : b = d ↦ hd (hbd ▸ hb)]),
          Finsupp.notMem_support_iff.mp hd, mul_zero, map_zero]
    have hmulp : MvPolynomial.map (algebraMap R Rₘ) (MvPolynomial.C ((m : R) ^ k) * f) =
        MvPolynomial.map (algebraMap R Rₘ) (D * q₀) := by
      rw [map_mul, MvPolynomial.map_C, hq, map_mul, hq₀]
      ring
    have heq : MvPolynomial.C ((m : R) ^ k) * f = D * q₀ :=
      MvPolynomial.map_injective (algebraMap R Rₘ) hinjM hmulp
    exact hsat_pow k f ⟨q₀, heq⟩
  refine ⟨hD0, hDnu, fun f g hfg ↦ ?_⟩
  have hfgM : MvPolynomial.map (algebraMap R Rₘ) D ∣
      MvPolynomial.map (algebraMap R Rₘ) f * MvPolynomial.map (algebraMap R Rₘ) g := by
    rw [← map_mul]
    exact _root_.map_dvd (MvPolynomial.map (algebraMap R Rₘ)) hfg
  rw [← map_depressedDiscr (algebraMap R Rₘ) m] at hprimeM
  rcases hprimeM.dvd_or_dvd hfgM with hf | hg
  · exact Or.inl (hdvd_of_map f hf)
  · exact Or.inr (hdvd_of_map g hg)

/-- Over a field `K` of characteristic zero, `TauCeti.depressedDiscr K m` is prime in
`MvPolynomial (Fin (m - 1)) K` for every `m ≥ 2`. -/
theorem depressedDiscr_prime (K : Type*) [Field K] [CharZero K] (m : ℕ) (hm : 2 ≤ m) :
    Prime (depressedDiscr K m) :=
  prime_depressedDiscr_of_ne_zero two_ne_zero hm (Nat.cast_ne_zero.mpr (by omega))

end Tschirnhaus

/-! ### Degree-two criterion and sharpness -/

section LowDegree

/-- Over an integral domain `R`, `depressedDiscr R 2 = -4 X₀` is prime if and only if
`IsUnit (2 : R)`. -/
theorem prime_depressedDiscr_two_iff {R : Type*} [CommRing R] [IsDomain R] :
    Prime (depressedDiscr R 2) ↔ IsUnit (2 : R) := by
  rw [depressedDiscr_two]
  constructor
  · intro hp
    have h2 : (2 : R) ≠ 0 := fun h ↦ by
      apply hp.ne_zero
      have h4 : (-4 : R) = 0 := by
        calc (-4 : R) = -(2 * 2) := by norm_num
          _ = 0 := by rw [h, zero_mul, neg_zero]
      calc (-4 : MvPolynomial (Fin 1) R) * MvPolynomial.X 0
          = MvPolynomial.C (-4 : R) * MvPolynomial.X 0 := by rw [map_neg, map_ofNat]
        _ = 0 := by rw [h4, map_zero, zero_mul]
    have hdvd : (-4 : MvPolynomial (Fin 1) R) * MvPolynomial.X 0 ∣
        (-2 : MvPolynomial (Fin 1) R) * (2 * MvPolynomial.X 0) := ⟨1, by ring⟩
    rcases hp.dvd_or_dvd hdvd with ⟨q, hq⟩ | ⟨q, hq⟩
    · have hev := congrArg (MvPolynomial.eval (fun _ ↦ (0 : R))) hq
      simp only [map_mul, map_neg, map_ofNat, MvPolynomial.eval_X, mul_zero, zero_mul] at hev
      exact absurd (neg_eq_zero.mp hev) h2
    · have hmul : MvPolynomial.X 0 * (2 : MvPolynomial (Fin 1) R) =
          MvPolynomial.X 0 * (-4 * q) := by
        rw [mul_comm (MvPolynomial.X 0) 2, hq]; ring
      have h2eq : (2 : MvPolynomial (Fin 1) R) = -4 * q :=
        mul_left_cancel₀ (MvPolynomial.X_ne_zero 0) hmul
      have hev := congrArg (MvPolynomial.eval (fun _ ↦ (0 : R))) h2eq
      simp only [map_ofNat, map_mul, map_neg] at hev
      have hmul2 : (2 : R) * 1 = (2 : R) * (-(2 * MvPolynomial.eval (fun _ ↦ 0) q)) := by
        calc (2 : R) * 1 = 2 := mul_one 2
          _ = -4 * MvPolynomial.eval (fun _ ↦ 0) q := hev
          _ = 2 * -(2 * MvPolynomial.eval (fun _ ↦ 0) q) := by ring
      have h1 : (1 : R) = -(2 * MvPolynomial.eval (fun _ ↦ 0) q) :=
        mul_left_cancel₀ h2 hmul2
      refine ⟨⟨2, -(MvPolynomial.eval (fun _ ↦ 0) q), ?_, ?_⟩, rfl⟩
      · calc (2 : R) * -(MvPolynomial.eval (fun _ ↦ 0) q)
            = -(2 * MvPolynomial.eval (fun _ ↦ 0) q) := mul_neg _ _
          _ = 1 := h1.symm
      · rw [mul_comm]
        calc (2 : R) * -(MvPolynomial.eval (fun _ ↦ 0) q)
            = -(2 * MvPolynomial.eval (fun _ ↦ 0) q) := mul_neg _ _
          _ = 1 := h1.symm
  · intro hu
    have h4 : (-4 : R) = -(2 ^ 2) := by norm_num
    have h4u : IsUnit (MvPolynomial.C (-4 : R) : MvPolynomial (Fin 1) R) := by
      rw [h4]
      exact ((hu.pow 2).neg).map MvPolynomial.C
    have hC4 : (-4 : MvPolynomial (Fin 1) R) * MvPolynomial.X 0 =
        MvPolynomial.C (-4 : R) * MvPolynomial.X 0 := by rw [map_neg, map_ofNat]
    rw [hC4]
    exact ((associated_unit_mul_left (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) R) _
      h4u).symm).prime MvPolynomial.prime_X

/-- In characteristic `2`, `depressedDiscr R 2` is not prime. -/
theorem not_prime_depressedDiscr_two_of_charTwo (R : Type*) [CommRing R] [CharP R 2] :
    ¬ Prime (depressedDiscr R 2) := by
  rw [depressedDiscr_two_of_charTwo]
  exact not_prime_zero

/-- In characteristic `3`, `depressedDiscr R 3` is not prime. -/
theorem not_prime_depressedDiscr_three_of_charThree (R : Type*) [CommRing R] [CharP R 3] :
    ¬ Prime (depressedDiscr R 3) := by
  have := CharP.nontrivial_of_char_ne_one (R := R) (by decide : 3 ≠ 1)
  rw [depressedDiscr_three_of_charThree]
  intro hp
  have hp' : Prime (MvPolynomial.X 0 ^ 3 : MvPolynomial (Fin 2) R) := by
    simpa using Prime.neg hp
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
theorem not_prime_depressedDiscr_int_two : ¬ Prime (depressedDiscr ℤ 2) :=
  fun hp ↦ (Int.isUnit_iff.not.mpr (by decide)) (prime_depressedDiscr_two_iff.mp hp)

end LowDegree

end TauCeti
