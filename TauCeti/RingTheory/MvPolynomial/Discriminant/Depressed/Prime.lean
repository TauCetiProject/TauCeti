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
import TauCeti.Algebra.MvPolynomial.Coeff
import TauCeti.RingTheory.MvPolynomial.Discriminant.Generic
import TauCeti.RingTheory.MvPolynomial.Ideal
import TauCeti.RingTheory.Polynomial.Resultant.RootCoordinates

/-!
# Primality and Tschirnhaus transport of the generic depressed discriminant

When `(m : R)` is invertible, the Tschirnhaus `R`-algebra equivalence
`TauCeti.tschirnhausAlgEquiv : MvPolynomial (Fin m) R ≃ₐ[R] (MvPolynomial (Fin (m - 1)) R)[X]`
carries `(Polynomial.freeMonic R m).discr` to `Polynomial.C (TauCeti.depressedDiscr R m)` by
translation invariance of the discriminant (`TauCeti.tschirnhausAlgEquiv_discr_freeMonic`). Over any
integral domain `R` with `(2 : R) ≠ 0` and `IsUnit (m : R)`, this gives primality of
`TauCeti.depressedDiscr R m` for every `m ≥ 2` (`TauCeti.depressedDiscr_prime`).

For `3 ≤ m` over any integral domain `R` with `(2 : R) ≠ 0` and `(m : R) ≠ 0`, specializing to
`X ^ m - 1` and `X ^ m - X` shows that every constant divisor of `TauCeti.depressedDiscr R m` is a
unit (`TauCeti.isUnit_of_C_dvd_depressedDiscr_of_three_le`). Localizing away from `m` gives
primality over `Rₘ`, and specializing `X ^ m + a_{m-1} X` modulo `m` exhibits a unit coefficient
`±1` in `depressedDiscr (R ⧸ Ideal.span {(m : R)}) m`, which by McCoy's regularity lemma makes the
discriminant ideal saturated with respect to `m`. Hence `TauCeti.depressedDiscr R m` is prime
over any integral domain `R` with `(2 : R) ≠ 0` and `(m : R) ≠ 0` (`3 ≤ m`), without requiring
unique factorization (`TauCeti.prime_depressedDiscr_of_three_le`).

For `m = 2`, `TauCeti.depressedDiscr R 2 = -4 X₀` is prime over an integral domain `R` if and only
if `IsUnit (2 : R)` (`TauCeti.prime_depressedDiscr_two_iff`), and counterexamples when `2 = 0`,
when `3 = 0`, and over `ℤ` show sharpness.

## Main results

* `TauCeti.tschirnhausAlgEquiv_discr_freeMonic`,
  `TauCeti.prime_depressedDiscr_iff_prime_discr_freeMonic_of_isUnit`: identification of generic
  monic and depressed discriminants when `m` is invertible.
* `TauCeti.isUnit_of_C_dvd_depressedDiscr_of_three_le`,
  `TauCeti.prime_depressedDiscr_of_three_le`, `TauCeti.prime_depressedDiscr_of_ne_zero`: every
  constant divisor is a unit for `3 ≤ m` and integral-domain primality of `depressedDiscr`.
* `TauCeti.prime_depressedDiscr_two_iff`, `TauCeti.not_prime_depressedDiscr_two_of_two_eq_zero`,
  `TauCeti.not_prime_depressedDiscr_three_of_three_eq_zero`,
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

/-- Over a field `K` of characteristic different from `2` in which `(m : K) ≠ 0`,
`TauCeti.depressedDiscr K m` is prime in `MvPolynomial (Fin (m - 1)) K` for every `m ≥ 2`. -/
theorem prime_depressedDiscr_of_ne_zero {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {m : ℕ}
    (hm : 2 ≤ m) (hm0 : (m : K) ≠ 0) : Prime (depressedDiscr K m) :=
  depressedDiscr_prime h2 (IsUnit.mk0 _ hm0) hm

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

/-- For `3 ≤ m` over any commutative ring `R`, every constant divisor of `depressedDiscr R m`
is a unit: if `MvPolynomial.C r ∣ depressedDiscr R m`, then `IsUnit r`. -/
theorem isUnit_of_C_dvd_depressedDiscr_of_three_le {R : Type*} [CommRing R] {m : ℕ}
    (hm : 3 ≤ m) {r : R} (hr : MvPolynomial.C r ∣ depressedDiscr R m) : IsUnit r := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim r 1 ▸ isUnit_one
  -- Specializing to `X ^ m - 1` and `X ^ m - X` produces coprime powers of `m` and `m - 1`.
  have hdvd_m := dvd_pow_of_C_dvd_depressedDiscr_of_two_le (by omega) hr
  have hdvd_m1 := dvd_sub_one_pow_of_C_dvd_depressedDiscr_of_three_le hm hr
  have hcop : IsCoprime ((m : R) ^ m) (((m - 1 : ℕ) : R) ^ (m - 1)) := by
    refine IsCoprime.pow ⟨1, -1, ?_⟩
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    ring
  exact hcop.isUnit_of_dvd' hdvd_m hdvd_m1

/-- Evaluating an `MvPolynomial` by sending `j₀` to `Polynomial.X` and all other variables to `0`
yields a univariate polynomial whose `X ^ k` coefficient is `P.coeff (Finsupp.single j₀ k)`. -/
private theorem coeff_aeval_ite_X {A σ : Type*} [CommRing A] [DecidableEq σ]
    (j₀ : σ) (P : MvPolynomial σ A) (k : ℕ) :
    (MvPolynomial.aeval (fun j : σ ↦ if j = j₀ then (Polynomial.X : A[X]) else 0) P).coeff k =
      P.coeff (Finsupp.single j₀ k) := by
  induction P using MvPolynomial.induction_on generalizing k with
  | C a =>
    simp [Polynomial.coeff_C, MvPolynomial.coeff_C, eq_comm]
  | add p q hp hq =>
    simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, MvPolynomial.aeval_X]
    by_cases hi : i = j₀
    · subst hi
      simp only [↓reduceIte]
      rcases k with _ | k
      · simp [MvPolynomial.coeff_mul_X']
      · rw [Polynomial.coeff_mul_X, hp k]
        simp [Finsupp.single_add]
    · simp [hi, MvPolynomial.coeff_mul_X']

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
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one, hm0, zero_sub]
  -- Specialize the variable for `X` (`j₀ = m - 3`) to `Polynomial.X` and all others to `0`,
  -- sending `genericDepressed R₀ m` to `X ^ m + X * X`.
  let j₀ : Fin (m - 1) := ⟨m - 3, by omega⟩
  let φ : MvPolynomial (Fin (m - 1)) R₀ →ₐ[R₀] R₀[X] :=
    MvPolynomial.aeval fun j : Fin (m - 1) ↦ if j = j₀ then Polynomial.X else 0
  have hgen : (genericDepressed R₀ m).map φ.toRingHom =
      Polynomial.X ^ m - Polynomial.C (-Polynomial.X : R₀[X]) * Polynomial.X := by
    have hrhs : Polynomial.X ^ m - Polynomial.C (-Polynomial.X : R₀[X]) * Polynomial.X =
        Polynomial.X ^ m + Polynomial.C (Polynomial.X : R₀[X]) * Polynomial.X := by
      rw [map_neg]; ring
    rw [hrhs]
    ext k : 2
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
  have hunit : IsUnit ((depressedDiscr R₀ m).coeff (Finsupp.single j₀ m)) := by
    rw [← coeff_aeval_ite_X j₀ (depressedDiscr R₀ m) m, hdiscr_val, Polynomial.coeff_monomial_same]
    exact u.isUnit
  exact MvPolynomial.isRegular_of_isRegular_coeff (Finsupp.single j₀ m) hunit.isRegular

/-- **Primality of the generic depressed discriminant over an integral domain for `3 ≤ m`.**
Unlike degree `m = 2` (where `depressedDiscr ℤ 2 = -4 X 0` is divisible by `2`), for every `m ≥ 3`
over any integral domain `R` with `(2 : R) ≠ 0` and `(m : R) ≠ 0`, `TauCeti.depressedDiscr R m`
is prime in `MvPolynomial (Fin (m - 1)) R`. -/
theorem prime_depressedDiscr_of_three_le {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} (hm : 3 ≤ m) (hm0 : (m : R) ≠ 0) :
    Prime (depressedDiscr R m) := by
  set D := depressedDiscr R m with hD
  -- Step 1 (localization): over `Rₘ = Localization.Away (m : R)`, `(m : Rₘ)` is a unit so
  -- `depressedDiscr Rₘ m` is prime, which also forces `D ≠ 0` and `¬ IsUnit D`.
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
  have hprimeM : Prime (MvPolynomial.map (algebraMap R Rₘ) D) := by
    rw [hD, map_depressedDiscr]
    exact depressedDiscr_prime h2M hmM (by omega)
  have hD0 : D ≠ 0 := fun h0 ↦ hprimeM.ne_zero (by rw [h0, map_zero])
  have hDnu : ¬ IsUnit D :=
    fun hu ↦ hprimeM.not_isUnit (hu.map (MvPolynomial.map (algebraMap R Rₘ)))
  -- Step 2 (saturation): regularity of `depressedDiscr (R ⧸ (m)) m` makes divisibility by `D`
  -- `m`-saturated, so divisibility in `Rₘ` descends back to `R`.
  have hreg_quot : IsRegular
      (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {(m : R)})) D) := by
    rw [hD, map_depressedDiscr]
    exact isRegular_depressedDiscr_quotient hm
  have hm_reg : IsRegular (m : R) :=
    isRegular_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_ne_zero hm0)
  have hsat := MvPolynomial.dvd_of_C_pow_mul_dvd_of_isRegular_map_quotient hm_reg hreg_quot
  refine ⟨hD0, hDnu, fun f g hfg ↦ ?_⟩
  have hfgM : MvPolynomial.map (algebraMap R Rₘ) D ∣
      MvPolynomial.map (algebraMap R Rₘ) f * MvPolynomial.map (algebraMap R Rₘ) g := by
    rw [← map_mul]
    exact _root_.map_dvd (MvPolynomial.map (algebraMap R Rₘ)) hfg
  rcases hprimeM.dvd_or_dvd hfgM with hf | hg
  · exact Or.inl (MvPolynomial.dvd_of_map_isLocalization_away_dvd Rₘ hsat hf)
  · exact Or.inr (MvPolynomial.dvd_of_map_isLocalization_away_dvd Rₘ hsat hg)

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
      have h4 : (-4 : R) = 0 := by linear_combination -2 * h
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
      exact IsUnit.of_mul_eq_one (-(MvPolynomial.eval (fun _ ↦ 0) q))
        (mul_left_cancel₀ h2 (by linear_combination -hev))
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

/-- When `(2 : R) = 0`, `depressedDiscr R 2` is not prime. -/
theorem not_prime_depressedDiscr_two_of_two_eq_zero {R : Type*} [CommRing R] (h2 : (2 : R) = 0) :
    ¬ Prime (depressedDiscr R 2) := by
  rw [depressedDiscr_two_of_two_eq_zero h2]
  exact not_prime_zero

/-- When `(3 : R) = 0`, `depressedDiscr R 3` is not prime. -/
theorem not_prime_depressedDiscr_three_of_three_eq_zero {R : Type*} [CommRing R]
    (h3 : (3 : R) = 0) : ¬ Prime (depressedDiscr R 3) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim (depressedDiscr R 3) 0]
    exact not_prime_zero
  rw [depressedDiscr_three_of_three_eq_zero h3]
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
`TauCeti.depressedDiscr_prime`). -/
theorem not_prime_depressedDiscr_int_two : ¬ Prime (depressedDiscr ℤ 2) :=
  fun hp ↦ (Int.isUnit_iff.not.mpr (by decide)) (prime_depressedDiscr_two_iff.mp hp)

end LowDegree

end TauCeti
