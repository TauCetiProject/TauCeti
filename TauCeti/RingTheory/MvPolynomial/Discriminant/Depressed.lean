/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import TauCeti.RingTheory.Polynomial.Resultant.GenericDepressed

import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Prime
import TauCeti.Algebra.MvPolynomial.Eval
import TauCeti.RingTheory.MvPolynomial.Discriminant.Generic
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import TauCeti.RingTheory.Polynomial.Resultant.RootCoordinates

/-!
# Primality and Tschirnhaus transport of the generic depressed discriminant

Let `R` be a commutative ring. A monic depressed polynomial of degree `m` over `R` has `m - 1`
free lower coefficients, represented universally by
`TauCeti.genericDepressed R m = X ^ m + a₂ X ^ (m - 2) + ⋯ + aₘ` over
`MvPolynomial (Fin (m - 1)) R` (defined in
`TauCeti.RingTheory.Polynomial.Resultant.GenericDepressed`). Under uniform scaling `rᵢ ↦ t rᵢ` of
the roots, `aₖ` acquires weight `k`, and over any commutative ring `R` and degree `m` the generic
depressed discriminant `TauCeti.depressedDiscr R m` is weighted homogeneous of weight
`m * (m - 1)` for `TauCeti.depressedWeight m` (`TauCeti.depressedDiscr_mem`).

Over a unique factorization domain `R` with `(2 : R) ≠ 0`, `TauCeti.depressedDiscr R m` is prime
whenever either `2 ≤ m` and `IsUnit (m : R)` (in particular over any field `K` with `(2 : K) ≠ 0`
and `(m : K) ≠ 0`, such as any field of characteristic zero) or `3 ≤ m` and `(m : R) ≠ 0`. Under
these hypotheses, the repeated-root locus where the generic depressed discriminant vanishes is an
irreducible weighted-homogeneous hypersurface of weight `m * (m - 1)`.
Likewise, on short Weierstrass cubics `y² = x³ + a x + b`, the coordinate scaling
`(x, y) ↦ (t² x, t³ y)` assigns `(a, b)` weights `(4, 6)` — twice `TauCeti.depressedWeight 3` —
and makes the discriminant factor `4 a³ + 27 b²` weighted homogeneous of weight `12` over any
commutative ring, and prime over any unique factorization domain `R` with `(2 : R) ≠ 0` and
`(3 : R) ≠ 0`.

1. **Generic depressed polynomial and weighted homogeneity.** `TauCeti.genericDepressed R m`
   satisfies the universal specialization property for monic depressed polynomials
   (`TauCeti.map_genericDepressed_eq_iff`, `TauCeti.map_algHom_genericDepressed_eq_iff`, in
   `TauCeti.RingTheory.Polynomial.Resultant.GenericDepressed`), while
   `TauCeti.depressedDiscr_mem_smul` gives weighted homogeneity of `TauCeti.depressedDiscr R m` of
   weight `(m * (m - 1)) • u` for any element `u` of an additive commutative monoid.

2. **Tschirnhaus transport and primality.** When `(m : R)` is a unit, the Tschirnhaus
   `R`-algebra equivalence `TauCeti.tschirnhausAlgEquiv : MvPolynomial (Fin m) R ≃ₐ[R]
   (MvPolynomial (Fin (m - 1)) R)[X]` (defined in
   `TauCeti.RingTheory.Polynomial.Resultant.GenericDepressed`) carries
   `(Polynomial.freeMonic R m).discr` to `Polynomial.C (TauCeti.depressedDiscr R m)` by
   translation invariance of the discriminant (`TauCeti.tschirnhausAlgEquiv_discr_freeMonic`).
   Primality of `TauCeti.depressedDiscr R m` follows for `2 ≤ m` over any unique factorization
   domain in which `(2 : R) ≠ 0` and `(m : R)` is invertible
   (`TauCeti.prime_depressedDiscr_of_isUnit`). For `3 ≤ m`, specializing to `X ^ m - 1`
   and `X ^ m - X` shows that `TauCeti.depressedDiscr R m` has unit content
   (`TauCeti.isUnit_of_C_dvd_depressedDiscr_of_three_le`), so `(m : R) ≠ 0` (with `(2 : R) ≠ 0`)
   suffices over any unique factorization domain (`TauCeti.prime_depressedDiscr_of_three_le`), and
   in particular `TauCeti.depressedDiscr K m` is prime for every `2 ≤ m` over any field of
   characteristic zero (`TauCeti.depressedDiscr_prime`).

3. **Weierstrass cubic discriminant factor and sharpness.** Weighted homogeneity and primality are
   established for the Weierstrass cubic discriminant factor
   `TauCeti.weierstrassDiscrFactor R = 4 X₀³ + 27 X₁²` of weight `12` for weights `(4, 6)`,
   together with counterexamples showing that `(2 : R) ≠ 0` in degree `2`, `(3 : R) ≠ 0` in degree
   `3`, and `IsUnit (2 : R)` over `ℤ` in degree `2` are all necessary.

## Main definitions

* `TauCeti.weierstrassDiscrFactor`: the Weierstrass cubic discriminant factor `4 X₀³ + 27 X₁²`.

## Main results

* `TauCeti.tschirnhausAlgEquiv_discr_freeMonic`,
  `TauCeti.prime_depressedDiscr_iff_prime_discr_freeMonic_of_isUnit`: identification of generic
  monic and depressed discriminants when `m` is invertible.
* `TauCeti.isUnit_of_C_dvd_depressedDiscr_of_three_le`, `TauCeti.prime_depressedDiscr_of_isUnit`,
  `TauCeti.prime_depressedDiscr_of_three_le`, `TauCeti.prime_depressedDiscr_of_ne_zero`,
  `TauCeti.depressedDiscr_prime`: unit content for `3 ≤ m` and primality of `depressedDiscr`.
* `TauCeti.isWeightedHomogeneous_weierstrassDiscrFactor`, `TauCeti.prime_weierstrassDiscrFactor`:
  weighted homogeneity and primality of the Weierstrass cubic discriminant factor.
* `TauCeti.not_prime_depressedDiscr_two_of_charTwo`,
  `TauCeti.not_prime_depressedDiscr_three_of_charThree`,
  `TauCeti.not_prime_depressedDiscr_int_two`: sharpness counterexamples.

## References

* S. Lang, *Algebra*, Revised Third Edition, GTM 211, Springer (2002), Chapter IV, §8.
* I. M. Gelfand, M. M. Kapranov, A. V. Zelevinsky, *Discriminants, Resultants, and
  Multidimensional Determinants*, Birkhäuser (1994), Chapter 12, §1.B.
-/

public section

open Finset MvPolynomial Polynomial

/-! ### Tschirnhaus invariance and primality of the generic depressed discriminant -/

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
    (monic_genericDepressed (R := R) (m := m)).discr_map, discr_genericDepressed,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv] at h
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

/-- A constant divisor of `depressedDiscr R m` divides the discriminant of any monic depressed
polynomial of degree `m`. -/
private theorem dvd_discr_of_C_dvd_depressedDiscr {R : Type*} [CommRing R] {m : ℕ} {r : R}
    (hr : MvPolynomial.C r ∣ depressedDiscr R m) {f : R[X]} (hf_mon : f.Monic)
    (hf_deg : f.natDegree = m) (hf_next : f.nextCoeff = 0) : r ∣ f.discr := by
  have hmap := _root_.map_dvd (MvPolynomial.aeval (R := R) fun i : Fin (m - 1) ↦
    f.coeff (m - 2 - (i : ℕ))) hr
  simpa [← discr_eq_eval_depressedDiscr hf_mon hf_deg hf_next] using hmap

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
    have hpC : p = MvPolynomial.C (p.coeff 0) := MvPolynomial.eq_C_of_map_eq_C hinj hq
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
theorem depressedDiscr_prime (K : Type*) [Field K] [CharZero K] (m : ℕ) (hm : 2 ≤ m) :
    Prime (depressedDiscr K m) :=
  prime_depressedDiscr_of_ne_zero two_ne_zero hm (Nat.cast_ne_zero.mpr (by omega))

end Tschirnhaus

/-! ### Sharpness and Weierstrass discriminant -/

section LowDegree

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

/-- The **Weierstrass cubic discriminant factor** `4 X₀³ + 27 X₁²` over `R`, equal to
`-TauCeti.depressedDiscr R 3`. -/
noncomputable def weierstrassDiscrFactor (R : Type*) [CommRing R] : MvPolynomial (Fin 2) R :=
  4 * MvPolynomial.X 0 ^ 3 + 27 * MvPolynomial.X 1 ^ 2

/-- Definitional equation for `TauCeti.weierstrassDiscrFactor`. -/
theorem weierstrassDiscrFactor_def (R : Type*) [CommRing R] :
    weierstrassDiscrFactor R = 4 * MvPolynomial.X 0 ^ 3 + 27 * MvPolynomial.X 1 ^ 2 := (rfl)

/-- `TauCeti.weierstrassDiscrFactor R = -TauCeti.depressedDiscr R 3`. -/
theorem weierstrassDiscrFactor_eq_neg_depressedDiscr_three (R : Type*) [CommRing R] :
    weierstrassDiscrFactor R = -depressedDiscr R 3 := by
  rw [weierstrassDiscrFactor_def, depressedDiscr_three]
  ring

/-- The **Weierstrass cubic discriminant factor**
`TauCeti.weierstrassDiscrFactor R = -depressedDiscr R 3` is weighted homogeneous of weight `12` when
`X₀` and `X₁` are given integer weights `4` and `6`. -/
theorem isWeightedHomogeneous_weierstrassDiscrFactor (R : Type*) [CommRing R] :
    (weierstrassDiscrFactor R).IsWeightedHomogeneous ![(4 : ℤ), 6] 12 := by
  have hw : (![(4 : ℤ), 6] : Fin 2 → ℤ) = fun i : Fin 2 ↦ ((i : ℕ) + 2) • (2 : ℤ) :=
    funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩)
  rw [weierstrassDiscrFactor_eq_neg_depressedDiscr_three, hw,
    ← MvPolynomial.mem_weightedHomogeneousSubmodule]
  exact Submodule.neg_mem _ (depressedDiscr_mem_smul R 3 (2 : ℤ))

/-- Over a unique factorization domain `R` with `(2 : R) ≠ 0` and `(3 : R) ≠ 0` (including `ℤ`,
any field `k` of characteristic neither `2` nor `3`, and `k[t]` for such a field `k`), the
Weierstrass cubic discriminant factor `TauCeti.weierstrassDiscrFactor R` is prime in
`MvPolynomial (Fin 2) R`. -/
theorem prime_weierstrassDiscrFactor {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0) :
    Prime (weierstrassDiscrFactor R) := by
  rw [weierstrassDiscrFactor_eq_neg_depressedDiscr_three]
  exact Prime.neg (prime_depressedDiscr_of_three_le h2 (by omega) (by simpa using h3))

end LowDegree

end TauCeti
