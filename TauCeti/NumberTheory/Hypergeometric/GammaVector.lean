/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Hypergeometric.CyclotomicData
import TauCeti.RingTheory.Polynomial.Cyclotomic.ProdXPowSubOne

/-!
# The gamma vector of a cyclotomic datum

Every cyclotomic polynomial is a product of integer powers of the polynomials `X ^ n - 1`
(Möbius inversion of `X ^ n - 1 = ∏_{d ∣ n} Φ_d`). Hence so is the defining rational function
`Q = Φ_A / Φ_B` of a cyclotomic datum `(A, B)`:
`Φ_A / Φ_B = ∏_n (X ^ n - 1) ^ γ(n)` with
`γ(n) = ∑_{a ∈ A, n ∣ a} μ(a / n) - ∑_{b ∈ B, n ∣ b} μ(b / n)`.
The function `γ` is the *gamma vector* of the datum. It is the parametrization of
Beukers, Cohen and Mellit, in which the finite hypergeometric sums take their gamma-vector form
at every prime power prime to the indices.

This file defines the gamma vector, proves its defining identity, cleared of denominators,
`Φ_A · ∏_n (X ^ n - 1) ^ max(-γ(n), 0) = Φ_B · ∏_n (X ^ n - 1) ^ max(γ(n), 0)` over every
commutative ring, and proves that in characteristic zero this identity determines `γ` among
all finitely supported exponent functions, because the polynomials `X ^ n - 1`, `n ≥ 1`, are
multiplicatively independent there (`Polynomial.eq_of_prod_X_pow_sub_one_pow_eq`).
It also defines the *gamma multiset* of the LMFDB, which lists `n` with multiplicity `γ(n)` when
`γ(n) > 0` and `-n` with multiplicity `-γ(n)` when `γ(n) < 0`, and proves that it has no zero
entry and sum `0`; the latter is the comparison of degrees in the defining identity.

## Main declarations

* `TauCeti.Hypergeometric.CyclotomicData.gamma`: the gamma vector, supported in
  `gammaSupport`, the divisors of the indices, and negated by the swap.
* `TauCeti.Hypergeometric.CyclotomicData.ratFunc_eq_prod_zpow`: `Q = ∏_n (X ^ n - 1) ^ γ(n)`.
* `TauCeti.Hypergeometric.CyclotomicData.phiA_mul_prod_eq_phiB_mul_prod`: the defining identity
  in `R[X]`.
* `TauCeti.Hypergeometric.CyclotomicData.eq_gamma_of_phiA_mul_prod_eq_phiB_mul_prod`: its
  uniqueness in characteristic zero.
* `TauCeti.Hypergeometric.CyclotomicData.sum_mul_gamma_eq_zero`: `∑_n n γ(n) = 0`.
* `TauCeti.Hypergeometric.CyclotomicData.gammaMultiset`: the gamma multiset, with
  `count_natCast_gammaMultiset`, `count_neg_natCast_gammaMultiset`, `zero_notMem_gammaMultiset`
  and `sum_gammaMultiset_eq_zero`.

## References

* F. Beukers, H. Cohen and A. Mellit, *Finite hypergeometric functions*, Pure Appl. Math. Q. 11
  (2015), §1.
* D. P. Roberts and F. Rodriguez-Villegas, *Hypergeometric motives*, Notices Amer. Math. Soc. 69
  (2022), §2.
-/

public section

open Polynomial
open scoped ArithmeticFunction.Moebius

namespace TauCeti.Hypergeometric

namespace CyclotomicData

variable (D : CyclotomicData)

/-! ### The gamma vector -/

/-- The finite set of indices at which the gamma vector can be nonzero: the divisors of the
elements of `A` and `B`. -/
def gammaSupport : Finset ℕ := (D.A + D.B).toFinset.biUnion Nat.divisors

theorem mem_gammaSupport {n : ℕ} : n ∈ D.gammaSupport ↔ ∃ m ∈ D.A + D.B, n ∣ m := by
  simp only [gammaSupport, Finset.mem_biUnion, Multiset.mem_toFinset, Nat.mem_divisors]
  exact exists_congr fun m ↦ and_congr_right fun hm ↦ and_iff_left (D.pos m hm).ne'

theorem pos_of_mem_gammaSupport {n : ℕ} (hn : n ∈ D.gammaSupport) : 0 < n := by
  obtain ⟨m, hm, hnm⟩ := D.mem_gammaSupport.1 hn
  exact Nat.pos_of_dvd_of_pos hnm (D.pos m hm)

theorem zero_notMem_gammaSupport : 0 ∉ D.gammaSupport :=
  fun h ↦ (D.pos_of_mem_gammaSupport h).ne' rfl

@[simp]
theorem gammaSupport_swap : D.swap.gammaSupport = D.gammaSupport := by
  rw [gammaSupport, gammaSupport, swap_A, swap_B, add_comm]

@[simp]
theorem gammaSupport_default : (default : CyclotomicData).gammaSupport = ∅ := by
  simp [gammaSupport]

/-- The gamma vector `γ(n) = ∑_{a ∈ A, n ∣ a} μ(a / n) - ∑_{b ∈ B, n ∣ b} μ(b / n)` of a
cyclotomic datum: the exponents with `Φ_A / Φ_B = ∏_n (X ^ n - 1) ^ γ(n)`. Positive values come
from `A`. -/
def gamma (n : ℕ) : ℤ :=
  ((D.A.filter (n ∣ ·)).map fun a ↦ μ (a / n)).sum -
    ((D.B.filter (n ∣ ·)).map fun b ↦ μ (b / n)).sum

theorem gamma_def (n : ℕ) : D.gamma n =
    ((D.A.filter (n ∣ ·)).map fun a ↦ μ (a / n)).sum -
      ((D.B.filter (n ∣ ·)).map fun b ↦ μ (b / n)).sum :=
  (rfl)

@[simp]
theorem gamma_zero : D.gamma 0 = 0 := by
  simp [gamma_def]

/-- The gamma vector vanishes outside the divisors of the indices. -/
theorem gamma_eq_zero_of_notMem {n : ℕ} (hn : n ∉ D.gammaSupport) : D.gamma n = 0 := by
  have h {S : Multiset ℕ} (hS : S ≤ D.A + D.B) : S.filter (n ∣ ·) = 0 :=
    Multiset.filter_eq_nil.2 fun m hm hnm ↦ hn (D.mem_gammaSupport.2 ⟨m, Multiset.mem_of_le hS hm,
      hnm⟩)
  rw [gamma_def, h (Multiset.le_add_right _ _), h (Multiset.le_add_left _ _)]
  simp

/-- The swap `(A, B) ↦ (B, A)` negates the gamma vector. -/
@[simp]
theorem gamma_swap (n : ℕ) : D.swap.gamma n = -D.gamma n := by
  rw [gamma_def, gamma_def, swap_A, swap_B, neg_sub]

/-- The empty datum has gamma vector `0`. -/
@[simp]
theorem gamma_default (n : ℕ) : (default : CyclotomicData).gamma n = 0 := by
  simp [gamma_def]

/-! ### The defining identity -/

section RatFunc

variable {K : Type*} [Field K]

/-- The image of `X ^ n - 1` in `RatFunc K` is nonzero for `n ≠ 0`. -/
private lemma algebraMap_X_pow_sub_one_ne_zero {n : ℕ} (hn : n ≠ 0) :
    algebraMap K[X] (RatFunc K) (X ^ n - 1) ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).2
    (X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) 1)

/-- Möbius inversion for one cyclotomic polynomial, with the product spread over a finite set of
indices containing the divisors of `a`. -/
private lemma algebraMap_cyclotomic_eq_prod {a : ℕ} (ha : a ≠ 0) {S : Finset ℕ}
    (hS : a.divisors ⊆ S) :
    algebraMap K[X] (RatFunc K) (cyclotomic a K) =
      ∏ n ∈ S, algebraMap K[X] (RatFunc K) (X ^ n - 1) ^ (if n ∣ a then μ (a / n) else 0) := by
  rw [cyclotomic_eq_prod_X_pow_sub_one_pow_moebius,
    Nat.prod_divisorsAntidiagonal' fun i j ↦ algebraMap K[X] (RatFunc K) (X ^ j - 1) ^ μ i,
    ← Finset.prod_subset hS fun n _ hn ↦ by
      rw [ite_eq_right fun h ↦ hn (Nat.mem_divisors.2 ⟨h, ha⟩), zpow_zero]]
  exact Finset.prod_congr rfl fun n hn ↦ by rw [ite_eq_left (Nat.dvd_of_mem_divisors hn)]

/-- Möbius inversion for a product of cyclotomic polynomials. -/
private lemma algebraMap_prod_cyclotomic_eq_prod (A : Multiset ℕ) (hA : ∀ a ∈ A, a ≠ 0)
    {S : Finset ℕ} (hS : ∀ a ∈ A, a.divisors ⊆ S) (hS₀ : 0 ∉ S) :
    algebraMap K[X] (RatFunc K) (A.map fun a ↦ cyclotomic a K).prod =
      ∏ n ∈ S, algebraMap K[X] (RatFunc K) (X ^ n - 1) ^
        ((A.filter (n ∣ ·)).map fun a ↦ μ (a / n)).sum := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons a A ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, map_mul,
      algebraMap_cyclotomic_eq_prod (hA a (Multiset.mem_cons_self a A))
        (hS a (Multiset.mem_cons_self a A)),
      ih (fun b hb ↦ hA b (Multiset.mem_cons_of_mem hb)) fun b hb ↦
        hS b (Multiset.mem_cons_of_mem hb),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun n hn ↦ ?_
    rw [← zpow_add₀ (algebraMap_X_pow_sub_one_ne_zero fun h ↦ hS₀ (h ▸ hn)), Multiset.filter_cons]
    split_ifs <;> simp

/-- The defining rational function of a cyclotomic datum is `∏_n (X ^ n - 1) ^ γ(n)`. -/
theorem ratFunc_eq_prod_zpow :
    D.ratFunc K = ∏ n ∈ D.gammaSupport, algebraMap K[X] (RatFunc K) (X ^ n - 1) ^ D.gamma n := by
  have hS {S : Multiset ℕ} (hS : S ≤ D.A + D.B) : ∀ a ∈ S, a.divisors ⊆ D.gammaSupport :=
    fun a ha n hn ↦ D.mem_gammaSupport.2 ⟨a, Multiset.mem_of_le hS ha, Nat.dvd_of_mem_divisors hn⟩
  have hA : ∀ a ∈ D.A, a ≠ 0 := fun a ha ↦ (D.pos_of_mem_A ha).ne'
  have hB : ∀ b ∈ D.B, b ≠ 0 := fun b hb ↦ (D.pos_of_mem_B hb).ne'
  rw [ratFunc_def, phiA_def, phiB_def,
    algebraMap_prod_cyclotomic_eq_prod _ hA (hS (Multiset.le_add_right _ _))
      D.zero_notMem_gammaSupport,
    algebraMap_prod_cyclotomic_eq_prod _ hB (hS (Multiset.le_add_left _ _))
      D.zero_notMem_gammaSupport,
    ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun n hn ↦ ?_
  rw [gamma_def, zpow_sub₀ (algebraMap_X_pow_sub_one_ne_zero (D.pos_of_mem_gammaSupport hn).ne')]

end RatFunc

/-- An identity of the shape of the defining identity holds over `S` as soon as it holds over
`R`, for every ring homomorphism `R →+* S`. -/
private lemma phiA_mul_prod_eq_of_ringHom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {I : Finset ℕ} {e e' : ℕ → ℕ}
    (h : D.phiA R * ∏ n ∈ I, (X ^ n - 1 : R[X]) ^ e n =
      D.phiB R * ∏ n ∈ I, (X ^ n - 1 : R[X]) ^ e' n) :
    D.phiA S * ∏ n ∈ I, (X ^ n - 1 : S[X]) ^ e n =
      D.phiB S * ∏ n ∈ I, (X ^ n - 1 : S[X]) ^ e' n := by
  simpa [Polynomial.map_mul, Polynomial.map_prod, map_phiA, map_phiB] using
    congr_arg (Polynomial.map f) h

/-- An identity of the shape of the defining identity holds over `ℤ` as soon as it holds over
some ring of characteristic zero. -/
private lemma phiA_mul_prod_eq_int {R : Type*} [CommRing R] [CharZero R] {I : Finset ℕ}
    {e e' : ℕ → ℕ}
    (h : D.phiA R * ∏ n ∈ I, (X ^ n - 1 : R[X]) ^ e n =
      D.phiB R * ∏ n ∈ I, (X ^ n - 1 : R[X]) ^ e' n) :
    D.phiA ℤ * ∏ n ∈ I, (X ^ n - 1 : ℤ[X]) ^ e n =
      D.phiB ℤ * ∏ n ∈ I, (X ^ n - 1 : ℤ[X]) ^ e' n := by
  refine Polynomial.map_injective (Int.castRingHom R) Int.cast_injective ?_
  simpa [Polynomial.map_mul, Polynomial.map_prod, map_phiA, map_phiB] using h

/-- The defining identity of the gamma vector, cleared of denominators:
`Φ_A · ∏_{γ(n) < 0} (X ^ n - 1) ^ (-γ(n)) = Φ_B · ∏_{γ(n) > 0} (X ^ n - 1) ^ γ(n)`, over every
commutative ring. -/
theorem phiA_mul_prod_eq_phiB_mul_prod (R : Type*) [CommRing R] :
    D.phiA R * ∏ n ∈ D.gammaSupport, (X ^ n - 1 : R[X]) ^ (-D.gamma n).toNat =
      D.phiB R * ∏ n ∈ D.gammaSupport, (X ^ n - 1 : R[X]) ^ (D.gamma n).toNat := by
  refine D.phiA_mul_prod_eq_of_ringHom (Int.castRingHom R) (D.phiA_mul_prod_eq_int (R := ℚ) ?_)
  have hne {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
      algebraMap ℚ[X] (RatFunc ℚ) ((X ^ n - 1) ^ k) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ (algebraMap_X_pow_sub_one_ne_zero hn)
  have hprod (e : ℕ → ℕ) :
      algebraMap ℚ[X] (RatFunc ℚ) (∏ n ∈ D.gammaSupport, (X ^ n - 1) ^ e n) ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun n hn ↦ hne (D.pos_of_mem_gammaSupport hn).ne' _
  have key := D.ratFunc_eq_prod_zpow (K := ℚ)
  have hzpow : ∀ n ∈ D.gammaSupport, algebraMap ℚ[X] (RatFunc ℚ) (X ^ n - 1) ^ D.gamma n =
      algebraMap ℚ[X] (RatFunc ℚ) ((X ^ n - 1) ^ (D.gamma n).toNat) /
        algebraMap ℚ[X] (RatFunc ℚ) ((X ^ n - 1) ^ (-D.gamma n).toNat) := fun n hn ↦ by
    rw [map_pow, map_pow, ← zpow_natCast, ← zpow_natCast,
      ← zpow_sub₀ (algebraMap_X_pow_sub_one_ne_zero (D.pos_of_mem_gammaSupport hn).ne'),
      Int.toNat_sub_toNat_neg]
  rw [Finset.prod_congr rfl hzpow, Finset.prod_div_distrib, ← map_prod, ← map_prod, ratFunc_def,
    div_eq_div_iff (D.phiB_ne_zero ℚ |> (map_ne_zero_iff _
      (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).2) (hprod _), ← map_mul, ← map_mul] at key
  exact (IsFractionRing.injective ℚ[X] (RatFunc ℚ) key).trans (mul_comm _ _)

/-! ### Uniqueness -/

/-- Uniqueness of the gamma vector: in characteristic zero, a finitely supported `g : ℕ → ℤ`
satisfying the defining identity
`Φ_A · ∏_n (X ^ n - 1) ^ max(-g(n), 0) = Φ_B · ∏_n (X ^ n - 1) ^ max(g(n), 0)` is the gamma
vector. In characteristic `p` uniqueness fails, since `X ^ p - 1 = (X - 1) ^ p`. -/
theorem eq_gamma_of_phiA_mul_prod_eq_phiB_mul_prod {R : Type*} [CommRing R] [CharZero R]
    {g : ℕ → ℤ} {I : Finset ℕ} (hI : ∀ n ∉ I, g n = 0)
    (hg : D.phiA R * ∏ n ∈ I, (X ^ n - 1 : R[X]) ^ (-g n).toNat =
      D.phiB R * ∏ n ∈ I, (X ^ n - 1 : R[X]) ^ (g n).toNat) :
    g = D.gamma := by
  replace hg := D.phiA_mul_prod_eq_int hg
  -- `g 0 = 0`, since otherwise exactly one side of `hg` has the factor `X ^ 0 - 1 = 0`.
  have h0 : g 0 = 0 := by
    by_contra h0
    have hz {e : ℕ → ℕ} (he : e 0 ≠ 0) : ∏ n ∈ I, (X ^ n - 1 : ℤ[X]) ^ e n = 0 :=
      Finset.prod_eq_zero (by_contra fun h ↦ h0 (hI 0 h)) (by simp [he])
    rcases lt_or_gt_of_ne h0 with hlt | hlt
    · rw [hz (e := fun n ↦ (-g n).toNat) (by simp; omega), mul_zero] at hg
      exact mul_ne_zero (D.phiB_ne_zero ℤ)
        (monic_prod_X_pow_sub_one_pow (e := fun n ↦ (g n).toNat) (by simp; omega)).ne_zero hg.symm
    · rw [hz (e := fun n ↦ (g n).toNat) (by simp; omega), mul_zero] at hg
      exact mul_ne_zero (D.phiA_ne_zero ℤ)
        (monic_prod_X_pow_sub_one_pow (e := fun n ↦ (-g n).toNat) (by simp; omega)).ne_zero hg
  -- Spread both identities over `U = I ∪ gammaSupport` and divide one by the other.
  set U := I ∪ D.gammaSupport
  have hU {I' : Finset ℕ} (hI' : I' ⊆ U) {f : ℕ → ℤ} (hf : ∀ n ∉ I', f n = 0) (e : ℤ → ℕ)
      (he : e 0 = 0) :
      ∏ n ∈ I', (X ^ n - 1 : ℤ[X]) ^ e (f n) = ∏ n ∈ U, (X ^ n - 1 : ℤ[X]) ^ e (f n) :=
    Finset.prod_subset hI' fun n _ hn ↦ by rw [hf n hn, he, pow_zero]
  have hγ := D.phiA_mul_prod_eq_phiB_mul_prod ℤ
  rw [hU Finset.subset_union_left hI (fun z ↦ (-z).toNat) rfl,
    hU Finset.subset_union_left hI (fun z ↦ z.toNat) rfl] at hg
  rw [hU Finset.subset_union_right (fun n ↦ D.gamma_eq_zero_of_notMem) (fun z ↦ (-z).toNat) rfl,
    hU Finset.subset_union_right (fun n ↦ D.gamma_eq_zero_of_notMem) (fun z ↦ z.toNat) rfl] at hγ
  have key : ∏ n ∈ U, (X ^ n - 1 : ℤ[X]) ^ ((D.gamma n).toNat + (-g n).toNat) =
      ∏ n ∈ U, (X ^ n - 1 : ℤ[X]) ^ ((g n).toNat + (-D.gamma n).toNat) := by
    simp_rw [pow_add, Finset.prod_mul_distrib]
    refine mul_left_cancel₀ (D.phiB_ne_zero ℤ) ?_
    linear_combination (∏ n ∈ U, (X ^ n - 1 : ℤ[X]) ^ (-D.gamma n).toNat) * hg -
      (∏ n ∈ U, (X ^ n - 1 : ℤ[X]) ^ (-g n).toNat) * hγ
  have hkey := eq_of_prod_X_pow_sub_one_pow_eq (by simp [h0]) (by simp [h0]) key
  funext n
  by_cases hn : n ∈ U
  · have h₁ := congr_arg (Nat.cast : ℕ → ℤ) (hkey n hn)
    have h₂ := Int.toNat_sub_toNat_neg (g n)
    have h₃ := Int.toNat_sub_toNat_neg (D.gamma n)
    push_cast at h₁
    linarith
  · rw [hI n fun h ↦ hn (Finset.mem_union_left _ h),
      D.gamma_eq_zero_of_notMem fun h ↦ hn (Finset.mem_union_right _ h)]

/-! ### The degree identity and the gamma multiset -/

/-- Comparing degrees in the defining identity: `∑_n n γ(n) = 0`. -/
theorem sum_mul_gamma_eq_zero : ∑ n ∈ D.gammaSupport, (n : ℤ) * D.gamma n = 0 := by
  have h := congr_arg natDegree (D.phiA_mul_prod_eq_phiB_mul_prod ℤ)
  rw [(D.monic_phiA ℤ).natDegree_mul (monic_prod_X_pow_sub_one_pow (by simp)),
    (D.monic_phiB ℤ).natDegree_mul (monic_prod_X_pow_sub_one_pow (by simp)),
    natDegree_phiA, natDegree_phiB, natDegree_prod_X_pow_sub_one_pow (by simp),
    natDegree_prod_X_pow_sub_one_pow (by simp)] at h
  replace h := congr_arg (Nat.cast : ℕ → ℤ) (Nat.add_left_cancel h)
  push_cast at h
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at h
  rw [← neg_eq_zero, ← h, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  linear_combination (n : ℤ) * Int.toNat_sub_toNat_neg (D.gamma n)

/-- The gamma multiset of the LMFDB: the positive integer `n` with multiplicity `γ(n)` when
`γ(n) > 0`, and the negative integer `-n` with multiplicity `-γ(n)` when `γ(n) < 0`. -/
def gammaMultiset : Multiset ℤ :=
  ∑ n ∈ D.gammaSupport,
    (Multiset.replicate (D.gamma n).toNat (n : ℤ) + Multiset.replicate (-D.gamma n).toNat (-n : ℤ))

theorem gammaMultiset_def : D.gammaMultiset = ∑ n ∈ D.gammaSupport,
    (Multiset.replicate (D.gamma n).toNat (n : ℤ) +
      Multiset.replicate (-D.gamma n).toNat (-n : ℤ)) :=
  (rfl)

/-- A positive integer `n` occurs in the gamma multiset with multiplicity `max(γ(n), 0)`. -/
@[simp]
theorem count_natCast_gammaMultiset (n : ℕ) :
    D.gammaMultiset.count (n : ℤ) = (D.gamma n).toNat := by
  rw [gammaMultiset_def, Multiset.count_sum',
    Finset.sum_congr rfl fun k hk ↦ show _ = if k = n then (D.gamma k).toNat else 0 by
      have := D.pos_of_mem_gammaSupport hk
      rw [Multiset.count_add, Multiset.count_replicate, Multiset.count_replicate]
      split_ifs <;> omega,
    Finset.sum_ite_eq']
  split_ifs with hn
  · rfl
  · rw [D.gamma_eq_zero_of_notMem hn, Int.toNat_zero]

/-- A negative integer `-n` occurs in the gamma multiset with multiplicity `max(-γ(n), 0)`. -/
@[simp]
theorem count_neg_natCast_gammaMultiset (n : ℕ) :
    D.gammaMultiset.count (-n : ℤ) = (-D.gamma n).toNat := by
  rw [gammaMultiset_def, Multiset.count_sum',
    Finset.sum_congr rfl fun k hk ↦ show _ = if k = n then (-D.gamma k).toNat else 0 by
      have := D.pos_of_mem_gammaSupport hk
      rw [Multiset.count_add, Multiset.count_replicate, Multiset.count_replicate]
      split_ifs <;> omega,
    Finset.sum_ite_eq']
  split_ifs with hn
  · rfl
  · rw [D.gamma_eq_zero_of_notMem hn, neg_zero, Int.toNat_zero]

/-- The gamma multiset has no zero entry. -/
theorem zero_notMem_gammaMultiset : (0 : ℤ) ∉ D.gammaMultiset := by
  rw [← Multiset.count_eq_zero, ← Nat.cast_zero, count_natCast_gammaMultiset, gamma_zero,
    Int.toNat_zero]

/-- The entries of the gamma multiset sum to `0`. -/
theorem sum_gammaMultiset_eq_zero : D.gammaMultiset.sum = 0 := by
  rw [gammaMultiset_def, ← Multiset.coe_sumAddMonoidHom, map_sum, ← D.sum_mul_gamma_eq_zero]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [Multiset.coe_sumAddMonoidHom, Multiset.sum_add, Multiset.sum_replicate,
    Multiset.sum_replicate, nsmul_eq_mul, nsmul_eq_mul]
  linear_combination (n : ℤ) * Int.toNat_sub_toNat_neg (D.gamma n)

/-- The swap `(A, B) ↦ (B, A)` negates the entries of the gamma multiset. -/
@[simp]
theorem gammaMultiset_swap : D.swap.gammaMultiset = D.gammaMultiset.map Neg.neg := by
  rw [gammaMultiset_def, gammaMultiset_def, gammaSupport_swap, ← Multiset.coe_mapAddMonoidHom,
    map_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [Multiset.coe_mapAddMonoidHom, Multiset.map_add, Multiset.map_replicate,
    Multiset.map_replicate, gamma_swap, neg_neg, neg_neg, add_comm]

/-- The empty datum has the empty gamma multiset. -/
@[simp]
theorem gammaMultiset_default : (default : CyclotomicData).gammaMultiset = 0 := by
  simp [gammaMultiset_def]

end CyclotomicData

end TauCeti.Hypergeometric
