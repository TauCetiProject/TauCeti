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

The positive and negative entries are counted with multiplicity by `gammaPosCount` and
`gammaNegCount`. The rational scale `gammaScale` is the product of the powers `n ^ (n γ(n))`
that normalize the hypergeometric coefficients.

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
  `count_gammaMultiset`, `mem_gammaMultiset`, `zero_notMem_gammaMultiset` and
  `sum_gammaMultiset_eq_zero`.

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

theorem gammaSupport_eq_biUnion_divisors :
    D.gammaSupport = (D.A + D.B).toFinset.biUnion Nat.divisors := (rfl)

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
cyclotomic datum: the exponents with `Φ_A / Φ_B = ∏_n (X ^ n - 1) ^ γ(n)`. The sum over `A`
enters with a plus sign and the sum over `B` with a minus sign, so the swap negates `γ`. -/
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

/-- For weights `f` on cyclotomic indices, the quotient of products on the two
sides equals the product of their divisor products with exponents given by `γ`. -/
theorem prod_map_div_prod_map_eq_prod_zpow_gamma {G : Type*} [CommGroup G]
    (f : ℕ → G) :
    (D.A.map f).prod / (D.B.map f).prod =
      ∏ m ∈ D.gammaSupport, (∏ d ∈ m.divisors, f d) ^ D.gamma m := by
  let g (m : ℕ) := ∏ d ∈ m.divisors, f d
  have hinv := (ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq (f := f) (g := g)).1
    (fun _ _ ↦ rfl)
  have hindex (a : ℕ) (ha : a ∈ D.A + D.B) :
      f a = ∏ m ∈ D.gammaSupport, g m ^ (if m ∣ a then μ (a / m) else 0) := by
    rw [← hinv a (D.pos a ha), Nat.prod_divisorsAntidiagonal' (fun i j ↦ g j ^ μ i)]
    have hsub : a.divisors ⊆ D.gammaSupport := fun d hd ↦
      D.mem_gammaSupport.2 ⟨a, ha, Nat.dvd_of_mem_divisors hd⟩
    rw [← Finset.prod_subset hsub (fun m _ hm ↦ by
      rw [ite_eq_right (fun h ↦ hm (Nat.mem_divisors.2 ⟨h, (D.pos a ha).ne'⟩)), zpow_zero])]
    exact Finset.prod_congr rfl fun d hd ↦ by simp [Nat.dvd_of_mem_divisors hd]
  have hside (S : Multiset ℕ) (hS : S ≤ D.A + D.B) :
      (S.map f).prod = ∏ m ∈ D.gammaSupport,
        g m ^ ((S.filter (m ∣ ·)).map fun a ↦ μ (a / m)).sum := by
    induction S using Multiset.induction_on with
    | empty => simp
    | cons a S ih =>
      rw [Multiset.map_cons, Multiset.prod_cons,
        hindex a (Multiset.mem_of_le hS (Multiset.mem_cons_self ..)),
        ih ((Multiset.le_cons_self ..).trans hS),
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun m _ ↦ ?_
      rw [← zpow_add, Multiset.filter_cons]
      split_ifs <;> simp
  rw [hside _ (Multiset.le_add_right _ _), hside _ (Multiset.le_add_left _ _),
    ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl fun m _ ↦ by rw [gamma_def, zpow_sub, div_eq_mul_inv]

/-! ### The defining identity -/

section RatFunc

variable {K : Type*} [Field K]

/-- The defining rational function of a cyclotomic datum is `∏_n (X ^ n - 1) ^ γ(n)`. -/
theorem ratFunc_eq_prod_zpow :
    D.ratFunc K = ∏ n ∈ D.gammaSupport, algebraMap K[X] (RatFunc K) (X ^ n - 1) ^ D.gamma n := by
  have hS {S : Multiset ℕ} (hS : S ≤ D.A + D.B) : ∀ a ∈ S, a.divisors ⊆ D.gammaSupport :=
    fun a ha n hn ↦ D.mem_gammaSupport.2 ⟨a, Multiset.mem_of_le hS ha, Nat.dvd_of_mem_divisors hn⟩
  rw [ratFunc_def, phiA_def, phiB_def,
    algebraMap_prod_cyclotomic_eq_prod_zpow _ (hS (Multiset.le_add_right _ _)),
    algebraMap_prod_cyclotomic_eq_prod_zpow _ (hS (Multiset.le_add_left _ _)),
    ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun n hn ↦ ?_
  rw [gamma_def,
    zpow_sub₀ (RatFunc.algebraMap_ne_zero (X_pow_sub_C_ne_zero (D.pos_of_mem_gammaSupport hn) 1))]

end RatFunc

/-- An identity of the shape of the defining identity holds over `S` as soon as it holds over
`R`, for every ring homomorphism `R →+* S`. -/
private lemma phiA_mul_prod_eq_of_ringHom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {I : Finset ℕ} {e e' : ℕ → ℕ}
    (h : D.phiA R * ∏ n ∈ I, (X ^ n - 1 : R[X]) ^ e n =
      D.phiB R * ∏ n ∈ I, (X ^ n - 1 : R[X]) ^ e' n) :
    D.phiA S * ∏ n ∈ I, (X ^ n - 1 : S[X]) ^ e n =
      D.phiB S * ∏ n ∈ I, (X ^ n - 1 : S[X]) ^ e' n := by
  have h' := congr_arg (Polynomial.map f) h
  rwa [Polynomial.map_mul, Polynomial.map_mul, map_phiA, map_phiB, map_prod_X_pow_sub_one_pow,
    map_prod_X_pow_sub_one_pow] at h'

/-- An identity of the shape of the defining identity holds over `ℤ` as soon as it holds over
some ring of characteristic zero. -/
private lemma phiA_mul_prod_eq_int {R : Type*} [CommRing R] [CharZero R] {I : Finset ℕ}
    {e e' : ℕ → ℕ}
    (h : D.phiA R * ∏ n ∈ I, (X ^ n - 1 : R[X]) ^ e n =
      D.phiB R * ∏ n ∈ I, (X ^ n - 1 : R[X]) ^ e' n) :
    D.phiA ℤ * ∏ n ∈ I, (X ^ n - 1 : ℤ[X]) ^ e n =
      D.phiB ℤ * ∏ n ∈ I, (X ^ n - 1 : ℤ[X]) ^ e' n := by
  refine Polynomial.map_injective (Int.castRingHom R) Int.cast_injective ?_
  rwa [Polynomial.map_mul, Polynomial.map_mul, map_phiA, map_phiB, map_prod_X_pow_sub_one_pow,
    map_prod_X_pow_sub_one_pow]

/-- The defining identity of the gamma vector, cleared of denominators:
`Φ_A · ∏_{γ(n) < 0} (X ^ n - 1) ^ (-γ(n)) = Φ_B · ∏_{γ(n) > 0} (X ^ n - 1) ^ γ(n)`, over every
commutative ring. -/
theorem phiA_mul_prod_eq_phiB_mul_prod (R : Type*) [CommRing R] :
    D.phiA R * ∏ n ∈ D.gammaSupport, (X ^ n - 1 : R[X]) ^ (-D.gamma n).toNat =
      D.phiB R * ∏ n ∈ D.gammaSupport, (X ^ n - 1 : R[X]) ^ (D.gamma n).toNat := by
  refine D.phiA_mul_prod_eq_of_ringHom (Int.castRingHom R) (D.phiA_mul_prod_eq_int (R := ℚ) ?_)
  -- In `RatFunc ℚ`, `(X ^ n - 1) ^ max(γ(n), 0)` is
  -- `(X ^ n - 1) ^ γ(n) · (X ^ n - 1) ^ max(-γ(n), 0)`, and the product of the factors
  -- `(X ^ n - 1) ^ γ(n)` is `Φ_A / Φ_B`.
  have hsplit : ∀ n ∈ D.gammaSupport,
      algebraMap ℚ[X] (RatFunc ℚ) (X ^ n - 1) ^ (D.gamma n).toNat =
        algebraMap ℚ[X] (RatFunc ℚ) (X ^ n - 1) ^ D.gamma n *
          algebraMap ℚ[X] (RatFunc ℚ) (X ^ n - 1) ^ (-D.gamma n).toNat := fun n hn ↦ by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ <|
      RatFunc.algebraMap_ne_zero (X_pow_sub_C_ne_zero (D.pos_of_mem_gammaSupport hn) 1)]
    congr 1
    omega
  refine IsFractionRing.injective ℚ[X] (RatFunc ℚ) ?_
  simp_rw [map_mul, map_prod, map_pow]
  rw [Finset.prod_congr rfl hsplit, Finset.prod_mul_distrib, ← ratFunc_eq_prod_zpow, ratFunc_def,
    ← mul_assoc, mul_div_cancel₀ _ (RatFunc.algebraMap_ne_zero (D.phiB_ne_zero ℚ))]

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

/-- An integer `z` occurs in the gamma multiset with multiplicity `max(sign(z) γ(|z|), 0)`: a
positive `n` occurs `max(γ(n), 0)` times, a negative `-n` occurs `max(-γ(n), 0)` times, and `0`
does not occur. -/
@[simp]
theorem count_gammaMultiset (z : ℤ) :
    D.gammaMultiset.count z = (z.sign * D.gamma z.natAbs).toNat := by
  rw [gammaMultiset_def, Multiset.count_sum',
    Finset.sum_congr rfl fun k hk ↦
      show _ = if k = z.natAbs then (z.sign * D.gamma k).toNat else 0 by
        have := D.pos_of_mem_gammaSupport hk
        rw [Multiset.count_add, Multiset.count_replicate, Multiset.count_replicate]
        rcases lt_trichotomy z 0 with h | rfl | h
        · rw [Int.sign_eq_neg_one_of_neg h]
          split_ifs <;> omega
        · rw [Int.sign_zero]
          split_ifs <;> omega
        · rw [Int.sign_eq_one_of_pos h]
          split_ifs <;> omega,
    Finset.sum_ite_eq']
  split_ifs with hz
  · rfl
  · rw [D.gamma_eq_zero_of_notMem hz, mul_zero, Int.toNat_zero]

/-- A positive integer `n` occurs in the gamma multiset with multiplicity `max(γ(n), 0)`. -/
theorem count_natCast_gammaMultiset (n : ℕ) :
    D.gammaMultiset.count (n : ℤ) = (D.gamma n).toNat := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.cast_zero, count_gammaMultiset, Int.sign_zero, zero_mul, gamma_zero]
  · rw [count_gammaMultiset, Int.sign_natCast_of_ne_zero hn, Int.natAbs_natCast, one_mul]

/-- A negative integer `-n` occurs in the gamma multiset with multiplicity `max(-γ(n), 0)`. -/
theorem count_neg_natCast_gammaMultiset (n : ℕ) :
    D.gammaMultiset.count (-n : ℤ) = (-D.gamma n).toNat := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.cast_zero, neg_zero, count_gammaMultiset, Int.sign_zero, zero_mul, gamma_zero, neg_zero]
  · rw [count_gammaMultiset, Int.sign_neg, Int.sign_natCast_of_ne_zero hn, Int.natAbs_neg,
      Int.natAbs_natCast, neg_one_mul]

/-- An integer `z` lies in the gamma multiset exactly when `sign(z) γ(|z|) > 0`. -/
theorem mem_gammaMultiset {z : ℤ} : z ∈ D.gammaMultiset ↔ 0 < z.sign * D.gamma z.natAbs := by
  rw [← Multiset.count_pos, count_gammaMultiset, Int.lt_toNat, Nat.cast_zero]

/-- The gamma multiset has no zero entry. -/
theorem zero_notMem_gammaMultiset : (0 : ℤ) ∉ D.gammaMultiset := by
  simp [mem_gammaMultiset]

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

/-- The number `r` of positive entries in the signed gamma multiset. -/
def gammaPosCount : ℕ := D.gammaMultiset.countP (0 < ·)

/-- The number `s` of negative entries in the signed gamma multiset. -/
def gammaNegCount : ℕ := D.gammaMultiset.countP (· < 0)

theorem gammaPosCount_eq_countP : D.gammaPosCount = D.gammaMultiset.countP (0 < ·) := (rfl)

theorem gammaNegCount_eq_countP : D.gammaNegCount = D.gammaMultiset.countP (· < 0) := (rfl)

@[simp]
theorem gammaPosCount_swap : D.swap.gammaPosCount = D.gammaNegCount := by
  rw [gammaPosCount_eq_countP, gammaNegCount_eq_countP, gammaMultiset_swap, Multiset.countP_map,
    Multiset.countP_eq_card_filter]
  simp

@[simp]
theorem gammaNegCount_swap : D.swap.gammaNegCount = D.gammaPosCount := by
  simpa only [swap_swap] using D.swap.gammaPosCount_swap.symm

/-- The number of positive entries is the sum of the positive parts of the exponents. -/
theorem gammaPosCount_eq_sum : D.gammaPosCount = ∑ m ∈ D.gammaSupport, (D.gamma m).toNat := by
  rw [gammaPosCount_eq_countP, gammaMultiset_def, ← Multiset.coe_countPAddMonoidHom, map_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  simp [← Multiset.nsmul_singleton, map_nsmul, map_add, Multiset.countP_eq_card_filter,
    Multiset.filter_singleton, D.pos_of_mem_gammaSupport hm]

/-- The number of negative entries is the sum of the negative parts of the exponents. -/
theorem gammaNegCount_eq_sum : D.gammaNegCount = ∑ m ∈ D.gammaSupport, (-D.gamma m).toNat := by
  simpa using D.swap.gammaPosCount_eq_sum

@[simp]
theorem gammaPosCount_default : (default : CyclotomicData).gammaPosCount = 0 := by
  simp [gammaPosCount_eq_sum]

@[simp]
theorem gammaNegCount_default : (default : CyclotomicData).gammaNegCount = 0 := by
  simp [gammaNegCount_eq_sum]

/-- The sums of the positive and absolute negative gamma entries agree. -/
theorem sum_mul_gamma_toNat_eq :
    ∑ m ∈ D.gammaSupport, m * (D.gamma m).toNat =
      ∑ m ∈ D.gammaSupport, m * (-D.gamma m).toNat := by
  zify
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← D.sum_mul_gamma_eq_zero]
  exact Finset.sum_congr rfl fun m _ ↦ by rw [← mul_sub, Int.toNat_sub_toNat_neg]

/-- The positive rational scale `M = ∏ m ^ (m γ(m))` in the factorial
formula for the hypergeometric coefficients. -/
def gammaScale : ℚ := ∏ m ∈ D.gammaSupport, (m : ℚ) ^ ((m : ℤ) * D.gamma m)

theorem gammaScale_def : D.gammaScale =
    ∏ m ∈ D.gammaSupport, (m : ℚ) ^ ((m : ℤ) * D.gamma m) := (rfl)

@[simp]
theorem gammaScale_pos : 0 < D.gammaScale := by
  rw [gammaScale_def]
  exact Finset.prod_pos fun m hm ↦ zpow_pos (by exact_mod_cast D.pos_of_mem_gammaSupport hm) _

@[simp]
theorem gammaScale_swap : D.swap.gammaScale = D.gammaScale⁻¹ := by
  simp [gammaScale_def, Finset.prod_inv_distrib]

@[simp]
theorem gammaScale_default : (default : CyclotomicData).gammaScale = 1 := by
  simp [gammaScale_def]

end CyclotomicData

end TauCeti.Hypergeometric
