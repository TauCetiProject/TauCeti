/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Ring.QPochhammer
public import TauCeti.RingTheory.Polynomial.Cyclotomic.IndexMonoid
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import TauCeti.NumberTheory.Divisors

/-!
# Factorial polynomials

The factorial polynomial `P_N = (q; q)_N = (1 - q) (1 - q²) ⋯ (1 - q ^ N)` over a commutative
ring `R`. Its multiples form the cofinal system of ideals behind the full cyclotomic (Habiro)
completion `lim R[q] / (P_N)`, and its products `a_n(q) P_n(q)` are the terms of the factorial
expansions of elements of that completion.

The basic fact is the signed cyclotomic factorization
`(-1) ^ N P_N = ∏_{d = 1}^{N} Φ_d ^ ⌊N / d⌋`, obtained by factoring each `q ^ i - 1` into the
cyclotomic polynomials of the divisors of `i` and counting, for each `d`, the `⌊N / d⌋` multiples
of `d` among `1, …, N`. It holds over every commutative ring, including the zero ring. Its sign
is the one needed for monic division: `P_N` itself has leading coefficient `(-1) ^ N`, so it is
not monic for odd `N`, but `(-1) ^ N P_N` is a monic cyclotomic index. Consequently the ideals
`(P_N)` and the cyclotomic ideals `(f)`, `f ∈ cycloIndex R S`, are mutually cofinal for `S` the
set of all positive orders, and so are the ideals `(P_N)` and `((q ^ m - 1) ^ k)`.

Over a characteristic-zero domain the multiplicity `⌊N / d⌋` is sharp: `Φ_d ^ k ∣ P_N` exactly
when `d k ≤ N`. In characteristic two it is not, since there `Φ_1 = Φ_2`.

## Main definitions

* `TauCeti.factorialPoly R N`: the factorial polynomial `P_N = ∏_{i = 1}^{N} (1 - X ^ i)` in
  `R[X]`, that is, the finite q-Pochhammer product `(X; X)_N`.

## Main results

* `TauCeti.factorialPoly_succ`: `P_{N + 1} = P_N (1 - X ^ (N + 1))`.
* `TauCeti.map_factorialPoly`: coefficient change.
* `TauCeti.factorialPoly_dvd_factorialPoly`: `P_M ∣ P_N` for `M ≤ N`.
* `TauCeti.neg_one_pow_mul_factorialPoly_eq_prod_cyclotomic`: the signed cyclotomic factorization
  `(-1) ^ N P_N = ∏_{d = 1}^{N} Φ_d ^ (N / d)`.
* `TauCeti.monic_neg_one_pow_mul_factorialPoly`, `TauCeti.leadingCoeff_factorialPoly`,
  `TauCeti.natDegree_factorialPoly`: `(-1) ^ N P_N` is monic, `P_N` has leading coefficient
  `(-1) ^ N`, and degree `N (N + 1) / 2` over a nontrivial ring.
* `TauCeti.prod_cyclotomic_pow_dvd_factorialPoly`: `∏_{d ∈ s} Φ_d ^ e_d ∣ P_N` once
  `d e_d ≤ N` for every `d ∈ s`.
* `TauCeti.exists_dvd_factorialPoly`, `TauCeti.neg_one_pow_mul_factorialPoly_mem_cycloIndex`:
  every cyclotomic index divides some `P_N`, and `(-1) ^ N P_N` is a cyclotomic index for any
  set of orders containing `1, …, N`.
* `TauCeti.X_pow_sub_one_pow_dvd_factorialPoly`, `TauCeti.factorialPoly_dvd_X_pow_sub_one_pow`:
  `(X ^ m - 1) ^ k ∣ P_N` for `0 < m` and `m k ≤ N`, and `P_N ∣ (X ^ m - 1) ^ N` when every
  `1 ≤ i ≤ N` divides `m`.
* `TauCeti.X_sub_C_pow_dvd_factorialPoly`: `(X - ζ) ^ k ∣ P_N` for `ζ ^ d = 1`, `0 < d` and
  `d k ≤ N`.
* `TauCeti.cyclotomic_pow_dvd_factorialPoly_iff`: over a characteristic-zero domain,
  `Φ_d ^ k ∣ P_N ↔ d k ≤ N` for `0 < d`.

## References

* K. Habiro, *Cyclotomic completions of polynomial rings*, Publ. RIMS Kyoto Univ. 40 (2004),
  1127–1146, §1 and Proposition 7.1.
* K. Habiro, *Cyclotomic completions of polynomial rings*, arXiv:math/0209324v1, §1.
-/

public section

open Polynomial Finset

namespace TauCeti

section CommRing

variable (R : Type*) [CommRing R] {R' : Type*} [CommRing R']

/-- The factorial polynomial `P_N = (1 - X) (1 - X ^ 2) ⋯ (1 - X ^ N)`, the finite q-Pochhammer
product `(X; X)_N` in `R[X]`. Its leading coefficient is `(-1) ^ N`, so `(-1) ^ N P_N`, rather
than `P_N`, is the monic associate used for division. -/
noncomputable def factorialPoly (N : ℕ) : R[X] :=
  qPochhammer X X N

/-- The factorial polynomial is the q-Pochhammer product `(X; X)_N`. -/
theorem factorialPoly_eq_qPochhammer (N : ℕ) : factorialPoly R N = qPochhammer X X N :=
  (rfl)

/-- The defining product formula `P_N = ∏_{i < N} (1 - X ^ (i + 1))`. -/
theorem factorialPoly_def (N : ℕ) :
    factorialPoly R N = ∏ i ∈ range N, (1 - X ^ (i + 1)) := by
  rw [factorialPoly_eq_qPochhammer, qPochhammer_self]

/-- `P_0 = 1`. -/
@[simp]
theorem factorialPoly_zero : factorialPoly R 0 = 1 := by
  simp [factorialPoly_eq_qPochhammer]

/-- `P_1 = 1 - X`. -/
@[simp]
theorem factorialPoly_one : factorialPoly R 1 = 1 - X := by
  simp [factorialPoly_eq_qPochhammer]

/-- The recursion `P_{N + 1} = P_N (1 - X ^ (N + 1))`. -/
theorem factorialPoly_succ (N : ℕ) :
    factorialPoly R (N + 1) = factorialPoly R N * (1 - X ^ (N + 1)) := by
  simp [factorialPoly_def, prod_range_succ]

variable {R}

/-- The factorial polynomial commutes with coefficient change. -/
@[simp]
theorem map_factorialPoly (φ : R →+* R') (N : ℕ) :
    (factorialPoly R N).map φ = factorialPoly R' N := by
  simp [factorialPoly_eq_qPochhammer]

/-- `P_N (0) = 1`. -/
@[simp]
theorem eval_zero_factorialPoly (N : ℕ) : (factorialPoly R N).eval 0 = 1 := by
  simp [factorialPoly_def, eval_prod]

/-- The constant coefficient of `P_N` is one. -/
@[simp]
theorem coeff_zero_factorialPoly (N : ℕ) : (factorialPoly R N).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, eval_zero_factorialPoly]

/-- `P_M ∣ P_N` for `M ≤ N`. -/
theorem factorialPoly_dvd_factorialPoly {M N : ℕ} (h : M ≤ N) :
    factorialPoly R M ∣ factorialPoly R N := by
  rw [factorialPoly_def, factorialPoly_def]
  exact prod_dvd_prod_of_subset _ _ _ (range_subset_range.mpr h)

/-- The sign-corrected factorial polynomial is the product of the monic factors `X ^ i - 1`:
`(-1) ^ N P_N = ∏_{i < N} (X ^ (i + 1) - 1)`. -/
theorem neg_one_pow_mul_factorialPoly (N : ℕ) :
    (-1) ^ N * factorialPoly R N = ∏ i ∈ range N, (X ^ (i + 1) - 1) := by
  have h := prod_neg (s := range N) (f := fun i ↦ (1 : R[X]) - X ^ (i + 1))
  rw [card_range] at h
  rw [factorialPoly_def, ← h]
  exact prod_congr rfl fun _ _ ↦ neg_sub _ _

/-- `(-1) ^ N P_N` is monic. -/
theorem monic_neg_one_pow_mul_factorialPoly (N : ℕ) :
    ((-1) ^ N * factorialPoly R N).Monic := by
  rw [neg_one_pow_mul_factorialPoly]
  exact monic_prod_of_monic _ _ fun i _ ↦ monic_X_pow_sub_C 1 i.succ_ne_zero

/-- The signed cyclotomic factorization of the factorial polynomial:
`(-1) ^ N P_N = ∏_{d = 1}^{N} Φ_d ^ ⌊N / d⌋`. -/
theorem neg_one_pow_mul_factorialPoly_eq_prod_cyclotomic (N : ℕ) :
    (-1) ^ N * factorialPoly R N = ∏ d ∈ Ioc 0 N, cyclotomic d R ^ (N / d) := by
  rw [neg_one_pow_mul_factorialPoly, ← Nat.prod_Ioc_prod_divisors, ← Ico_add_one_add_one_eq_Ioc,
    ← prod_Ico_add', ← range_eq_Ico]
  exact prod_congr rfl fun i _ ↦ (prod_cyclotomic_eq_X_pow_sub_one i.succ_pos R).symm

/-- `P_N` is `(-1) ^ N` times its monic associate. -/
private theorem factorialPoly_eq_C_mul (N : ℕ) :
    factorialPoly R N = C ((-1) ^ N) * ((-1) ^ N * factorialPoly R N) := by
  rw [← mul_assoc]
  simp [← mul_pow]

/-- The leading coefficient of `P_N` is `(-1) ^ N`. -/
@[simp]
theorem leadingCoeff_factorialPoly (N : ℕ) : (factorialPoly R N).leadingCoeff = (-1) ^ N := by
  rw [factorialPoly_eq_C_mul, leadingCoeff_mul_monic (monic_neg_one_pow_mul_factorialPoly N),
    leadingCoeff_C]

/-- Over a nontrivial ring `P_N` has degree `N (N + 1) / 2`. -/
@[simp]
theorem natDegree_factorialPoly [Nontrivial R] (N : ℕ) :
    (factorialPoly R N).natDegree = N * (N + 1) / 2 := by
  rw [factorialPoly_eq_C_mul, natDegree_C_mul_of_isUnit (isUnit_neg_one.pow N),
    neg_one_pow_mul_factorialPoly,
    natDegree_prod_of_monic _ _ fun i _ ↦ monic_X_pow_sub_C 1 i.succ_ne_zero]
  rw [sum_congr rfl fun i _ ↦ by rw [← C_1, natDegree_X_pow_sub_C]]
  have h := sum_range_id_mul_two (N + 1)
  simp [sum_range_succ', mul_comm (N + 1)] at h
  omega

/-- A product `∏_{d ∈ s} Φ_d ^ e_d` of powers of distinct cyclotomic polynomials divides `P_N`
once `d e_d ≤ N` for every `d ∈ s`. -/
theorem prod_cyclotomic_pow_dvd_factorialPoly {s : Finset ℕ} {e : ℕ → ℕ} {N : ℕ}
    (h : ∀ d ∈ s, d * e d ≤ N) : ∏ d ∈ s, cyclotomic d R ^ e d ∣ factorialPoly R N := by
  rw [← ((isUnit_neg_one (α := R[X])).pow N).dvd_mul_left,
    neg_one_pow_mul_factorialPoly_eq_prod_cyclotomic]
  -- Outside `Ioc 0 N` the factor `Φ_d ^ (N / d)` is one, so only `d ∈ s ∩ Ioc 0 N` matter.
  have hout : ∀ d ∈ s, d ∉ Ioc 0 N → cyclotomic d R ^ e d = 1 := by
    intro d hd hdN
    rcases Nat.eq_zero_or_pos d with rfl | hpos
    · simp
    · have : e d = 0 := by
        by_contra he
        exact hdN (mem_Ioc.mpr ⟨hpos, le_trans (Nat.le_mul_of_pos_right d
          (Nat.pos_of_ne_zero he)) (h d hd)⟩)
      simp [this]
  rw [← prod_subset (inter_subset_left (s₁ := s) (s₂ := Ioc 0 N))
    fun d hd hd' ↦ hout d hd fun h' ↦ hd' (mem_inter.mpr ⟨hd, h'⟩)]
  refine (prod_dvd_prod_of_dvd _ _ fun d hd ↦ pow_dvd_pow _ ?_).trans
    (prod_dvd_prod_of_subset _ _ _ inter_subset_right)
  obtain ⟨hds, hdN⟩ := mem_inter.mp hd
  exact (Nat.le_div_iff_mul_le (mem_Ioc.mp hdN).1).mpr (mul_comm d (e d) ▸ h d hds)

/-- `Φ_d ^ k ∣ P_N` once `d k ≤ N`. -/
theorem cyclotomic_pow_dvd_factorialPoly {d k N : ℕ} (h : d * k ≤ N) :
    cyclotomic d R ^ k ∣ factorialPoly R N := by
  simpa using prod_cyclotomic_pow_dvd_factorialPoly (R := R) (s := {d}) (e := fun _ ↦ k)
    (by simpa using h)

/-- The cofinal chain of cyclotomic indices is dominated by the factorial polynomials:
`∏_{d ∈ S, 1 ≤ d ≤ N} Φ_d ^ N ∣ P_{N²}`. -/
theorem cycloChain_dvd_factorialPoly (S : Set ℕ) (N : ℕ) :
    cycloChain R S N ∣ factorialPoly R (N * N) := by
  classical
  rw [cycloChain_def]
  exact prod_cyclotomic_pow_dvd_factorialPoly fun d hd ↦
    Nat.mul_le_mul_right N (mem_Icc.mp (mem_filter.mp hd).1).2

/-- Factorial cofinality: every cyclotomic index divides some factorial polynomial. -/
theorem exists_dvd_factorialPoly {S : Set ℕ} {f : R[X]} (hf : f ∈ cycloIndex R S) :
    ∃ N, f ∣ factorialPoly R N := by
  obtain ⟨N, hN⟩ := exists_dvd_cycloChain hf
  exact ⟨N * N, hN.trans (cycloChain_dvd_factorialPoly S N)⟩

/-- The monic associate `(-1) ^ N P_N` is a cyclotomic index for any set of orders containing
`1, …, N`. -/
theorem neg_one_pow_mul_factorialPoly_mem_cycloIndex {S : Set ℕ} {N : ℕ}
    (hS : Set.Ioc 0 N ⊆ S) : (-1) ^ N * factorialPoly R N ∈ cycloIndex R S := by
  rw [neg_one_pow_mul_factorialPoly_eq_prod_cyclotomic]
  exact prod_cyclotomic_pow_mem_cycloIndex _ _ _ fun d hd ↦ hS (by simpa using hd)

/-- `(X ^ m - 1) ^ k ∣ P_N` for `0 < m` and `m k ≤ N`: each cyclotomic factor `Φ_d`, `d ∣ m`,
of `X ^ m - 1` occurs at least `k` times in `P_N`. -/
theorem X_pow_sub_one_pow_dvd_factorialPoly {m k N : ℕ} (hm : 0 < m) (h : m * k ≤ N) :
    (X ^ m - 1 : R[X]) ^ k ∣ factorialPoly R N := by
  rw [← prod_cyclotomic_eq_X_pow_sub_one hm, ← prod_pow]
  exact prod_cyclotomic_pow_dvd_factorialPoly fun d hd ↦
    (Nat.mul_le_mul_right k (Nat.divisor_le hd)).trans h

/-- `(X - ζ) ^ k ∣ P_N` for `ζ ^ d = 1`, `0 < d` and `d k ≤ N`: the factors `1 - X ^ (d j)`,
`1 ≤ j ≤ k`, of `P_N` all vanish at `ζ`. -/
theorem X_sub_C_pow_dvd_factorialPoly {ζ : R} {d k N : ℕ} (hd : 0 < d) (hζ : ζ ^ d = 1)
    (h : d * k ≤ N) : (X - C ζ) ^ k ∣ factorialPoly R N := by
  induction k generalizing N with
  | zero => simp
  | succ k ih =>
    obtain ⟨M, hM⟩ : ∃ M, d * (k + 1) = M + 1 :=
      ⟨d * (k + 1) - 1, by have : 0 < d * (k + 1) := Nat.mul_pos hd (by omega); omega⟩
    have hk : d * k ≤ M := by rw [Nat.mul_succ] at hM; omega
    refine Dvd.dvd.trans ?_ (factorialPoly_dvd_factorialPoly (hM ▸ h))
    rw [pow_succ, factorialPoly_succ]
    refine mul_dvd_mul (ih hk) (dvd_iff_isRoot.mpr ?_)
    rw [← hM, IsRoot, eval_sub, eval_one, eval_pow, eval_X, pow_mul, hζ, one_pow, sub_self]

/-- `P_N ∣ (X ^ m - 1) ^ N` when every `1 ≤ i ≤ N` divides `m`, for instance `m = N!`. -/
theorem factorialPoly_dvd_X_pow_sub_one_pow {m N : ℕ} (h : ∀ i ∈ Ioc 0 N, i ∣ m) :
    factorialPoly R N ∣ (X ^ m - 1 : R[X]) ^ N := by
  have hpow : (X ^ m - 1 : R[X]) ^ N = ∏ _i ∈ range N, (X ^ m - 1 : R[X]) := by
    rw [prod_const, card_range]
  rw [← ((isUnit_neg_one (α := R[X])).pow N).mul_left_dvd, neg_one_pow_mul_factorialPoly, hpow]
  refine prod_dvd_prod_of_dvd _ _ fun i hi ↦ ?_
  obtain ⟨c, rfl⟩ := h (i + 1) (mem_Ioc.mpr ⟨i.succ_pos, mem_range.mp hi⟩)
  exact pow_one_sub_dvd_pow_mul_sub_one (X : R[X]) (i + 1) c

end CommRing

section CharZero

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

/-- Over a characteristic-zero domain the multiplicity of `Φ_d` in `P_N` is exactly `⌊N / d⌋`:
for `0 < d`, `Φ_d ^ k ∣ P_N` if and only if `d k ≤ N`. -/
theorem cyclotomic_pow_dvd_factorialPoly_iff {d k N : ℕ} (hd : 0 < d) :
    cyclotomic d R ^ k ∣ factorialPoly R N ↔ d * k ≤ N := by
  refine ⟨fun h ↦ ?_, cyclotomic_pow_dvd_factorialPoly⟩
  -- Pass to the fraction field `K`, where distinct cyclotomic polynomials are coprime.
  let K := FractionRing R
  have hK : cyclotomic d K ^ k ∣ (-1) ^ N * factorialPoly K N := by
    rw [((isUnit_neg_one (α := K[X])).pow N).dvd_mul_left]
    simpa using map_dvd (mapRingHom (algebraMap R K)) h
  -- Split off the factor `Φ_d ^ (N / d)` of `(-1) ^ N P_N`; it is `1` if `d > N`.
  have hsplit : (-1) ^ N * factorialPoly K N =
      cyclotomic d K ^ (N / d) * ∏ e ∈ (Ioc 0 N).erase d, cyclotomic e K ^ (N / e) := by
    rw [neg_one_pow_mul_factorialPoly_eq_prod_cyclotomic]
    by_cases hdN : d ∈ Ioc 0 N
    · exact (mul_prod_erase _ _ hdN).symm
    · rw [erase_eq_of_notMem hdN, Nat.div_eq_of_lt (by simpa [hd] using hdN), pow_zero, one_mul]
  have hcop : IsCoprime (cyclotomic d K ^ k)
      (∏ e ∈ (Ioc 0 N).erase d, cyclotomic e K ^ (N / e)) := by
    refine IsCoprime.pow_left (IsCoprime.prod_right fun e he ↦ IsCoprime.pow_right ?_)
    simpa using (cyclotomic.isCoprime_rat (ne_of_mem_erase he).symm).map
      (mapRingHom (Rat.castHom K))
  rw [hsplit] at hK
  have hpos : 0 < (cyclotomic d K).natDegree := by
    rw [natDegree_cyclotomic]
    exact Nat.totient_pos.mpr hd
  rw [mul_comm, ← Nat.le_div_iff_mul_le hd, ← pow_dvd_pow_iff (cyclotomic_ne_zero d K)
    (not_isUnit_of_natDegree_pos _ hpos)]
  exact hcop.dvd_of_dvd_mul_right hK

end CharZero

/-! ### Reference values -/

/-- `P_2 = 1 - q - q² + q³`. -/
example : factorialPoly ℤ 2 = 1 - X - X ^ 2 + X ^ 3 := by
  simp [factorialPoly_def, prod_range_succ]
  ring

/-- `P_3 = 1 - q - q² + q⁴ + q⁵ - q⁶`. -/
example : factorialPoly ℤ 3 = 1 - X - X ^ 2 + X ^ 4 + X ^ 5 - X ^ 6 := by
  simp [factorialPoly_def, prod_range_succ]
  ring

/-- `P_3 = -Φ_1³ Φ_2 Φ_3`, the signed cyclotomic factorization for `N = 3`. -/
example : factorialPoly ℤ 3 = -(cyclotomic 1 ℤ ^ 3 * cyclotomic 2 ℤ * cyclotomic 3 ℤ) := by
  have h := neg_one_pow_mul_factorialPoly_eq_prod_cyclotomic (R := ℤ) 3
  rw [show Ioc 0 3 = {1, 2, 3} by decide, prod_insert (by decide), prod_insert (by decide),
    prod_singleton] at h
  norm_num only at h
  linear_combination -h

/-- `P_1 = 1 - q` is not monic over `ℤ`: its leading coefficient is `-1`. -/
example : ¬(factorialPoly ℤ 1).Monic := by
  rw [Monic, leadingCoeff_factorialPoly]
  decide

/-- `P_3` has degree `6`. -/
example : (factorialPoly ℤ 3).natDegree = 6 := by
  simp

/-- The bound `⌊N / d⌋` is sharp over `ℤ`: `Φ_3² ∣ P_6` but `Φ_3² ∤ P_5`. -/
example : cyclotomic 3 ℤ ^ 2 ∣ factorialPoly ℤ 6 ∧ ¬cyclotomic 3 ℤ ^ 2 ∣ factorialPoly ℤ 5 := by
  simp only [cyclotomic_pow_dvd_factorialPoly_iff three_pos]
  decide

/-- `(q² - 1)² ∣ P_4`. -/
example : (X ^ 2 - 1 : ℤ[X]) ^ 2 ∣ factorialPoly ℤ 4 :=
  X_pow_sub_one_pow_dvd_factorialPoly two_pos le_rfl

end TauCeti
