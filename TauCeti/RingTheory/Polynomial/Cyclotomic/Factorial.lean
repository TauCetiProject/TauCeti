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

Every polynomial `g` has a normalized factorial expansion `g = ∑_{n < N} a_n P_n + P_N r_N` with
`deg a_n ≤ n`, computed by the recursion `r_0 = g`, `r_n = a_n + (1 - X ^ (n + 1)) r_{n + 1}`:
`a_n` is the remainder and `-r_{n + 1}` the quotient of `r_n` by the monic `X ^ (n + 1) - 1`. The
digits `a_n` with `n < N` are unique and depend only on the class of `g` modulo `P_N`; this is what
lets them pass to the completion `lim R[q] / (P_N)`.

## Main definitions

* `TauCeti.factorialPoly R N`: the factorial polynomial `P_N = ∏_{i = 1}^{N} (1 - X ^ i)` in
  `R[X]`, that is, the finite q-Pochhammer product `(X; X)_N`.
* `TauCeti.factorialIndex R N`: the monic associate `(-1) ^ N P_N` as an index of the full
  cyclotomic completion.
* `Polynomial.factorialDigit g n`, `Polynomial.factorialResidual g n`: the normalized factorial
  digits and residuals of a polynomial.

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
* `TauCeti.cyclotomic_pow_dvd_factorialPoly_iff`: over a characteristic-zero domain,
  `Φ_d ^ k ∣ P_N ↔ d k ≤ N` for `0 < d`.
* `TauCeti.eventually_dvd_factorialIndex`: every index of the full completion divides
  `(-1) ^ N P_N` for all large `N`.
* `Polynomial.sum_factorialDigit_mul_add_mul_factorialResidual`: the finite factorial expansion
  `g = ∑_{n < N} a_n P_n + P_N r_N`, with `Polynomial.degree_factorialDigit_le`: `deg a_n ≤ n`.
* `Polynomial.factorialDigit_eq_of_sum_add_eq`, `Polynomial.factorialResidual_eq_of_sum_add_eq`:
  uniqueness of bounded-degree factorial expansions.
* `Polynomial.factorialDigit_eq_of_dvd_sub`: the first `N` digits depend only on the class modulo
  `P_N`.
* `Polynomial.factorialDigit_sum_mul_factorialPoly`: digit extraction after reconstruction.
* `Polynomial.factorialDigit_add`, `Polynomial.factorialDigit_smul`,
  `Polynomial.factorialDigit_map`: digits are `R`-linear and commute with coefficient change.

## References

* K. Habiro, *Cyclotomic completions of polynomial rings*, Publ. RIMS Kyoto Univ. 40 (2004),
  1127–1146, §1 and Proposition 7.1.
* K. Habiro, *Cyclotomic completions of polynomial rings*, arXiv:math/0209324v1, §1 and the
  proof of Lemma 3.1.
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

variable (R) in
/-- The monic associate `(-1) ^ N P_N` of the factorial polynomial, as an index of the full
cyclotomic completion, whose orders are all positive integers. -/
noncomputable def factorialIndex (N : ℕ) : cycloIndex R {n | 0 < n} :=
  ⟨(-1) ^ N * factorialPoly R N, neg_one_pow_mul_factorialPoly_mem_cycloIndex fun _ hn ↦ hn.1⟩

@[simp]
theorem coe_factorialIndex (N : ℕ) :
    (factorialIndex R N : R[X]) = (-1) ^ N * factorialPoly R N :=
  (rfl)

/-- Divisibility by the index `(-1) ^ N P_N` is divisibility by `P_N`. -/
theorem factorialIndex_dvd_iff {N : ℕ} {p : R[X]} :
    (factorialIndex R N : R[X]) ∣ p ↔ factorialPoly R N ∣ p := by
  rw [coe_factorialIndex, ((isUnit_neg_one (α := R[X])).pow N).mul_left_dvd]

/-- `(-1) ^ M P_M ∣ (-1) ^ N P_N` for `M ≤ N`. -/
theorem factorialIndex_dvd_factorialIndex {M N : ℕ} (h : M ≤ N) :
    (factorialIndex R M : R[X]) ∣ factorialIndex R N :=
  factorialIndex_dvd_iff.mpr ((factorialPoly_dvd_factorialPoly h).trans (dvd_mul_left _ _))

/-- Factorial cofinality for the full completion: every index divides `(-1) ^ N P_N` for all
large `N`. -/
theorem eventually_dvd_factorialIndex (f : cycloIndex R {n | 0 < n}) :
    ∀ᶠ N in Filter.atTop, (f : R[X]) ∣ factorialIndex R N := by
  obtain ⟨N₀, hN₀⟩ := exists_dvd_factorialPoly f.property
  filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
  exact (hN₀.trans (dvd_mul_left _ _)).trans (factorialIndex_dvd_factorialIndex hN)

/-- `(X ^ m - 1) ^ k ∣ P_N` for `0 < m` and `m k ≤ N`: each cyclotomic factor `Φ_d`, `d ∣ m`,
of `X ^ m - 1` occurs at least `k` times in `P_N`. -/
theorem X_pow_sub_one_pow_dvd_factorialPoly {m k N : ℕ} (hm : 0 < m) (h : m * k ≤ N) :
    (X ^ m - 1 : R[X]) ^ k ∣ factorialPoly R N := by
  rw [← prod_cyclotomic_eq_X_pow_sub_one hm, ← prod_pow]
  exact prod_cyclotomic_pow_dvd_factorialPoly fun d hd ↦
    (Nat.mul_le_mul_right k (Nat.divisor_le hd)).trans h

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

end TauCeti

/-! ### Normalized factorial digits of a polynomial -/

namespace Polynomial

open TauCeti

variable {R : Type*} [CommRing R] {R' : Type*} [CommRing R']

/-- The residuals of the normalized factorial expansion of `g`: `r_0 = g`, and `r_{n + 1}` is the
negative of the quotient of `r_n` by the monic polynomial `X ^ (n + 1) - 1`. Thus
`r_n = a_n + (1 - X ^ (n + 1)) r_{n + 1}`, where `a_n = g.factorialDigit n` is the remainder. -/
noncomputable def factorialResidual (g : R[X]) : ℕ → R[X]
  | 0 => g
  | n + 1 => -(g.factorialResidual n /ₘ (X ^ (n + 1) - 1))

/-- The `n`th normalized factorial digit of `g`: the remainder of the residual `r_n` modulo the
monic polynomial `X ^ (n + 1) - 1`. The digits are the unique polynomials `a_n` with
`deg a_n ≤ n` and `g ≡ ∑_{n < N} a_n P_n` modulo every factorial polynomial `P_N`. -/
noncomputable def factorialDigit (g : R[X]) (n : ℕ) : R[X] :=
  g.factorialResidual n %ₘ (X ^ (n + 1) - 1)

/-- The zeroth factorial residual is the polynomial itself. -/
@[simp]
theorem factorialResidual_zero (g : R[X]) : g.factorialResidual 0 = g :=
  (rfl)

/-- The factorial residual recursion `r_{n + 1} = -(r_n /ₘ (X ^ (n + 1) - 1))`. -/
theorem factorialResidual_succ (g : R[X]) (n : ℕ) :
    g.factorialResidual (n + 1) = -(g.factorialResidual n /ₘ (X ^ (n + 1) - 1)) :=
  (rfl)

/-- The `n`th factorial digit is the remainder of `r_n` modulo `X ^ (n + 1) - 1`. -/
theorem factorialDigit_def (g : R[X]) (n : ℕ) :
    g.factorialDigit n = g.factorialResidual n %ₘ (X ^ (n + 1) - 1) :=
  (rfl)

/-- One step of the factorial recursion: `r_n = a_n + (1 - X ^ (n + 1)) r_{n + 1}`. -/
theorem factorialDigit_add_mul_factorialResidual_succ (g : R[X]) (n : ℕ) :
    g.factorialDigit n + (1 - X ^ (n + 1)) * g.factorialResidual (n + 1) =
      g.factorialResidual n := by
  rw [factorialDigit_def, factorialResidual_succ, mul_neg, ← neg_mul, neg_sub]
  exact modByMonic_add_div _ _

/-- The `n`th factorial digit has degree at most `n`. -/
theorem degree_factorialDigit_le (g : R[X]) (n : ℕ) : (g.factorialDigit n).degree ≤ n := by
  nontriviality R
  refine Order.le_of_lt_succ ?_
  have h := degree_modByMonic_lt (g.factorialResidual n)
    (monic_X_pow_sub_one (R := R) n.succ_ne_zero)
  rwa [← C_1, degree_X_pow_sub_C n.succ_pos] at h

/-- The factorial expansion of a polynomial up to precision `N`:
`g = ∑_{n < N} a_n P_n + P_N r_N`. -/
theorem sum_factorialDigit_mul_add_mul_factorialResidual (g : R[X]) (N : ℕ) :
    ∑ n ∈ range N, g.factorialDigit n * factorialPoly R n +
      factorialPoly R N * g.factorialResidual N = g := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, factorialPoly_succ]
    conv_rhs => rw [← ih, ← factorialDigit_add_mul_factorialResidual_succ g N]
    ring

/-- Splitting off the zeroth term of a shifted factorial expansion: with the shifted products
`(X ^ (k + 1); X)_n = (1 - X ^ (k + 1)) ⋯ (1 - X ^ (k + n))`, the terms after the zeroth are
`1 - X ^ (k + 1)` times an expansion shifted by one more. -/
private theorem sum_qPochhammer_add_mul_succ (k N : ℕ) (e : ℕ → R[X]) (c : R[X]) :
    ∑ n ∈ range (N + 1), e n * qPochhammer (X ^ (k + 1)) X n +
        qPochhammer (X ^ (k + 1)) X (N + 1) * c =
      e 0 + (1 - X ^ (k + 1)) * (∑ n ∈ range N, e (n + 1) *
        qPochhammer (X ^ (k + 1 + 1)) X n + qPochhammer (X ^ (k + 1 + 1)) X N * c) := by
  have hterm : ∀ n ∈ range N, e (n + 1) * qPochhammer (X ^ (k + 1)) X (n + 1) =
      (1 - X ^ (k + 1)) * (e (n + 1) * qPochhammer (X ^ (k + 1 + 1)) X n) := fun n _ ↦ by
    rw [qPochhammer_succ', ← pow_succ]
    ring
  rw [sum_range_succ', sum_congr rfl hterm, ← mul_sum, qPochhammer_zero, qPochhammer_succ',
    ← pow_succ]
  ring

/-- Uniqueness of shifted factorial expansions: with digits `a_n` of degree at most `k + n`, the
expansion `∑_{n < N} a_n (X ^ (k + 1); X)_n + (X ^ (k + 1); X)_N c` determines the digits and the
remainder `c`. -/
private theorem eq_of_sum_qPochhammer_add_eq (N : ℕ) :
    ∀ (k : ℕ) {a b : ℕ → R[X]} {c d : R[X]},
      (∀ n < N, (a n).degree ≤ (k + n : ℕ)) → (∀ n < N, (b n).degree ≤ (k + n : ℕ)) →
      ∑ n ∈ range N, a n * qPochhammer (X ^ (k + 1)) X n +
          qPochhammer (X ^ (k + 1)) X N * c =
        ∑ n ∈ range N, b n * qPochhammer (X ^ (k + 1)) X n +
          qPochhammer (X ^ (k + 1)) X N * d →
      (∀ n < N, a n = b n) ∧ c = d := by
  induction N with
  | zero => intro k a b c d _ _ h; simpa using h
  | succ N ih =>
    intro k a b c d ha hb h
    nontriviality R
    rw [sum_qPochhammer_add_mul_succ, sum_qPochhammer_add_mul_succ] at h
    set s := ∑ n ∈ range N, a (n + 1) * qPochhammer (X ^ (k + 1 + 1)) X n +
      qPochhammer (X ^ (k + 1 + 1)) X N * c
    set t := ∑ n ∈ range N, b (n + 1) * qPochhammer (X ^ (k + 1 + 1)) X n +
      qPochhammer (X ^ (k + 1 + 1)) X N * d
    -- Both sides are divisions with remainder by the monic `X ^ (k + 1) - 1`, so the zeroth
    -- digits and the tails agree.
    have hm : (X ^ (k + 1) - 1 : R[X]).Monic := monic_X_pow_sub_one k.succ_ne_zero
    have hlt {e : ℕ → R[X]} (he : ∀ n < N + 1, (e n).degree ≤ (k + n : ℕ)) :
        (e 0).degree < (X ^ (k + 1) - 1 : R[X]).degree := by
      rw [← C_1, degree_X_pow_sub_C k.succ_pos]
      exact Order.lt_succ_of_le (by simpa using he 0 (by omega))
    have h₁ := div_modByMonic_unique (f := a 0 + (1 - X ^ (k + 1)) * s) (-s) (a 0) hm
      ⟨by ring, hlt ha⟩
    have h₂ := div_modByMonic_unique (f := a 0 + (1 - X ^ (k + 1)) * s) (-t) (b 0) hm
      ⟨by rw [h]; ring, hlt hb⟩
    have hdeg {e : ℕ → R[X]} (he : ∀ n < N + 1, (e n).degree ≤ (k + n : ℕ)) :
        ∀ n < N, (e (n + 1)).degree ≤ (k + 1 + n : ℕ) := fun n hn ↦ by
      have h := he (n + 1) (by omega)
      rwa [show k + (n + 1) = k + 1 + n by omega] at h
    obtain ⟨hab, hcd⟩ := ih (k + 1) (hdeg ha) (hdeg hb) (neg_injective (h₁.1.symm.trans h₂.1))
    refine ⟨fun n hn ↦ ?_, hcd⟩
    rcases n with _ | n
    · exact h₁.2.symm.trans h₂.2
    · exact hab n (by omega)

/-- Uniqueness of bounded-degree factorial expansions at a finite precision. -/
private theorem eq_of_sum_mul_factorialPoly_add_eq {N : ℕ} {a b : ℕ → R[X]} {c d : R[X]}
    (ha : ∀ n < N, (a n).degree ≤ n) (hb : ∀ n < N, (b n).degree ≤ n)
    (h : ∑ n ∈ range N, a n * factorialPoly R n + factorialPoly R N * c =
      ∑ n ∈ range N, b n * factorialPoly R n + factorialPoly R N * d) :
    (∀ n < N, a n = b n) ∧ c = d := by
  simp only [factorialPoly_eq_qPochhammer] at h
  exact eq_of_sum_qPochhammer_add_eq N 0 (by simpa using ha) (by simpa using hb)
    (by simpa using h)

/-- **Uniqueness of factorial digits.** If `g = ∑_{n < N} a_n P_n + P_N c` with `deg a_n ≤ n`,
then the `a_n` are the first `N` factorial digits of `g`. -/
theorem factorialDigit_eq_of_sum_add_eq {g c : R[X]} {a : ℕ → R[X]} {N : ℕ}
    (ha : ∀ n < N, (a n).degree ≤ n)
    (h : ∑ n ∈ range N, a n * factorialPoly R n + factorialPoly R N * c = g) {n : ℕ}
    (hn : n < N) : g.factorialDigit n = a n :=
  ((eq_of_sum_mul_factorialPoly_add_eq (fun n _ ↦ degree_factorialDigit_le g n) ha
    ((sum_factorialDigit_mul_add_mul_factorialResidual g N).trans h.symm)).1 n hn)

/-- If `g = ∑_{n < N} a_n P_n + P_N c` with `deg a_n ≤ n`, then `c` is the `N`th factorial
residual of `g`. -/
theorem factorialResidual_eq_of_sum_add_eq {g c : R[X]} {a : ℕ → R[X]} {N : ℕ}
    (ha : ∀ n < N, (a n).degree ≤ n)
    (h : ∑ n ∈ range N, a n * factorialPoly R n + factorialPoly R N * c = g) :
    g.factorialResidual N = c :=
  (eq_of_sum_mul_factorialPoly_add_eq (fun n _ ↦ degree_factorialDigit_le g n) ha
    ((sum_factorialDigit_mul_add_mul_factorialResidual g N).trans h.symm)).2

/-- Changing `g` by a multiple of `P_N` does not change its first `N` factorial digits. -/
theorem factorialDigit_add_factorialPoly_mul (g c : R[X]) {n N : ℕ} (hn : n < N) :
    (g + factorialPoly R N * c).factorialDigit n = g.factorialDigit n := by
  refine factorialDigit_eq_of_sum_add_eq (c := g.factorialResidual N + c)
    (fun n _ ↦ degree_factorialDigit_le g n) ?_ hn
  rw [mul_add, ← add_assoc, sum_factorialDigit_mul_add_mul_factorialResidual]

/-- The first `N` factorial digits of `g` depend only on the class of `g` modulo `P_N`. -/
theorem factorialDigit_eq_of_dvd_sub {g g' : R[X]} {N : ℕ} (h : factorialPoly R N ∣ g - g')
    {n : ℕ} (hn : n < N) : g.factorialDigit n = g'.factorialDigit n := by
  obtain ⟨c, hc⟩ := h
  rw [sub_eq_iff_eq_add'.mp hc, factorialDigit_add_factorialPoly_mul _ _ hn]

/-- Once a factorial residual vanishes, so do all later digits. -/
theorem factorialDigit_eq_zero_of_factorialResidual_eq_zero {g : R[X]} {N : ℕ}
    (h : g.factorialResidual N = 0) {n : ℕ} (hn : N ≤ n) : g.factorialDigit n = 0 := by
  have hres : ∀ m, g.factorialResidual (N + m) = 0 := by
    intro m
    induction m with
    | zero => exact h
    | succ m ih => rw [← add_assoc, factorialResidual_succ, ih, zero_divByMonic, neg_zero]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [factorialDigit_def, hres, zero_modByMonic]

/-- **Digit extraction after reconstruction.** The factorial digits of a finite factorial sum
`∑_{i < N} a_i P_i` with `deg a_i ≤ i` are the `a_i`, followed by zeros. -/
theorem factorialDigit_sum_mul_factorialPoly {a : ℕ → R[X]} {N : ℕ}
    (ha : ∀ n < N, (a n).degree ≤ n) (n : ℕ) :
    (∑ i ∈ range N, a i * factorialPoly R i).factorialDigit n = if n < N then a n else 0 := by
  have h : ∑ i ∈ range N, a i * factorialPoly R i + factorialPoly R N * 0 =
      ∑ i ∈ range N, a i * factorialPoly R i := by
    rw [mul_zero, add_zero]
  split_ifs with hn
  · exact factorialDigit_eq_of_sum_add_eq ha h hn
  · exact factorialDigit_eq_zero_of_factorialResidual_eq_zero
      (factorialResidual_eq_of_sum_add_eq ha h) (not_lt.mp hn)

/-- The zeroth factorial digit is the value at `q = 1`. -/
theorem factorialDigit_zero_eq_C_eval_one (g : R[X]) : g.factorialDigit 0 = C (g.eval 1) := by
  rw [factorialDigit_def, factorialResidual_zero, zero_add, pow_one, ← C_1,
    modByMonic_X_sub_C_eq_C_eval]

/-- Factorial digits are additive. -/
@[simp]
theorem factorialDigit_add (g h : R[X]) (n : ℕ) :
    (g + h).factorialDigit n = g.factorialDigit n + h.factorialDigit n := by
  refine factorialDigit_eq_of_sum_add_eq (N := n + 1)
    (c := g.factorialResidual (n + 1) + h.factorialResidual (n + 1))
    (fun m _ ↦ degree_add_le_of_degree_le (degree_factorialDigit_le g m)
      (degree_factorialDigit_le h m)) ?_ n.lt_add_one
  conv_rhs => rw [← sum_factorialDigit_mul_add_mul_factorialResidual g (n + 1),
    ← sum_factorialDigit_mul_add_mul_factorialResidual h (n + 1)]
  simp only [add_mul, sum_add_distrib, mul_add]
  ring

/-- Factorial digits commute with scalar multiplication. -/
@[simp]
theorem factorialDigit_smul (r : R) (g : R[X]) (n : ℕ) :
    (r • g).factorialDigit n = r • g.factorialDigit n := by
  refine factorialDigit_eq_of_sum_add_eq (N := n + 1) (c := r • g.factorialResidual (n + 1))
    (fun m _ ↦ (degree_smul_le r _).trans (degree_factorialDigit_le g m)) ?_ n.lt_add_one
  conv_rhs => rw [← sum_factorialDigit_mul_add_mul_factorialResidual g (n + 1)]
  simp only [smul_add, smul_sum, smul_mul_assoc, mul_smul_comm]

/-- The zero polynomial has all factorial digits zero. -/
@[simp]
theorem factorialDigit_zero (n : ℕ) : (0 : R[X]).factorialDigit n = 0 := by
  simpa using factorialDigit_smul (0 : R) (0 : R[X]) n

/-- Factorial residuals commute with coefficient change. -/
@[simp]
theorem factorialResidual_map (φ : R →+* R') (g : R[X]) (n : ℕ) :
    (g.map φ).factorialResidual n = (g.factorialResidual n).map φ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [factorialResidual_succ, factorialResidual_succ, Polynomial.map_neg,
      map_divByMonic φ (monic_X_pow_sub_one n.succ_ne_zero), ih]
    simp

/-- Factorial digits commute with coefficient change. -/
@[simp]
theorem factorialDigit_map (φ : R →+* R') (g : R[X]) (n : ℕ) :
    (g.map φ).factorialDigit n = (g.factorialDigit n).map φ := by
  rw [factorialDigit_def, factorialDigit_def,
    map_modByMonic φ (monic_X_pow_sub_one n.succ_ne_zero), factorialResidual_map]
  simp

end Polynomial

namespace TauCeti

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

/-- The zeroth factorial residual is the polynomial itself: `r_0 = q² + q + 1`. -/
example : (X ^ 2 + X + 1 : ℤ[X]).factorialResidual 0 = X ^ 2 + X + 1 :=
  factorialResidual_zero _

/-- `q = 1 · P_0 + (-1) · P_1` has factorial digits `1, -1, 0, 0, …`; the sign of `-1` comes from
the negated quotient in the recursion. -/
example (n : ℕ) :
    (X : ℤ[X]).factorialDigit n = if n = 0 then 1 else if n = 1 then -1 else 0 := by
  have h : ∑ i ∈ range 2, (if i = 0 then 1 else -1 : ℤ[X]) * factorialPoly ℤ i = X := by
    simp [sum_range_succ]
  rw [← h, factorialDigit_sum_mul_factorialPoly fun m hm ↦ by interval_cases m <;> simp]
  rcases n with _ | _ | n <;> simp

/-- `1 - q = P_1` has factorial digits `0, 1, 0, 0, …`. -/
example (n : ℕ) : (1 - X : ℤ[X]).factorialDigit n = if n = 1 then 1 else 0 := by
  have h : ∑ i ∈ range 2, (if i = 1 then 1 else 0 : ℤ[X]) * factorialPoly ℤ i = 1 - X := by
    simp
  rw [← h, factorialDigit_sum_mul_factorialPoly fun m hm ↦ by interval_cases m <;> simp]
  rcases n with _ | _ | n <;> simp

/-- The first factorial residual of `q` is `-1`. -/
example : (X : ℤ[X]).factorialResidual 1 = -1 :=
  factorialResidual_eq_of_sum_add_eq (a := fun _ ↦ 1) (fun _ _ ↦ by simp) (by simp)

/-- The factorial residuals of `2 - q = 1 · P_0 + 1 · P_1` at indices one and two are `1` and
`0`. -/
example : (2 - X : ℤ[X]).factorialResidual 1 = 1 ∧ (2 - X : ℤ[X]).factorialResidual 2 = 0 := by
  refine ⟨factorialResidual_eq_of_sum_add_eq (a := fun _ ↦ 1) (fun _ _ ↦ by simp) ?_,
    factorialResidual_eq_of_sum_add_eq (a := fun _ ↦ 1) (fun _ _ ↦ by simp) ?_⟩ <;>
    simp [sum_range_succ] <;> ring

/-- Over `ZMod 2`, changing a representative by a multiple of `P_N` leaves the first `N` digits
unchanged; no domain hypothesis is involved. -/
example (g c : (ZMod 2)[X]) : (g + factorialPoly (ZMod 2) 3 * c).factorialDigit 2 =
    g.factorialDigit 2 :=
  factorialDigit_add_factorialPoly_mul g c (by norm_num)

end TauCeti
