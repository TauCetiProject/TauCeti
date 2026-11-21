/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.NumberTheory.Divisors
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
public import TauCeti.Algebra.Polynomial.MonicOfCoeffs
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Tactic.LinearCombination

/-!
# The `L`-series of a multiplicative function on monic polynomials

Let `F` be a finite field and `λ : F[X] → R` a function that is multiplicative on monic
polynomials: `λ 1 = 1` and `λ (g * h) = λ g * λ h` for monic `g` and `h`
(`Polynomial.IsMonicMultiplicative`; the values off the monic polynomials do not matter). Its
`L`-series is the power series

`L(λ, T) = ∑_{d ≥ 0} (∑_{g monic, deg g = d} λ(g)) T ^ d` (`Polynomial.lSeries`),

whose degree-`d` coefficient sums over the `q ^ d` monic polynomials `X ^ d + ∑_{i < d} c_i X ^ i`
(`Polynomial.monicOfCoeffs`). The character sums of Weil's theorem are coefficients of such
series. This file proves the three facts that make the series useful.

* **The Euler product.** Unique factorization in `F[X]` gives
  `L(λ, T) = ∏_P (1 - λ(P) T ^ deg P)⁻¹` over the monic irreducible `P`, as an infinite product
  in Mathlib's coefficientwise topology `PowerSeries.WithPiTopology`. Only the finitely many `P`
  of degree at most `n` affect the coefficient of `T ^ n`, so the finite products converge
  coefficientwise. The Euler factor `(1 - λ(P) T ^ deg P)⁻¹` is
  `Polynomial.lSeriesFactor λ P = ∑_k λ(P) ^ k T ^ (k deg P)`, which makes sense over any
  commutative semiring `R`; over a field it is the inverse.
* **The logarithmic derivative.** `T L'(λ, T) = (∑_{n ≥ 1} S_n(λ) T ^ n) L(λ, T)`, where
  `S_n(λ) = ∑_P deg P · λ(P) ^ (n / deg P)` over the monic irreducible `P` of degree dividing `n`
  (`Polynomial.lSeriesPowerSum`). Each Euler factor `E` satisfies `T E' = D E` with
  `D = deg P · λ(P) T ^ deg P · E`, and the identity for `L` is the limit of the finite products.
* **The polynomial criterion.** If the coefficient sums vanish from degree `d₀` on, then
  `L(λ, T)` is a polynomial of degree less than `d₀`.

The definitions, the identities for a single Euler factor and the polynomial criterion hold for
every finite commutative semiring `F`. The Euler product and the logarithmic derivative of
`L(λ, T)` use unique factorization in `F[X]`, so they need a field.

## Main definitions

* `Polynomial.IsMonicMultiplicative λ`: `λ` is multiplicative on monic polynomials.
* `Polynomial.lSeries λ`: the `L`-series `L(λ, T)`.
* `Polynomial.lSeriesFactor λ P`: the Euler factor `∑_k λ(P) ^ k T ^ (k deg P)`.
* `Polynomial.lSeriesPowerSum λ n`: the power sum `S_n(λ)`.

## Main results

* `Polynomial.coeff_lSeries`, `Polynomial.constantCoeff_lSeries_of_isMonicMultiplicative`: the
  coefficients of `L(λ, T)`, and its constant coefficient `1`.
* `Polynomial.coeff_prod_lSeriesFactor`: for a finite set `S` of monic irreducibles, the
  coefficient of `T ^ n` in `∏_{P ∈ S} lSeriesFactor λ P` is the sum of `λ` over the monic
  polynomials of degree `n` whose irreducible factors lie in `S`.
* `Polynomial.hasProd_lSeriesFactor`, `Polynomial.hasProd_inv_one_sub_lSeries`,
  `Polynomial.lSeries_eq_tprod`: the Euler product.
* `Polynomial.X_mul_derivative_lSeries`, `Polynomial.X_mul_derivative_lSeries_mul_inv`: the
  logarithmic derivative.
* `Polynomial.exists_degree_lt_coe_eq_lSeries`: the polynomial criterion.
-/

public section

open Finset UniqueFactorizationMonoid

namespace PowerSeries

/-- The coefficients of `X f'` are `n` times those of `f`. -/
theorem coeff_X_mul_derivative {R : Type*} [CommSemiring R] (f : PowerSeries R) (n : ℕ) :
    coeff n (X * derivative (R := R) f) = n * coeff n f := by
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

end PowerSeries

namespace Polynomial

section CommSemiring

variable {F R : Type*} [CommSemiring F] [CommSemiring R]

/-! ### Multiplicative functions on monic polynomials -/

/-- A function on `F[X]` is *multiplicative on monic polynomials* if it sends `1` to `1` and
`g * h` to `λ g * λ h` for all monic `g` and `h`. -/
def IsMonicMultiplicative (lam : F[X] → R) : Prop :=
  lam 1 = 1 ∧ ∀ g h : F[X], g.Monic → h.Monic → lam (g * h) = lam g * lam h

theorem IsMonicMultiplicative.map_pow {lam : F[X] → R} (h : IsMonicMultiplicative lam)
    {P : F[X]} (hP : P.Monic) (k : ℕ) : lam (P ^ k) = lam P ^ k := by
  induction k with
  | zero => simpa using h.1
  | succ k ih => rw [pow_succ, h.2 _ _ (hP.pow k) hP, ih, pow_succ]

theorem IsMonicMultiplicative.map_prod_pow {lam : F[X] → R} (h : IsMonicMultiplicative lam)
    {ι : Type*} (s : Finset ι) (P : ι → F[X]) (e : ι → ℕ)
    (hP : ∀ i ∈ s, (P i).Monic) : lam (∏ i ∈ s, P i ^ e i) = ∏ i ∈ s, lam (P i) ^ e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h.1
  | insert i s hi ih =>
    rw [prod_insert hi, prod_insert hi,
      h.2 _ _ ((hP i (mem_insert_self i s)).pow _)
        (monic_prod_of_monic _ _ fun j hj ↦ (hP j (mem_insert_of_mem hj)).pow _),
      h.map_pow (hP i (mem_insert_self i s)), ih fun j hj ↦ hP j (mem_insert_of_mem hj)]

/-! ### Euler factors -/

/-- The Euler factor `∑_k λ(P) ^ k T ^ (k deg P)` of `L(λ, T)` at `P`, which is
`(1 - λ(P) T ^ deg P)⁻¹` (`Polynomial.one_sub_mul_lSeriesFactor`). -/
noncomputable def lSeriesFactor (lam : F[X] → R) (P : F[X]) : PowerSeries R :=
  PowerSeries.mk fun m ↦ if P.natDegree ∣ m then lam P ^ (m / P.natDegree) else 0

/-- The Euler factor is the inverse of `1 - λ(P) T ^ deg P`. -/
theorem one_sub_mul_lSeriesFactor {R : Type*} [CommRing R] (lam : F[X] → R) {P : F[X]}
    (hP : 0 < P.natDegree) :
    (1 - PowerSeries.C (lam P) * PowerSeries.X ^ P.natDegree) * lSeriesFactor lam P = 1 := by
  ext m
  simp only [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', lSeriesFactor, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  set d := P.natDegree
  by_cases hdm : d ∣ m
  · obtain ⟨k, rfl⟩ := hdm
    rcases k with _ | j
    · simp [hP.ne']
    · have h1 : d ≤ d * (j + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos j)
      have h2 : d * (j + 1) - d = d * j := by rw [Nat.mul_succ, Nat.add_sub_cancel]
      have h3 : d * (j + 1) ≠ 0 := Nat.mul_ne_zero hP.ne' (Nat.succ_ne_zero j)
      simp only [dvd_mul_right, h1, h2, h3, ↓reduceIte, Nat.mul_div_cancel_left _ hP]
      rw [pow_succ, mul_comm, sub_self]
  · have h : ¬(d ≤ m ∧ d ∣ m - d) := fun h ↦
      hdm (by simpa [Nat.sub_add_cancel h.1] using Nat.dvd_add h.2 (dvd_refl d))
    have hm : m ≠ 0 := fun hm ↦ hdm (hm ▸ dvd_zero d)
    have h4 : (if d ≤ m then (if d ∣ m - d then lam P ^ ((m - d) / d) else 0) else 0) = 0 := by
      split_ifs with h1 h2
      · exact (h ⟨h1, h2⟩).elim
      all_goals rfl
    simp only [hdm, hm, h4, ↓reduceIte, mul_zero, sub_zero]

/-- Over a field, the Euler factor is `(1 - λ(P) T ^ deg P)⁻¹`. -/
theorem lSeriesFactor_eq_inv {K : Type*} [Field K] (lam : F[X] → K) {P : F[X]}
    (hP : 0 < P.natDegree) :
    lSeriesFactor lam P = (1 - PowerSeries.C (lam P) * PowerSeries.X ^ P.natDegree)⁻¹ := by
  rw [PowerSeries.eq_inv_iff_mul_eq_one, mul_comm, one_sub_mul_lSeriesFactor lam hP]
  simp [hP.ne']

/-! ### The logarithmic derivative -/

/-- The logarithmic derivative of an Euler factor: `X E' = D E` with
`D = λ(P) deg P · X ^ deg P · E`, where `E = lSeriesFactor λ P`. -/
theorem X_mul_derivative_lSeriesFactor {R : Type*} [CommRing R] (lam : F[X] → R) {P : F[X]}
    (hP : 0 < P.natDegree) :
    PowerSeries.X * PowerSeries.derivative (R := R) (lSeriesFactor lam P) =
      PowerSeries.C (lam P * P.natDegree) * PowerSeries.X ^ P.natDegree * lSeriesFactor lam P *
        lSeriesFactor lam P := by
  set E := lSeriesFactor lam P
  set d := P.natDegree
  have h := one_sub_mul_lSeriesFactor lam hP
  have hd := congrArg (PowerSeries.derivative (R := R)) h
  rw [Derivation.leibniz, Derivation.map_one_eq_zero, map_sub, Derivation.map_one_eq_zero,
    zero_sub, PowerSeries.derivative_C_mul_X_pow, smul_eq_mul, smul_eq_mul] at hd
  have hX : PowerSeries.X ^ (d - 1) * PowerSeries.X = (PowerSeries.X ^ d : PowerSeries R) := by
    rw [← pow_succ, Nat.sub_add_cancel hP]
  calc PowerSeries.X * PowerSeries.derivative (R := R) E
      = ((1 - PowerSeries.C (lam P) * PowerSeries.X ^ d) * E) *
          (PowerSeries.X * PowerSeries.derivative (R := R) E) := by
        rw [h, one_mul]
    _ = PowerSeries.X * E * ((1 - PowerSeries.C (lam P) * PowerSeries.X ^ d) *
          PowerSeries.derivative (R := R) E) := by
        ring
    _ = PowerSeries.X * E * (E * (PowerSeries.C (lam P * d) * PowerSeries.X ^ (d - 1))) := by
        rw [← sub_eq_zero, ← mul_sub, sub_eq_add_neg, ← mul_neg, hd, mul_zero]
    _ = _ := by rw [← hX]; ring

/-- The logarithmic derivative of a finite Euler product:
`X (∏_{P ∈ S} E_P)' = (∑_{P ∈ S} D_P) ∏_{P ∈ S} E_P`. -/
theorem X_mul_derivative_prod_lSeriesFactor {R : Type*} [CommRing R] (lam : F[X] → R)
    (S : Finset F[X]) (hS : ∀ P ∈ S, 0 < P.natDegree) :
    PowerSeries.X * PowerSeries.derivative (R := R) (∏ P ∈ S, lSeriesFactor lam P) =
      (∑ P ∈ S, PowerSeries.C (lam P * P.natDegree) * PowerSeries.X ^ P.natDegree *
        lSeriesFactor lam P) * ∏ P ∈ S, lSeriesFactor lam P := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert Q S hQ ih =>
    have h1 := ih fun P hP ↦ hS P (mem_insert_of_mem hP)
    have h2 := X_mul_derivative_lSeriesFactor lam (hS Q (mem_insert_self Q S))
    rw [prod_insert hQ, sum_insert hQ, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    linear_combination (lSeriesFactor lam Q) * h1 + (∏ P ∈ S, lSeriesFactor lam P) * h2

/-- The coefficients of `D_P = λ(P) deg P · X ^ deg P · lSeriesFactor λ P`. -/
theorem coeff_C_mul_X_pow_mul_lSeriesFactor {R : Type*} [CommRing R] (lam : F[X] → R)
    {P : F[X]} (hP : 0 < P.natDegree) (i : ℕ) :
    PowerSeries.coeff i (PowerSeries.C (lam P * P.natDegree) * PowerSeries.X ^ P.natDegree *
        lSeriesFactor lam P) =
      if P.natDegree ∣ i ∧ i ≠ 0 then P.natDegree * lam P ^ (i / P.natDegree) else 0 := by
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', lSeriesFactor,
    PowerSeries.coeff_mk]
  set d := P.natDegree
  by_cases hdi : d ∣ i
  · obtain ⟨k, rfl⟩ := hdi
    rcases k with _ | j
    · simp [hP.ne']
    · have h1 : d ≤ d * (j + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos j)
      have h2 : d * (j + 1) - d = d * j := by rw [Nat.mul_succ, Nat.add_sub_cancel]
      have h3 : d * (j + 1) ≠ 0 := Nat.mul_ne_zero hP.ne' (Nat.succ_ne_zero j)
      simp only [dvd_mul_right, h1, h2, h3, ↓reduceIte, Nat.mul_div_cancel_left _ hP, ne_eq,
        not_false_eq_true, and_self]
      ring
  · have h : ¬(d ≤ i ∧ d ∣ i - d) := fun h ↦
      hdi (by simpa [Nat.sub_add_cancel h.1] using Nat.dvd_add h.2 (dvd_refl d))
    have h4 : (if d ≤ i then (if d ∣ i - d then lam P ^ ((i - d) / d) else 0) else 0) = 0 := by
      split_ifs with h1 h2
      · exact (h ⟨h1, h2⟩).elim
      all_goals rfl
    simp only [h4, hdi, false_and, ↓reduceIte, mul_zero]

/-! ### The `L`-series -/

variable [Fintype F] [DecidableEq F]

/-- The `L`-series `L(λ, T) = ∑_d (∑_{g monic, deg g = d} λ(g)) T ^ d` of a function on `F[X]`,
where the degree-`d` coefficient sums over the monic polynomials `monicOfCoeffs c`,
`c : Fin d → F`. -/
noncomputable def lSeries (lam : F[X] → R) : PowerSeries R :=
  PowerSeries.mk fun d ↦ ∑ c : Fin d → F, lam (monicOfCoeffs c)

/-- The degree-`d` coefficient of `L(λ, T)` is the sum of `λ` over the monic polynomials of
degree `d`. -/
theorem coeff_lSeries (lam : F[X] → R) (d : ℕ) :
    PowerSeries.coeff d (lSeries lam) = ∑ g ∈ monicsOfDegree F d, lam g := by
  rw [lSeries, PowerSeries.coeff_mk, sum_monicsOfDegree]

/-- The constant coefficient of `L(λ, T)` is `λ 1`. -/
theorem constantCoeff_lSeries (lam : F[X] → R) :
    PowerSeries.constantCoeff (lSeries lam) = lam 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, lSeries, PowerSeries.coeff_mk]
  simp

/-- The `L`-series of a function multiplicative on monic polynomials has constant
coefficient `1`. -/
theorem constantCoeff_lSeries_of_isMonicMultiplicative {lam : F[X] → R}
    (hlam : IsMonicMultiplicative lam) : PowerSeries.constantCoeff (lSeries lam) = 1 := by
  rw [constantCoeff_lSeries, hlam.1]

/-! ### The polynomial criterion -/

/-- **The polynomial criterion.** If the coefficient sums of `L(λ, T)` vanish in every degree
`d ≥ d₀`, then `L(λ, T)` is a polynomial of degree less than `d₀` (the zero polynomial if
`d₀ = 0`). -/
theorem exists_degree_lt_coe_eq_lSeries (lam : F[X] → R) {d₀ : ℕ}
    (h : ∀ d ≥ d₀, PowerSeries.coeff d (lSeries lam) = 0) :
    ∃ p : R[X], p.degree < d₀ ∧ (p : PowerSeries R) = lSeries lam := by
  refine ⟨PowerSeries.trunc d₀ (lSeries lam), PowerSeries.degree_trunc_lt _ _, ?_⟩
  ext d
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with hd
  · rfl
  · exact (h d (not_lt.1 hd)).symm

end CommSemiring

section Field

variable {F R : Type*} [Field F] [CommSemiring R]

/-! ### Products of powers of monic irreducibles -/

/-- The normalized factors of `∏_{Q ∈ S} Q ^ e Q`, for a finite set `S` of monic irreducible
polynomials, are the `Q ∈ S`, each `e Q` times. -/
theorem normalizedFactors_prod_pow [DecidableEq F] {S : Finset F[X]}
    (hS : ∀ P ∈ S, P.Monic ∧ Irreducible P) (e : F[X] → ℕ) :
    normalizedFactors (∏ Q ∈ S, Q ^ e Q) = ∑ Q ∈ S, e Q • {Q} := by
  have hprod : ∏ Q ∈ S, Q ^ e Q = (∑ Q ∈ S, e Q • {Q} : Multiset F[X]).prod := by
    rw [Multiset.prod_sum]
    exact prod_congr rfl fun Q _ ↦ by rw [Multiset.prod_nsmul, Multiset.prod_singleton]
  have hmem {Q : F[X]} (hQ : Q ∈ ∑ Q ∈ S, e Q • ({Q} : Multiset F[X])) :
      Q.Monic ∧ Irreducible Q := by
    obtain ⟨R, hR, hQR⟩ := Multiset.mem_sum.1 hQ
    rw [Multiset.mem_nsmul] at hQR
    rw [Multiset.mem_singleton.1 hQR.2]
    exact hS R hR
  rw [hprod, normalizedFactors_prod_eq _ (fun Q hQ ↦ (hmem hQ).2),
    Multiset.map_congr rfl (fun Q hQ ↦ (hmem hQ).1.normalize_eq_self), Multiset.map_id']

/-- In `∏_{Q ∈ S} Q ^ e Q`, for a finite set `S` of monic irreducible polynomials, each `P ∈ S`
occurs `e P` times as a normalized factor. -/
theorem count_normalizedFactors_prod_pow [DecidableEq F] {S : Finset F[X]}
    (hS : ∀ P ∈ S, P.Monic ∧ Irreducible P) (e : F[X] → ℕ) {P : F[X]} (hP : P ∈ S) :
    (normalizedFactors (∏ Q ∈ S, Q ^ e Q)).count P = e P := by
  rw [normalizedFactors_prod_pow hS, Multiset.count_sum', sum_eq_single P]
  · simp
  · intro Q _ hQP
    simp [hQP.symm]
  · exact fun h ↦ (h hP).elim

/-- A monic polynomial `g` whose normalized factors lie in a finite set `S` is
`∏_{P ∈ S} P ^ m P`, where `m P` is the number of times that `P` occurs as a normalized factor. -/
theorem prod_pow_count_normalizedFactors [DecidableEq F] {g : F[X]} (hg : g.Monic)
    {S : Finset F[X]} (hgS : (normalizedFactors g).toFinset ⊆ S) :
    ∏ P ∈ S, P ^ (normalizedFactors g).count P = g := by
  rw [← prod_multiset_count_of_subset _ _ hgS, prod_normalizedFactors_eq hg.ne_zero,
    hg.normalize_eq_self]

/-- A monic polynomial `g` whose normalized factors lie in a finite set `S` has degree
`∑_{P ∈ S} deg P · m P`, where `m P` is the number of times that `P` occurs as a normalized
factor. -/
theorem natDegree_eq_sum_mul_count_normalizedFactors [DecidableEq F] {g : F[X]} (hg : g.Monic)
    {S : Finset F[X]} (hgS : (normalizedFactors g).toFinset ⊆ S) :
    g.natDegree = ∑ P ∈ S, P.natDegree * (normalizedFactors g).count P := by
  have hmonic : ∀ P ∈ normalizedFactors g, P.Monic := fun P hP ↦
    normalize_normalized_factor P hP ▸
      monic_normalize (irreducible_of_normalized_factor P hP).ne_zero
  conv_lhs => rw [← hg.normalize_eq_self, ← prod_normalizedFactors_eq hg.ne_zero,
    natDegree_multiset_prod_of_monic _ hmonic, Finset.sum_multiset_map_count]
  refine (sum_subset hgS fun P _ hP ↦ ?_).trans (sum_congr rfl fun P _ ↦ ?_)
  · rw [Multiset.count_eq_zero.2 fun h ↦ hP (Multiset.mem_toFinset.2 h), zero_smul]
  · rw [smul_eq_mul, mul_comm]

/-! ### The finite Euler product -/

variable [Fintype F] [DecidableEq F]

/-- **The finite Euler product.** For a finite set `S` of monic irreducible polynomials, the
coefficient of `T ^ n` in `∏_{P ∈ S} lSeriesFactor λ P` is the sum of `λ` over the monic
polynomials of degree `n` whose irreducible factors lie in `S`. -/
theorem coeff_prod_lSeriesFactor {lam : F[X] → R} (hlam : IsMonicMultiplicative lam)
    {S : Finset F[X]} (hS : ∀ P ∈ S, P.Monic ∧ Irreducible P) (n : ℕ) :
    PowerSeries.coeff n (∏ P ∈ S, lSeriesFactor lam P) =
      ∑ g ∈ (monicsOfDegree F n).filter (fun g ↦ (normalizedFactors g).toFinset ⊆ S), lam g := by
  classical
  have hdeg : ∀ P ∈ S, 0 < P.natDegree := fun P hP ↦ (hS P hP).2.natDegree_pos
  rw [PowerSeries.coeff_prod]
  simp only [lSeriesFactor, PowerSeries.coeff_mk, prod_ite_zero, ← sum_filter]
  -- An exponent vector `l` with `deg P ∣ l P` corresponds to `∏_{P ∈ S} P ^ (l P / deg P)`.
  refine sum_nbij' (fun l ↦ ∏ P ∈ S, P ^ (l P / P.natDegree))
    (fun g ↦ Finsupp.onFinset S
      (fun P ↦ if P ∈ S then P.natDegree * (normalizedFactors g).count P else 0)
      (fun P hP ↦ by by_contra h; simp [h] at hP)) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simp only [mem_filter, mem_finsuppAntidiag] at hl
    simp only [mem_filter, mem_monicsOfDegree]
    refine ⟨⟨monic_prod_of_monic _ _ fun P hP ↦ (hS P hP).1.pow _, ?_⟩, ?_⟩
    · rw [natDegree_prod_of_monic _ _ fun P hP ↦ (hS P hP).1.pow _, ← hl.1.1]
      refine sum_congr rfl fun P hP ↦ ?_
      rw [(hS P hP).1.natDegree_pow, Nat.div_mul_cancel (hl.2 P hP)]
    · rw [normalizedFactors_prod_pow hS]
      intro Q hQ
      obtain ⟨R, hR, hQR⟩ := Multiset.mem_sum.1 (Multiset.mem_toFinset.1 hQ)
      rw [Multiset.mem_nsmul] at hQR
      rwa [Multiset.mem_singleton.1 hQR.2]
  · intro g hg
    simp only [mem_filter, mem_monicsOfDegree] at hg
    obtain ⟨⟨hgm, hgn⟩, hgS⟩ := hg
    simp only [mem_filter, mem_finsuppAntidiag, Finsupp.onFinset_apply]
    refine ⟨⟨?_, Finsupp.support_onFinset_subset⟩, fun P hP ↦ by simp [hP]⟩
    rw [← hgn, natDegree_eq_sum_mul_count_normalizedFactors hgm hgS]
    exact sum_congr rfl fun P hP ↦ by simp [hP]
  · intro l hl
    simp only [mem_filter, mem_finsuppAntidiag] at hl
    ext P
    simp only [Finsupp.onFinset_apply]
    split_ifs with hP
    · rw [count_normalizedFactors_prod_pow hS _ hP, Nat.mul_div_cancel' (hl.2 P hP)]
    · exact (Finsupp.notMem_support_iff.1 fun h ↦ hP (hl.1.2 h)).symm
  · intro g hg
    simp only [mem_filter, mem_monicsOfDegree] at hg
    obtain ⟨⟨hgm, -⟩, hgS⟩ := hg
    simp only [Finsupp.onFinset_apply]
    refine (prod_congr rfl fun P hP ↦ ?_).trans (prod_pow_count_normalizedFactors hgm hgS)
    simp only [hP, ↓reduceIte, Nat.mul_div_cancel_left _ (hdeg P hP)]
  · intro l _
    rw [hlam.map_prod_pow _ _ _ fun P hP ↦ (hS P hP).1]

/-- Once `S` contains every monic irreducible of degree at most `n`, the coefficient of `T ^ n`
in the finite Euler product over `S` is that of `L(λ, T)`. -/
theorem coeff_prod_lSeriesFactor_eq_coeff_lSeries {lam : F[X] → R}
    (hlam : IsMonicMultiplicative lam) {S : Finset F[X]} (hS : ∀ P ∈ S, P.Monic ∧ Irreducible P)
    {n : ℕ} (hn : ∀ P : F[X], P.Monic → Irreducible P → P.natDegree ≤ n → P ∈ S) :
    PowerSeries.coeff n (∏ P ∈ S, lSeriesFactor lam P) = PowerSeries.coeff n (lSeries lam) := by
  rw [coeff_prod_lSeriesFactor hlam hS, coeff_lSeries, filter_true_of_mem]
  intro g hg P hP
  have hgm := mem_monicsOfDegree.1 hg
  have hPg : P ∈ normalizedFactors g := Multiset.mem_toFinset.1 hP
  have hPirr : Irreducible P := irreducible_of_normalized_factor P hPg
  have hPmon : P.Monic := by
    rw [← normalize_normalized_factor P hPg]
    exact monic_normalize hPirr.ne_zero
  refine hn P hPmon hPirr ?_
  rw [← hgm.2]
  exact natDegree_le_of_dvd (dvd_of_mem_normalizedFactors hPg) hgm.1.ne_zero

/-! ### The Euler product -/

section EulerProduct

open PowerSeries.WithPiTopology

variable [TopologicalSpace R]

/-- **The Euler product**, with the factors `lSeriesFactor λ P` over the monic irreducible `P`,
in the coefficientwise topology. -/
theorem hasProd_lSeriesFactor {lam : F[X] → R} (hlam : IsMonicMultiplicative lam) :
    HasProd (fun P : {P : F[X] // P.Monic ∧ Irreducible P} ↦ lSeriesFactor lam P)
      (lSeries lam) := by
  classical
  simp only [HasProd, SummationFilter.unconditional_filter]
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  -- the monic irreducibles of degree at most `n`
  let s₀ : Finset {P : F[X] // P.Monic ∧ Irreducible P} :=
    ((range (n + 1)).biUnion (monicsOfDegree F)).subtype _
  refine tendsto_atTop_of_eventually_const (i₀ := s₀) fun s hs ↦ ?_
  have hS : ∀ P ∈ s.map (Function.Embedding.subtype _), P.Monic ∧ Irreducible P := by
    intro P hP
    obtain ⟨Q, -, rfl⟩ := mem_map.1 hP
    exact Q.property
  rw [show ∏ P ∈ s, lSeriesFactor lam P =
      ∏ P ∈ s.map (Function.Embedding.subtype _), lSeriesFactor lam P by rw [prod_map]; rfl]
  refine coeff_prod_lSeriesFactor_eq_coeff_lSeries hlam hS fun P hPm hPirr hPn ↦ ?_
  refine mem_map.2 ⟨⟨P, hPm, hPirr⟩, hs ?_, rfl⟩
  simp only [s₀, mem_subtype, mem_biUnion, mem_range]
  exact ⟨P.natDegree, Nat.lt_succ_of_le hPn, mem_monicsOfDegree.2 ⟨hPm, rfl⟩⟩

/-- **The Euler product** `L(λ, T) = ∏_P (1 - λ(P) T ^ deg P)⁻¹` over the monic irreducible `P`,
for values in a field. -/
theorem hasProd_inv_one_sub_lSeries {K : Type*} [Field K] [TopologicalSpace K] {lam : F[X] → K}
    (hlam : IsMonicMultiplicative lam) :
    HasProd (fun P : {P : F[X] // P.Monic ∧ Irreducible P} ↦
      (1 - PowerSeries.C (lam P) * PowerSeries.X ^ (P : F[X]).natDegree)⁻¹) (lSeries lam) := by
  convert hasProd_lSeriesFactor hlam using 2 with P
  exact (lSeriesFactor_eq_inv lam P.property.2.natDegree_pos).symm

/-- **The Euler product** as an infinite product, for values in a Hausdorff topological field. -/
theorem lSeries_eq_tprod {K : Type*} [Field K] [TopologicalSpace K] [T2Space K]
    {lam : F[X] → K} (hlam : IsMonicMultiplicative lam) :
    lSeries lam = ∏' P : {P : F[X] // P.Monic ∧ Irreducible P},
      (1 - PowerSeries.C (lam P) * PowerSeries.X ^ (P : F[X]).natDegree)⁻¹ :=
  (hasProd_inv_one_sub_lSeries hlam).tprod_eq.symm

end EulerProduct

/-! ### The logarithmic derivative of the `L`-series -/

open Classical in
/-- The power sum `S_n(λ) = ∑_P deg P · λ(P) ^ (n / deg P)` over the monic irreducible `P` whose
degree divides `n`; it is `0` for `n = 0`. -/
noncomputable def lSeriesPowerSum (lam : F[X] → R) (n : ℕ) : R :=
  ∑ P ∈ n.divisors.biUnion fun e ↦ (monicsOfDegree F e).filter Irreducible,
    (P.natDegree : R) * lam P ^ (n / P.natDegree)

/-- Once `S` contains every monic irreducible of degree at most `i`, the coefficient of `T ^ i`
in `∑_{P ∈ S} D_P` is `S_i(λ)`. -/
theorem sum_ite_eq_lSeriesPowerSum (lam : F[X] → R) {S : Finset F[X]}
    (hS : ∀ P ∈ S, P.Monic ∧ Irreducible P) {i : ℕ}
    (hi : ∀ P : F[X], P.Monic → Irreducible P → P.natDegree ≤ i → P ∈ S) :
    ∑ P ∈ S, (if P.natDegree ∣ i ∧ i ≠ 0 then (P.natDegree : R) * lam P ^ (i / P.natDegree)
      else 0) = lSeriesPowerSum lam i := by
  classical
  rw [← sum_filter, lSeriesPowerSum]
  refine sum_congr (ext fun P ↦ ?_) fun _ _ ↦ rfl
  simp only [mem_filter, mem_biUnion, Nat.mem_divisors, mem_monicsOfDegree]
  constructor
  · rintro ⟨hP, hdi, hi0⟩
    exact ⟨P.natDegree, ⟨hdi, hi0⟩, ⟨(hS P hP).1, rfl⟩, (hS P hP).2⟩
  · rintro ⟨e, ⟨hei, hi0⟩, ⟨hPm, rfl⟩, hPirr⟩
    exact ⟨hi P hPm hPirr (Nat.le_of_dvd (Nat.pos_of_ne_zero hi0) hei), hei, hi0⟩

/-- **The logarithmic derivative** of the `L`-series: `X L' = (∑_n S_n(λ) X ^ n) L`. -/
theorem X_mul_derivative_lSeries {R : Type*} [CommRing R] {lam : F[X] → R}
    (hlam : IsMonicMultiplicative lam) :
    PowerSeries.X * PowerSeries.derivative (R := R) (lSeries lam) =
      PowerSeries.mk (lSeriesPowerSum lam) * lSeries lam := by
  classical
  ext n
  -- the monic irreducibles of degree at most `n`
  let S : Finset F[X] := ((range (n + 1)).biUnion (monicsOfDegree F)).filter Irreducible
  have hS : ∀ P ∈ S, P.Monic ∧ Irreducible P := fun P hP ↦ by
    simp only [S, mem_filter, mem_biUnion, mem_monicsOfDegree] at hP
    obtain ⟨⟨e, -, hPm, -⟩, hPirr⟩ := hP
    exact ⟨hPm, hPirr⟩
  have hSn : ∀ m ≤ n, ∀ P : F[X], P.Monic → Irreducible P → P.natDegree ≤ m → P ∈ S :=
    fun m hm P hPm hPirr hPd ↦ by
      simp only [S, mem_filter, mem_biUnion, mem_range, mem_monicsOfDegree]
      exact ⟨⟨P.natDegree, by omega, hPm, rfl⟩, hPirr⟩
  have hdeg : ∀ P ∈ S, 0 < P.natDegree := fun P hP ↦ (hS P hP).2.natDegree_pos
  have hA : ∀ j ≤ n, PowerSeries.coeff j (∏ P ∈ S, lSeriesFactor lam P) =
      PowerSeries.coeff j (lSeries lam) :=
    fun j hj ↦ coeff_prod_lSeriesFactor_eq_coeff_lSeries hlam hS (hSn j hj)
  have hB : ∀ i ≤ n, PowerSeries.coeff i (∑ P ∈ S, PowerSeries.C (lam P * P.natDegree) *
      PowerSeries.X ^ P.natDegree * lSeriesFactor lam P) = lSeriesPowerSum lam i := by
    intro i hi
    rw [map_sum, sum_congr rfl fun P hP ↦ coeff_C_mul_X_pow_mul_lSeriesFactor lam (hdeg P hP) i]
    exact sum_ite_eq_lSeriesPowerSum lam hS (hSn i hi)
  rw [PowerSeries.coeff_X_mul_derivative, ← hA n le_rfl, ← PowerSeries.coeff_X_mul_derivative,
    X_mul_derivative_prod_lSeriesFactor lam S hdeg, PowerSeries.coeff_mul,
    PowerSeries.coeff_mul]
  refine sum_congr rfl fun ij hij ↦ ?_
  have := mem_antidiagonal.1 hij
  rw [hA ij.2 (by omega), hB ij.1 (by omega), PowerSeries.coeff_mk]

/-- **The logarithmic derivative** of the `L`-series over a field:
`X L' / L = ∑_n S_n(λ) X ^ n`. -/
theorem X_mul_derivative_lSeries_mul_inv {K : Type*} [Field K] {lam : F[X] → K}
    (hlam : IsMonicMultiplicative lam) :
    PowerSeries.X * PowerSeries.derivative (R := K) (lSeries lam) * (lSeries lam)⁻¹ =
      PowerSeries.mk (lSeriesPowerSum lam) := by
  rw [X_mul_derivative_lSeries hlam, mul_assoc, PowerSeries.mul_inv_cancel, mul_one]
  rw [constantCoeff_lSeries_of_isMonicMultiplicative hlam]
  exact one_ne_zero

end Field

end Polynomial
