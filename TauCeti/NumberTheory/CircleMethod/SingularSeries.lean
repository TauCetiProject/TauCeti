/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.CircleMethod.RamanujanSum
public import TauCeti.NumberTheory.EulerProduct.Squarefree
public import Mathlib.Analysis.PSeries
import TauCeti.Algebra.Order.BigOperators.OneSubOneDivSq

/-!
# The singular series of the three-primes problem

For an integer `N`, the singular series is
`𝔖(N) = ∑_{q ≥ 1} μ(q) c_q(N) / φ(q)³`,
where `c_q` is the Ramanujan sum. It is the arithmetic factor in the asymptotic formula
`∑_{n₁ + n₂ + n₃ = N} Λ(n₁) Λ(n₂) Λ(n₃) ∼ 𝔖(N) N² / 2` of the circle method: the major arcs
around the fractions `a/q` with `gcd(a, q) = 1` together contribute `μ(q) c_q(N) / φ(q)³` times the
singular integral.

The `q`-th term is multiplicative in `q`, vanishes off the squarefree integers, and is bounded by
`φ(q)⁻²` uniformly in `N`, so the series converges absolutely and has an Euler product whose factor
at `p` is `1 - (p - 1)⁻²` if `p ∣ N` and `1 + (p - 1)⁻³` otherwise.

## Main definitions

* `TauCeti.singularSeriesTerm N q`: the term `μ(q) c_q(N) / φ(q)³`.
* `TauCeti.singularSeries N`: the singular series `𝔖(N)`.
* `TauCeti.singularSeriesEulerFactor N p`: its Euler factor at `p`.

## Main results

* `TauCeti.ofReal_singularSeriesTerm`: the term in `ℂ` is `μ(q) c_q(N) / φ(q)³`.
* `TauCeti.abs_singularSeriesTerm_le`: `|μ(q) c_q(N) / φ(q)³| ≤ φ(q)⁻²`.
* `TauCeti.singularSeries_hasProd`: the Euler product of `𝔖(N)`.
* `TauCeti.singularSeries_eq_zero_of_even`: `𝔖(N) = 0` for even `N`, the factor at `2` being `0`.
* `TauCeti.one_le_singularSeries_of_odd`, `TauCeti.singularSeries_lower_bound_of_odd`:
  `1 ≤ 𝔖(N)` for odd `N`, so `𝔖` is bounded below by a positive constant on the odd integers.
* `TauCeti.exists_abs_singularSeries_le`: `𝔖(N)` is bounded uniformly in `N`.
* `TauCeti.exists_abs_sum_singularSeriesTerm_sub_le`: truncating the series at `q ≤ Q` costs
  `O(Q^{-1/2})`, uniformly in `N` and in the real cutoff `Q > 0`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., GTM 74, Springer, 2000, Chapter 26.
* R. C. Vaughan, *The Hardy–Littlewood Method*, 2nd ed., Cambridge Tracts in Mathematics 125,
  1997, Chapter 3.
-/

public section

noncomputable section

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

namespace TauCeti

/-! ### The terms of the series -/

/-- The `q`-th term `μ(q) c_q(N) / φ(q)³` of the singular series, with `c_q(N)` the Ramanujan sum,
which is real. The term at `q = 0` is `0`. -/
def singularSeriesTerm (N : ℤ) (q : ℕ) : ℝ :=
  (μ q : ℝ) / (q.totient : ℝ) ^ 3 * (ramanujanSum q N).re

/-- Unfolding `singularSeriesTerm`. -/
theorem singularSeriesTerm_def (N : ℤ) (q : ℕ) :
    singularSeriesTerm N q = (μ q : ℝ) / (q.totient : ℝ) ^ 3 * (ramanujanSum q N).re :=
  (rfl)

/-- The complex form `μ(q) c_q(N) / φ(q)³` of the term, the Ramanujan sum `c_q(N)` being real. -/
theorem ofReal_singularSeriesTerm (N : ℤ) (q : ℕ) :
    (singularSeriesTerm N q : ℂ) = (μ q : ℂ) / (q.totient : ℂ) ^ 3 * ramanujanSum q N := by
  conv_rhs => rw [← Complex.re_add_im (ramanujanSum q N), ramanujanSum_im]
  simp [singularSeriesTerm_def]

/-- The term at `q = 0` is `0`, as `μ(0) = 0`. -/
@[simp]
theorem singularSeriesTerm_zero_right (N : ℤ) : singularSeriesTerm N 0 = 0 := by
  simp [singularSeriesTerm_def]

/-- The term at `q = 1` is `μ(1) c_1(N) / φ(1)³ = 1`. -/
@[simp]
theorem singularSeriesTerm_one_right (N : ℤ) : singularSeriesTerm N 1 = 1 := by
  simp [singularSeriesTerm_def]

/-- The term vanishes off the squarefree integers, with `μ`. -/
theorem singularSeriesTerm_eq_zero_of_not_squarefree (N : ℤ) {q : ℕ} (hq : ¬Squarefree q) :
    singularSeriesTerm N q = 0 := by
  simp [singularSeriesTerm_def, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq]

/-- The term is multiplicative in `q`. -/
theorem singularSeriesTerm_mul (N : ℤ) {q r : ℕ} (h : q.Coprime r) :
    singularSeriesTerm N (q * r) = singularSeriesTerm N q * singularSeriesTerm N r := by
  simp only [singularSeriesTerm_def,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h, Nat.totient_mul h,
    ramanujanSum_mul h, Complex.mul_re, ramanujanSum_im, mul_zero, sub_zero]
  push_cast
  ring

/-- The term at a prime `p` is `-(p - 1)⁻²` if `p ∣ N` and `(p - 1)⁻³` otherwise. -/
theorem singularSeriesTerm_prime (N : ℤ) {p : ℕ} (hp : p.Prime) :
    singularSeriesTerm N p =
      if (p : ℤ) ∣ N then -1 / ((p : ℝ) - 1) ^ 2 else 1 / ((p : ℝ) - 1) ^ 3 := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hp.one_lt.ne')
  rw [singularSeriesTerm_def, ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp,
    Nat.cast_sub hp.one_le, ramanujanSum_prime hp]
  split_ifs <;>
    simp only [Int.cast_neg, Int.cast_one, Nat.cast_one, Complex.sub_re, Complex.natCast_re,
      Complex.one_re, Complex.neg_re] <;>
    field_simp

/-- The term vanishes at the prime powers `p ^ k` with `k ≥ 2`. -/
theorem singularSeriesTerm_prime_pow_eq_zero (N : ℤ) {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    singularSeriesTerm N (p ^ k) = 0 :=
  singularSeriesTerm_eq_zero_of_not_squarefree N fun h ↦ by
    have := (Nat.squarefree_pow_iff hp.ne_one (by omega)).1 h
    omega

/-- The term bound `|μ(q) c_q(N) / φ(q)³| ≤ φ(q)⁻²`, uniform in `N`, from `|c_q(N)| ≤ φ(q)`. -/
theorem abs_singularSeriesTerm_le (N : ℤ) (q : ℕ) :
    |singularSeriesTerm N q| ≤ 1 / (q.totient : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos q.totient with h | h
  · rw [Nat.totient_eq_zero] at h
    simp [h]
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast h
  have hμ : |(μ q : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hc : |(ramanujanSum q N).re| ≤ q.totient :=
    (Complex.abs_re_le_norm _).trans (norm_ramanujanSum_le_totient q N)
  rw [singularSeriesTerm_def, abs_mul, abs_div, abs_pow, abs_of_pos hφ]
  calc |(μ q : ℝ)| / (q.totient : ℝ) ^ 3 * |(ramanujanSum q N).re|
      ≤ 1 / (q.totient : ℝ) ^ 3 * q.totient := by gcongr
    _ = 1 / (q.totient : ℝ) ^ 2 := by field_simp

/-! ### Summability -/

/-- The majorant `μ(q)² √q / φ(q)²`, nonnegative, multiplicative and supported on the squarefree
integers. It dominates the terms of the series, and the factor `√q` pays for its tail. -/
private def weight (q : ℕ) : ℝ :=
  (μ q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * √q

private theorem weight_nonneg (q : ℕ) : 0 ≤ weight q := by
  unfold weight
  positivity

/-- At a prime, `√p / (p - 1)² ≤ 4 p^{-3/2}`, since `p - 1 ≥ p / 2`. -/
private theorem weight_prime_le {p : ℕ} (hp : p.Prime) : weight p ≤ 4 * (p : ℝ) ^ (-3 / 2 : ℝ) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hw : weight p = √p / ((p : ℝ) - 1) ^ 2 := by
    rw [weight, ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp,
      Nat.cast_sub hp.one_le]
    push_cast
    ring
  have hrpow : (p : ℝ) ^ (-3 / 2 : ℝ) = √p / (p : ℝ) ^ 2 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_sub hp0]
    norm_num
  rw [hw, hrpow]
  calc √p / ((p : ℝ) - 1) ^ 2 ≤ √p / ((p : ℝ) / 2) ^ 2 := by gcongr; linarith
    _ = 4 * (√p / (p : ℝ) ^ 2) := by ring

private theorem summable_weight : Summable weight := by
  refine summable_of_summable_primes_of_squarefree weight_nonneg (by simp [weight])
    (fun {m n} h ↦ ?_) (fun {p k} hp hk ↦ ?_) ?_
  · simp only [weight, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h,
      Nat.totient_mul h, Nat.cast_mul, Int.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m)]
    ring
  · simp [weight, ArithmeticFunction.moebius_apply_prime_pow hp (by omega : k ≠ 0),
      show k ≠ 1 by omega]
  exact (((Real.summable_nat_rpow.2 (by norm_num : (-3 / 2 : ℝ) < -1)).mul_left 4).comp_injective
    Subtype.val_injective).of_nonneg_of_le (fun p ↦ weight_nonneg p) fun p ↦ weight_prime_le p.prop

private theorem abs_singularSeriesTerm_le_moebius_sq_div (N : ℤ) (q : ℕ) :
    |singularSeriesTerm N q| ≤ (μ q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 := by
  by_cases hq : Squarefree q
  · have hμ : (μ q : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hq
    rw [hμ]
    exact abs_singularSeriesTerm_le N q
  · simp [singularSeriesTerm_eq_zero_of_not_squarefree N hq,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq]

private theorem abs_singularSeriesTerm_le_weight_div {N : ℤ} {q : ℕ} {x : ℝ} (hx : 0 < x)
    (hq : x ≤ q) : |singularSeriesTerm N q| ≤ weight q / √x := by
  rw [weight, mul_div_assoc]
  refine (abs_singularSeriesTerm_le_moebius_sq_div N q).trans
    (le_mul_of_one_le_right (by positivity) ?_)
  rw [one_le_div (Real.sqrt_pos.2 hx)]
  exact Real.sqrt_le_sqrt hq

private theorem abs_singularSeriesTerm_le_weight (N : ℤ) (q : ℕ) :
    |singularSeriesTerm N q| ≤ weight q := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [weight]
  simpa using abs_singularSeriesTerm_le_weight_div (N := N) one_pos (by exact_mod_cast hq)

/-- The series `∑_q μ(q) c_q(N) / φ(q)³` converges absolutely. -/
theorem summable_abs_singularSeriesTerm (N : ℤ) :
    Summable fun q ↦ |singularSeriesTerm N q| :=
  summable_weight.of_nonneg_of_le (fun _ ↦ abs_nonneg _) (abs_singularSeriesTerm_le_weight N)

/-- The series `∑_q μ(q) c_q(N) / φ(q)³` converges absolutely, stated with the norm. -/
theorem summable_norm_singularSeriesTerm (N : ℤ) :
    Summable fun q ↦ ‖singularSeriesTerm N q‖ := by
  simpa only [Real.norm_eq_abs] using summable_abs_singularSeriesTerm N

/-- The series `∑_q μ(q) c_q(N) / φ(q)³` converges. -/
theorem summable_singularSeriesTerm (N : ℤ) : Summable (singularSeriesTerm N) :=
  (summable_abs_singularSeriesTerm N).of_abs

/-! ### The singular series -/

/-- The singular series `𝔖(N) = ∑_{q ≥ 1} μ(q) c_q(N) / φ(q)³` of the three-primes problem. -/
def singularSeries (N : ℤ) : ℝ :=
  ∑' q, singularSeriesTerm N q

/-- Unfolding `singularSeries`. -/
theorem singularSeries_def (N : ℤ) : singularSeries N = ∑' q, singularSeriesTerm N q :=
  (rfl)

/-- The series `∑_q μ(q) c_q(N) / φ(q)³` sums to `𝔖(N)`. -/
theorem hasSum_singularSeries (N : ℤ) : HasSum (singularSeriesTerm N) (singularSeries N) :=
  (summable_singularSeriesTerm N).hasSum

/-! ### The Euler product -/

/-- The Euler factor of `𝔖(N)` at `p`: `1 - (p - 1)⁻²` if `p ∣ N` and `1 + (p - 1)⁻³` otherwise. -/
def singularSeriesEulerFactor (N : ℤ) (p : ℕ) : ℝ :=
  if (p : ℤ) ∣ N then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 + 1 / ((p : ℝ) - 1) ^ 3

/-- Unfolding `singularSeriesEulerFactor`. -/
theorem singularSeriesEulerFactor_def (N : ℤ) (p : ℕ) :
    singularSeriesEulerFactor N p =
      if (p : ℤ) ∣ N then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 + 1 / ((p : ℝ) - 1) ^ 3 :=
  (rfl)

/-- The Euler factor at `2` is `1 + (2 - 1)⁻³ = 2` for odd `N`. -/
theorem singularSeriesEulerFactor_two_of_odd {N : ℤ} (hN : Odd N) :
    singularSeriesEulerFactor N 2 = 2 := by
  have h2N : ¬((2 : ℕ) : ℤ) ∣ N := fun h ↦
    Int.not_even_iff_odd.2 hN (even_iff_two_dvd.2 (by exact_mod_cast h))
  simp only [singularSeriesEulerFactor_def, h2N, ↓reduceIte]
  norm_num

/-- Every Euler factor is at least `1 - (p - 1)⁻²`, its value when `p ∣ N`. -/
theorem one_sub_one_div_sq_le_singularSeriesEulerFactor (N : ℤ) (p : ℕ) :
    1 - 1 / ((p : ℝ) - 1) ^ 2 ≤ singularSeriesEulerFactor N p := by
  rw [singularSeriesEulerFactor_def]
  split_ifs
  · exact le_rfl
  rcases p with _ | p
  · norm_num
  · simp only [Nat.cast_add_one, add_sub_cancel_right]
    have h1 : 0 ≤ 1 / (p : ℝ) ^ 2 := by positivity
    have h2 : 0 ≤ 1 / (p : ℝ) ^ 3 := by positivity
    linarith

/-- The Euler product
`𝔖(N) = ∏_{p ∣ N} (1 - (p - 1)⁻²) ∏_{p ∤ N} (1 + (p - 1)⁻³)`. -/
theorem singularSeries_hasProd (N : ℤ) :
    HasProd (fun p : Nat.Primes ↦ singularSeriesEulerFactor N p) (singularSeries N) := by
  have h := EulerProduct.eulerProduct_hasProd (singularSeriesTerm_one_right N)
    (fun h ↦ singularSeriesTerm_mul N h)
    (summable_norm_singularSeriesTerm N) (singularSeriesTerm_zero_right N)
  rw [singularSeries_def]
  convert h using 1
  funext p
  rw [tsum_pow_eq_one_add_of_squarefree (singularSeriesTerm_one_right N)
    fun hk ↦ singularSeriesTerm_prime_pow_eq_zero N p.prop hk, singularSeriesTerm_prime N p.prop,
    singularSeriesEulerFactor_def]
  split_ifs <;> ring

/-- `𝔖(N) = 0` for even `N`: the Euler factor at `2` is `1 - (2 - 1)⁻² = 0`. -/
theorem singularSeries_eq_zero_of_even {N : ℤ} (hN : Even N) : singularSeries N = 0 :=
  (singularSeries_hasProd N).unique <| hasProd_zero_of_exists_eq_zero
    ⟨⟨2, Nat.prime_two⟩, by simp [singularSeriesEulerFactor_def, even_iff_two_dvd.1 hN]; norm_num⟩

/-- `𝔖(0) = 0`. -/
@[simp]
theorem singularSeries_zero : singularSeries 0 = 0 :=
  singularSeries_eq_zero_of_even ⟨0, rfl⟩

/-- `1 ≤ 𝔖(N)` for odd `N`: the Euler factor at `2` is `2`, and the factors at odd primes are at
least `1 - (p - 1)⁻²`, whose finite products over `p ≥ 3` are at least `1/2`. -/
theorem one_le_singularSeries_of_odd {N : ℤ} (hN : Odd N) : 1 ≤ singularSeries N := by
  set two : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hF2 : singularSeriesEulerFactor N (two : ℕ) = 2 := singularSeriesEulerFactor_two_of_odd hN
  have h3 : ∀ p : Nat.Primes, p ≠ two → 3 ≤ (p : ℕ) := fun p hp ↦ by
    have : (p : ℕ) ≠ 2 := fun h ↦ hp (Subtype.ext h)
    have := p.prop.two_le
    omega
  -- At an odd prime `p`, `1 - (p - 1)⁻²` is nonnegative and at most the Euler factor at `p`.
  have hF : ∀ p : Nat.Primes, p ≠ two →
      0 ≤ 1 - 1 / (((p : ℕ) - 1 : ℕ) : ℝ) ^ 2 ∧
        1 - 1 / (((p : ℕ) - 1 : ℕ) : ℝ) ^ 2 ≤ singularSeriesEulerFactor N p := by
    intro p hp
    refine ⟨(one_sub_one_div_sq_mem_Icc (x := (((p : ℕ) - 1 : ℕ) : ℝ))
      (by exact_mod_cast (by have := h3 p hp; omega : 1 ≤ (p : ℕ) - 1))).1, ?_⟩
    rw [Nat.cast_pred p.prop.pos]
    exact one_sub_one_div_sq_le_singularSeriesEulerFactor N p
  refine ge_of_tendsto (singularSeries_hasProd N) (eventually_atTop.2 ⟨{two}, fun s hs ↦ ?_⟩)
  rw [← mul_prod_erase s _ (hs (mem_singleton_self _)), hF2]
  have := half_le_prod_one_sub_one_div_sq (K := ℝ) (s := s.erase two)
    (f := fun p : Nat.Primes ↦ (p : ℕ) - 1)
    (fun p _ q _ h ↦ Nat.Primes.coe_nat_injective <| by
      have := p.prop.two_le
      have := q.prop.two_le
      simp only at h
      omega)
    fun p hp ↦ by have := h3 p (ne_of_mem_erase hp); omega
  have := this.trans (prod_le_prod₀ (fun p hp ↦ (hF p (ne_of_mem_erase hp)).1)
    fun p hp ↦ (hF p (ne_of_mem_erase hp)).2)
  linarith

/-- `𝔖` is bounded below by a positive constant on the odd integers. -/
theorem singularSeries_lower_bound_of_odd :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℤ, Odd N → c ≤ singularSeries N :=
  ⟨1, one_pos, fun _ ↦ one_le_singularSeries_of_odd⟩

/-! ### Uniform bounds -/

/-- `𝔖(N)` is bounded uniformly in `N`. -/
theorem exists_abs_singularSeries_le : ∃ C : ℝ, ∀ N : ℤ, |singularSeries N| ≤ C := by
  refine ⟨∑' q, weight q, fun N ↦ ?_⟩
  rw [singularSeries_def, ← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm (summable_norm_singularSeriesTerm N)).trans
    ((summable_norm_singularSeriesTerm N).tsum_le_tsum (abs_singularSeriesTerm_le_weight N)
      summable_weight)

/-- Truncating the singular series at `q ≤ Q` costs `O(Q^{-1/2})`, uniformly in `N` and in the real
cutoff `Q > 0`. -/
theorem exists_abs_sum_singularSeriesTerm_sub_le :
    ∃ C : ℝ, ∀ (N : ℤ) (Q : ℝ), 0 < Q →
      |∑ q ∈ Icc 1 ⌊Q⌋₊, singularSeriesTerm N q - singularSeries N| ≤ C / √Q := by
  refine ⟨∑' q, weight q, fun N Q hQ ↦ ?_⟩
  -- Every `q` beyond the cutoff `n = ⌊Q⌋₊` satisfies `Q ≤ q`.
  have hQn : Q < ⌊Q⌋₊ + 1 := Nat.lt_floor_add_one Q
  generalize ⌊Q⌋₊ = n at hQn ⊢
  -- The difference is the tail `∑_{q > n}`, whose terms are at most `weight q / √Q`.
  -- The sum over `Icc 1 n` is the sum over `range (n + 1)`, the term at `0` being `0`.
  have hrange : ∑ q ∈ Icc 1 n, singularSeriesTerm N q =
      ∑ q ∈ range (n + 1), singularSeriesTerm N q :=
    sum_subset (fun q hq ↦ by simp only [mem_Icc, mem_range] at hq ⊢; omega) fun q hq hq' ↦ by
      obtain rfl : q = 0 := by simp only [mem_Icc, mem_range] at hq hq'; omega
      exact singularSeriesTerm_zero_right N
  have htail : ∑ q ∈ Icc 1 n, singularSeriesTerm N q - singularSeries N =
      -∑' k, singularSeriesTerm N (k + (n + 1)) := by
    rw [hrange, singularSeries_def,
      ← (summable_singularSeriesTerm N).sum_add_tsum_nat_add (n + 1)]
    ring
  have hnorm : Summable fun k ↦ ‖singularSeriesTerm N (k + (n + 1))‖ :=
    (summable_nat_add_iff (n + 1)).2 (summable_norm_singularSeriesTerm N)
  have hw : Summable fun k ↦ weight (k + (n + 1)) :=
    (summable_nat_add_iff (n + 1)).2 summable_weight
  have hprefix : 0 ≤ ∑ q ∈ range (n + 1), weight q := sum_nonneg fun q _ ↦ weight_nonneg q
  rw [htail, abs_neg, ← Real.norm_eq_abs]
  calc ‖∑' k, singularSeriesTerm N (k + (n + 1))‖
      ≤ ∑' k, ‖singularSeriesTerm N (k + (n + 1))‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k, weight (k + (n + 1)) / √Q :=
        hnorm.tsum_le_tsum (fun k ↦ abs_singularSeriesTerm_le_weight_div hQ
          (by push_cast; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])) (hw.div_const _)
    _ = (∑' k, weight (k + (n + 1))) / √Q := tsum_div_const
    _ ≤ (∑' q, weight q) / √Q := by
        refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        linarith [summable_weight.sum_add_tsum_nat_add (n + 1)]

/-! ### Examples -/

example (N : ℤ) : ∑ q ∈ Icc 1 1, singularSeriesTerm N q = 1 := by simp

example : singularSeriesTerm 1 2 = 1 := by
  rw [singularSeriesTerm_prime 1 Nat.prime_two]
  norm_num

example : singularSeriesTerm 6 3 = -1 / 4 := by
  rw [singularSeriesTerm_prime 6 Nat.prime_three]
  norm_num

end TauCeti
