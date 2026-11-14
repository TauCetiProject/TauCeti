/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The square of the Möbius function and divisor-count Möbius inversion

In the Dirichlet ring of arithmetic functions, `ζ * ζ = σ 0` is the divisor-count function
`n ↦ #n.divisors`, and its Dirichlet inverse is the convolution square `μ * μ` of the Möbius
function: `(μ * μ) * σ 0 = 1`. At a prime power `p ^ k`, `(μ * μ) (p ^ k)` takes the values
`1`, `-2`, `1`, and `0` for `k = 0`, `1`, `2`, and `k ≥ 3` respectively.

Consequently, a divisor-count convolution `g(n) = ∑_{d ∣ n} #(n / d).divisors • f(d)` in any
additive commutative group (or ring) inverts to `f(n) = ∑_{d ∣ n} (μ * μ)(n / d) • g(d)`, both
globally on positive integers and on any divisor-closed set `s ⊆ ℕ` — in particular on the
divisors of a single nonzero integer `N`.

## Main results

* `ArithmeticFunction.zeta_mul_zeta`, `ArithmeticFunction.coe_zeta_mul_coe_zeta`: `ζ * ζ = σ 0`.
* `ArithmeticFunction.moebius_mul_moebius_mul_coe_sigma_zero`,
  `ArithmeticFunction.coe_sigma_zero_mul_moebius_mul_moebius`,
  `ArithmeticFunction.coe_moebius_mul_coe_moebius_mul_coe_sigma_zero`,
  `ArithmeticFunction.coe_sigma_zero_mul_coe_moebius_mul_coe_moebius`: `μ * μ` and `σ 0` are
  Dirichlet inverses.
* `ArithmeticFunction.moebius_mul_moebius_apply_prime_pow`,
  `ArithmeticFunction.moebius_mul_moebius_apply_prime`: values of `μ * μ` at prime powers and
  primes.
* `ArithmeticFunction.sum_card_divisors_smul_eq_iff_sum_moebius_mul_moebius_smul_eq`,
  `ArithmeticFunction.sum_card_divisors_smul_eq_iff_sum_moebius_mul_moebius_smul_eq_on`,
  `ArithmeticFunction.sum_card_divisors_mul_eq_iff_sum_moebius_mul_moebius_mul_eq`,
  `ArithmeticFunction.sum_card_divisors_mul_eq_iff_sum_moebius_mul_moebius_mul_eq_on`: Möbius
  inversion for convolution against `#(n / d).divisors`.
* `ArithmeticFunction.eq_sum_divisors_moebius_mul_moebius_smul_of_dvd`,
  `ArithmeticFunction.eq_sum_divisors_moebius_mul_moebius_mul_of_dvd`: specialization to the
  divisors of a fixed nonzero integer `N`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.8.3.
-/

public section

open Finset Nat

namespace ArithmeticFunction

open scoped Moebius zeta ArithmeticFunction.sigma

variable {G R : Type*}

/-! ### `ζ * ζ = σ 0` and its Dirichlet inverse `μ * μ` -/

/-- The Dirichlet square of `ζ` is the divisor-count function `σ 0`. -/
theorem zeta_mul_zeta : (ζ * ζ : ArithmeticFunction ℕ) = σ 0 :=
  pow_zero_eq_zeta ▸ zeta_mul_pow_eq_sigma

/-- The Dirichlet square of `ζ` in `ArithmeticFunction R` is `σ 0`. -/
theorem coe_zeta_mul_coe_zeta [Semiring R] : (ζ * ζ : ArithmeticFunction R) = σ 0 := by
  rw [← natCoe_mul, zeta_mul_zeta]

/-- `μ * μ` is the left Dirichlet inverse of `σ 0` over `ℤ`. -/
@[simp]
theorem moebius_mul_moebius_mul_coe_sigma_zero :
    (μ * μ * σ 0 : ArithmeticFunction ℤ) = 1 :=
  calc (μ * μ * σ 0 : ArithmeticFunction ℤ)
      = μ * (μ * ζ) * ζ := by rw [← coe_zeta_mul_coe_zeta, ← mul_assoc (μ * μ), mul_assoc μ μ]
    _ = 1 := by rw [moebius_mul_coe_zeta, mul_one, moebius_mul_coe_zeta]

/-- `μ * μ` is the right Dirichlet inverse of `σ 0` over `ℤ`. -/
@[simp]
theorem coe_sigma_zero_mul_moebius_mul_moebius :
    ((σ 0 : ArithmeticFunction ℤ) * (μ * μ) : ArithmeticFunction ℤ) = 1 := by
  rw [mul_comm, moebius_mul_moebius_mul_coe_sigma_zero]

/-- `μ * μ` is the left Dirichlet inverse of `σ 0` over any ring. -/
@[simp]
theorem coe_moebius_mul_coe_moebius_mul_coe_sigma_zero [Ring R] :
    (μ * μ * σ 0 : ArithmeticFunction R) = 1 := by
  rw [← coe_coe, ← intCoe_mul, ← intCoe_mul, moebius_mul_moebius_mul_coe_sigma_zero, intCoe_one]

/-- `μ * μ` is the right Dirichlet inverse of `σ 0` over any ring. -/
@[simp]
theorem coe_sigma_zero_mul_coe_moebius_mul_coe_moebius [Ring R] :
    ((σ 0 : ArithmeticFunction R) * (μ * μ) : ArithmeticFunction R) = 1 := by
  rw [← coe_coe, ← intCoe_mul, ← intCoe_mul, coe_sigma_zero_mul_moebius_mul_moebius, intCoe_one]

/-! ### Prime-power values of `μ * μ` -/

/-- At a prime power `p ^ k`, `(μ * μ) (p ^ k)` is `1` at `k = 0`, `-2` at `k = 1`, `1` at `k = 2`,
and `0` for `k ≥ 3`. -/
theorem moebius_mul_moebius_apply_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (μ * μ) (p ^ k) =
      if k = 0 then 1 else if k = 1 then -2 else if k = 2 then 1 else 0 := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b ↦ μ a * μ b),
    Nat.sum_divisors_prime_pow hp]
  have hterm : ∑ j ∈ range (k + 1), μ (p ^ j) * μ (p ^ k / p ^ j) =
      ∑ j ∈ range (k + 1), μ (p ^ j) * μ (p ^ (k - j)) :=
    Finset.sum_congr rfl fun j hj ↦ by
      rw [Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hp.pos]
  rw [hterm]
  rcases k with _ | _ | _ | k
  · simp
  · simp [Finset.sum_range_succ, moebius_apply_prime hp]
  · simp [Finset.sum_range_succ, moebius_apply_prime hp,
      moebius_apply_prime_pow hp (by decide : 2 ≠ 0)]
  · have hk0 : k + 3 ≠ 0 := by omega
    have hk1 : k + 3 ≠ 1 := by omega
    have hk2 : k + 3 ≠ 2 := by omega
    simp only [hk0, hk1, hk2, ↓reduceIte]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    have hjlt : j < k + 4 := Finset.mem_range.mp hj
    rcases le_or_gt 2 j with hj2 | hj2
    · have hj0 : j ≠ 0 := by omega
      have hj1 : j ≠ 1 := by omega
      simp [moebius_apply_prime_pow hp hj0, hj1]
    · have hsub0 : k + 3 - j ≠ 0 := by omega
      have hsub1 : k + 3 - j ≠ 1 := by omega
      simp [moebius_apply_prime_pow hp hsub0, hsub1]

/-- At a prime `p`, `(μ * μ) p = -2`. -/
theorem moebius_mul_moebius_apply_prime {p : ℕ} (hp : p.Prime) : (μ * μ) p = -2 := by
  simpa using moebius_mul_moebius_apply_prime_pow hp 1

/-! ### Möbius inversion for divisor-count convolutions -/

/-- **Divisor-count Möbius inversion** for functions to an `AddCommGroup`. -/
theorem sum_card_divisors_smul_eq_iff_sum_moebius_mul_moebius_smul_eq
    [AddCommGroup G] {f g : ℕ → G} :
    (∀ n > 0, ∑ d ∈ n.divisors, #(n / d).divisors • f d = g n) ↔
      ∀ n > 0, ∑ d ∈ n.divisors, (μ * μ) (n / d) • g d = f n := by
  let f' : ArithmeticFunction G := ⟨fun x ↦ if x = 0 then 0 else f x, rfl⟩
  let g' : ArithmeticFunction G := ⟨fun x ↦ if x = 0 then 0 else g x, rfl⟩
  have hσ (n : ℕ) :
      ((σ 0 : ArithmeticFunction ℤ) • f') n =
        ∑ d ∈ n.divisors, #(n / d).divisors • f d := by
    rw [ArithmeticFunction.smul_apply,
      Nat.sum_divisorsAntidiagonal' (f := fun x y ↦ ((σ 0 : ArithmeticFunction ℤ) x) • f' y)]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    simp [f', sigma_zero_apply, hd0]
  have hμ (n : ℕ) :
      ((μ * μ) • g') n = ∑ d ∈ n.divisors, (μ * μ) (n / d) • g d := by
    rw [ArithmeticFunction.smul_apply,
      Nat.sum_divisorsAntidiagonal' (f := fun x y ↦ (μ * μ) x • g' y)]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    simp [g', hd0]
  trans (σ 0 : ArithmeticFunction ℤ) • f' = g'
  · rw [ArithmeticFunction.ext_iff]
    refine forall_congr' fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hpos : 0 < n := Nat.pos_of_ne_zero hn
      simp [hpos, hσ n, g', hn]
  trans (μ * μ) • g' = f'
  · refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [← h, ← mul_smul, moebius_mul_moebius_mul_coe_sigma_zero, one_smul]
    · rw [← h, ← mul_smul, coe_sigma_zero_mul_moebius_mul_moebius, one_smul]
  · rw [ArithmeticFunction.ext_iff]
    refine forall_congr' fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hpos : 0 < n := Nat.pos_of_ne_zero hn
      simp [hpos, hμ n, f', hn]

/-- **Divisor-count Möbius inversion on a divisor-closed set**, for functions to an
`AddCommGroup`. -/
theorem sum_card_divisors_smul_eq_iff_sum_moebius_mul_moebius_smul_eq_on
    [AddCommGroup G] {f g : ℕ → G} (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) :
    (∀ n > 0, n ∈ s → ∑ d ∈ n.divisors, #(n / d).divisors • f d = g n) ↔
      ∀ n > 0, n ∈ s → ∑ d ∈ n.divisors, (μ * μ) (n / d) • g d = f n := by
  refine ⟨fun h n hn hns ↦ ?_, fun h n hn hns ↦ ?_⟩
  · have hinv := (sum_card_divisors_smul_eq_iff_sum_moebius_mul_moebius_smul_eq
      (f := f) (g := fun m ↦ ∑ d ∈ m.divisors, #(m / d).divisors • f d)).mp (fun _ _ ↦ rfl) n hn
    rw [← hinv]
    exact Finset.sum_congr rfl fun d hd ↦ by
      rw [h d (Nat.pos_of_mem_divisors hd) (hs d n (Nat.dvd_of_mem_divisors hd) hns)]
  · have hinv := (sum_card_divisors_smul_eq_iff_sum_moebius_mul_moebius_smul_eq
      (f := fun m ↦ ∑ d ∈ m.divisors, (μ * μ) (m / d) • g d) (g := g)).mpr (fun _ _ ↦ rfl) n hn
    rw [← hinv]
    exact Finset.sum_congr rfl fun d hd ↦ by
      rw [h d (Nat.pos_of_mem_divisors hd) (hs d n (Nat.dvd_of_mem_divisors hd) hns)]

/-- **Divisor-count Möbius inversion** for functions to a ring. -/
theorem sum_card_divisors_mul_eq_iff_sum_moebius_mul_moebius_mul_eq
    [NonAssocRing R] {f g : ℕ → R} :
    (∀ n > 0, ∑ d ∈ n.divisors, (#(n / d).divisors : R) * f d = g n) ↔
      ∀ n > 0, ∑ d ∈ n.divisors, ((μ * μ) (n / d) : R) * g d = f n := by
  simpa only [nsmul_eq_mul, zsmul_eq_mul] using
    sum_card_divisors_smul_eq_iff_sum_moebius_mul_moebius_smul_eq (f := f) (g := g)

/-- **Divisor-count Möbius inversion on a divisor-closed set**, for functions to a ring. -/
theorem sum_card_divisors_mul_eq_iff_sum_moebius_mul_moebius_mul_eq_on
    [NonAssocRing R] {f g : ℕ → R} (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) :
    (∀ n > 0, n ∈ s → ∑ d ∈ n.divisors, (#(n / d).divisors : R) * f d = g n) ↔
      ∀ n > 0, n ∈ s → ∑ d ∈ n.divisors, ((μ * μ) (n / d) : R) * g d = f n := by
  simpa only [nsmul_eq_mul, zsmul_eq_mul] using
    sum_card_divisors_smul_eq_iff_sum_moebius_mul_moebius_smul_eq_on (f := f) (g := g) s hs

/-- **Divisor-count Möbius inversion at a fixed nonzero level**, for functions to an
`AddCommGroup`: if `∑_{d ∣ m} #(m / d).divisors • f d = g m` holds for every divisor `m ∣ N`,
then `f N = ∑_{d ∣ N} (μ * μ) (N / d) • g d`. -/
theorem eq_sum_divisors_moebius_mul_moebius_smul_of_dvd [AddCommGroup G] {N : ℕ} (hN : N ≠ 0)
    {f g : ℕ → G} (h : ∀ m, m ∣ N → ∑ d ∈ m.divisors, #(m / d).divisors • f d = g m) :
    f N = ∑ d ∈ N.divisors, (μ * μ) (N / d) • g d :=
  ((sum_card_divisors_smul_eq_iff_sum_moebius_mul_moebius_smul_eq_on {m | m ∣ N}
    fun _ _ hmn hmN ↦ hmn.trans hmN).mp (fun m _ hmN ↦ h m hmN) N (Nat.pos_of_ne_zero hN)
      dvd_rfl).symm

/-- **Divisor-count Möbius inversion at a fixed nonzero level**, for functions to a ring: if
`∑_{d ∣ m} #(m / d).divisors * f d = g m` holds for every divisor `m ∣ N`, then
`f N = ∑_{d ∣ N} (μ * μ) (N / d) * g d`. -/
theorem eq_sum_divisors_moebius_mul_moebius_mul_of_dvd [NonAssocRing R] {N : ℕ} (hN : N ≠ 0)
    {f g : ℕ → R} (h : ∀ m, m ∣ N → ∑ d ∈ m.divisors, (#(m / d).divisors : R) * f d = g m) :
    f N = ∑ d ∈ N.divisors, ((μ * μ) (N / d) : R) * g d :=
  ((sum_card_divisors_mul_eq_iff_sum_moebius_mul_moebius_mul_eq_on {m | m ∣ N}
    fun _ _ hmn hmN ↦ hmn.trans hmN).mp (fun m _ hmN ↦ h m hmN) N (Nat.pos_of_ne_zero hN)
      dvd_rfl).symm

end ArithmeticFunction
