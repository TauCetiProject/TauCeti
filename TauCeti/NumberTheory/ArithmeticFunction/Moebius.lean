/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

import Mathlib.Algebra.Module.BigOperators
import TauCeti.NumberTheory.Divisors

/-!
# Convolution square of the Möbius function and divisor-count inversion

In the Dirichlet ring of arithmetic functions, the divisor-counting function `σ 0`
(`n ↦ #n.divisors`) is the convolution square `ζ * ζ` of the constant-`1` function `ζ`. Since
`μ * ζ = 1`, the convolution inverse of `σ 0` over `ℤ` (and over any ring) is the convolution
square `μ * μ` of the Möbius function.

This file records the convolution identities relating `ζ * ζ`, `σ 0`, and `μ * μ`, evaluates `μ * μ`
at prime powers (`1, -2, 1, 0, 0, …` on `1, p, p², p³, …`), and derives Möbius-square inversion for
sums weighted by `#(n / d).divisors`: if `g(n) = ∑_{d ∣ n} #(n / d).divisors • f(d)`, then
`f(n) = ∑_{d ∣ n} (μ * μ)(n / d) • g(d)`, globally, on divisor-closed sets, at a fixed level `N`,
and along multiples of a fixed divisor `c ∣ N`.

## Main results

* `ArithmeticFunction.zeta_mul_zeta`: `ζ * ζ = σ 0` in `ArithmeticFunction ℕ`.
* `ArithmeticFunction.moebius_mul_moebius_mul_coe_sigma_zero`,
  `ArithmeticFunction.coe_sigma_zero_mul_moebius_mul_moebius`, and their `[Ring R]` forms: `μ * μ`
  and `σ 0` are mutually inverse under Dirichlet convolution.
* `ArithmeticFunction.isMultiplicative_moebius_mul_moebius`: `μ * μ` is multiplicative.
* `ArithmeticFunction.moebius_mul_moebius_apply_prime_pow` (with specializations at `1`, `p`, `p²`,
  and `p ^ k` for `3 ≤ k`): prime-power values of `μ * μ`.
* `ArithmeticFunction.sum_divisors_smul_eq_of_mul_eq_one_on`: general Dirichlet-inverse inversion on
  a divisor-closed set for `α * β = 1`.
* `ArithmeticFunction.sum_card_divisors_smul_eq_iff_sum_moebius_mul_moebius_smul_eq` and its `_on`
  and ring-multiplication variants: equivalence between divisor-count weighted sums and `(μ * μ)`
  inversion sums.
* `ArithmeticFunction.eq_sum_divisors_moebius_mul_moebius_smul` and
  `ArithmeticFunction.eq_sum_divisors_filter_dvd_moebius_mul_moebius_smul` (plus `_mul` variants):
  single-level inversion at `N > 0`, unrestricted or restricted to multiples of `c ∣ N`.
-/

public section

open Finset Nat
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius ArithmeticFunction.sigma

namespace ArithmeticFunction

variable {R : Type*}

/-! ### Dirichlet convolution identities and prime-power values of `μ * μ` -/

/-- **The Dirichlet square of `ζ` is the divisor-counting function `σ 0`.** -/
theorem zeta_mul_zeta : (ζ * ζ : ArithmeticFunction ℕ) = σ 0 := by
  rw [← pow_zero_eq_zeta]
  exact zeta_mul_pow_eq_sigma

/-- **`μ * μ` is the left Dirichlet inverse of `σ 0` over `ℤ`.** -/
@[simp]
theorem moebius_mul_moebius_mul_coe_sigma_zero :
    (μ * μ * σ 0 : ArithmeticFunction ℤ) = 1 := by
  rw [← zeta_mul_zeta, natCoe_mul]
  have h : (μ * μ * (ζ * ζ) : ArithmeticFunction ℤ) = (μ * ζ) * (μ * ζ) := by ring
  rw [h, moebius_mul_coe_zeta, one_mul]

/-- **`μ * μ` is the right Dirichlet inverse of `σ 0` over `ℤ`.** -/
@[simp]
theorem coe_sigma_zero_mul_moebius_mul_moebius :
    (σ 0 * (μ * μ) : ArithmeticFunction ℤ) = 1 := by
  rw [mul_comm, moebius_mul_moebius_mul_coe_sigma_zero]

/-- **`μ * μ` is the left Dirichlet inverse of `σ 0` over any ring.** -/
@[simp]
theorem coe_moebius_mul_coe_moebius_mul_coe_sigma_zero [Ring R] :
    (μ * μ * σ 0 : ArithmeticFunction R) = 1 := by
  rw [← intCoe_mul (f := μ) (g := μ), ← coe_coe, ← intCoe_mul,
    moebius_mul_moebius_mul_coe_sigma_zero, intCoe_one]

/-- **`μ * μ` is the right Dirichlet inverse of `σ 0` over any ring.** -/
@[simp]
theorem coe_sigma_zero_mul_coe_moebius_mul_coe_moebius [Ring R] :
    (σ 0 * (μ * μ) : ArithmeticFunction R) = 1 := by
  rw [← intCoe_mul (f := μ) (g := μ), ← coe_coe, ← intCoe_mul,
    coe_sigma_zero_mul_moebius_mul_moebius, intCoe_one]

/-- **`μ * μ` is multiplicative**, as the Dirichlet product of two multiplicative functions. -/
@[arith_mult]
theorem isMultiplicative_moebius_mul_moebius : IsMultiplicative (μ * μ) :=
  isMultiplicative_moebius.mul isMultiplicative_moebius

-- The pointwise evaluations below are not `@[simp]`: Mathlib marks
-- `ArithmeticFunction.mul_apply` `@[simp]`, rewriting `(μ * μ) n` to an antidiagonal sum
-- (so `simp` already proves `n = 1` and `simpNF` rejects `@[simp]` on prime powers).

/-- At `1`, `(μ * μ) 1 = 1`. -/
theorem moebius_mul_moebius_apply_one : (μ * μ) 1 = 1 :=
  isMultiplicative_moebius_mul_moebius.map_one

/-- **Prime-power values of `μ * μ`.** On `1, p, p², p³, …`, `μ * μ` takes the values
`1, -2, 1, 0, 0, …`, reflecting `(1 - X)² = 1 - 2X + X²` in the Euler factor at `p`. -/
theorem moebius_mul_moebius_apply_prime_pow {p k : ℕ} (hp : p.Prime) :
    (μ * μ) (p ^ k) = if k = 0 then 1 else if k = 1 then -2 else if k = 2 then 1 else 0 := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal fun a b ↦ μ a * μ b,
    sum_divisors_prime_pow hp]
  match k with
  | 0 => simp
  | 1 => simp [sum_range_succ, Nat.div_self hp.pos, moebius_apply_prime hp]
  | 2 =>
    have hp2 : p ^ 2 / p = p := by rw [sq, Nat.mul_div_cancel _ hp.pos]
    simp [sum_range_succ, hp2, moebius_apply_prime hp,
      moebius_apply_prime_pow hp (by decide : (2 : ℕ) ≠ 0)]
  | m + 3 =>
    simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte,
      Nat.reduceEqDiff]
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    rw [Nat.pow_div (by omega : i ≤ m + 3) hp.pos]
    by_cases hi2 : 2 ≤ i
    · rw [moebius_apply_prime_pow (k := i) hp (by omega), ite_eq_right (by omega), zero_mul]
    · rw [moebius_apply_prime_pow (k := m + 3 - i) hp (by omega), ite_eq_right (by omega),
        mul_zero]

/-- At a prime `p`, `(μ * μ) p = -2`. -/
theorem moebius_mul_moebius_apply_prime {p : ℕ} (hp : p.Prime) : (μ * μ) p = -2 := by
  simpa using moebius_mul_moebius_apply_prime_pow (k := 1) hp

/-- At the square of a prime `p`, `(μ * μ) (p ^ 2) = 1`. -/
theorem moebius_mul_moebius_apply_prime_sq {p : ℕ} (hp : p.Prime) : (μ * μ) (p ^ 2) = 1 := by
  simpa using moebius_mul_moebius_apply_prime_pow (k := 2) hp

/-- At a prime power `p ^ k` with `3 ≤ k`, `(μ * μ) (p ^ k) = 0`. -/
theorem moebius_mul_moebius_apply_prime_pow_eq_zero {p k : ℕ} (hp : p.Prime) (hk : 3 ≤ k) :
    (μ * μ) (p ^ k) = 0 := by
  rw [moebius_mul_moebius_apply_prime_pow hp]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  simp

/-! ### Divisor-count (`σ 0`) and `μ * μ` inversion -/

/-- **General Dirichlet-inverse inversion on a divisor-closed set.** If `α * β = 1` in
`ArithmeticFunction S` and `g n = ∑_{d ∣ n} β (n / d) • f d` for every positive `n ∈ s` in a
divisor-closed set `s`, then `f n = ∑_{d ∣ n} α (n / d) • g d` for every positive `n ∈ s`. -/
theorem sum_divisors_smul_eq_of_mul_eq_one_on {S : Type*} [Semiring S] [AddCommMonoid R]
    [Module S R] {α β : ArithmeticFunction S} (hαβ : α * β = 1) {f g : ℕ → R} (s : Set ℕ)
    (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s)
    (h : ∀ n > 0, n ∈ s → ∑ d ∈ n.divisors, β (n / d) • f d = g n) :
    ∀ n > 0, n ∈ s → ∑ d ∈ n.divisors, α (n / d) • g d = f n := by
  let f' : ArithmeticFunction R := ⟨fun x ↦ if x = 0 then 0 else f x, ite_eq_left rfl⟩
  intro n hn hns
  have hβ : ∀ d ∈ n.divisors, (β • f') d = g d := fun d hd ↦ by
    have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
    rw [ArithmeticFunction.smul_apply,
      Nat.sum_divisorsAntidiagonal' (f := fun x y ↦ β x • f' y),
      ← h d hd_pos (hs d n (Nat.dvd_of_mem_divisors hd) hns)]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    simp only [f', coe_mk, ite_eq_right (Nat.pos_of_mem_divisors hk).ne']
  calc ∑ d ∈ n.divisors, α (n / d) • g d
      = ∑ d ∈ n.divisors, α (n / d) • (β • f') d :=
        Finset.sum_congr rfl fun d hd ↦ by rw [hβ d hd]
    _ = (α • (β • f')) n := by
        rw [ArithmeticFunction.smul_apply,
          Nat.sum_divisorsAntidiagonal' (f := fun x y ↦ α x • (β • f') y)]
    _ = f n := by
        rw [← mul_smul, hαβ, one_smul]
        simp only [f', coe_mk, ite_eq_right hn.ne']

/-- **Möbius-square inversion on a divisor-closed set, for an `AddCommGroup`.** Since `σ 0` and
`μ * μ` are Dirichlet inverses over `ℤ`, weighting divisor sums by `#(n / d).divisors` is inverted
by weighting divisor sums by `(μ * μ) (n / d)`. -/
theorem sum_card_divisors_smul_eq_iff_sum_moebius_mul_moebius_smul_eq_on [AddCommGroup R]
    {f g : ℕ → R} (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) :
    (∀ n > 0, n ∈ s → ∑ d ∈ n.divisors, #(n / d).divisors • f d = g n) ↔
      ∀ n > 0, n ∈ s → ∑ d ∈ n.divisors, (μ * μ) (n / d) • g d = f n := by
  have hσ (n : ℕ) : (∑ d ∈ n.divisors, #(n / d).divisors • f d) =
      ∑ d ∈ n.divisors, ((σ 0 : ArithmeticFunction ℤ) (n / d)) • f d :=
    Finset.sum_congr rfl fun d _ ↦ by rw [natCoe_apply, sigma_zero_apply, natCast_zsmul]
  simp_rw [hσ]
  exact ⟨sum_divisors_smul_eq_of_mul_eq_one_on moebius_mul_moebius_mul_coe_sigma_zero s hs,
    sum_divisors_smul_eq_of_mul_eq_one_on coe_sigma_zero_mul_moebius_mul_moebius s hs⟩

/-- **Möbius-square inversion for functions to an `AddCommGroup`.** -/
theorem sum_card_divisors_smul_eq_iff_sum_moebius_mul_moebius_smul_eq [AddCommGroup R]
    {f g : ℕ → R} :
    (∀ n > 0, ∑ d ∈ n.divisors, #(n / d).divisors • f d = g n) ↔
      ∀ n > 0, ∑ d ∈ n.divisors, (μ * μ) (n / d) • g d = f n := by
  simpa using sum_card_divisors_smul_eq_iff_sum_moebius_mul_moebius_smul_eq_on (f := f) (g := g)
    Set.univ fun _ _ _ _ ↦ trivial

/-- **Möbius-square inversion on a divisor-closed set, for functions to a ring.** -/
theorem sum_card_divisors_mul_eq_iff_sum_moebius_mul_moebius_mul_eq_on [NonAssocRing R]
    {f g : ℕ → R} (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) :
    (∀ n > 0, n ∈ s → ∑ d ∈ n.divisors, (#(n / d).divisors : R) * f d = g n) ↔
      ∀ n > 0, n ∈ s → ∑ d ∈ n.divisors, ((μ * μ) (n / d) : R) * g d = f n := by
  simp_rw [← nsmul_eq_mul, ← zsmul_eq_mul]
  exact sum_card_divisors_smul_eq_iff_sum_moebius_mul_moebius_smul_eq_on s hs

/-- **Möbius-square inversion for functions to a ring.** -/
theorem sum_card_divisors_mul_eq_iff_sum_moebius_mul_moebius_mul_eq [NonAssocRing R]
    {f g : ℕ → R} :
    (∀ n > 0, ∑ d ∈ n.divisors, (#(n / d).divisors : R) * f d = g n) ↔
      ∀ n > 0, ∑ d ∈ n.divisors, ((μ * μ) (n / d) : R) * g d = f n := by
  simp_rw [← nsmul_eq_mul, ← zsmul_eq_mul]
  exact sum_card_divisors_smul_eq_iff_sum_moebius_mul_moebius_smul_eq

/-- **Single-level Möbius-square inversion for an `AddCommGroup`.** If
`g M = ∑ d ∈ M.divisors, #(M / d).divisors • f d` holds at every divisor `M` of `N > 0`, then
`f N = ∑ M ∈ N.divisors, (μ * μ) (N / M) • g M`. -/
theorem eq_sum_divisors_moebius_mul_moebius_smul [AddCommGroup R] {f g : ℕ → R} {N : ℕ}
    (hN : 0 < N) (h : ∀ M, M ∣ N → g M = ∑ d ∈ M.divisors, #(M / d).divisors • f d) :
    f N = ∑ M ∈ N.divisors, (μ * μ) (N / M) • g M :=
  ((sum_card_divisors_smul_eq_iff_sum_moebius_mul_moebius_smul_eq_on {m | m ∣ N}
    fun _ _ hmn hn ↦ hmn.trans hn).mp (fun M _ hMN ↦ (h M hMN).symm) N hN dvd_rfl).symm

/-- **Single-level Möbius-square inversion for a ring.** -/
theorem eq_sum_divisors_moebius_mul_moebius_mul [NonAssocRing R] {f g : ℕ → R} {N : ℕ}
    (hN : 0 < N) (h : ∀ M, M ∣ N → g M = ∑ d ∈ M.divisors, (#(M / d).divisors : R) * f d) :
    f N = ∑ M ∈ N.divisors, ((μ * μ) (N / M) : R) * g M := by
  simp_rw [← nsmul_eq_mul] at h
  simp_rw [← zsmul_eq_mul]
  exact eq_sum_divisors_moebius_mul_moebius_smul hN h

/-- **Single-level Möbius-square inversion restricted to multiples of a divisor `c ∣ N`.** When a
relation `g M = ∑_{c ∣ d ∣ M} #(M / d).divisors • f d` holds for every intermediate multiple
`c ∣ M ∣ N` (for instance, when `c` is the conductor of a Dirichlet character mod `N`), rescaling
by `c` recovers `f N = ∑_{c ∣ M ∣ N} (μ * μ) (N / M) • g M`. -/
theorem eq_sum_divisors_filter_dvd_moebius_mul_moebius_smul [AddCommGroup R] {f g : ℕ → R}
    {c N : ℕ} (hcN : c ∣ N) (hN : 0 < N)
    (h : ∀ M, c ∣ M → M ∣ N → g M = ∑ d ∈ M.divisors with c ∣ d, #(M / d).divisors • f d) :
    f N = ∑ M ∈ N.divisors with c ∣ M, (μ * μ) (N / M) • g M := by
  obtain ⟨Q, rfl⟩ := hcN
  have hc0 : c ≠ 0 := left_ne_zero_of_mul hN.ne'
  have hcpos : 0 < c := Nat.pos_of_ne_zero hc0
  have hQ : 0 < Q := Nat.pos_of_ne_zero (right_ne_zero_of_mul hN.ne')
  have key := eq_sum_divisors_moebius_mul_moebius_smul (f := fun m ↦ f (c * m))
    (g := fun m ↦ g (c * m)) hQ fun m hmQ ↦ by
      rw [h (c * m) (dvd_mul_right c m) (mul_dvd_mul_left c hmQ), Nat.filter_dvd_divisors_mul hc0,
        Finset.sum_map]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      simp [Nat.mul_div_mul_left m k hcpos]
  rw [key, Nat.filter_dvd_divisors_mul hc0, Finset.sum_map]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  simp [Nat.mul_div_mul_left Q m hcpos]

/-- **Single-level Möbius-square inversion restricted to multiples of `c ∣ N`, in a ring.** -/
theorem eq_sum_divisors_filter_dvd_moebius_mul_moebius_mul [NonAssocRing R] {f g : ℕ → R}
    {c N : ℕ} (hcN : c ∣ N) (hN : 0 < N)
    (h : ∀ M, c ∣ M → M ∣ N →
      g M = ∑ d ∈ M.divisors with c ∣ d, (#(M / d).divisors : R) * f d) :
    f N = ∑ M ∈ N.divisors with c ∣ M, ((μ * μ) (N / M) : R) * g M := by
  simp_rw [← nsmul_eq_mul] at h
  simp_rw [← zsmul_eq_mul]
  exact eq_sum_divisors_filter_dvd_moebius_mul_moebius_smul hcN hN h

end ArithmeticFunction

end
