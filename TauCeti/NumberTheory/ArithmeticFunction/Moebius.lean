/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

import Mathlib.Algebra.Module.BigOperators

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

/-- Reassociating a nested `divisorsAntidiagonal` sum over `ℤ`: convolving `φ` with `β` and then `α`
is the same as convolving `φ` with the Dirichlet product of `α` and `β`. Stated for plain functions
`ℕ → ℤ` and `ℕ → R` so no zero-at-`0` normalization is required. -/
private lemma sum_divisorsAntidiagonal_smul_sum [AddCommGroup R]
    (α β : ℕ → ℤ) (φ : ℕ → R) (n : ℕ) :
    ∑ x ∈ n.divisorsAntidiagonal, α x.1 • ∑ y ∈ x.2.divisorsAntidiagonal, β y.1 • φ y.2 =
      ∑ z ∈ n.divisorsAntidiagonal,
        (∑ w ∈ z.1.divisorsAntidiagonal, α w.1 * β w.2) • φ z.2 := by
  simp only [Finset.smul_sum, Finset.sum_smul, mul_smul, sum_sigma']
  refine Finset.sum_nbij' (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ ↦ ⟨(i * k, l), (i, k)⟩)
    (fun ⟨⟨_m, l⟩, ⟨i, k⟩⟩ ↦ ⟨(i, k * l), (k, l)⟩) ?_ ?_ ?_ ?_ ?_ <;>
    aesop (add simp mul_assoc)

/-- Collapsing a convolution against the Dirichlet identity `1` at `n > 0`. -/
private lemma sum_divisorsAntidiagonal_one_apply_smul [AddCommGroup R] (φ : ℕ → R) {n : ℕ}
    (hn : 0 < n) :
    ∑ z ∈ n.divisorsAntidiagonal, (1 : ArithmeticFunction ℤ) z.1 • φ z.2 = φ n := by
  rw [Nat.sum_divisorsAntidiagonal fun a b ↦ (1 : ArithmeticFunction ℤ) a • φ b,
    Finset.sum_eq_single 1]
  · simp
  · intro d _ hd1
    rw [one_apply_ne hd1, zero_smul]
  · exact fun h ↦ absurd (Nat.one_mem_divisors.mpr hn.ne') h

/-- **Möbius-square inversion on a divisor-closed set, for an `AddCommGroup`.** Since `σ 0` and
`μ * μ` are Dirichlet inverses over `ℤ`, weighting divisor sums by `#(n / d).divisors` is inverted
by weighting divisor sums by `(μ * μ) (n / d)`. -/
theorem sum_card_divisors_smul_eq_iff_sum_moebius_mul_moebius_smul_eq_on [AddCommGroup R]
    {f g : ℕ → R} (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) :
    (∀ n > 0, n ∈ s → ∑ d ∈ n.divisors, #(n / d).divisors • f d = g n) ↔
      ∀ n > 0, n ∈ s → ∑ d ∈ n.divisors, (μ * μ) (n / d) • g d = f n := by
  constructor <;> intro h n hn hns
  · rw [← Nat.sum_divisorsAntidiagonal' (f := fun a b ↦ (μ * μ) a • g b)]
    have hcongr : ∑ x ∈ n.divisorsAntidiagonal, (μ * μ) x.1 • g x.2 =
        ∑ x ∈ n.divisorsAntidiagonal, (μ * μ) x.1 •
          ∑ y ∈ x.2.divisorsAntidiagonal, (σ 0 y.1 : ℤ) • f y.2 := by
      refine Finset.sum_congr rfl fun x hx ↦ congrArg ((μ * μ) x.1 • ·) ?_
      have hx_dvd : x.2 ∣ n := Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)
      rw [← h x.2 (Nat.pos_of_dvd_of_pos hx_dvd hn) (hs x.2 n hx_dvd hns),
        ← Nat.sum_divisorsAntidiagonal' (f := fun a b ↦ #a.divisors • f b)]
      exact Finset.sum_congr rfl fun y _ ↦ by rw [sigma_zero_apply, natCast_zsmul]
    rw [hcongr, sum_divisorsAntidiagonal_smul_sum (fun k ↦ (μ * μ) k) (fun k ↦ (σ 0 k : ℤ)) f n]
    have hmul : ∀ z ∈ n.divisorsAntidiagonal,
        (∑ w ∈ z.1.divisorsAntidiagonal, (μ * μ) w.1 * (σ 0 w.2 : ℤ)) =
          (1 : ArithmeticFunction ℤ) z.1 := fun z _ ↦ by
      change ((μ * μ) * (σ 0 : ArithmeticFunction ℤ)) z.1 = _
      rw [moebius_mul_moebius_mul_coe_sigma_zero]
    rw [Finset.sum_congr rfl fun z hz ↦ by rw [hmul z hz]]
    exact sum_divisorsAntidiagonal_one_apply_smul f hn
  · rw [← Nat.sum_divisorsAntidiagonal' (f := fun a b ↦ #a.divisors • f b)]
    have hcongr : ∑ x ∈ n.divisorsAntidiagonal, #x.1.divisors • f x.2 =
        ∑ x ∈ n.divisorsAntidiagonal, (σ 0 x.1 : ℤ) •
          ∑ y ∈ x.2.divisorsAntidiagonal, (μ * μ) y.1 • g y.2 := by
      refine Finset.sum_congr rfl fun x hx ↦ ?_
      have hx_dvd : x.2 ∣ n := Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)
      rw [sigma_zero_apply, natCast_zsmul,
        ← h x.2 (Nat.pos_of_dvd_of_pos hx_dvd hn) (hs x.2 n hx_dvd hns),
        Nat.sum_divisorsAntidiagonal' (f := fun a b ↦ (μ * μ) a • g b)]
    rw [hcongr, sum_divisorsAntidiagonal_smul_sum (fun k ↦ (σ 0 k : ℤ)) (fun k ↦ (μ * μ) k) g n]
    have hmul : ∀ z ∈ n.divisorsAntidiagonal,
        (∑ w ∈ z.1.divisorsAntidiagonal, (σ 0 w.1 : ℤ) * (μ * μ) w.2) =
          (1 : ArithmeticFunction ℤ) z.1 := fun z _ ↦ by
      change ((σ 0 : ArithmeticFunction ℤ) * (μ * μ)) z.1 = _
      rw [coe_sigma_zero_mul_moebius_mul_moebius]
    rw [Finset.sum_congr rfl fun z hz ↦ by rw [hmul z hz]]
    exact sum_divisorsAntidiagonal_one_apply_smul g hn

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

/-- The divisors of `c * m` that are multiples of `c > 0` are `c` times the divisors of `m`. -/
private lemma filter_dvd_divisors_mul {c m : ℕ} (hc : c ≠ 0) :
    {d ∈ (c * m).divisors | c ∣ d} = m.divisors.map ⟨(c * ·), mul_right_injective₀ hc⟩ := by
  ext d
  simp only [mem_filter, mem_divisors, mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨⟨hdcm, hcm0⟩, k, rfl⟩
    exact ⟨k, ⟨(mul_dvd_mul_iff_left hc).mp hdcm, right_ne_zero_of_mul hcm0⟩, rfl⟩
  · rintro ⟨k, ⟨hkm, hm0⟩, rfl⟩
    exact ⟨⟨mul_dvd_mul_left c hkm, mul_ne_zero hc hm0⟩, dvd_mul_right c k⟩

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
      rw [h (c * m) (dvd_mul_right c m) (mul_dvd_mul_left c hmQ), filter_dvd_divisors_mul hc0,
        Finset.sum_map]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      simp [Nat.mul_div_mul_left m k hcpos]
  rw [key, filter_dvd_divisors_mul hc0, Finset.sum_map]
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
