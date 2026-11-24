/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk, The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import TauCeti.NumberTheory.ArithmeticFunction.Sigma.Basic
import TauCeti.NumberTheory.Divisors

/-!
# The square of the Möbius function, divisor-count Möbius inversion and upper-divisor sums

In the Dirichlet ring of arithmetic functions, `ζ * ζ = σ 0` is the divisor-count function
`n ↦ #n.divisors`, and its Dirichlet inverse is the convolution square `μ * μ` of the Möbius
function: `(μ * μ) * σ 0 = 1`. Being a Dirichlet product of multiplicative functions, `μ * μ` is
multiplicative; at a prime power `p ^ k`, `(μ * μ) (p ^ k)` takes the values `1`, `-2`, `1`, and `0`
for `k = 0`, `1`, `2`, and `k ≥ 3` respectively.

Convolutions weighted by `#(N / M).divisors` arise whenever an ambient invariant at level `N`
decomposes over pairs `(M, d)` with `d * M ∣ N` whose contribution depends only on `M` — most
notably in the Atkin–Lehner–Li decomposition of spaces of cusp forms by level-raising operators,
where each divisor level `M ∣ N` contributes `#(N / M).divisors` isomorphic copies of its new
subspace. Inverting `g(n) = ∑_{d ∣ n} #(n / d).divisors • f(d)` yields
`f(n) = ∑_{d ∣ n} (μ * μ)(n / d) • g(d)`, turning ambient dimension formulas into newspace
dimension formulas. Because `μ * μ` takes negative values (such as `-2` at primes), the target must
admit subtraction (`AddCommGroup` or `NonAssocRing`), and natural-valued dimensions are cast to `ℤ`
before inverting. Both directions follow from general Dirichlet-inverse inversion on divisor-closed
sets (`ArithmeticFunction.sum_divisors_smul_eq_of_mul_eq_one_on`). The `_on`, `_of_dvd`, and
divisor-filtered `_filter_dvd_..._of_dvd` variants handle quantities (such as fixed-nebentypus
dimensions along characters of conductor `c ∣ N`) defined or obeying the convolution identity only
on the divisors of a fixed nonzero level `N`, or on those divisible by `c`.

The four Dirichlet-inverse lemmas for `μ * μ` and `σ 0` and the four global / divisor-closed
divisor-count inversion equivalences closely adapt the statement pattern and proof plan of
`ArithmeticFunction.moebius_mul_coe_zeta`..`ArithmeticFunction.coe_zeta_mul_coe_moebius` and
`ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq`..`sum_eq_iff_sum_mul_moebius_eq_on` in
`Mathlib.NumberTheory.ArithmeticFunction.Moebius`.

For squarefree `m`, the Möbius function summed over the divisors of `m` that are multiples
of `l` vanishes unless `l = m`, when the sum is `μ l` (`ArithmeticFunction.sum_moebius_upper`).

Summing `μ²` over the divisors of `n ≠ 0` counts its squarefree divisors, giving `2 ^ ω(n)`
(`ArithmeticFunction.sum_divisors_moebius_sq`); this is the convolution identity `μ² * ζ = 2 ^ ω`
behind the Dirichlet series `ζ(s)² / ζ(2s)` of `2 ^ ω`.

## Main results

* `ArithmeticFunction.moebius_mul_moebius_mul_coe_sigma_zero`,
  `ArithmeticFunction.coe_sigma_zero_mul_moebius_mul_moebius`,
  `ArithmeticFunction.coe_moebius_mul_coe_moebius_mul_coe_sigma_zero`,
  `ArithmeticFunction.coe_sigma_zero_mul_coe_moebius_mul_coe_moebius`: `μ * μ` and `σ 0` are
  Dirichlet inverses.
* `ArithmeticFunction.isMultiplicative_moebius_mul_moebius`: `μ * μ` is multiplicative.
* `ArithmeticFunction.moebius_mul_moebius_apply_prime_pow` (with specializations at `1`, `p`, `p²`,
  and `p ^ k` for `3 ≤ k`): values of `μ * μ` at `1` and prime powers.
* `ArithmeticFunction.sum_divisors_smul_eq_of_mul_eq_one_on`: general Dirichlet-inverse inversion on
  a divisor-closed set for `α * β = 1`.
* `ArithmeticFunction.sum_card_divisors_smul_eq_iff_sum_moebius_mul_moebius_smul_eq`,
  `ArithmeticFunction.sum_card_divisors_smul_eq_iff_sum_moebius_mul_moebius_smul_eq_on`,
  `ArithmeticFunction.sum_card_divisors_mul_eq_iff_sum_moebius_mul_moebius_mul_eq`,
  `ArithmeticFunction.sum_card_divisors_mul_eq_iff_sum_moebius_mul_moebius_mul_eq_on`: Möbius
  inversion for convolution against `#(n / d).divisors`.
* `ArithmeticFunction.eq_sum_divisors_moebius_mul_moebius_smul_of_dvd`,
  `ArithmeticFunction.eq_sum_divisors_moebius_mul_moebius_mul_of_dvd`,
  `ArithmeticFunction.eq_sum_divisors_filter_dvd_moebius_mul_moebius_smul_of_dvd`,
  `ArithmeticFunction.eq_sum_divisors_filter_dvd_moebius_mul_moebius_mul_of_dvd`: specialization to
  the divisors of a fixed nonzero integer `N`, unrestricted or restricted to multiples of `c ∣ N`.
* `ArithmeticFunction.sum_moebius_upper`: upper-divisor sum of `μ` on a squarefree integer.
* `ArithmeticFunction.sum_divisors_moebius_sq`: `∑_{d ∣ n} μ(d)² = 2 ^ ω(n)` for `n ≠ 0`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.8.3.
-/

public section

open Finset Nat

namespace ArithmeticFunction

open scoped Moebius zeta ArithmeticFunction.sigma

variable {G R : Type*}

/-! ### Dirichlet inverse `μ * μ` of `σ 0` -/

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

/-! ### Multiplicativity and prime-power values of `μ * μ` -/

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

/-- At the square of a prime `p`, `(μ * μ) (p ^ 2) = 1`. -/
theorem moebius_mul_moebius_apply_prime_sq {p : ℕ} (hp : p.Prime) : (μ * μ) (p ^ 2) = 1 := by
  simpa using moebius_mul_moebius_apply_prime_pow hp 2

/-- At a prime power `p ^ k` with `3 ≤ k`, `(μ * μ) (p ^ k) = 0`. -/
theorem moebius_mul_moebius_apply_prime_pow_eq_zero {p k : ℕ} (hp : p.Prime) (hk : 3 ≤ k) :
    (μ * μ) (p ^ k) = 0 := by
  rw [moebius_mul_moebius_apply_prime_pow hp k]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  simp

/-! ### Möbius inversion for divisor-count convolutions -/

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

/-- **Divisor-count Möbius inversion on a divisor-closed set**, for functions to an
`AddCommGroup`. -/
theorem sum_card_divisors_smul_eq_iff_sum_moebius_mul_moebius_smul_eq_on
    [AddCommGroup G] {f g : ℕ → G} (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) :
    (∀ n > 0, n ∈ s → ∑ d ∈ n.divisors, #(n / d).divisors • f d = g n) ↔
      ∀ n > 0, n ∈ s → ∑ d ∈ n.divisors, (μ * μ) (n / d) • g d = f n := by
  have hσ (n : ℕ) : (∑ d ∈ n.divisors, #(n / d).divisors • f d) =
      ∑ d ∈ n.divisors, ((σ 0 : ArithmeticFunction ℤ) (n / d)) • f d :=
    Finset.sum_congr rfl fun d _ ↦ by rw [natCoe_apply, sigma_zero_apply, natCast_zsmul]
  simp_rw [hσ]
  exact ⟨sum_divisors_smul_eq_of_mul_eq_one_on moebius_mul_moebius_mul_coe_sigma_zero s hs,
    sum_divisors_smul_eq_of_mul_eq_one_on coe_sigma_zero_mul_moebius_mul_moebius s hs⟩

/-- **Divisor-count Möbius inversion** for functions to an `AddCommGroup`. -/
theorem sum_card_divisors_smul_eq_iff_sum_moebius_mul_moebius_smul_eq
    [AddCommGroup G] {f g : ℕ → G} :
    (∀ n > 0, ∑ d ∈ n.divisors, #(n / d).divisors • f d = g n) ↔
      ∀ n > 0, ∑ d ∈ n.divisors, (μ * μ) (n / d) • g d = f n := by
  simpa using sum_card_divisors_smul_eq_iff_sum_moebius_mul_moebius_smul_eq_on (f := f) (g := g)
    Set.univ fun _ _ _ _ ↦ trivial

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

/-- **Divisor-count Möbius inversion restricted to multiples of `c ∣ N`**, for functions to an
`AddCommGroup`: if `∑_{c ∣ d ∣ m} #(m / d).divisors • f d = g m` holds for every intermediate
multiple `c ∣ m ∣ N` of a nonzero level `N` (for instance, when `c` is the conductor of a Dirichlet
character modulo `N`), rescaling by `c` yields `f N = ∑_{c ∣ m ∣ N} (μ * μ) (N / m) • g m`. -/
theorem eq_sum_divisors_filter_dvd_moebius_mul_moebius_smul_of_dvd [AddCommGroup G] {c N : ℕ}
    (hcN : c ∣ N) (hN : N ≠ 0) {f g : ℕ → G}
    (h : ∀ m, c ∣ m → m ∣ N → ∑ d ∈ m.divisors with c ∣ d, #(m / d).divisors • f d = g m) :
    f N = ∑ m ∈ N.divisors with c ∣ m, (μ * μ) (N / m) • g m := by
  obtain ⟨Q, rfl⟩ := hcN
  have hcpos : 0 < c := Nat.pos_of_ne_zero (left_ne_zero_of_mul hN)
  have hQ0 : Q ≠ 0 := right_ne_zero_of_mul hN
  have key := eq_sum_divisors_moebius_mul_moebius_smul_of_dvd (f := fun m ↦ f (c * m))
    (g := fun m ↦ g (c * m)) hQ0 fun m hmQ ↦ by
      rw [← h (c * m) (dvd_mul_right c m) (mul_dvd_mul_left c hmQ),
        Nat.sum_divisors_filter_dvd (dvd_mul_right c m), Nat.mul_div_cancel_left m hcpos]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Nat.mul_div_mul_left m k hcpos]
  rw [key, Nat.sum_divisors_filter_dvd (dvd_mul_right c Q), Nat.mul_div_cancel_left Q hcpos]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [Nat.mul_div_mul_left Q m hcpos]

/-- **Divisor-count Möbius inversion restricted to multiples of `c ∣ N`**, for functions to a
ring. -/
theorem eq_sum_divisors_filter_dvd_moebius_mul_moebius_mul_of_dvd [NonAssocRing R] {c N : ℕ}
    (hcN : c ∣ N) (hN : N ≠ 0) {f g : ℕ → R}
    (h : ∀ m, c ∣ m → m ∣ N →
      ∑ d ∈ m.divisors with c ∣ d, (#(m / d).divisors : R) * f d = g m) :
    f N = ∑ m ∈ N.divisors with c ∣ m, ((μ * μ) (N / m) : R) * g m := by
  simp_rw [← nsmul_eq_mul] at h
  simp_rw [← zsmul_eq_mul]
  exact eq_sum_divisors_filter_dvd_moebius_mul_moebius_smul_of_dvd hcN hN h

/-! ### Upper-divisor sums -/

/-- The Möbius sum over divisors of a squarefree number that are multiples of `l`. -/
theorem sum_moebius_upper (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then (μ d : ℤ) else 0) =
      if l = m then (μ l : ℤ) else 0 := by
  revert hm
  revert m
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on'
    {n | Squarefree n} (fun _ _ => Squarefree.squarefree_of_dvd) (by simp)).mpr
  intro m hm
  rw [sum_divisorsAntidiagonal' (f := fun x y => μ x • if l = y then μ l else 0)]
  by_cases hl : l ∣ m
  · rw [ite_eq_left hl, sum_eq_single l]
    · have hmul : m / l * l = m := Nat.div_mul_cancel hl
      rw [ite_eq_left rfl, smul_eq_mul, ← isMultiplicative_moebius.map_mul_of_coprime, hmul]
      exact coprime_of_squarefree_mul (hmul.symm ▸ hm)
    · intro d _ hdl
      rw [ite_eq_right hdl.symm, smul_zero]
    · intro h
      exact False.elim (h (mem_divisors.mpr ⟨hl, hm.ne_zero⟩))
  · rw [ite_eq_right hl, sum_eq_zero]
    intro d hd
    rw [ite_eq_right, smul_zero]
    intro h
    exact hl (h ▸ dvd_of_mem_divisors hd)

/-! ### Squares of the Möbius function over divisors -/

open scoped omega in
/-- The squares of the Möbius function summed over the divisors of a nonzero `n` count its
squarefree divisors, which are the products of subsets of its distinct prime factors:
`∑_{d ∣ n} μ(d)² = 2 ^ ω(n)`. -/
theorem sum_divisors_moebius_sq [Ring R] {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (μ d : R) ^ 2 = 2 ^ ω n := by
  have hsq (d : ℕ) : (μ d : R) ^ 2 = if Squarefree d then 1 else 0 := by
    split_ifs with hd
    · rw [← Int.cast_pow, moebius_sq_eq_one_of_squarefree hd, Int.cast_one]
    · simp [moebius_eq_zero_of_not_squarefree hd]
  simp_rw [hsq, ← sum_filter, sum_divisors_filter_squarefree hn, sum_const, card_powerset,
    factors_eq]
  simp [cardDistinctFactors_eq_card_primeFactors]

end ArithmeticFunction
