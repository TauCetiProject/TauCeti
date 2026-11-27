/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk, The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import TauCeti.NumberTheory.ArithmeticFunction.DilateSq
import Mathlib.Algebra.Order.Ring.Abs
import TauCeti.NumberTheory.ArithmeticFunction.Misc
import TauCeti.NumberTheory.ArithmeticFunction.Sigma.Basic

/-!
# The square of the Möbius function, divisor-count Möbius inversion and upper-divisor sums

In the Dirichlet ring of arithmetic functions, `ζ * ζ = σ 0` is the divisor-count function
`n ↦ #n.divisors`, and its Dirichlet inverse is the convolution square `μ * μ` of the Möbius
function: `(μ * μ) * σ 0 = 1`. At a prime power `p ^ k`, `(μ * μ) (p ^ k)` takes the values
`1`, `-2`, `1`, and `0` for `k = 0`, `1`, `2`, and `k ≥ 3` respectively.

Convolutions weighted by `#(N / M).divisors` arise whenever an ambient invariant at level `N`
decomposes over pairs `(M, d)` with `d * M ∣ N` whose contribution depends only on `M` — most
notably in the Atkin–Lehner–Li decomposition of spaces of cusp forms by level-raising operators,
where each divisor level `M ∣ N` contributes `#(N / M).divisors` isomorphic copies of its new
subspace. Inverting `g(n) = ∑_{d ∣ n} #(n / d).divisors • f(d)` yields
`f(n) = ∑_{d ∣ n} (μ * μ)(n / d) • g(d)`, turning ambient dimension formulas into newspace
dimension formulas. Because `μ * μ` takes negative values (such as `-2` at primes), the target must
admit subtraction (`AddCommGroup` or `NonAssocRing`), and natural-valued dimensions are cast to `ℤ`
before inverting. The `_on` and `_of_dvd` variants handle quantities (such as fixed-nebentypus
dimensions along raised characters) defined or obeying the convolution identity only on the
divisors of a fixed nonzero level `N`.

The four Dirichlet-inverse lemmas for `μ * μ` and `σ 0` and the four global / divisor-closed
divisor-count inversion equivalences closely adapt the statement pattern and proof plan of
`ArithmeticFunction.moebius_mul_coe_zeta`..`ArithmeticFunction.coe_zeta_mul_coe_moebius` and
`ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq`..`sum_eq_iff_sum_mul_moebius_eq_on` in
`Mathlib.NumberTheory.ArithmeticFunction.Moebius`.

For squarefree `m`, the Möbius function summed over the divisors of `m` that are multiples
of `l` vanishes unless `l = m`, when the sum is `μ l` (`ArithmeticFunction.sum_moebius_upper`).

Summing `μ²` over the divisors of `n ≠ 0` counts its squarefree divisors, giving `2 ^ ω(n)`
(`ArithmeticFunction.sum_divisors_moebius_sq`); this is the convolution identity `μ² * ζ = 2 ^ ω`
behind the Dirichlet series `ζ(s)² / ζ(2s)` of `2 ^ ω`. Over an interval `L < m ≤ M` the same
squares sum to at most `M - L` (`ArithmeticFunction.sum_Ioc_moebius_sq_le`), the Möbius coefficient
energy of bilinear estimates. Since `|μ(n)| ≤ 1`, multiplying by `μ(n)` never increases an
absolute value (`ArithmeticFunction.abs_moebius_mul_le`).

Summed over the divisors `d` with `d² ∣ n`, the Möbius function gives back its own square:
`μ(n)² = ∑_{d² ∣ n} μ(d)` (`ArithmeticFunction.sum_divisors_filter_sq_dvd_moebius`). The right side
is multiplicative in `n` (`ArithmeticFunction.IsMultiplicative.sum_divisors_filter_pow_dvd_mul`),
so the identity reduces to prime powers, where both sides are `1` for exponents at most `1` and
`0` beyond. This identity and its proof by multiplicativity are adapted from `moebius_sq_eq` in
[Alex Kontorovich, Terence Tao and contributors, *Prime Number Theorem and More*][PNT-moebius-sq].

## Main results

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
* `ArithmeticFunction.sum_divisors_moebius_sq`: `∑_{d ∣ n} μ(d)² = 2 ^ ω(n)` for `n ≠ 0`.
* `ArithmeticFunction.sum_Ioc_moebius_sq_le`: `∑_{L<m≤M} μ(m)² ≤ M - L`.
* `ArithmeticFunction.abs_moebius_mul_le`: `|μ(n) a| ≤ |a|` in a ring whose linear order is
  compatible with addition.
* `ArithmeticFunction.IsMultiplicative.moebius_sq_mul_nonneg`: `μ(n)² f(n) ≥ 0` for a
  multiplicative `f` with nonnegative prime values.
* `ArithmeticFunction.moebius_sq_apply_prime_pow`,
  `ArithmeticFunction.sum_divisors_filter_sq_dvd_moebius_prime_pow`: both sides of
  `μ(n)² = ∑_{d² ∣ n} μ(d)` at prime powers.
* `ArithmeticFunction.sum_divisors_filter_sq_dvd_moebius`: `∑_{d² ∣ n} μ(d) = μ(n)²`.
* `ArithmeticFunction.coe_zeta_mul_dilateSq_moebius_apply`: the convolution form
  `(ζ * μ_□)(n) = μ(n)²`, with `μ_□` the dilation `ArithmeticFunction.dilateSq` of `μ` by squares.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.8.3.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53 (2004),
  (1.33).

[PNT-moebius-sq]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/bfce4045596606d2495e00701eaec933d8893910/PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean#L1295-L1420
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

/-- The squares of the Möbius function over an interval `L < m ≤ M` sum to at most its length
`M - L`: each `μ(m)²` is `0` or `1`. -/
theorem sum_Ioc_moebius_sq_le [Ring R] [PartialOrder R] [IsOrderedRing R] (L M : ℕ) :
    ∑ m ∈ Ioc L M, (μ m : R) ^ 2 ≤ ((M - L : ℕ) : R) := by
  rw [← Nat.card_Ioc, ← nsmul_one]
  refine sum_le_card_nsmul _ _ _ fun m _ ↦ ?_
  rw [← Int.cast_pow, moebius_sq]
  split_ifs <;> simp

/-! ### Absolute values -/

/-- Multiplying by a value of the Möbius function does not increase the absolute value:
`|μ(n) a| ≤ |a|`, as `μ(n)` is `0` or `±1`. -/
theorem abs_moebius_mul_le [NonAssocRing R] [LinearOrder R] [AddLeftMono R] (n : ℕ) (a : R) :
    |(μ n : R) * a| ≤ |a| := by
  obtain h | h | h : μ n = 0 ∨ μ n = 1 ∨ μ n = -1 := by
    have := abs_le.mp (abs_moebius_le_one (n := n))
    omega
  all_goals simp [h]

/-! ### Nonnegativity on squarefree integers -/

/-- A multiplicative function with nonnegative prime values is nonnegative on squarefree
integers, so `μ(n)² f(n) ≥ 0` for every `n`. -/
theorem IsMultiplicative.moebius_sq_mul_nonneg [CommRing R] [PartialOrder R]
    [IsOrderedRing R] {f : ArithmeticFunction R} (hf : f.IsMultiplicative)
    (hf0 : ∀ p : ℕ, p.Prime → 0 ≤ f p) (n : ℕ) : 0 ≤ (μ n : R) ^ 2 * f n := by
  by_cases hn : Squarefree n
  · rw [← Int.cast_pow, moebius_sq_eq_one_of_squarefree hn, Int.cast_one, one_mul,
      ← hf.prod_primeFactors hn]
    exact prod_nonneg fun p hp ↦ hf0 p (prime_of_mem_primeFactors hp)
  · simp [moebius_eq_zero_of_not_squarefree hn]

/-! ### The Möbius function over square divisors -/

/-- At a prime power, `μ(p ^ k)²` is `1` for `k ≤ 1` and `0` for `k ≥ 2`. -/
theorem moebius_sq_apply_prime_pow [Ring R] {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (μ (p ^ k) : R) ^ 2 = if k ≤ 1 then 1 else 0 := by
  rcases k with _ | _ | k
  · simp
  · simp [moebius_apply_prime hp]
  · simp [moebius_apply_prime_pow hp]

/-- At a prime power, `∑_{d² ∣ p ^ k} μ(d)` is `1` for `k ≤ 1` and `μ(1) + μ(p) = 0` for
`k ≥ 2`. -/
theorem sum_divisors_filter_sq_dvd_moebius_prime_pow [Ring R] {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∑ d ∈ (p ^ k).divisors with d ^ 2 ∣ p ^ k, (μ d : R) = if k ≤ 1 then 1 else 0 := by
  rw [sum_filter, Nat.sum_divisors_prime_pow hp]
  simp_rw [← pow_mul, Nat.pow_dvd_pow_iff_le_right hp.one_lt]
  rcases k with _ | _ | k
  · simp
  · simp [sum_range_succ]
  · rw [sum_range_succ', sum_range_succ']
    simp [moebius_apply_prime hp, moebius_apply_prime_pow hp]

/-- **`μ²` as a sum over square divisors** (Iwaniec–Kowalski (1.33)):
`μ(n)² = ∑_{d² ∣ n} μ(d)`. Both sides are `1` when `n` is squarefree and `0` otherwise
(`ArithmeticFunction.moebius_sq`). -/
theorem sum_divisors_filter_sq_dvd_moebius [Ring R] (n : ℕ) :
    ∑ d ∈ n.divisors with d ^ 2 ∣ n, (μ d : R) = (μ n : R) ^ 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp _ =>
    rw [sum_divisors_filter_sq_dvd_moebius_prime_pow hp, moebius_sq_apply_prime_pow hp]
  | zero => simp
  | one => simp [sum_filter]
  | coprime m n _ _ hmn hm hn =>
    have hf := (isMultiplicative_moebius.intCast (R := R)).sum_divisors_filter_pow_dvd_mul 2 hmn
    simp only [intCoe_apply] at hf
    rw [hf, hm, hn, isMultiplicative_moebius.map_mul_of_coprime hmn, Int.cast_mul,
      (Int.cast_commute _ _).mul_pow]

/-- **`μ² = ζ * μ_□`**: the convolution of `ζ` with the dilation of `μ` by squares is `μ²`,
`(ζ * μ_□)(n) = ∑_{d² ∣ n} μ(d) = μ(n)²`, in any ring. -/
theorem coe_zeta_mul_dilateSq_moebius_apply [Ring R] (n : ℕ) :
    ((ζ : ArithmeticFunction R) * (μ : ArithmeticFunction R).dilateSq) n = (μ n : R) ^ 2 := by
  rw [mul_dilateSq_apply, ← sum_divisors_filter_sq_dvd_moebius]
  refine sum_congr rfl fun d hd ↦ ?_
  rw [mem_filter, mem_divisors] at hd
  rw [natCoe_apply, zeta_apply_ne ((Nat.div_ne_zero_iff_of_dvd hd.2).2
    ⟨hd.1.2, pow_ne_zero 2 (ne_zero_of_dvd_ne_zero hd.1.2 hd.1.1)⟩), Nat.cast_one, one_mul,
    intCoe_apply]

end ArithmeticFunction
