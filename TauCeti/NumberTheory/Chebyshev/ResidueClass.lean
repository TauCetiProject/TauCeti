/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.PrimesInAP
import TauCeti.NumberTheory.PrimeCounting
import TauCeti.NumberTheory.SumPrimePow

/-!
# Chebyshev functions in a residue class

For a modulus `q : ℕ`, a residue `a : ZMod q` and a real cutoff `x`, this file defines

* `Chebyshev.psiAP q a x = ψ(x; q, a) = ∑_{n ≤ x, n ≡ a (mod q)} Λ(n)`,
* `Chebyshev.thetaAP q a x = θ(x; q, a) = ∑_{p ≤ x prime, p ≡ a (mod q)} log p`,
* `Chebyshev.primeCountAP q a x = π(x; q, a)`, the number of primes `p ≤ x` with `p ≡ a (mod q)`,

with the cutoffs of Mathlib's `Chebyshev.psi`, `Chebyshev.theta` and `Nat.primeCounting`: the
index runs over `1 ≤ n ≤ ⌊x⌋₊`. These finite sums need no coprimality of `a` and `q`; the
asymptotic theorems about them (Dirichlet's theorem, Siegel–Walfisz) concern the classes with
`IsUnit a`, in which a prime power `n ≤ x` lies according to the class of `n` itself, not of its
prime.

Besides the basic API (nonnegativity, monotonicity, dependence on `⌊x⌋₊` only, vanishing below
`2`, comparison with the unrestricted functions, the trivial modulus `q = 1`, and summation over
all residue classes), the file proves the two facts that let exponential sums over primes be
evaluated class by class:

* the decomposition `∑_{n ≤ x} Λ(n) f(n) = ∑_a ψ(x; q, a) f(a)` for any weight `f` on `ZMod q`;
* the bound `∑_{a not a unit} ψ(x; q, a) ≤ ω(q) log x` for `x ≥ 1`, since a prime power `pᵏ` is
  not coprime to `q` exactly when `p ∣ q`, and `ψ(x; p, 0) = ⌊log_p x⌋ log p ≤ log x` for a prime
  `p` and `x ≥ 1`.

Together they reduce `∑_{n ≤ x} Λ(n) f(n)` to the reduced classes with an error at most
`ω(q) log x` for `x ≥ 1` when `|f| ≤ 1`, which is how the major arcs of the circle method pass
from the exponential sum `∑_{n ≤ x} Λ(n) e(an/q)` to `ψ(x; q, b)` for units `b`.

## Main definitions

* `Chebyshev.psiAP`, `Chebyshev.thetaAP`, `Chebyshev.primeCountAP`.

## Main results

* `Chebyshev.sum_psiAP`, `Chebyshev.sum_thetaAP`, `Chebyshev.sum_primeCountAP`: summing over all
  residue classes modulo `q ≠ 0` recovers `ψ`, `θ` and `π`.
* `Chebyshev.sum_psiAP_smul`: `∑_a ψ(x; q, a) • f(a) = ∑_{n ≤ x} Λ(n) • f(n)`.
* `Chebyshev.psiAP_zero_of_prime`, `Chebyshev.thetaAP_zero_of_prime`,
  `Chebyshev.primeCountAP_zero_of_prime`: the zero class modulo a prime `p`.
* `Chebyshev.sum_psiAP_not_isUnit_le_card_mul_log`: the non-reduced classes carry at most
  `ω(q) log x` for `x ≥ 1`.
* `Chebyshev.norm_sum_vonMangoldt_smul_sub_sum_psiAP_smul_le`: restricting the decomposition to
  the reduced classes costs at most `ω(q) log x` for `x ≥ 1` and a weight bounded by `1`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., GTM 74, Chapter 20 (the functions
  `ψ(x; q, a)`) and Chapter 26 (their use on the major arcs).
-/

public section

open Finset ArithmeticFunction
open scoped Chebyshev Nat.Prime

namespace Chebyshev

/-- The von Mangoldt sum `ψ(x; q, a) = ∑_{1 ≤ n ≤ x, n ≡ a (mod q)} Λ(n)` over a residue class. -/
noncomputable def psiAP (q : ℕ) (a : ZMod q) (x : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊ with ((n : ℕ) : ZMod q) = a, Λ n

/-- The Chebyshev sum `θ(x; q, a) = ∑_{p ≤ x prime, p ≡ a (mod q)} log p` over a residue class. -/
noncomputable def thetaAP (q : ℕ) (a : ZMod q) (x : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊x⌋₊ with ((p : ℕ) : ZMod q) = a, Real.log p

/-- The number `π(x; q, a)` of primes `p ≤ x` with `p ≡ a (mod q)`. -/
noncomputable def primeCountAP (q : ℕ) (a : ZMod q) (x : ℝ) : ℕ :=
  #{p ∈ Nat.primesLE ⌊x⌋₊ | ((p : ℕ) : ZMod q) = a}

variable {q : ℕ} {a : ZMod q} {x : ℝ}

theorem psiAP_def (q : ℕ) (a : ZMod q) (x : ℝ) :
    psiAP q a x = ∑ n ∈ Ioc 0 ⌊x⌋₊ with ((n : ℕ) : ZMod q) = a, Λ n := (rfl)

theorem thetaAP_def (q : ℕ) (a : ZMod q) (x : ℝ) :
    thetaAP q a x = ∑ p ∈ Nat.primesLE ⌊x⌋₊ with ((p : ℕ) : ZMod q) = a, Real.log p := (rfl)

theorem primeCountAP_def (q : ℕ) (a : ZMod q) (x : ℝ) :
    primeCountAP q a x = #{p ∈ Nat.primesLE ⌊x⌋₊ | ((p : ℕ) : ZMod q) = a} := (rfl)

/-! ### Basic properties -/

theorem psiAP_nonneg (q : ℕ) (a : ZMod q) (x : ℝ) : 0 ≤ psiAP q a x :=
  sum_nonneg fun _ _ ↦ vonMangoldt_nonneg

theorem thetaAP_nonneg (q : ℕ) (a : ZMod q) (x : ℝ) : 0 ≤ thetaAP q a x :=
  sum_nonneg fun p _ ↦ Real.log_natCast_nonneg p

/-- `ψ(x; q, a)` agrees with Mathlib's restriction `ArithmeticFunction.vonMangoldt.residueClass`
of `Λ` to the class `a`, summed over `1 ≤ n ≤ x`. -/
theorem psiAP_eq_sum_residueClass (q : ℕ) (a : ZMod q) (x : ℝ) :
    psiAP q a x = ∑ n ∈ Ioc 0 ⌊x⌋₊, vonMangoldt.residueClass a n := by
  simp [psiAP, sum_filter, Set.indicator_apply]

theorem psiAP_eq_psiAP_coe_floor (q : ℕ) (a : ZMod q) (x : ℝ) :
    psiAP q a x = psiAP q a ⌊x⌋₊ := by
  simp [psiAP]

theorem thetaAP_eq_thetaAP_coe_floor (q : ℕ) (a : ZMod q) (x : ℝ) :
    thetaAP q a x = thetaAP q a ⌊x⌋₊ := by
  simp [thetaAP]

theorem primeCountAP_eq_primeCountAP_coe_floor (q : ℕ) (a : ZMod q) (x : ℝ) :
    primeCountAP q a x = primeCountAP q a ⌊x⌋₊ := by
  simp [primeCountAP]

theorem psiAP_mono (q : ℕ) (a : ZMod q) : Monotone (psiAP q a) := fun _ _ hxy ↦
  sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ <| Ioc_subset_Ioc_right <|
    Nat.floor_mono hxy) fun _ _ _ ↦ vonMangoldt_nonneg

theorem thetaAP_mono (q : ℕ) (a : ZMod q) : Monotone (thetaAP q a) := fun _ _ hxy ↦
  sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ <| Nat.primesLE_mono <| Nat.floor_mono hxy)
    fun p _ _ ↦ Real.log_natCast_nonneg p

theorem primeCountAP_mono (q : ℕ) (a : ZMod q) : Monotone (primeCountAP q a) := fun _ _ hxy ↦
  card_le_card <| filter_subset_filter _ <| Nat.primesLE_mono <| Nat.floor_mono hxy

/-! ### Comparison with the unrestricted functions -/

theorem psiAP_le_psi (q : ℕ) (a : ZMod q) (x : ℝ) : psiAP q a x ≤ ψ x :=
  sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ ↦ vonMangoldt_nonneg

theorem thetaAP_le_theta (q : ℕ) (a : ZMod q) (x : ℝ) : thetaAP q a x ≤ θ x := by
  rw [theta_eq_sum_primesLE]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p _ _ ↦ Real.log_natCast_nonneg p

theorem primeCountAP_le_primeCounting (q : ℕ) (a : ZMod q) (x : ℝ) :
    primeCountAP q a x ≤ π ⌊x⌋₊ :=
  (card_le_card (filter_subset _ _)).trans_eq (Nat.primesLE_card_eq_primeCounting _)

/-- In each residue class the primes contribute at most the prime powers: `θ(x; q, a) ≤ ψ(x; q, a)`.
-/
theorem thetaAP_le_psiAP (q : ℕ) (a : ZMod q) (x : ℝ) : thetaAP q a x ≤ psiAP q a x := by
  rw [thetaAP, psiAP]
  refine (sum_congr rfl fun p hp ↦ ?_).trans_le <| sum_le_sum_of_subset_of_nonneg
    (filter_subset_filter _ fun p hp ↦ ?_) fun _ _ _ ↦ vonMangoldt_nonneg
  · rw [vonMangoldt_apply_prime (Nat.prime_of_mem_primesLE (mem_filter.1 hp).1)]
  · exact mem_Ioc.2 ⟨(Nat.prime_of_mem_primesLE hp).pos, Nat.le_of_mem_primesLE hp⟩

theorem psiAP_eq_zero_of_lt_two (hx : x < 2) : psiAP q a x = 0 :=
  le_antisymm ((psiAP_le_psi q a x).trans_eq (psi_eq_zero_of_lt_two hx)) (psiAP_nonneg q a x)

theorem thetaAP_eq_zero_of_lt_two (hx : x < 2) : thetaAP q a x = 0 :=
  le_antisymm ((thetaAP_le_theta q a x).trans_eq (theta_eq_zero_of_lt_two hx))
    (thetaAP_nonneg q a x)

theorem primeCountAP_eq_zero_of_lt_two (hx : x < 2) : primeCountAP q a x = 0 := by
  have hN : ⌊x⌋₊ < 2 := (Nat.floor_lt' two_ne_zero).2 (mod_cast hx)
  refine card_eq_zero.2 <| filter_eq_empty_iff.2 fun p hp ↦ absurd ?_ hN.not_ge
  exact (Nat.prime_of_mem_primesLE hp).two_le.trans (Nat.le_of_mem_primesLE hp)

/-! ### The trivial modulus and summation over residue classes -/

@[simp]
theorem psiAP_one (a : ZMod 1) (x : ℝ) : psiAP 1 a x = ψ x := by
  rw [psiAP, psi, filter_true_of_mem fun _ _ ↦ Subsingleton.elim _ _]

@[simp]
theorem thetaAP_one (a : ZMod 1) (x : ℝ) : thetaAP 1 a x = θ x := by
  rw [thetaAP, theta_eq_sum_primesLE, filter_true_of_mem fun _ _ ↦ Subsingleton.elim _ _]

@[simp]
theorem primeCountAP_one (a : ZMod 1) (x : ℝ) : primeCountAP 1 a x = π ⌊x⌋₊ := by
  rw [primeCountAP, filter_true_of_mem fun _ _ ↦ Subsingleton.elim _ _,
    Nat.primesLE_card_eq_primeCounting]

/-- Decomposition of a weighted von Mangoldt sum along the residue classes modulo `q ≠ 0`:
`∑_a ψ(x; q, a) • f(a) = ∑_{1 ≤ n ≤ x} Λ(n) • f(n)` for any weight `f` on `ZMod q`. -/
theorem sum_psiAP_smul [NeZero q] {M : Type*} [AddCommMonoid M] [Module ℝ M] (f : ZMod q → M)
    (x : ℝ) : ∑ a, psiAP q a x • f a = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n • f n := by
  simp_rw [psiAP, sum_smul]
  rw [← sum_fiberwise (Ioc 0 ⌊x⌋₊) (fun n : ℕ ↦ (n : ZMod q))]
  exact sum_congr rfl fun a _ ↦ sum_congr rfl fun n hn ↦ by rw [(mem_filter.1 hn).2]

/-- Summing `ψ(x; q, a)` over all residue classes modulo `q ≠ 0` gives `ψ(x)`. -/
theorem sum_psiAP [NeZero q] (x : ℝ) : ∑ a : ZMod q, psiAP q a x = ψ x :=
  sum_fiberwise _ _ _

/-- Summing `θ(x; q, a)` over all residue classes modulo `q ≠ 0` gives `θ(x)`. -/
theorem sum_thetaAP [NeZero q] (x : ℝ) : ∑ a : ZMod q, thetaAP q a x = θ x := by
  rw [theta_eq_sum_primesLE]
  exact sum_fiberwise _ _ _

/-- Summing `π(x; q, a)` over all residue classes modulo `q ≠ 0` gives `π(x)`. -/
theorem sum_primeCountAP [NeZero q] (x : ℝ) : ∑ a : ZMod q, primeCountAP q a x = π ⌊x⌋₊ := by
  simp_rw [primeCountAP, card_eq_sum_ones]
  rw [sum_fiberwise, ← card_eq_sum_ones, Nat.primesLE_card_eq_primeCounting]

/-! ### The zero class modulo a prime -/

/-- Modulo a prime `p`, the zero class contains the single prime `p`:
`θ(x; p, 0) = log p` for `x ≥ p` and `0` otherwise. -/
theorem thetaAP_zero_of_prime {p : ℕ} (hp : p.Prime) (x : ℝ) :
    thetaAP p 0 x = if (p : ℝ) ≤ x then Real.log p else 0 := by
  simp_rw [thetaAP, ZMod.natCast_eq_zero_iff, hp.filter_dvd_primesLE]
  by_cases h : (p : ℝ) ≤ x <;> simp [h, Nat.le_floor_iff' hp.ne_zero]

/-- Modulo a prime `p`, the zero class contains the single prime `p`:
`π(x; p, 0) = 1` for `x ≥ p` and `0` otherwise. -/
theorem primeCountAP_zero_of_prime {p : ℕ} (hp : p.Prime) (x : ℝ) :
    primeCountAP p 0 x = if (p : ℝ) ≤ x then 1 else 0 := by
  simp_rw [primeCountAP, ZMod.natCast_eq_zero_iff, hp.filter_dvd_primesLE]
  by_cases h : (p : ℝ) ≤ x <;> simp [h, Nat.le_floor_iff' hp.ne_zero]

/-- Modulo a prime `p`, the zero class of `ψ` consists of the powers `pᵏ ≤ x` with `k ≥ 1`:
`ψ(x; p, 0) = ⌊log_p x⌋ log p` for `x ≥ 1`, with `Nat.log p ⌊x⌋₊` the number of these powers
(and `0` for `x < 1`). -/
theorem psiAP_zero_of_prime {p : ℕ} (hp : p.Prime) (x : ℝ) :
    psiAP p 0 x = p.log ⌊x⌋₊ * Real.log p := by
  rw [psiAP, sum_filter, ← Icc_add_one_left_eq_Ioc, zero_add,
    Nat.sum_Icc_eq_sum_primesLE_sum_Icc_log fun n hn ↦ by simp [vonMangoldt_eq_zero_iff.2 hn],
    sum_eq_single p (fun r hr hrp ↦ sum_eq_zero fun k _ ↦ ?_) fun hp' ↦ ?_]
  · calc _ = ∑ _ ∈ Icc 1 (p.log ⌊x⌋₊), Real.log p := sum_congr rfl fun k hk ↦ by
          have hk : k ≠ 0 := by simp at hk; lia
          simp [vonMangoldt_apply_pow hk, vonMangoldt_apply_prime hp, hk]
      _ = _ := by simp
  · rw [ite_eq_right_iff, ZMod.natCast_eq_zero_iff]
    exact fun h ↦ absurd ((Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primesLE hr)).1
      (hp.dvd_of_dvd_pow h)).symm hrp
  · rw [Nat.log_of_lt (not_le.1 fun h ↦ hp' (Nat.mem_primesLE.2 ⟨h, hp⟩))]
    simp

/-- The zero class modulo a prime carries at most a logarithm: `ψ(x; p, 0) ≤ log x` for
`x ≥ 1`. -/
theorem psiAP_zero_le_log {p : ℕ} (hp : p.Prime) (hx : 1 ≤ x) : psiAP p 0 x ≤ Real.log x := by
  have hN : 0 < ⌊x⌋₊ := (Nat.one_le_floor_iff x).2 hx
  rw [psiAP_zero_of_prime hp, ← Real.log_pow]
  calc Real.log ((p : ℝ) ^ p.log ⌊x⌋₊) ≤ Real.log ⌊x⌋₊ :=
        Real.log_le_log (by have := hp.pos; positivity) (mod_cast Nat.pow_log_le_self p hN.ne')
    _ ≤ Real.log x := Real.log_le_log (mod_cast hN) (Nat.floor_le (by linarith))

/-! ### The non-reduced residue classes -/

/-- The residue classes modulo `q ≠ 0` that are not units carry no more von Mangoldt mass than
the zero classes modulo the primes dividing `q`. -/
theorem sum_psiAP_not_isUnit_le [NeZero q] (x : ℝ) :
    ∑ a with ¬IsUnit a, psiAP q a x ≤ ∑ p ∈ q.primeFactors, psiAP p 0 x := by
  have hΛ : ∀ n, 0 ≤ Λ n := fun _ ↦ vonMangoldt_nonneg
  calc ∑ a with ¬IsUnit a, psiAP q a x
      = ∑ n ∈ Ioc 0 ⌊x⌋₊, if IsUnit (n : ZMod q) then 0 else Λ n := by
        have := sum_psiAP_smul (fun a : ZMod q ↦ if IsUnit a then (0 : ℝ) else 1) x
        simp only [smul_eq_mul, mul_ite, mul_zero, mul_one] at this
        rw [sum_filter, ← this]
        exact sum_congr rfl fun a _ ↦ by split_ifs <;> rfl
    _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, ∑ p ∈ q.primeFactors, if (n : ZMod p) = 0 then Λ n else 0 := by
        refine sum_le_sum fun n _ ↦ ?_
        have hnonneg : ∀ p ∈ q.primeFactors, 0 ≤ if (n : ZMod p) = 0 then Λ n else 0 :=
          fun p _ ↦ by split_ifs <;> simp [hΛ]
        split_ifs with h
        · exact sum_nonneg hnonneg
        · rw [ZMod.isUnit_iff_coprime] at h
          obtain ⟨p, hp, hpn, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.1 h
          have hmem : p ∈ q.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpq, NeZero.ne q⟩
          refine le_of_eq_of_le ?_ (single_le_sum hnonneg hmem)
          simp [(ZMod.natCast_eq_zero_iff n p).2 hpn]
    _ = ∑ p ∈ q.primeFactors, psiAP p 0 x := by
        rw [sum_comm]
        simp only [psiAP, sum_filter]

/-- The residue classes modulo `q ≠ 0` that are not units carry at most `ω(q) log x` of the von
Mangoldt mass up to `x ≥ 1`: a prime power `pᵏ` fails to be coprime to `q` only when `p ∣ q`. -/
theorem sum_psiAP_not_isUnit_le_card_mul_log [NeZero q] (hx : 1 ≤ x) :
    ∑ a with ¬IsUnit a, psiAP q a x ≤ #q.primeFactors * Real.log x := by
  refine (sum_psiAP_not_isUnit_le x).trans ?_
  rw [← nsmul_eq_mul, ← sum_const]
  exact sum_le_sum fun p hp ↦ psiAP_zero_le_log (Nat.prime_of_mem_primeFactors hp) hx

/-- Restricting the residue-class decomposition `∑_{n ≤ x} Λ(n) • f(n) = ∑_a ψ(x; q, a) • f(a)` to
the reduced classes costs at most `ω(q) log x` for `x ≥ 1` when `‖f(a)‖ ≤ 1` on the non-reduced
classes. -/
theorem norm_sum_vonMangoldt_smul_sub_sum_psiAP_smul_le [NeZero q] {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] {f : ZMod q → E}
    (hf : ∀ a, ¬IsUnit a → ‖f a‖ ≤ 1) (hx : 1 ≤ x) :
    ‖∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n • f n - ∑ a with IsUnit a, psiAP q a x • f a‖ ≤
      #q.primeFactors * Real.log x := by
  rw [← sum_psiAP_smul, ← sum_filter_add_sum_filter_not univ IsUnit, add_sub_cancel_left]
  refine (norm_sum_le _ _).trans <| (sum_le_sum fun a ha ↦ ?_).trans
    (sum_psiAP_not_isUnit_le_card_mul_log hx)
  rw [norm_smul, Real.norm_of_nonneg (psiAP_nonneg q a x)]
  exact mul_le_of_le_one_right (psiAP_nonneg q a x) (hf a (mem_filter.1 ha).2)

/-! ### Examples

A prime power is filed under its own class, not under the class of its prime: `9 ≡ 1 (mod 4)`
enters `ψ(10; 4, 1)`, while `3 ≡ 3 (mod 4)` does not enter `θ(10; 4, 1)`. A non-reduced class
holds only boundedly many primes. -/

example : thetaAP 4 1 10 = Real.log 5 := by
  have : {p ∈ Nat.primesLE ⌊(10 : ℝ)⌋₊ | ((p : ℕ) : ZMod 4) = 1} = {5} := by
    rw [Nat.floor_ofNat]; decide
  rw [thetaAP, this, sum_singleton, Nat.cast_ofNat]

example : psiAP 4 1 10 = Real.log 15 := by
  have : {n ∈ Ioc 0 ⌊(10 : ℝ)⌋₊ | ((n : ℕ) : ZMod 4) = 1} = {1, 5, 9} := by
    rw [Nat.floor_ofNat]; decide
  rw [psiAP, this, sum_insert (by decide), sum_insert (by decide), sum_singleton,
    vonMangoldt_apply_one, vonMangoldt_apply_prime Nat.prime_five, show (9 : ℕ) = 3 ^ 2 from rfl,
    vonMangoldt_apply_pow two_ne_zero, vonMangoldt_apply_prime Nat.prime_three,
    show (15 : ℝ) = 5 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  push_cast; ring

example : psiAP 2 0 4 = 2 * Real.log 2 := by
  rw [psiAP_zero_of_prime Nat.prime_two, Nat.floor_ofNat]
  norm_num [show Nat.log 2 4 = 2 by decide]

example : psiAP 2 0 10 = 3 * Real.log 2 := by
  rw [psiAP_zero_of_prime Nat.prime_two, Nat.floor_ofNat]
  norm_num [show Nat.log 2 10 = 3 by decide]

example : psiAP 1 0 10 = Real.log 2520 := by
  rw [psiAP_one, ← Nat.cast_ofNat, psi_eq_log_lcmUpto,
    show Nat.lcmUpto 10 = 2520 by decide]
  norm_num

example {x : ℝ} (hx : 2 ≤ x) : thetaAP 2 0 x = Real.log 2 := by
  rw [thetaAP_zero_of_prime Nat.prime_two]; simp [hx]

example : primeCountAP 4 3 10 = 2 := by
  rw [primeCountAP, Nat.floor_ofNat]; decide

example : primeCountAP 4 3 7 = 2 := by
  rw [primeCountAP, Nat.floor_ofNat]; decide

example : primeCountAP 4 3 (6.9 : ℝ) = 1 := by
  rw [primeCountAP, show ⌊(6.9 : ℝ)⌋₊ = 6 by norm_num [Nat.floor_eq_iff]]; decide

example : primeCountAP 2 0 100 = 1 := by
  rw [primeCountAP_zero_of_prime Nat.prime_two]; norm_num

end Chebyshev
