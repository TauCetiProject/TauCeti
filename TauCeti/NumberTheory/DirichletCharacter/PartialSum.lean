/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Data.Nat.Periodic
import TauCeti.Analysis.SpecificLimits.Normed
import TauCeti.Data.Nat.Factorization.Basic
import TauCeti.Data.Nat.Interval
import TauCeti.Data.ZMod.FinEquiv

/-!
# Partial sums of nonprincipal Dirichlet characters

The sum of a nonprincipal character over a full period vanishes. Consequently its partial
sums depend only on the endpoint modulo the level, and for characters valued in a normed
field their norms are bounded by the level, hence are `O(1)` at infinity. This cancellation is
the input to partial summation estimates for continued Dirichlet L-functions.

Bounds on partial sums survive sieving: if every partial sum `∑ n ∈ Icc 1 K, χ n` has norm at
most `B`, then every partial sum over the `n` prime to `m` has norm at most `2 ^ ω m * B`
(`DirichletCharacter.norm_sum_Icc_filter_coprime_le_two_pow_mul`). Removing the multiples of one
prime `p` subtracts `χ p` times a partial sum of the same kind up to `K / p`. This turns bounds for
a primitive character into bounds for the imprimitive characters it induces.
-/

public section

open Finset Filter Asymptotics

namespace DirichletCharacter

variable {N : ℕ}

section Level

variable [NeZero N]

/-- The sum of a nonprincipal character over a full period vanishes. -/
theorem sum_range_level_eq_zero {R : Type*} [CommRing R] [IsDomain R]
    (χ : DirichletCharacter R N) (hχ : χ ≠ 1) : ∑ k ∈ range N, χ k = 0 := by
  rw [← Fin.sum_univ_eq_sum_range]
  simpa only [RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, ZMod.finEquiv_apply] using
    ((ZMod.finEquiv N).toEquiv.sum_comp χ).trans (MulChar.sum_eq_zero_of_ne_one hχ)

/-- The partial sum of a nonprincipal character depends only on the endpoint modulo its level. -/
theorem sum_range_eq_sum_range_mod {R : Type*} [CommRing R] [IsDomain R]
    (χ : DirichletCharacter R N) (hχ : χ ≠ 1) (n : ℕ) :
    ∑ k ∈ range n, χ k = ∑ k ∈ range (n % N), χ k := by
  have hperiod : Function.Periodic (fun n : ℕ ↦ ∑ k ∈ range n, χ k) N := by
    intro n
    dsimp only
    rw [add_comm n N, sum_range_add, χ.sum_range_level_eq_zero hχ, zero_add]
    simp
  exact (hperiod.map_mod_nat n).symm

/-- Partial sums of a nonprincipal character valued in a normed field are bounded by its level,
independently of the endpoint. -/
theorem norm_sum_Icc_le_level {F : Type*} [NormedField F]
    (χ : DirichletCharacter F N) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Icc 1 n, χ k‖ ≤ (N : ℝ) := by
  have hsum : ∑ k ∈ Icc 1 n, χ k = ∑ k ∈ range (n + 1), χ k := by
    rw [Nat.range_succ_eq_Icc_zero, ← insert_Icc_add_one_left_eq_Icc n.zero_le]
    simp [χ.map_zero' (by rintro rfl; exact hχ (Subsingleton.elim _ _))]
  rw [hsum, χ.sum_range_eq_sum_range_mod hχ]
  calc
    _ ≤ ∑ _ ∈ range ((n + 1) % N), (1 : ℝ) :=
      (norm_sum_le _ _).trans (sum_le_sum fun k _ ↦ χ.norm_le_one k)
    _ ≤ (N : ℝ) := by simpa using (Nat.cast_le.mpr (Nat.mod_lt (n + 1) (NeZero.pos N)).le :
      (((n + 1) % N : ℕ) : ℝ) ≤ N)

/-- Partial sums of a nonprincipal character valued in a normed field are `O(1)` at infinity. -/
theorem isBigO_sum_Icc_one {F : Type*} [NormedField F]
    (χ : DirichletCharacter F N) (hχ : χ ≠ 1) :
    (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, χ k) =O[atTop] fun _ ↦ (1 : ℝ) :=
  isBigO_iff.mpr ⟨N, Eventually.of_forall fun n ↦ by simpa using χ.norm_sum_Icc_le_level hχ n⟩

end Level

/-- A level-zero Dirichlet character contributes only at `1` on the naturals, so its
weighted sum vanishes if the weight vanishes at `1`. -/
theorem sum_mul_eq_zero_of_level_zero {R : Type*} [CommSemiring R]
    (χ : DirichletCharacter R 0) (s : Finset ℕ) (f : ℕ → R) (hf : f 1 = 0) :
    ∑ n ∈ s, χ n * f n = 0 := by
  refine sum_eq_zero fun n _ ↦ ?_
  by_cases hn : n = 1
  · simp only [hn, hf, mul_zero]
  · have hunit : ¬ IsUnit (n : ZMod 0) := by
      simpa only [ZMod.isUnit_iff_coprime, Nat.coprime_zero_right] using hn
    rw [χ.map_nonunit hunit, zero_mul]

/-- The partial sums of `χ(n) log n / n` are uniformly bounded for any nonprincipal
complex Dirichlet character. -/
theorem exists_norm_sum_mul_log_div_le (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ B : ℝ, ∀ m : ℕ, ‖∑ n ∈ Ioc 0 m, χ n * (Real.log n : ℂ) / (n : ℂ)‖ ≤ B := by
  by_cases hN : N = 0
  · subst N
    refine ⟨0, fun m ↦ ?_⟩
    simp_rw [mul_div_assoc]
    rw [χ.sum_mul_eq_zero_of_level_zero (Ioc 0 m) (fun n ↦ (Real.log n : ℂ) / n) (by simp),
      norm_zero]
  let _ : NeZero N := ⟨hN⟩
  let w (n : ℕ) : ℝ := Real.log n / (n : ℝ)
  have hanti : AntitoneOn w (Set.Ioi 2) := by
    intro a ha b hb hab
    have hmem (n : ℕ) (hn : n ∈ Set.Ioi 2) : (n : ℝ) ∈ Set.Ici (Real.exp 1) := by
      have hn' : 3 ≤ n := Nat.succ_le_of_lt (Set.mem_Ioi.mp hn)
      exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hn')
    exact Real.log_div_self_antitoneOn (hmem a ha) (hmem b hb) (by exact_mod_cast hab)
  have htail (m : ℕ) := TauCeti.norm_sum_Ioc_smul_le (a := fun n ↦ χ n) hanti
    (fun n hn ↦ div_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.one_le_of_lt hn)))
      (Nat.cast_nonneg n)) (χ.norm_sum_Icc_le_level hχ) m
  have hw (n : ℕ) : w n • χ n = χ n * (Real.log n : ℂ) / (n : ℂ) := by
    simp only [w, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  simp only [hw] at htail
  refine ⟨(∑ n ∈ Ioc (0 : ℕ) 2, ‖χ n * (Real.log n : ℂ) / (n : ℂ)‖) + 2 * N * w 3, fun m ↦ ?_⟩
  by_cases hm : 2 ≤ m
  · rw [← sum_Ioc_consecutive _ (by decide : 0 ≤ 2) hm]
    exact (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) (htail m))
  · refine ((norm_sum_le _ _).trans (sum_le_sum_of_subset_of_nonneg
      (Ioc_subset_Ioc_right (le_of_not_ge hm)) fun _ _ _ ↦ norm_nonneg _)).trans ?_
    exact le_add_of_nonneg_right (by positivity)

section Sieve

open scoped ArithmeticFunction.omega

variable {F : Type*} [NormedField F]

/-- Sieving the partial sums of `χ` by a finite set `s` of primes: one prime at a time, removing
the multiples of `p` subtracts `χ p` times a sieved partial sum up to `K / p`. -/
private lemma norm_sum_Icc_filter_forall_not_dvd_le (χ : DirichletCharacter F N) {B : ℝ}
    (hB : ∀ K : ℕ, ‖∑ n ∈ Icc 1 K, χ n‖ ≤ B) {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (K : ℕ) :
    ‖∑ n ∈ Icc 1 K with ∀ p ∈ s, ¬ p ∣ n, χ n‖ ≤ 2 ^ #s * B := by
  induction s using Finset.induction_on generalizing K with
  | empty => simpa using hB K
  | insert p s hps ih =>
    have hp := hs p (mem_insert_self p s)
    have ih' := ih (fun q hq ↦ hs q (mem_insert_of_mem hq))
    have hdvd (k : ℕ) : (∀ q ∈ s, ¬ q ∣ p * k) ↔ ∀ q ∈ s, ¬ q ∣ k := by
      refine forall₂_congr fun q hq ↦ not_congr ⟨fun h ↦ ?_, (Dvd.dvd.mul_left · p)⟩
      refine ((hs q (mem_insert_of_mem hq)).dvd_mul.mp h).resolve_left fun hqp ↦ hps ?_
      rwa [← (Nat.prime_dvd_prime_iff_eq (hs q (mem_insert_of_mem hq)) hp).mp hqp]
    have hmul : χ p * ∑ k ∈ Icc 1 (K / p) with ∀ q ∈ s, ¬ q ∣ k, χ k =
        ∑ n ∈ Icc 1 K with p ∣ n, if ∀ q ∈ s, ¬ q ∣ n then χ n else 0 := by
      rw [Nat.sum_Icc_filter_dvd_eq, sum_filter, mul_sum]
      refine sum_congr rfl fun k _ ↦ ?_
      simp only [hdvd, Nat.cast_mul, map_mul]
      split_ifs <;> simp
    have hsplit : ∑ n ∈ Icc 1 K with ∀ q ∈ insert p s, ¬ q ∣ n, χ n =
        ∑ n ∈ Icc 1 K with ∀ q ∈ s, ¬ q ∣ n, χ n -
          χ p * ∑ k ∈ Icc 1 (K / p) with ∀ q ∈ s, ¬ q ∣ k, χ k := by
      rw [hmul, eq_sub_iff_add_eq, sum_filter, sum_filter, sum_filter, ← sum_add_distrib]
      refine sum_congr rfl fun n _ ↦ ?_
      by_cases hpn : p ∣ n <;> simp [hpn]
    rw [hsplit, card_insert_of_notMem hps, pow_succ]
    calc _ ≤ ‖∑ n ∈ Icc 1 K with ∀ q ∈ s, ¬ q ∣ n, χ n‖ +
          ‖χ p‖ * ‖∑ k ∈ Icc 1 (K / p) with ∀ q ∈ s, ¬ q ∣ k, χ k‖ := by
          rw [← norm_mul]
          exact norm_sub_le _ _
      _ ≤ 2 ^ #s * B + 1 * (2 ^ #s * B) := by
          gcongr
          · exact ih' K
          · exact χ.norm_le_one _
          · exact ih' (K / p)
      _ = _ := by ring

/-- **Sieving bounded character sums.** If every partial sum `∑ n ∈ Icc 1 K, χ n` of a
Dirichlet character valued in a normed field has norm at most `B`, then every partial sum over
the `n` prime to `m` has norm at most `2 ^ ω m * B`. -/
theorem norm_sum_Icc_filter_coprime_le_two_pow_mul (χ : DirichletCharacter F N) {B : ℝ}
    (hB : ∀ K : ℕ, ‖∑ n ∈ Icc 1 K, χ n‖ ≤ B) (m K : ℕ) :
    ‖∑ n ∈ Icc 1 K with n.Coprime m, χ n‖ ≤ 2 ^ ω m * B := by
  rcases eq_or_ne m 0 with rfl | hm
  · -- Only `n = 1` is prime to `0`.
    have h : {n ∈ Icc 1 K | n.Coprime 0} = Icc 1 (min K 1) := by
      ext n
      simp only [mem_filter, mem_Icc, Nat.coprime_zero_right]
      omega
    rw [h, ArithmeticFunction.cardDistinctFactors_zero, pow_zero, one_mul]
    exact hB _
  have hcop (n : ℕ) : n.Coprime m ↔ ∀ p ∈ m.primeFactors, ¬ p ∣ n :=
    Nat.coprime_comm.trans (Nat.coprime_iff_forall_mem_primeFactors_not_dvd hm)
  simp_rw [hcop, ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors]
  exact χ.norm_sum_Icc_filter_forall_not_dvd_le hB (fun p hp ↦ Nat.prime_of_mem_primeFactors hp) K

end Sieve

end DirichletCharacter
