/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.RingTheory.Radical.NatInt
public import TauCeti.NumberTheory.DirichletCharacter.IntervalSum
import Mathlib.Analysis.Normed.Group.Int
import Mathlib.Data.Int.CardIntervalMod
import TauCeti.Data.Nat.Factorization.Basic
import TauCeti.Data.ZMod.Units
import TauCeti.NumberTheory.ArithmeticFunction.Moebius
import TauCeti.NumberTheory.DirichletCharacter.Conductor

/-!
# Interval sums of induced Dirichlet characters

On raising the level from `c` to `q`, the only additional zeros come from primes dividing `q`
but not `c`. Möbius inversion over their product expresses the induced interval sum as a
finite combination of interval sums at the inducing level. In particular, a bound for the
maximal interval sum at the conductor transfers with a factor of two per additional prime.

The argument is the reduction to primitive characters in Montgomery and Vaughan,
*Multiplicative Number Theory I: Classical Theory* (2007), §9.4.
-/

public section

open Finset UniqueFactorizationMonoid
open scoped ArithmeticFunction.Moebius ArithmeticFunction.omega

namespace DirichletCharacter

/-- Raising the level from `c` to a nonzero multiple `q` sieves out exactly the primes of `q`
not dividing `c`. The squarefree modulus of that sieve is `radical q / gcd (radical q) c`. -/
theorem changeLevel_intCast_eq_ite_coprime {R : Type*} [CommMonoidWithZero R] {c q : ℕ}
    [NeZero q] (χ : DirichletCharacter R c) (hcq : c ∣ q) (n : ℤ) :
    changeLevel hcq χ (n : ZMod q) =
      if n.natAbs.Coprime (radical q / (radical q).gcd c) then χ (n : ZMod c) else 0 := by
  have hu (m : ℕ) : IsUnit (n : ZMod m) ↔ n.natAbs.Coprime m := by
    rw [Int.isUnit_intCast_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast, Nat.Coprime]
  have hrq : radical q / (radical q).gcd c ∣ q :=
    (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)).trans radical_dvd_self
  by_cases hq : n.natAbs.Coprime q
  · rw [ite_eq_left (hq.coprime_dvd_right hrq)]
    exact changeLevel_eq_cast_of_dvd' χ hcq
      ((ZMod.isUnit_intCast_iff_isCoprime _ _).mp ((hu q).mpr hq)).symm
  rw [(changeLevel hcq χ).map_nonunit (mt (hu q).mp hq)]
  split_ifs with hr
  · symm
    refine χ.map_nonunit fun hu' ↦ hq ?_
    have h := hr.mul_right (((hu c).mp hu').coprime_dvd_right (Nat.gcd_dvd_right (radical q) c))
    rwa [Nat.div_mul_cancel (Nat.gcd_dvd_left _ _), Nat.radical_eq_prod_primeFactors,
      Nat.coprime_prod_primeFactors_right_iff (NeZero.ne q)] at h
  · rfl

/-- The interval sum of an induced character is a sum of dilated interval sums of the inducing
character, with coefficients `μ(d) χ(d)` over the divisors of the product of the extra primes.
The endpoints are divided using integer floor division, including for negative endpoints. -/
theorem intervalSum_changeLevel_eq_sum_divisors {R : Type*} [CommRing R] {c q : ℕ} [NeZero q]
    (χ : DirichletCharacter R c) (hcq : c ∣ q) (M : ℤ) (H : ℕ) :
    let r := radical q / (radical q).gcd c
    (changeLevel hcq χ).intervalSum M H =
      ∑ d ∈ r.divisors, (μ d : R) * χ d * ∑ k ∈ Ioc (M / d) ((M + H) / d), χ k := by
  intro r
  have hsq : Squarefree r := squarefree_radical.squarefree_of_dvd
    (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
  rw [intervalSum_def]
  simp_rw [χ.changeLevel_intCast_eq_ite_coprime hcq]
  rw [← sum_filter,
    ArithmeticFunction.sum_filter_natAbs_coprime_eq_sum_divisors_smul _ _ hsq.ne_zero]
  refine sum_congr rfl fun d hd ↦ ?_
  have hdpos : 0 < (d : ℤ) := by exact_mod_cast Nat.pos_of_mem_divisors hd
  rw [Int.Ioc_filter_dvd_eq _ _ hdpos, sum_map]
  simp only [Function.Embedding.coeFn_mk, Int.cast_mul, Int.cast_natCast,
    Rat.floor_intCast_div_natCast, map_mul, ← sum_mul, zsmul_eq_mul]
  ring

/-- The maximal interval sum at a raised level is bounded by that of the inducing nonprincipal
character, with one factor of two for each extra prime of the new level. -/
theorem maxIntervalSum_changeLevel_le {F : Type*} [NormedField F] {c q : ℕ} [NeZero c]
    [NeZero q] (χ : DirichletCharacter F c) (hcq : c ∣ q) (hχ : χ ≠ 1) :
    (changeLevel hcq χ).maxIntervalSum ≤
      2 ^ ω (radical q / (radical q).gcd c) * χ.maxIntervalSum := by
  let r := radical q / (radical q).gcd c
  have hsq : Squarefree r := squarefree_radical.squarefree_of_dvd
    (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
  refine (maxIntervalSum_le_iff (changeLevel_eq_one_iff hcq |>.not.mpr hχ)).mpr fun M H ↦ ?_
  rw [χ.intervalSum_changeLevel_eq_sum_divisors hcq]
  have hcard : r.divisors.card = 2 ^ ω r := by
    rw [Nat.card_divisors hsq.ne_zero, ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors]
    calc
      _ = ∏ _ ∈ r.primeFactors, 2 := prod_congr rfl fun p hp ↦ by
        rw [Nat.factorization_eq_one_of_squarefree hsq (Nat.prime_of_mem_primeFactors hp)
          (Nat.dvd_of_mem_primeFactors hp)]
      _ = _ := by simp
  calc
    _ ≤ ∑ _ ∈ r.divisors, χ.maxIntervalSum := by
      apply (norm_sum_le _ _).trans
      refine sum_le_sum fun d hd ↦ ?_
      have hdpos : 0 < (d : ℤ) := by exact_mod_cast Nat.pos_of_mem_divisors hd
      have hle : M / (d : ℤ) ≤ (M + (H : ℤ)) / d := Int.ediv_le_ediv hdpos (by omega)
      have hlen := Int.toNat_of_nonneg (sub_nonneg.mpr hle)
      have hsum : (∑ k ∈ Ioc (M / (d : ℤ)) ((M + H) / d), χ k) =
          χ.intervalSum (M / d) (((M + H) / d - M / d : ℤ).toNat) := by
        rw [intervalSum_def, hlen]
        congr 2
        omega
      rw [hsum, mul_assoc, ← zsmul_eq_mul]
      refine (norm_zsmul_le _ _).trans ?_
      rw [norm_mul]
      calc
        _ ≤ 1 * (1 * χ.maxIntervalSum) := by
          gcongr
          · rw [Int.norm_eq_abs]
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
          · exact χ.norm_le_one _
          · exact norm_intervalSum_le_maxIntervalSum hχ _ _
        _ = _ := by simp
    _ = _ := by simp [hcard, nsmul_eq_mul, r]

/-- Reduction to the conductor: the maximal interval sum of a nonprincipal character is at
most the inducing primitive character's maximal interval sum times `2^ω(r)`, where `r` is the
product of primes of the level not dividing the conductor. -/
theorem maxIntervalSum_le_primitiveCharacter {F : Type*} [NormedField F] {q : ℕ} [NeZero q]
    (χ : DirichletCharacter F q) (hχ : χ ≠ 1) :
    let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    let r := radical q / (radical q).gcd χ.conductor
    χ.maxIntervalSum ≤ 2 ^ ω r * χ.primitiveCharacter.maxIntervalSum := by
  intro _
  simpa only [changeLevel_primitiveCharacter] using
    χ.primitiveCharacter.maxIntervalSum_changeLevel_le χ.conductor_dvd_level
      (mt χ.primitiveCharacter_eq_one_iff.mp hχ)

end DirichletCharacter
