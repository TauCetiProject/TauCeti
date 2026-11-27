/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Algebra.BigOperators.Intervals
import TauCeti.Analysis.SpecialFunctions.Pow.IntervalKernel
import TauCeti.Analysis.SpecificLimits.NatHalving
import TauCeti.NumberTheory.DirichletCharacter.LFunction.VonMangoldt

/-!
# From half-interval to full-range Dirichlet explicit formulas

A half-interval estimate for the character-weighted von Mangoldt sum can be applied repeatedly
with the *same* finite zero sum and truncation height. The main terms telescope after rounding
the lower endpoints of the intervals. The losses consist of the summed block errors, the
rounding cost proportional to total multiplicity, and the initial Chebyshev sum below the last
cutoff. The interval kernel is kept intact at each endpoint comparison, even for zeros close to
zero. For the application to the prime number theorem with a possible exceptional term, see
Iwaniec and Kowalski, *Analytic Number Theory*, Theorem 5.27.
-/

public section

open Finset ArithmeticFunction

namespace DirichletCharacter

/-- Assemble half-interval formulas with height `T` above an integer cutoff `k₀` into a formula
for all indices up to `X`. The same finite set `Z` of spectral points and multiplicities `m`
must be used in each block. The final low endpoint is the first integer halving below
`max k₀ T`. The factor `J / 2 + 1` pays at most half a unit per block and one unit at `X`; its
coefficient counts spectral points with multiplicity. The theorem is an error transfer and
makes no assertion about the availability of the half-interval formula or of a zero count. -/
theorem exists_norm_sum_mul_vonMangoldt_add_zero_sum_le_of_half_interval {N k₀ : ℕ}
    (χ : DirichletCharacter ℂ N) (Z : Finset ℂ) (m : ℂ → ℕ) {X T C : ℝ}
    (hX : 1 ≤ X) (hT : 0 ≤ T) (hK : 2 ≤ max k₀ ⌈T⌉₊) (hC : 0 ≤ C)
    (hZ : ∀ ρ ∈ Z, ρ.re ≤ 1)
    (hblock : ∀ k : ℕ, k₀ ≤ k → T ≤ k → k ≤ ⌊X⌋₊ →
      ‖(∑ n ∈ Ioc (k / 2) k, χ n * (Λ n : ℂ)) +
        ∑ ρ ∈ Z, (m ρ : ℂ) * (((k : ℂ) ^ ρ - ((k : ℂ) / 2) ^ ρ) / ρ)‖ ≤
        C * ((k : ℝ) / T + 1) * Real.log ((N : ℝ) * k) ^ 2) :
    ∃ J : ℕ, J ≤ Nat.log 2 ⌊X⌋₊ ∧
      (∀ j < J, max k₀ ⌈T⌉₊ ≤ ⌊X⌋₊ / 2 ^ j) ∧
      1 ≤ ⌊X⌋₊ / 2 ^ J ∧ ((⌊X⌋₊ / 2 ^ J : ℕ) : ℝ) < max (k₀ : ℝ) T ∧
      ‖(∑ n ∈ Ioc 0 ⌊X⌋₊, χ n * (Λ n : ℂ)) +
        ∑ ρ ∈ Z, (m ρ : ℂ) * (((X : ℂ) ^ ρ - ((⌊X⌋₊ / 2 ^ J : ℕ) : ℂ) ^ ρ) / ρ)‖ ≤
        C * (2 * X / T + J) * Real.log ((N : ℝ) * X) ^ 2 +
          (∑ ρ ∈ Z, (m ρ : ℝ)) * ((J : ℝ) / 2 + 1) +
          (Real.log 4 + 4) * max (k₀ : ℝ) T := by
  let S (k : ℕ) := ∑ n ∈ Ioc 0 k, χ n * (Λ n : ℂ)
  let F (x : ℝ) := ∑ ρ ∈ Z, (m ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)
  let B := C * Real.log ((N : ℝ) * X) ^ 2
  have hF_sub (a b : ℝ) : F b - F a =
      ∑ ρ ∈ Z, (m ρ : ℂ) * (((b : ℂ) ^ ρ - (a : ℂ) ^ ρ) / ρ) := by
    simp only [F, ← sum_sub_distrib, mul_sub, sub_div]
  have hF (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
      ‖F b - F a‖ ≤ (∑ ρ ∈ Z, (m ρ : ℝ)) * (b - a) := by
    rw [hF_sub, sum_mul]
    refine (norm_sum_le _ _).trans (sum_le_sum fun ρ hρ ↦ ?_)
    rw [norm_mul, Complex.norm_natCast]
    gcongr
    exact Complex.norm_ofReal_cpow_sub_ofReal_cpow_div_le_sub ha hab (hZ ρ hρ)
  have hblock' (k : ℕ) (hk : max k₀ ⌈T⌉₊ ≤ k) (hkX : k ≤ ⌊X⌋₊) :
      ‖S k - S (k / 2) + (F k - F ((k : ℝ) / 2))‖ ≤ B / T * k + B := by
    have hS : S k - S (k / 2) = ∑ n ∈ Ioc (k / 2) k, χ n * (Λ n : ℂ) :=
      sub_eq_of_eq_add' (sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.div_le_self ..)).symm
    have hk₁ : 1 ≤ k := by omega
    have hkX' : (k : ℝ) ≤ X := (Nat.cast_le.mpr hkX).trans (Nat.floor_le (by linarith))
    rw [hS, hF_sub, Complex.ofReal_natCast, Complex.ofReal_div, Complex.ofReal_natCast,
      Complex.ofReal_ofNat]
    refine (hblock k ((le_max_left ..).trans hk) (Nat.ceil_le.mp ((le_max_right ..).trans hk))
      hkX).trans ?_
    have hlog : Real.log ((N : ℝ) * k) ^ 2 ≤ Real.log ((N : ℝ) * X) ^ 2 := by
      by_cases hN : N = 0
      · simp [hN]
      have hNk : 1 ≤ (N : ℝ) * k := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hN (by omega)))
      gcongr
      exact Real.log_nonneg hNk
    calc
      _ ≤ C * ((k : ℝ) / T + 1) * Real.log ((N : ℝ) * X) ^ 2 := by gcongr
      _ = _ := by dsimp [B]; ring
  obtain ⟨J, hJ, hbefore, hpos, hstop, herr⟩ := TauCeti.exists_norm_halving_error_le S F hX hK
    (div_nonneg (mul_nonneg hC (sq_nonneg _)) hT) hF hblock'
  have hstop' : ((⌊X⌋₊ / 2 ^ J : ℕ) : ℝ) < max (k₀ : ℝ) T := by
    rcases lt_max_iff.mp hstop with hk | ht
    · exact lt_max_of_lt_left (Nat.cast_lt.mpr hk)
    · exact lt_max_of_lt_right (Nat.lt_ceil.mp ht)
  refine ⟨J, hJ, hbefore, hpos, hstop', ?_⟩
  have hlow : ‖S (⌊X⌋₊ / 2 ^ J)‖ ≤ (Real.log 4 + 4) * max (k₀ : ℝ) T := calc
    _ ≤ Chebyshev.psi ((⌊X⌋₊ / 2 ^ J : ℕ) : ℝ) := by
      simpa only [S, Nat.floor_natCast] using χ.norm_sum_mul_vonMangoldt_le_psi (⌊X⌋₊ / 2 ^ J : ℕ)
    _ ≤ _ := (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _)).trans (by gcongr)
  calc
    _ = ‖(S ⌊X⌋₊ - S (⌊X⌋₊ / 2 ^ J) + (F X - F ↑(⌊X⌋₊ / 2 ^ J))) +
        S (⌊X⌋₊ / 2 ^ J)‖ := by rw [hF_sub]; congr 1; dsimp only [S]; push_cast; abel
    _ ≤ _ := (norm_add_le ..).trans ((add_le_add herr hlow).trans (by dsimp [B]; ring_nf; rfl))

end DirichletCharacter
