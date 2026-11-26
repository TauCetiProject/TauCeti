/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Entire
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Dirichlet L-functions under level changes with the same prime factors

Increasing the level without introducing new prime factors leaves the entire and regularized
L-functions unchanged. In particular this preserves their values at `1`, where the principal
L-function itself has a pole. The comparison comes from Mathlib's `LFunction_changeLevel`.
-/

open Filter Topology in
/-- Raising the level without adding any prime factors leaves the pole-removed L-function
unchanged, including its value at `1`. -/
public theorem DirichletCharacter.entireLFunction_changeLevel_of_primeFactors_eq
    {M N : ℕ} [NeZero M] [NeZero N] (χ : DirichletCharacter ℂ M) (hMN : M ∣ N)
    (hprimes : N.primeFactors = M.primeFactors) :
    (changeLevel hMN χ).entireLFunction = χ.entireLFunction := by
  have hL (s : ℂ) (hs : s ≠ 1) : (changeLevel hMN χ).LFunction s = χ.LFunction s := by
    rw [LFunction_changeLevel hMN χ (.inr hs), hprimes]
    rw [Finset.prod_eq_one, mul_one]
    intro p hp
    have hχp : χ (p : ZMod M) = 0 := by
      apply χ.map_nonunit
      rw [ZMod.isUnit_iff_coprime, (Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd]
      exact not_not_intro (Nat.dvd_of_mem_primeFactors hp)
    simp [hχp]
  apply AnalyticOnNhd.eq_of_eventuallyEq (z₀ := 2)
    (fun s _ ↦ (changeLevel hMN χ).analyticAt_entireLFunction s)
    (fun s _ ↦ χ.analyticAt_entireLFunction s)
  filter_upwards [eventually_ne_nhds (by norm_num : (2 : ℂ) ≠ 1)] with s hs
  obtain rfl | hχ := eq_or_ne χ 1
  · simpa only [map_one, entireLFunction_one_apply hs] using congrArg ((s - 1) * ·) (hL s hs)
  · simpa only [entireLFunction_of_ne_one hχ,
      entireLFunction_of_ne_one (mt (changeLevel_eq_one_iff hMN).mp hχ)] using hL s hs

/-- Raising the level without adding any prime factors leaves the regularized L-function
unchanged. -/
public theorem DirichletCharacter.regularizedLFunction_changeLevel_of_primeFactors_eq
    {M N : ℕ} [NeZero M] [NeZero N] (χ : DirichletCharacter ℂ M) (hMN : M ∣ N)
    (hprimes : N.primeFactors = M.primeFactors) :
    (changeLevel hMN χ).regularizedLFunction = χ.regularizedLFunction := by
  have hE := χ.entireLFunction_changeLevel_of_primeFactors_eq hMN hprimes
  obtain rfl | hχ := eq_or_ne χ 1
  · simp only [map_one] at hE ⊢
    funext s
    simp only [regularizedLFunction_one_apply, hE]
  · have hχ' := mt (changeLevel_eq_one_iff hMN).mp hχ
    rw [regularizedLFunction_of_ne_one _ hχ', regularizedLFunction_of_ne_one _ hχ]
    simpa only [entireLFunction_of_ne_one hχ, entireLFunction_of_ne_one hχ'] using hE
