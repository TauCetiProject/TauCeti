/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.Transcendental.SchneiderLang.Auxiliary

/-!
# Schneider–Lang auxiliary function normalizations

Single-term examples distinguish the polynomial coordinates from the frequency coordinates
and check that the frequency cutoff scales the exponential growth estimate.
-/

open TauCeti.SchneiderLang

/-- With cutoff zero the sole term is the constant coefficient. -/
example (d₀ d₁ n : ℕ) (h : d₀ ≤ n) (x : Fin d₁ → Fin n → ℂ) (c : ℂ) (z : Fin n → ℂ) :
    auxiliaryFunction h x (Pi.single (0 : AuxiliaryIndex d₀ d₁ 0) c) z = c := by simp

/-- The polynomial factor occupies the first coordinate even when the frequency only uses the
second coordinate. -/
example (z : Fin 2 → ℂ) :
    auxiliaryFunction (by decide : 1 ≤ 2) (fun _ : Fin 1 ↦ ![0, 1])
      (Pi.single ((fun _ ↦ 1, fun _ ↦ 1) : AuxiliaryIndex 1 1 1) 1) z =
      z 0 * Complex.exp (z 1) := by
  have hfirst : Fin.castLE (by decide : 1 ≤ 2) (0 : Fin 1) = 0 := rfl
  have hτ₀ : auxiliaryExponent (by decide : 1 ≤ 2) (fun _ ↦ (1 : Fin 2)) 0 = 1 := by
    rw [← hfirst, auxiliaryExponent_castLE]
    rfl
  simp [auxiliaryFunction_apply_single, hτ₀, Fin.sum_univ_two, Fin.prod_univ_two]

/-- A frequency multiplier of two gives `exp (2 z)` in the absence of polynomial coordinates. -/
example (z : Fin 1 → ℂ) :
    auxiliaryFunction (by decide : 0 ≤ 1) (fun (_ : Fin 1) _ ↦ 1)
      (Pi.single ((0, fun _ ↦ 2) : AuxiliaryIndex 0 1 2) 1) z =
      Complex.exp (2 * z 0) := by
  simp [auxiliaryFunction_apply_single, auxiliaryExponent_eq_zero_of_le]

/-- The same cutoff appears in the growth bound for a unit frequency generator. -/
example (ρ : ℝ) : auxiliaryGrowth 0 1 2 0 1 ρ = 3 * Real.exp (2 * ρ) := by
  norm_num [auxiliaryGrowth_def]
