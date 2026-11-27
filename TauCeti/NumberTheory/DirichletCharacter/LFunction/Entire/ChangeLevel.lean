/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Entire
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel

/-!
# Pole removal and change of level

Raising the level without introducing a new prime divisor leaves both the entire and
regularized Dirichlet L-functions unchanged, including at `1`. In particular, estimates for
these functions can be transferred between powers of the same base modulus.
-/

public section

namespace DirichletCharacter

/-- Raising the level without introducing a new prime divisor leaves the entire Dirichlet
L-function unchanged, including the pole-cleared value at `1` for a principal character. -/
theorem entireLFunction_changeLevel_eq_of_primeFactors_eq {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (hMN : M ∣ N) (h : N.primeFactors = M.primeFactors) :
    (χ.changeLevel hMN).entireLFunction = χ.entireLFunction := by
  rcases eq_or_ne χ 1 with rfl | hχ
  · refine Continuous.ext_on (dense_compl_singleton (1 : ℂ))
      ((changeLevel hMN (1 : DirichletCharacter ℂ M)).differentiable_entireLFunction.continuous)
      ((1 : DirichletCharacter ℂ M).differentiable_entireLFunction.continuous) ?_
    intro z hz
    have hz' : z ≠ 1 := hz
    have hL := (1 : DirichletCharacter ℂ M).LFunction_changeLevel_eq_of_primeFactors_eq
      hMN h (.inr hz')
    rw [map_one] at hL ⊢
    rw [entireLFunction_one_apply hz', entireLFunction_one_apply hz', hL]
  · have hlift : χ.changeLevel hMN ≠ 1 := fun he ↦ hχ ((changeLevel_eq_one_iff hMN).mp he)
    rw [entireLFunction_of_ne_one hlift, entireLFunction_of_ne_one hχ]
    funext z
    exact χ.LFunction_changeLevel_eq_of_primeFactors_eq hMN h (.inl hχ)

/-- Raising the level without introducing a new prime divisor leaves the regularized Dirichlet
L-function unchanged. -/
theorem regularizedLFunction_changeLevel_eq_of_primeFactors_eq {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (hMN : M ∣ N) (h : N.primeFactors = M.primeFactors) :
    (χ.changeLevel hMN).regularizedLFunction = χ.regularizedLFunction := by
  have hE := χ.entireLFunction_changeLevel_eq_of_primeFactors_eq hMN h
  rcases eq_or_ne χ 1 with rfl | hχ
  · rw [map_one] at hE ⊢
    funext z
    rw [regularizedLFunction_one_apply, regularizedLFunction_one_apply, hE]
  · have hlift : χ.changeLevel hMN ≠ 1 := fun he ↦ hχ ((changeLevel_eq_one_iff hMN).mp he)
    simpa only [regularizedLFunction_of_ne_one _ hlift, regularizedLFunction_of_ne_one _ hχ,
      entireLFunction_of_ne_one hlift, entireLFunction_of_ne_one hχ] using hE

end DirichletCharacter
