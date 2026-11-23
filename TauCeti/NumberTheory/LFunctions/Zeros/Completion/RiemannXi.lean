/-
Copyright (c) 2026 Matteo Cipollina and The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Dirichlet.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Basic

/-!
# The Riemann ξ-function

Riemann's ξ-function is `ξ(s) = 1/2 + (1/2) s (s - 1) Λ₀(s)`, where `Λ₀` is Mathlib's entire
pole-subtracted completion `completedRiemannZeta₀`. It is the entire extension of
`(1/2) s (s - 1) π^(-s/2) Γ(s/2) ζ(s)` across the poles of the completed zeta function, rather
than the pointwise product, which would vanish at `0` and `1`: here `ξ(0) = ξ(1) = 1/2`.

## Main results

* `TauCeti.LFunctions.riemannXi`: the function `ξ`.
* `TauCeti.LFunctions.differentiable_riemannXi`: `ξ` is entire.
* `TauCeti.LFunctions.riemannXi_one_sub`: the reflection `ξ(1 - s) = ξ(s)`.
* `TauCeti.LFunctions.riemannXi_eq_mul_completedRiemannZeta`,
  `TauCeti.LFunctions.riemannXi_eq_mul_Gammaℝ_mul_riemannZeta`: the product formulas away from
  the poles.
* `TauCeti.LFunctions.two_mul_riemannXi_eq_dirichletData_entireCompletion`: `2ξ` is the entire
  completion of the L-function record of the character modulo `1`.
* The values `ξ(0) = ξ(1) = 1/2` and `ξ(2) = ξ(-1) = π/6`, the latter using
  `TauCeti.completedRiemannZeta_two`.

## References

* K. S. Kedlaya, *Notes on analytic number theory*, §5.1.

This file is adapted from the Prime Number Theorem and more project by Alex Kontorovich,
Terence Tao and contributors, specifically
`PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/CompletedXi.lean` and
`PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannZetaValues.lean`; the proofs here
are rerouted through `zetaEntireCompletion`.
-/

public section

open Complex
open scoped Real

namespace TauCeti

namespace LFunctions

/-- Riemann's ξ-function `ξ(s) = (s (s - 1) Λ₀(s) + 1) / 2`, the entire extension of
`(1/2) s (s - 1) Λ(s)` across the poles of `Λ = completedRiemannZeta` at `0` and `1`. -/
noncomputable def riemannXi (s : ℂ) : ℂ :=
  (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

theorem riemannXi_def (s : ℂ) :
    riemannXi s = (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2 := (rfl)

/-- Twice the ξ-function is the explicit entire completion of zeta. -/
theorem two_mul_riemannXi (s : ℂ) : 2 * riemannXi s = zetaEntireCompletion s := by
  rw [riemannXi_def, zetaEntireCompletion_def]
  ring

/-- `2ξ` is the entire completion of the L-function record of the character modulo `1`. This
is an identity of entire functions, valid also at `0` and `1`. -/
theorem two_mul_riemannXi_eq_dirichletData_entireCompletion (χ : DirichletCharacter ℂ 1)
    (hχ : χ.IsPrimitive) (s : ℂ) :
    2 * riemannXi s = (dirichletData χ hχ).entireCompletion s := by
  rw [dirichletData_modOne, riemannZetaData_entireCompletion, two_mul_riemannXi]

/-- The ξ-function is entire. -/
theorem differentiable_riemannXi : Differentiable ℂ riemannXi := by
  have h : riemannXi = fun s ↦ zetaEntireCompletion s / 2 := by
    funext s
    rw [← two_mul_riemannXi]
    ring
  rw [h]
  exact differentiable_zetaEntireCompletion.div_const 2

/-- The reflection `ξ(1 - s) = ξ(s)`. -/
theorem riemannXi_one_sub (s : ℂ) : riemannXi (1 - s) = riemannXi s := by
  apply mul_left_cancel₀ (two_ne_zero' ℂ)
  rw [two_mul_riemannXi, two_mul_riemannXi, zetaEntireCompletion_one_sub]

/-- Away from `0` and `1`, `ξ(s) = s (s - 1) Λ(s) / 2`. -/
theorem riemannXi_eq_mul_completedRiemannZeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = s * (s - 1) * completedRiemannZeta s / 2 := by
  rw [← zetaEntireCompletion_eq_mul hs0 hs1, ← two_mul_riemannXi]
  ring

/-- Away from `1` and the poles `0, -2, -4, …` of `Γ_ℝ`,
`ξ(s) = s (s - 1) π^(-s/2) Γ(s/2) ζ(s) / 2`. -/
theorem riemannXi_eq_mul_Gammaℝ_mul_riemannZeta {s : ℂ} (hs1 : s ≠ 1)
    (hs : ∀ n : ℕ, s ≠ -(2 * n)) :
    riemannXi s = s * (s - 1) * (Gammaℝ s * riemannZeta s) / 2 := by
  have hΓ : Gammaℝ s ≠ 0 := fun h ↦
    let ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp h
    hs n hn
  have hs0 : s ≠ 0 := by simpa using hs 0
  rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1, riemannZeta_def_of_ne_zero hs0,
    mul_div_cancel₀ _ hΓ]

@[simp]
theorem riemannXi_zero : riemannXi 0 = 1 / 2 := by
  simp [riemannXi_def]

@[simp]
theorem riemannXi_one : riemannXi 1 = 1 / 2 := by
  simp [riemannXi_def]

@[simp]
theorem riemannXi_two : riemannXi 2 = (π : ℂ) / 6 := by
  rw [riemannXi_eq_mul_completedRiemannZeta two_ne_zero (by norm_num), completedRiemannZeta_two]
  ring

@[simp]
theorem riemannXi_neg_one : riemannXi (-1) = (π : ℂ) / 6 := by
  rw [← riemannXi_one_sub]
  norm_num

end LFunctions

end TauCeti
