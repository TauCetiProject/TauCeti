/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Transcendental.AlgebraicLogs

import Mathlib.Analysis.Complex.IsIntegral
import TauCeti.NumberTheory.Transcendental.GelfondSchneider.Gelfond.Theorem

/-!
# Consequences of the Gelfond–Schneider theorem

This file derives the two classical corollaries of the Gelfond–Schneider theorem
`TauCeti.transcendental_exp_mul`, which says that `exp (β λ)` is transcendental whenever `λ ≠ 0`,
`exp λ` is algebraic and `β` is algebraic and irrational.

* Taking `λ = πi` and `β = -iα`: if `α` is algebraic and not a rational multiple of `i`, then
  `exp (π α)` is transcendental. For `α = 1` this is the transcendence of Gelfond's constant
  `e ^ π`.
* Two logarithms of algebraic numbers that are linearly independent over `ℚ` are linearly
  independent over the algebraic numbers. This is the case of two logarithms of Baker's theorem.

Here a logarithm of an algebraic number is an element of the `ℚ`-subspace
`TauCeti.algebraicLogs` of complex numbers `λ` with `exp λ` algebraic; every branch of the
logarithm is allowed.

## Main results

* `TauCeti.transcendental_exp_pi_mul`: `exp (π α)` is transcendental for algebraic `α` that is not
  a rational multiple of `i`.
* `TauCeti.transcendental_exp_pi`: `e ^ π` is transcendental.
* `TauCeti.mul_add_mul_ne_zero_of_linearIndependent`: if `λ₁, λ₂ ∈ 𝓛` are linearly independent
  over `ℚ`, then `β₁ λ₁ + β₂ λ₂ ≠ 0` for algebraic `β₁, β₂`, not both zero.
* `TauCeti.linearIndependent_integralClosure_iff_of_mem_algebraicLogs`: two elements of `𝓛` are
  linearly independent over the algebraic numbers if and only if they are linearly independent
  over `ℚ`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 4, §4.3, Corollaries 4.17
  and 4.18.
* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer (2000),
  §1.1, Theorem 1.4.
-/

public section

open Complex

namespace TauCeti

/-- **Transcendence of `exp (π α)`.** If `α` is an algebraic number that is not a rational
multiple of `i`, then `exp (π α)` is transcendental. -/
theorem transcendental_exp_pi_mul {α : ℂ} (hα : IsAlgebraic ℚ α) (hαI : ∀ q : ℚ, α ≠ q * I) :
    Transcendental ℚ (exp (Real.pi * α)) := by
  -- Apply the Gelfond–Schneider theorem to `λ = πi` and `β = -iα`, so that `β λ = π α`.
  have hl : (Real.pi : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero) I_ne_zero
  have hβ : IsAlgebraic ℚ (-I * α) := (isIntegral_I ℚ).isAlgebraic.neg.mul hα
  have hirr : ∀ q : ℚ, -I * α ≠ q := fun q hq ↦ hαI q (by linear_combination I * hq + α * I_sq)
  have hexp : -I * α * (Real.pi * I) = Real.pi * α := by
    linear_combination (-(Real.pi : ℂ) * α) * I_sq
  simpa only [hexp] using
    transcendental_exp_mul hl (mem_algebraicLogs.1 pi_mul_I_mem_algebraicLogs) hβ hirr

/-- **Gelfond's constant `e ^ π` is transcendental.** -/
theorem transcendental_exp_pi : Transcendental ℚ (Real.exp Real.pi) := by
  rw [← transcendental_algebraMap_iff (algebraMap ℝ ℂ).injective]
  simpa using transcendental_exp_pi_mul isAlgebraic_one fun q h ↦ by simpa using congrArg re h

/-- **Gelfond–Schneider for two logarithms.** If `λ₁, λ₂ ∈ 𝓛` are linearly independent over `ℚ`,
then `β₁ λ₁ + β₂ λ₂ ≠ 0` for all algebraic numbers `β₁, β₂` that are not both zero. -/
theorem mul_add_mul_ne_zero_of_linearIndependent {l₁ l₂ β₁ β₂ : ℂ} (hl₁ : l₁ ∈ algebraicLogs)
    (hl₂ : l₂ ∈ algebraicLogs) (hl : LinearIndependent ℚ ![l₁, l₂]) (hβ₁ : IsAlgebraic ℚ β₁)
    (hβ₂ : IsAlgebraic ℚ β₂) (hβ : β₁ ≠ 0 ∨ β₂ ≠ 0) : β₁ * l₁ + β₂ * l₂ ≠ 0 := by
  intro h
  have h₁ : l₁ ≠ 0 := by simpa using hl.ne_zero 0
  have hβ₂₀ : β₂ ≠ 0 := by
    rintro rfl
    simp_all
  -- Then `λ₂ = β λ₁` with `β = -β₁ / β₂` algebraic.
  set β := -β₁ / β₂ with hβdef
  have hl₂β : l₂ = β * l₁ := by
    rw [hβdef]
    field_simp
    linear_combination h
  by_cases hq : ∃ q : ℚ, β = q
  · -- If `β = q` is rational, then `q λ₁ - λ₂ = 0` contradicts linear independence over `ℚ`.
    obtain ⟨q, hq⟩ := hq
    have := LinearIndependent.pair_iff.1 hl q (-1) (by simp [Rat.smul_def, hl₂β, hq])
    exact absurd this.2 (by norm_num)
  · -- Otherwise `exp (β λ₁) = exp λ₂` is algebraic, contradicting Gelfond–Schneider.
    have hβalg : IsAlgebraic ℚ β := by
      rw [hβdef, div_eq_mul_inv]
      exact hβ₁.neg.mul hβ₂.inv
    rw [mem_algebraicLogs, hl₂β] at hl₂
    exact transcendental_exp_mul h₁ (mem_algebraicLogs.1 hl₁) hβalg (fun q ↦ (hq ⟨q, ·⟩)) hl₂

/-- Two logarithms of algebraic numbers `λ₁, λ₂ ∈ 𝓛` are linearly independent over the algebraic
numbers if and only if they are linearly independent over `ℚ`. -/
theorem linearIndependent_integralClosure_iff_of_mem_algebraicLogs {l₁ l₂ : ℂ}
    (hl₁ : l₁ ∈ algebraicLogs) (hl₂ : l₂ ∈ algebraicLogs) :
    LinearIndependent (integralClosure ℚ ℂ) ![l₁, l₂] ↔ LinearIndependent ℚ ![l₁, l₂] := by
  refine ⟨fun h ↦ h.restrict_scalars' ℚ, fun h ↦ LinearIndependent.pair_iff.2 fun s t hst ↦ ?_⟩
  by_contra hne
  refine mul_add_mul_ne_zero_of_linearIndependent hl₁ hl₂ h s.2.isAlgebraic t.2.isAlgebraic ?_ ?_
  · simpa [or_iff_not_imp_left] using hne
  · simpa [Subalgebra.smul_def] using hst

end TauCeti
