/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Order
public import TauCeti.LinearAlgebra.Eigenspace.SkewSwap

import Mathlib.Tactic.LinearCombination

/-!
# Positivity on the eigenspaces of the complex skew swap

On `ℂ × ℂ`, the skew swap `LinearEquiv.skewSwap ℂ ℂ ℂ : (x, y) ↦ (-y, x)` is the standard complex
structure, with eigenvalues `i` and `-i`. Writing `ω(a, b) = a.1 * b.2 - a.2 * b.1` for the
standard alternating form on `ℂ × ℂ`, this file shows that for `μ = i` or `μ = -i` the quantity
`-μ * ω(x, conj x) = μ * (x.2 * conj x.1 - x.1 * conj x.2)` is positive on every nonzero
`μ`-eigenvector `x`.
-/

public section

namespace TauCeti

open scoped ComplexOrder ComplexConjugate

/-- For `μ = i` or `μ = -i` (that is, `μ * μ = -1`), the expression
`μ * (x.2 * conj x.1 - x.1 * conj x.2)` is positive on every nonzero `μ`-eigenvector `x` of the
standard complex structure `(x, y) ↦ (-y, x)` on `ℂ × ℂ`. -/
theorem mul_snd_mul_conj_fst_sub_fst_mul_conj_snd_pos {μ : ℂ} (hμ : μ * μ = -1) {x : ℂ × ℂ}
    (hx : x ∈ Module.End.eigenspace (LinearEquiv.skewSwap ℂ ℂ ℂ).toLinearMap μ) (hx₀ : x ≠ 0) :
    0 < μ * (x.2 * conj x.1 - x.1 * conj x.2) := by
  have h₂ := snd_eq_neg_smul_fst_of_mem_eigenspace_skewSwap hx
  have h₁ : x.1 ≠ 0 := fun h => hx₀ (Prod.ext h (by simp [h₂, h]))
  have hnorm : Complex.normSq μ = 1 := by
    have h := congrArg Complex.normSq hμ
    rw [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_one] at h
    exact (mul_self_eq_one_iff.mp h).resolve_right (by linarith [Complex.normSq_nonneg μ])
  have hconj : μ * conj μ = 1 := by rw [Complex.mul_conj, hnorm, Complex.ofReal_one]
  have heq : μ * (x.2 * conj x.1 - x.1 * conj x.2) = 2 * (x.1 * conj x.1) := by
    rw [h₂, smul_eq_mul, map_mul, map_neg]
    linear_combination (-(x.1 * conj x.1)) * hμ + (x.1 * conj x.1) * hconj
  rw [heq, Complex.mul_conj]
  exact_mod_cast mul_pos two_pos (Complex.normSq_pos.mpr h₁)

end TauCeti
