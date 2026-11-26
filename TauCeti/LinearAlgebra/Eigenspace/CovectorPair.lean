/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Eigenvalues seen by a pair of covectors

Let `A` be an endomorphism of a vector space `V` over an ordered field `K`, and let `(φ, ψ)` be a
pair of linear functionals on which `A` acts as multiplication by the "complex number" `p + qi`:
`φ ∘ A = p φ - q ψ` and `ψ ∘ A = q φ + p ψ`. Any vector `v` that is not killed by both `φ` and `ψ`
then constrains `p + qi`:

* if `A² v = μ v` for a scalar `μ`, then `(p + qi)² = μ`, that is `pq = 0` and `p² - q² = μ`
  (`Module.End.mul_eq_zero_and_sq_sub_sq_eq_of_apply_apply_eq_smul`);
* if `A v = a v - b w` and `A w = b v + a w` with `b ≠ 0`, so that `v + iw` is an eigenvector for
  `a + bi`, then `p + qi = a ± bi`, that is `p = a` and `q² = b²`
  (`Module.End.eq_and_sq_eq_of_apply_eq_smul_sub_smul`).

Over `ℝ`, these read off the eigenvalues of `A` and of `A²` from coordinates in which `A` is
block-diagonal with `2 × 2` blocks of the form `[[p, -q], [q, p]]`.
-/

public section

namespace Module.End

variable {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup V]
  [Module K V] {A : End K V} {φ ψ : V →ₗ[K] K} {p q : K}

/-- If `A` acts on the pair of covectors `(φ, ψ)` as multiplication by `p + qi`, and `v` is an
eigenvector of `A²` for the eigenvalue `μ` not killed by both covectors, then `(p + qi)² = μ`:
`pq = 0` and `p² - q² = μ`. -/
theorem mul_eq_zero_and_sq_sub_sq_eq_of_apply_apply_eq_smul
    (hφ : ∀ w, φ (A w) = p * φ w - q * ψ w) (hψ : ∀ w, ψ (A w) = q * φ w + p * ψ w) {μ : K}
    {v : V} (hv : A (A v) = μ • v) (hφψ : φ v ≠ 0 ∨ ψ v ≠ 0) :
    p * q = 0 ∧ p ^ 2 - q ^ 2 = μ := by
  have h₁ := congrArg φ hv
  have h₂ := congrArg ψ hv
  rw [hφ, hφ, hψ, map_smul, smul_eq_mul] at h₁
  rw [hψ, hφ, hψ, map_smul, smul_eq_mul] at h₂
  -- `X = p² - q² - μ` and `Y = 2pq` satisfy `(X² + Y²) φ v = (X² + Y²) ψ v = 0`.
  have hφv : ((p ^ 2 - q ^ 2 - μ) ^ 2 + (2 * p * q) ^ 2) * φ v = 0 := by
    linear_combination (p ^ 2 - q ^ 2 - μ) * h₁ + 2 * p * q * h₂
  have hψv : ((p ^ 2 - q ^ 2 - μ) ^ 2 + (2 * p * q) ^ 2) * ψ v = 0 := by
    linear_combination -(2 * p * q) * h₁ + (p ^ 2 - q ^ 2 - μ) * h₂
  have h : (p ^ 2 - q ^ 2 - μ) ^ 2 + (2 * p * q) ^ 2 = 0 := by
    rcases hφψ with h | h
    · exact (mul_eq_zero.1 hφv).resolve_right h
    · exact (mul_eq_zero.1 hψv).resolve_right h
  have hX : p ^ 2 - q ^ 2 - μ = 0 := by
    nlinarith [sq_nonneg (p ^ 2 - q ^ 2 - μ), sq_nonneg (2 * p * q)]
  have hY : 2 * p * q = 0 := by
    nlinarith [sq_nonneg (p ^ 2 - q ^ 2 - μ), sq_nonneg (2 * p * q)]
  exact ⟨by linear_combination hY / 2, by linear_combination hX⟩

/-- If `A` acts on the pair of covectors `(φ, ψ)` as multiplication by `p + qi`, and `v + iw` is an
eigenvector of `A` for the eigenvalue `a + bi`, `b ≠ 0`, with `v` not killed by both covectors,
then `p + qi = a ± bi`: `p = a` and `q² = b²`. -/
theorem eq_and_sq_eq_of_apply_eq_smul_sub_smul
    (hφ : ∀ w, φ (A w) = p * φ w - q * ψ w) (hψ : ∀ w, ψ (A w) = q * φ w + p * ψ w) {a b : K}
    (hb : b ≠ 0) {v w : V} (hAv : A v = a • v - b • w) (hAw : A w = b • v + a • w)
    (hφψ : φ v ≠ 0 ∨ ψ v ≠ 0) :
    p = a ∧ q ^ 2 = b ^ 2 := by
  have h₁ := congrArg φ hAv
  have h₂ := congrArg ψ hAv
  have h₃ := congrArg φ hAw
  have h₄ := congrArg ψ hAw
  simp only [hφ, hψ, map_sub, map_add, map_smul, smul_eq_mul] at h₁ h₂ h₃ h₄
  -- With `κ = (p - a) + qi`, the relations say `κ (v + iw) = -b (w - iv)`, hence
  -- `(κ² + b²) (v + iw) = 0`; its real part is `R = (p - a)² - q² + b²` and its imaginary part
  -- `S = 2 (p - a) q`.
  have hφv : ((((p - a) ^ 2 - q ^ 2 + b ^ 2) ^ 2 + (2 * (p - a) * q) ^ 2)) * φ v = 0 := by
    linear_combination (((p - a) ^ 2 - q ^ 2 + b ^ 2) * (p - a) + 2 * (p - a) * q * q) * h₁ +
      (-((p - a) ^ 2 - q ^ 2 + b ^ 2) * q + 2 * (p - a) * q * (p - a)) * h₂ +
      (-((p - a) ^ 2 - q ^ 2 + b ^ 2) * b) * h₃ + (-(2 * (p - a) * q) * b) * h₄
  have hψv : ((((p - a) ^ 2 - q ^ 2 + b ^ 2) ^ 2 + (2 * (p - a) * q) ^ 2)) * ψ v = 0 := by
    linear_combination (-(2 * (p - a) * q) * (p - a) + ((p - a) ^ 2 - q ^ 2 + b ^ 2) * q) * h₁ +
      ((2 * (p - a) * q) * q + ((p - a) ^ 2 - q ^ 2 + b ^ 2) * (p - a)) * h₂ +
      ((2 * (p - a) * q) * b) * h₃ + (-((p - a) ^ 2 - q ^ 2 + b ^ 2) * b) * h₄
  have h : ((p - a) ^ 2 - q ^ 2 + b ^ 2) ^ 2 + (2 * (p - a) * q) ^ 2 = 0 := by
    rcases hφψ with h | h
    · exact (mul_eq_zero.1 hφv).resolve_right h
    · exact (mul_eq_zero.1 hψv).resolve_right h
  have hR : (p - a) ^ 2 - q ^ 2 + b ^ 2 = 0 := by
    nlinarith [sq_nonneg ((p - a) ^ 2 - q ^ 2 + b ^ 2), sq_nonneg (2 * (p - a) * q)]
  have hS : (p - a) * q = 0 := by
    nlinarith [sq_nonneg ((p - a) ^ 2 - q ^ 2 + b ^ 2), sq_nonneg (2 * (p - a) * q)]
  -- `q = 0` would give `(p - a)² + b² = 0`.
  have hq : q ≠ 0 := by
    rintro rfl
    exact hb (by nlinarith [sq_nonneg (p - a), sq_nonneg b])
  have hpa : p - a = 0 := (mul_eq_zero.1 hS).resolve_right hq
  exact ⟨by linear_combination hpa, by nlinarith⟩

end Module.End
