/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.Span.Basic

import Mathlib.Tactic.Ring

/-!
# Spans of monomials in two elements under a shear

Let `u` and `y` be elements of a commutative `R`-algebra `A`. The products `u ^ i y ^ j` with
`i + j < n` span the values at `(u, y)` of the polynomials of total degree less than `n`. A linear
change of coordinates `u ↦ u + c • y` preserves total degrees, so it does not change this span.
This is how statements about the polynomials of bounded degree in the affine coordinates of a
plane curve are transported between coordinate systems.

## Main results

* `TauCeti.add_smul_pow_mul_pow_mem_span`: `(u + c • y) ^ i y ^ j` lies in the span of the
  products `u ^ a y ^ b` with `a + b ≤ i + j`.
* `TauCeti.span_add_smul_pow_mul_pow`: the products `(u + c • y) ^ i y ^ j` and `u ^ i y ^ j`
  with `i + j < n` span the same submodule.
-/

public section

namespace TauCeti

open Submodule

section Semiring

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- A product `(u + c • y) ^ i y ^ j` lies in the span of the products `u ^ a y ^ b` of total
degree `a + b ≤ i + j`. -/
theorem add_smul_pow_mul_pow_mem_span (u y : A) (c : R) (i j : ℕ) :
    (u + c • y) ^ i * y ^ j ∈
      span R ((fun p : ℕ × ℕ ↦ u ^ p.1 * y ^ p.2) '' {p | p.1 + p.2 < i + j + 1}) := by
  induction i generalizing j with
  | zero => exact subset_span ⟨(0, j), by simp⟩
  | succ i ih =>
    -- Expand one factor: `(u + c • y) ^ (i + 1) y ^ j = u ((u + c • y) ^ i y ^ j)
    -- + c • ((u + c • y) ^ i y ^ (j + 1))`, and multiplication by `u` raises degrees by one.
    have hmul : ∀ z ∈ span R
        ((fun p : ℕ × ℕ ↦ u ^ p.1 * y ^ p.2) '' {p | p.1 + p.2 < i + j + 1}),
        u * z ∈ span R
          ((fun p : ℕ × ℕ ↦ u ^ p.1 * y ^ p.2) '' {p | p.1 + p.2 < i + 1 + j + 1}) := by
      intro z hz
      have hmap := mem_map_of_mem (f := LinearMap.mulLeft R u) hz
      rw [map_span, Set.image_image] at hmap
      refine span_mono ?_ hmap
      rintro _ ⟨p, hp, rfl⟩
      refine ⟨(p.1 + 1, p.2), by simp only [Set.mem_ofPred_eq] at hp ⊢; omega, ?_⟩
      simp only [LinearMap.mulLeft_apply]
      ring
    have h₁ := hmul _ (ih j)
    have h₂ := smul_mem _ c (ih (j + 1))
    rw [show i + (j + 1) + 1 = i + 1 + j + 1 by omega] at h₂
    have e : (u + c • y) ^ (i + 1) * y ^ j =
        u * ((u + c • y) ^ i * y ^ j) + c • ((u + c • y) ^ i * y ^ (j + 1)) := by
      simp only [Algebra.smul_def]
      ring
    rw [e]
    exact add_mem h₁ h₂

end Semiring

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- **A shear does not change the span of the monomials of bounded degree**: the products
`(u + c • y) ^ i y ^ j` and `u ^ i y ^ j` with `i + j < n` span the same submodule. -/
theorem span_add_smul_pow_mul_pow (u y : A) (c : R) (n : ℕ) :
    span R ((fun p : ℕ × ℕ ↦ (u + c • y) ^ p.1 * y ^ p.2) '' {p | p.1 + p.2 < n}) =
      span R ((fun p : ℕ × ℕ ↦ u ^ p.1 * y ^ p.2) '' {p | p.1 + p.2 < n}) := by
  -- Each side lies in the other, since `u = (u + c • y) + (-c) • y`.
  have key : ∀ (v : A) (b : R),
      span R ((fun p : ℕ × ℕ ↦ (v + b • y) ^ p.1 * y ^ p.2) '' {p | p.1 + p.2 < n}) ≤
        span R ((fun p : ℕ × ℕ ↦ v ^ p.1 * y ^ p.2) '' {p | p.1 + p.2 < n}) := by
    intro v b
    refine span_le.mpr ?_
    rintro _ ⟨p, hp, rfl⟩
    refine span_mono ?_ (add_smul_pow_mul_pow_mem_span v y b p.1 p.2)
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨q, by simp only [Set.mem_ofPred_eq] at hp hq ⊢; omega, rfl⟩
  refine le_antisymm (key u c) ?_
  simpa [neg_smul, add_neg_cancel_right] using key (u + c • y) (-c)

end TauCeti
