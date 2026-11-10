/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Span.Basic

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring

/-!
# Spans of monomials in two elements under a shear

Let `u` and `y` be elements of a commutative semiring `A` with a compatible `R`-module structure,
for instance a commutative `R`-algebra. The products `u ^ i y ^ j` with `i + j < n` span the values
at `(u, y)` of the polynomials of total degree less than `n`. A linear change of coordinates
`u ↦ u + c • y` preserves total degrees, so each product `(u + c • y) ^ i y ^ j` lies in the span
of the products `u ^ a y ^ b` with `a + b = i + j`. When `R` is a ring, the inverse shear
`u ↦ u + (-c) • y` gives the reverse inclusion, so the shear does not change the span of the
products of total degree less than `n`. Over a semiring the span can shrink: for `R = ℕ`,
`A = ℕ[X, Y]`, `u = X`, `y = Y`, `c = 1` and `n = 2`, the element `X` is not in the `ℕ`-span of
`1`, `X + Y` and `Y`.

This is how statements about the polynomials of bounded degree in the affine coordinates of a
plane curve are transported between coordinate systems.

## Main results

* `TauCeti.add_smul_pow_mul_pow_mem_span`: `(u + c • y) ^ i y ^ j` lies in the span of the
  products `u ^ a y ^ b` with `a + b = i + j`.
* `TauCeti.span_add_smul_pow_mul_pow`: for a ring `R`, the products `(u + c • y) ^ i y ^ j` and
  `u ^ i y ^ j` with `i + j < n` span the same submodule.
-/

public section

namespace TauCeti

open Submodule

section Semiring

variable {R A : Type*} [Semiring R] [CommSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

/-- A product `(u + c • y) ^ i y ^ j` lies in the span of the products `u ^ a y ^ b` of the same
total degree `a + b = i + j`. -/
theorem add_smul_pow_mul_pow_mem_span (u y : A) (c : R) (i j : ℕ) :
    (u + c • y) ^ i * y ^ j ∈
      span R ((fun p : ℕ × ℕ ↦ u ^ p.1 * y ^ p.2) '' {p | p.1 + p.2 = i + j}) := by
  rw [add_pow, Finset.sum_mul]
  refine sum_mem fun m hm ↦ ?_
  -- The `m`-th binomial term is a multiple of `u ^ m y ^ (i - m + j)`.
  have e : u ^ m * (c • y) ^ (i - m) * (i.choose m : A) * y ^ j =
      i.choose m • c ^ (i - m) • (u ^ m * y ^ (i - m + j)) := by
    rw [smul_pow, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, nsmul_eq_mul, mul_smul_comm]
    congr 1
    ring
  rw [e]
  refine nsmul_mem (Submodule.smul_mem _ _ (subset_span ?_)) _
  exact ⟨(m, i - m + j), by grind, rfl⟩

end Semiring

variable {R A : Type*} [Ring R] [CommSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

/-- **A shear does not change the span of the monomials of bounded degree**: the products
`(u + c • y) ^ i y ^ j` and `u ^ i y ^ j` with `i + j < n` span the same submodule. -/
theorem span_add_smul_pow_mul_pow (u y : A) (c : R) (n : ℕ) :
    span R ((fun p : ℕ × ℕ ↦ (u + c • y) ^ p.1 * y ^ p.2) '' {p | p.1 + p.2 < n}) =
      span R ((fun p : ℕ × ℕ ↦ u ^ p.1 * y ^ p.2) '' {p | p.1 + p.2 < n}) := by
  -- Each side lies in the other, since `u = (u + c • y) + (-c) • y`.
  have key (v : A) (b : R) :
      span R ((fun p : ℕ × ℕ ↦ (v + b • y) ^ p.1 * y ^ p.2) '' {p | p.1 + p.2 < n}) ≤
        span R ((fun p : ℕ × ℕ ↦ v ^ p.1 * y ^ p.2) '' {p | p.1 + p.2 < n}) := by
    refine span_le.mpr ?_
    rintro _ ⟨p, hp, rfl⟩
    refine span_mono (Set.image_mono fun q hq ↦ ?_) (add_smul_pow_mul_pow_mem_span v y b p.1 p.2)
    grind
  refine le_antisymm (key u c) ?_
  simpa [add_assoc, ← add_smul] using key (u + c • y) (-c)

end TauCeti
