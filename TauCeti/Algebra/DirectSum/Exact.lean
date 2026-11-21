/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Exact.Basic

/-!
# Exactness of componentwise maps on direct sums

A family of pairs of module maps is exact in every component if and only if the induced pair of
maps on the external direct sums is exact. This is the algebraic input for taking direct sums of
projective resolutions: kernels and ranges of the componentwise maps are themselves computed
componentwise.

## Main results

* `DirectSum.exact_lmap_iff`: a pair of componentwise maps of direct sums is exact if and only if
  every component pair is.
-/

public section

universe uR uι uM uN uP

namespace DirectSum

variable {R : Type uR} [Semiring R] {ι : Type uι}
  {M : ι → Type uM} {N : ι → Type uN} {P : ι → Type uP}
  [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (N i)] [∀ i, AddCommMonoid (P i)]
  [∀ i, Module R (M i)] [∀ i, Module R (N i)] [∀ i, Module R (P i)]
  {f : ∀ i, M i →ₗ[R] N i} {g : ∀ i, N i →ₗ[R] P i}

/-- A pair of componentwise maps of direct sums is exact if and only if every component pair of
module maps is exact. -/
theorem exact_lmap_iff :
    Function.Exact (lmap f) (lmap g) ↔ ∀ i, Function.Exact (f i) (g i) := by
  classical
  refine ⟨fun h i y ↦ ?_, fun h ↦ LinearMap.exact_iff.mpr ?_⟩
  · rw [← (of_injective i).eq_iff' (map_zero _), ← lmap_of, h]
    exact ⟨fun ⟨x, hx⟩ ↦ ⟨x i, by simpa using congr($hx i)⟩, fun ⟨x, hx⟩ ↦ ⟨of M i x, by simp [hx]⟩⟩
  · simp_rw [ker_lmap, range_lmap, fun i ↦ LinearMap.exact_iff.mp (h i)]

end DirectSum
