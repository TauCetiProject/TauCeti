/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul

/-!
# Dot products with words extended by zero

A vector indexed by `n` can be transported along an injective map `f : n → m` by extending it by
zero off the range of `f`. Its dot product with any vector indexed by `m` then only sees the
coordinates in the range of `f`. This lets orthogonality on a subset of coordinates be read off
in the ambient coordinate space.

## Main results

* `TauCeti.dotProduct_extend_zero`: the dot product with a vector extended by zero along an
  injective map is the dot product of the pulled-back vectors.
-/

public section

open scoped Matrix

namespace TauCeti

variable {m n α : Type*} [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring α]

/-- The dot product with a vector extended by zero along an injective map only sees the
coordinates in the range of that map. -/
theorem dotProduct_extend_zero {f : n → m} (hf : f.Injective) (x : m → α) (y : n → α) :
    x ⬝ᵥ f.extend y 0 = (x ∘ f) ⬝ᵥ y := by
  classical
  simp only [dotProduct, Function.comp_apply]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨f, hf⟩)), Finset.sum_map]
  · exact Finset.sum_congr rfl fun k _ ↦ by simp [hf.extend_apply]
  · intro i _ hi
    have hi : ¬∃ k, f k = i := by simpa using hi
    rw [Function.extend_apply' _ _ _ hi, Pi.zero_apply, mul_zero]

end TauCeti
