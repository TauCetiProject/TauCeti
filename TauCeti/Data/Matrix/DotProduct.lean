/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Dot product lemmas

A vector indexed by `n` can be transported along an injective map `f : n → m` by extending it by
zero off the range of `f`. Its dot product with any vector indexed by `m` then only sees the
coordinates in the range of `f`. This lets orthogonality on a subset of coordinates be read off
in the ambient coordinate space.

A nonnegative vector paired with strictly positive weights has dot product zero precisely when
the vector is zero.

## Main results

* `Function.Injective.dotProduct_extend_zero`: the dot product with a vector extended by zero
  along an injective map is the dot product of the pulled-back vectors.
* `TauCeti.dotProduct_eq_zero_iff_of_pos`: a nonnegative vector is zero if its pairing with
  strictly positive weights vanishes.
-/

public section

open scoped Matrix

namespace Function.Injective

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

end Function.Injective

namespace TauCeti

/-- For a vector `c` of strictly positive weights and a nonnegative vector `x`, the pairing
`c ⬝ᵥ x` vanishes only when `x` does. -/
@[simp]
theorem dotProduct_eq_zero_iff_of_pos {ι R : Type*} [Fintype ι] [NonUnitalNonAssocSemiring R]
    [PartialOrder R] [IsOrderedAddMonoid R] [PosMulMono R] [NoZeroDivisors R]
    {c x : ι → R} (hc : ∀ i, 0 < c i) (hx : 0 ≤ x) :
    c ⬝ᵥ x = 0 ↔ x = 0 := by
  refine ⟨fun h => funext fun i => ?_, fun h => by simp [h]⟩
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_nonneg (hc j).le (hx j)).1 h i
    (Finset.mem_univ i)
  exact (mul_eq_zero.1 hterm).resolve_left (hc i).ne'

end TauCeti
