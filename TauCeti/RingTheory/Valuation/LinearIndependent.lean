/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Linear independence from distinct valuations

Let `v` be a valuation on an algebra `B` over a commutative ring `A`, and let `f` be a family of
elements of `B`. Suppose that every nonzero scalar multiple `a • f i` has nonzero valuation, and
that multiples of two different members of the family never have the same valuation. Then `f` is
linearly independent over `A`: in a linear combination with a nonzero coefficient, the summand of
largest valuation is unique, so it dictates the valuation of the sum, which cannot vanish.

When `v` is trivial on `A`, the hypothesis only asks the members of the family to have pairwise
distinct nonzero valuations. When `v` is not trivial on `A`, it asks their valuations to lie in
different cosets of the image of `A`. This is how the value-group index of a valued field
extension, and with it the ramification index, is bounded by the degree of the extension.

## Main results

* `Valuation.linearIndependent_of_map_smul_ne`: a family whose nonzero scalar multiples have
  nonzero valuations, distinct for different members, is linearly independent.

## References

* J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer, 1999, Chapter II,
  Proposition 6.8, for the inequality `e f ≤ n` proved by this argument.
-/

public section

namespace Valuation

variable {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]

/-- **Elements whose multiples have distinct valuations are linearly independent.** If every
nonzero scalar multiple `a • f i` has nonzero valuation, and `v (a • f i) ≠ v (b • f j)` for
`i ≠ j` and nonzero scalars `a` and `b`, then `f` is linearly independent over `A`. -/
theorem linearIndependent_of_map_smul_ne {A B : Type*} [CommRing A] [Ring B] [Algebra A B]
    (v : Valuation B Γ₀) {ι : Type*} {f : ι → B} (hf : ∀ i (a : A), a ≠ 0 → v (a • f i) ≠ 0)
    (hne : ∀ i j, i ≠ j → ∀ a b : A, a ≠ 0 → b ≠ 0 → v (a • f i) ≠ v (b • f j)) :
    LinearIndependent A f := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  -- Restrict to the summands with nonzero coefficient; they have the same sum.
  set t := s.filter fun i ↦ g i ≠ 0 with ht
  have hit : i ∈ t := Finset.mem_filter.mpr ⟨hi, hgi⟩
  have hsum' : ∑ i ∈ t, g i • f i = 0 := by
    rw [← hsum, ht]
    exact Finset.sum_filter_of_ne fun i _ h hg ↦ h (by rw [hg, zero_smul])
  -- The summand of largest valuation is unique, so it dictates the valuation of the sum.
  obtain ⟨j, hjt, hmax⟩ := t.exists_max_image (fun i ↦ v (g i • f i)) ⟨i, hit⟩
  have hgj : g j ≠ 0 := (Finset.mem_filter.mp hjt).2
  have hlt : ∀ i ∈ t \ {j}, v (g i • f i) < v (g j • f j) := fun i hi ↦ by
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    exact lt_of_le_of_ne (hmax i hi.1) (hne i j hi.2 _ _ (Finset.mem_filter.mp hi.1).2 hgj)
  have h := v.map_sum_eq_of_lt hjt hlt
  rw [hsum', v.map_zero] at h
  exact hf j (g j) hgj h.symm

end Valuation

end
