/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution

/-!
# Integer discrete convolution as a sum over one index

Mathlib's `DiscreteConvolution.addConvolution` sums over the fibre `addFiber n`, the
antidiagonal `{(i, j) | i + j = n}`. Over `ℤ` that fibre is parametrised by its first
coordinate, which turns the convolution into a single sum:

* `DiscreteConvolution.intEquivAddFiber`: the parametrisation `k ↦ (k, n - k)`;
* `DiscreteConvolution.addConvolution_mul_apply`: `(f ⋆ g) n = ∑' k, f k * g (n - k)`, the
  familiar Laurent convolution.

The equivalence is an `Equiv` rather than a `Finset` because the antidiagonal in `ℤ × ℤ` is
infinite. Nothing here is specific to any ring of interest; it is the bridge between Mathlib's
fibre picture and the `ℤ`-indexed one.
-/

public section

namespace DiscreteConvolution

/-- **The antidiagonal `{(a, b) | a + b = n}`, parametrised by its first coordinate.** This is
where an index-set picture and Mathlib's fibre picture meet, and it is an `Equiv` rather than a
`Finset` because the antidiagonal need not be finite. -/
def equivAddFiber {G : Type*} [AddGroup G] (n : G) : G ≃ (addFiber n : Set (G × G)) where
  toFun k := ⟨(k, -k + n), by simp [mem_addFiber]⟩
  invFun ab := ab.1.1
  left_inv _ := rfl
  right_inv ab := by
    obtain ⟨⟨a, b⟩, hab⟩ := ab
    rw [mem_addFiber] at hab
    subst hab
    simp

/-- **The convolution over an additive group is a single sum**:
`(f ⋆ g) n = ∑' k, f k * g (-k + n)`. Reindexing Mathlib's sum over `addFiber n` by the
first coordinate is exactly `DiscreteConvolution.equivAddFiber`. -/
theorem addConvolution_mul_apply {G : Type*} [AddGroup G] {A : Type*} [Ring A]
    [TopologicalSpace A] (f g : G → A) (n : G) :
    addConvolution (LinearMap.mul ℤ A) f g n = ∑' k : G, f k * g (-k + n) :=
  ((equivAddFiber n).tsum_eq fun ab ↦ f ab.1.1 * g ab.1.2).symm

/-- **The commutative form**: `(f ⋆ g) n = ∑' k, f k * g (n - k)`, the familiar Laurent
convolution when the index group is `ℤ`. -/
theorem addConvolution_mul_apply_sub {G : Type*} [AddCommGroup G] {A : Type*} [Ring A]
    [TopologicalSpace A] (f g : G → A) (n : G) :
    addConvolution (LinearMap.mul ℤ A) f g n = ∑' k : G, f k * g (n - k) :=
  (addConvolution_mul_apply f g n).trans (tsum_congr fun k ↦ by rw [neg_add_eq_sub])

end DiscreteConvolution

end
