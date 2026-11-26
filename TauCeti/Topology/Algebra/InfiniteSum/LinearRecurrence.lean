/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The sums of first- and second-order linear recurrences

For a sequence `d` with sum `σ` obeying the inhomogeneous first-order recurrence
`d (r + 1) = D • d r + b (r + 1)` with `d 0 = b 0`, where `b` has sum `β`, the sum satisfies
`σ = D • σ + β`: termwise, `d` is the sum of `b` and of the shifted sequence
`0, D • d 0, D • d 1, …`, whose sum is `D • σ`. The values lie in a Hausdorff commutative additive
monoid with continuous addition, and each fixed scalar acts additively and continuously.

For a summable sequence `d` obeying `d (r + 2) = D • d (r + 1) - S • d r`, its sum `σ`
satisfies the identity:

`σ - D • σ + S • σ = d 0 + (d 1 - D • d 0)`.

Here the values lie in a Hausdorff additive group with continuous addition; negation need not be
continuous, since the proof sums the subtraction-free recurrence
`d (r + 2) + S • d r = D • d (r + 1)` and only rearranges the resulting equality. For a
nonassociative ring acting on itself by left multiplication, this gives
`(1 - D + S) * σ = d 0 + (d 1 - D * d 0)`.

In an associative ring, this corresponds to evaluating the characteristic polynomial at `1`
in the formal generating-function identity
`(1 - D x + S x²) ∑ d r xʳ = d 0 + (d 1 - D d 0) x`, and it is how a local Euler factor
`(1 - a_p p^{-s} + c_p p^{-2s})⁻¹` is recovered from a prime-power recurrence for the
coefficients of a Dirichlet series.

## Main results

* `HasSum.eq_smul_add_of_linearRec₁`: the first-order identity.
* `HasSum.sub_smul_add_smul_eq_of_linearRec₂`: the scalar-action identity.
* `HasSum.one_sub_add_mul_eq_of_linearRec₂`: the ring identity.
-/

public section

variable {A M : Type*} [TopologicalSpace M] [T2Space M] {D S : A} {σ : M} {d : ℕ → M}

section AddCommMonoid

variable [AddCommMonoid M] [DistribSMul A M] [ContinuousAdd M] [ContinuousConstSMul A M]

/-- **The sum of a first-order linear recurrence.** If `d` has sum `σ`, `b` has sum `β`,
`d 0 = b 0` and `d (r + 1) = D • d r + b (r + 1)`, then `σ = D • σ + β`. -/
theorem HasSum.eq_smul_add_of_linearRec₁ {b : ℕ → M} {β : M} (h : HasSum d σ)
    (hb : HasSum b β) (h0 : d 0 = b 0) (hd : ∀ r, d (r + 1) = D • d r + b (r + 1)) :
    σ = D • σ + β := by
  -- `d` is the termwise sum of `b` and of `0, D • d 0, D • d 1, …`, which sums to `D • σ`
  let c : ℕ → M := fun | 0 => 0 | r + 1 => D • d r
  have hc : HasSum c (D • σ) := by simpa [c] using (h.const_smul D).zero_add (f := c)
  refine h.unique <| (hc.add hb).congr_fun fun r ↦ ?_
  cases r <;> simp [c, h0, hd]

end AddCommMonoid

variable [AddCommGroup M] [DistribSMul A M] [ContinuousAdd M] [ContinuousConstSMul A M]

/-- **The sum of a second-order linear recurrence.** If `d` has sum `σ` and obeys
`d (r + 2) = D • d (r + 1) - S • d r`, then
`σ - D • σ + S • σ = d 0 + (d 1 - D • d 0)`. -/
theorem HasSum.sub_smul_add_smul_eq_of_linearRec₂ (h : HasSum d σ)
    (hd : ∀ r, d (r + 2) = D • d (r + 1) - S • d r) :
    σ - D • σ + S • σ = d 0 + (d 1 - D • d 0) := by
  -- sum `d (r + 2) + S • d r = D • d (r + 1)`: termwise, `d` plus `0, 0, S • d 0, S • d 1, …`
  -- is `0, D • d 0, D • d 1, …` plus `d 0, d 1 - D • d 0, 0, 0, …`
  let c₁ : ℕ → M := fun | 0 => 0 | r + 1 => D • d r
  let c₂ : ℕ → M := fun | 0 => 0 | 1 => 0 | r + 2 => S • d r
  let b : ℕ → M := fun | 0 => d 0 | 1 => d 1 - D • d 0 | _ + 2 => 0
  have hc₁ : HasSum c₁ (D • σ) := by simpa [c₁] using (h.const_smul D).zero_add (f := c₁)
  have hc₂ : HasSum c₂ (S • σ) := by
    simpa [c₂, Finset.sum_range_succ] using (h.const_smul S).sum_range_add (f := c₂) (k := 2)
  have hb : HasSum b (d 0 + (d 1 - D • d 0)) := by
    simpa [b, Finset.sum_range_succ] using hasSum_zero.sum_range_add (f := b) (k := 2)
  have hσ : σ + S • σ = D • σ + (d 0 + (d 1 - D • d 0)) :=
    (h.add hc₂).unique <| (hc₁.add hb).congr_fun fun
      | 0 | 1 => by simp [c₁, c₂, b]
      | r + 2 => by simp [c₁, c₂, b, hd]
  rw [sub_add_eq_add_sub, hσ, add_sub_cancel_left]

/-- **The sum of a second-order linear recurrence in a ring.** If `d` has sum `σ` and obeys
`d (r + 2) = D * d (r + 1) - S * d r`, then `(1 - D + S) * σ = d 0 + (d 1 - D * d 0)`. -/
theorem HasSum.one_sub_add_mul_eq_of_linearRec₂
    {R : Type*} [NonAssocRing R] [TopologicalSpace R]
    [ContinuousAdd R] [ContinuousConstSMul R R] [T2Space R]
    {D S σ : R} {d : ℕ → R} (h : HasSum d σ)
    (hd : ∀ r, d (r + 2) = D * d (r + 1) - S * d r) :
    (1 - D + S) * σ = d 0 + (d 1 - D * d 0) := by
  simpa only [smul_eq_mul, sub_mul, add_mul, one_mul] using
    h.sub_smul_add_smul_eq_of_linearRec₂ (D := D) (S := S)
      (by simpa only [smul_eq_mul] using hd)
