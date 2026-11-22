/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subsemiring.MulOpposite
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite patching in subsemirings

A finite right-multiplier certificate for one recovers an element from its denominator-cleared
multiples. Only the right coefficients of the certificate must belong to the subsemiring;
the denominators themselves need not. No commutativity, subtraction or cancellation is used.
The left-handed statement is the same argument in the opposite semiring.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics
  195 (2005), §5, for denominator patching in embedded skew Laurent rings.
-/

public section

namespace Subsemiring

variable {R ι : Type*} [Semiring R]

/-- A finite certificate `∑ aᵢ uᵢ = 1`, with `uᵢ` and `f aᵢ` in `H`, implies `f ∈ H`.
No membership hypothesis is needed on the individual `aᵢ`. -/
theorem mem_of_sum_mul_eq_one (H : Subsemiring R) (s : Finset ι) (a u : ι → R) {f : R}
    (h1 : ∑ i ∈ s, a i * u i = 1) (hu : ∀ i ∈ s, u i ∈ H)
    (hf : ∀ i ∈ s, f * a i ∈ H) : f ∈ H := by
  rw [← mul_one f, ← h1, Finset.mul_sum]
  exact H.sum_mem fun i hi ↦ by
    rw [← mul_assoc]
    exact H.mul_mem (hf i hi) (hu i hi)

/-- The left-multiplier form of finite patching, obtained in the opposite semiring. -/
theorem mem_of_sum_mul_eq_one_left (H : Subsemiring R) (s : Finset ι) (u a : ι → R) {f : R}
    (h1 : ∑ i ∈ s, u i * a i = 1) (hu : ∀ i ∈ s, u i ∈ H)
    (hf : ∀ i ∈ s, a i * f ∈ H) : f ∈ H := by
  have h := H.op.mem_of_sum_mul_eq_one s (fun i ↦ MulOpposite.op (a i))
    (fun i ↦ MulOpposite.op (u i)) (f := MulOpposite.op f)
    (by simpa only [← MulOpposite.op_mul, ← Finset.op_sum, MulOpposite.op_one] using
      congrArg MulOpposite.op h1)
    (by simpa only [mem_op, MulOpposite.unop_op] using hu)
    (by simpa only [mem_op, MulOpposite.unop_mul, MulOpposite.unop_op] using hf)
  exact h

end Subsemiring
