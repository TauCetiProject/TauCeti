/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Derivations of squares of ideals

A derivation `D : A → M` satisfies the Leibniz rule `D (a * b) = a • D b + b • D a`, so it maps
the square `I ^ 2` of an ideal `I` of `A` into `I • M`. In particular, an element `f` of an ideal
`I` with `D f ∉ I` does not lie in `I ^ 2`.

This is the elementary half of the Jacobian criterion: if a partial derivative of `f` does not
vanish at a point, then `f` is not in the square of the maximal ideal there, so `f` is a regular
parameter and the hypersurface `f = 0` is regular at the point.

## Main results

* `Derivation.apply_mem_smul_top_of_mem_sq`: a derivation maps `I ^ 2` into `I • M`.
-/

public section

namespace Derivation

variable {R A M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M]
  [Module A M] [Module R M]

/-- A derivation maps the square of an ideal `I` into `I • M`. -/
theorem apply_mem_smul_top_of_mem_sq (D : Derivation R A M) {I : Ideal A} {x : A}
    (hx : x ∈ I ^ 2) : D x ∈ I • (⊤ : Submodule A M) := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx (fun a ha b hb ↦ ?_) fun x y hx hy ↦ ?_
  · rw [D.leibniz]
    exact add_mem (Submodule.smul_mem_smul ha Submodule.mem_top)
      (Submodule.smul_mem_smul hb Submodule.mem_top)
  · rw [map_add]
    exact add_mem hx hy

end Derivation
