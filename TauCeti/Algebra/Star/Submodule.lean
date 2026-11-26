/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.Algebra.Module.Submodule.Map

/-!
# The pointwise star of a submodule

For a star module `A` over a commutative star semiring `R`, the pointwise image `star p` of a
submodule `p` is again a submodule: it is the preimage of `p` under the conjugate-linear
equivalence `starLinearEquiv R`. This mirrors Mathlib's `NonUnitalSubalgebra.instInvolutiveStar`.

In a star ring, `star` exchanges the two sides of multiplication, so it carries submodules closed
under right multiplication (right ideals) to submodules closed under left multiplication (left
ideals), `Submodule.mul_mem_star`.

## Main declarations

* `Submodule.instInvolutiveStar`: the pointwise star of submodules, an involution.
* `Submodule.mem_star_iff`: `x ∈ star p ↔ star x ∈ p`.
* `Submodule.mul_mem_star`: the star of a right ideal is a left ideal.
-/

public section

namespace Submodule

section Module

variable {R A : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid A] [StarAddMonoid A]
  [Module R A] [StarModule R A]

/-- The pointwise `star` of a submodule is a submodule: the preimage under the conjugate-linear
equivalence `starLinearEquiv R`. -/
instance instInvolutiveStar : InvolutiveStar (Submodule R A) where
  star p := p.comap (starLinearEquiv R (A := A)).toLinearMap
  star_involutive p := Submodule.ext fun x ↦ by simp

@[simp]
theorem mem_star_iff (p : Submodule R A) (x : A) : x ∈ star p ↔ star x ∈ p :=
  Iff.rfl

theorem star_mem_star_iff (p : Submodule R A) (x : A) : star x ∈ star p ↔ x ∈ p := by
  simp

end Module

variable {R A : Type*} [CommSemiring R] [StarRing R] [NonUnitalNonAssocSemiring A] [StarRing A]
  [Module R A] [StarModule R A]

/-- The star of a submodule closed under right multiplication is closed under left
multiplication: the star of a right ideal is a left ideal. -/
theorem mul_mem_star {p : Submodule R A} (hp : ∀ a : A, ∀ x ∈ p, x * a ∈ p) (a : A) {x : A}
    (hx : x ∈ star p) : a * x ∈ star p := by
  simpa [star_mul] using hp (star a) _ hx

end Submodule
