/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.Algebra.Star.Module

/-!
# The skew-adjoint Lie subalgebra of a star algebra

Over a scalar ring with trivial involution, the skew-adjoint elements of a star algebra
form a Lie subalgebra for the commutator bracket. Its underlying submodule is Mathlib's
`skewAdjoint.submodule`.

## Main declarations

* `skewAdjoint.lieSubalgebra`: the skew-adjoint elements with their commutator bracket.
* `skewAdjoint.mem_lieSubalgebra`: membership means `star x = -x`.
* `skewAdjoint.toSubmodule_lieSubalgebra`: the underlying skew-adjoint submodule.
* `skewAdjoint.coe_lieSubalgebra`: the carrier is Mathlib's skew-adjoint additive subgroup.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222
  (2015), Proposition 3.24 (the skew-adjoint matrix Lie algebras).
-/

public section

namespace skewAdjoint

attribute [local instance 100] LieRing.ofAssociativeRing

variable (𝕜 A : Type*) [CommRing 𝕜] [StarMul 𝕜] [TrivialStar 𝕜]
  [Ring A] [StarRing A] [Algebra 𝕜 A] [StarModule 𝕜 A]

/-- The skew-adjoint elements of a star algebra, as a Lie subalgebra under the commutator. -/
def lieSubalgebra : LieSubalgebra 𝕜 A :=
  { skewAdjoint.submodule 𝕜 A with
    lie_mem' := by
      intro x y hx hy
      -- The membership lemma is for the additive subgroup; expand the inherited submodule first.
      simp only [skewAdjoint.submodule, AddSubgroup.mem_carrier, skewAdjoint.mem_iff] at hx hy ⊢
      simp only [Ring.lie_def, star_sub, star_mul, hx, hy, neg_mul_neg, neg_sub] }


/-- An element belongs to the skew-adjoint Lie subalgebra exactly when `star x = -x`. -/
@[simp]
theorem mem_lieSubalgebra (x : A) : x ∈ lieSubalgebra 𝕜 A ↔ star x = -x := Iff.rfl

/-- The underlying submodule of the skew-adjoint Lie subalgebra is the skew-adjoint submodule. -/
@[simp]
theorem toSubmodule_lieSubalgebra :
    (lieSubalgebra 𝕜 A).toSubmodule = skewAdjoint.submodule 𝕜 A := by
  -- The Lie subalgebra extends this submodule without changing its fields.
  rfl

/-- The carrier of the skew-adjoint Lie subalgebra is the skew-adjoint additive subgroup. -/
@[simp]
theorem coe_lieSubalgebra : (lieSubalgebra 𝕜 A : Set A) = skewAdjoint A := by
  -- The Lie subalgebra inherits the skew-adjoint submodule's carrier.
  rfl

end skewAdjoint
