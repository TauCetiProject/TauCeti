/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Forms definite off the origin separate vectors

A semilinear map of two arguments `B` that is definite off the origin, `B x x ≠ 0` for `x ≠ 0`,
**separates** vectors: two vectors pairing identically against every vector are equal, because
their difference pairs to zero with itself.

## Main results

* `LinearMap.eq_of_forall_sesq_eq`: a form definite off the origin separates vectors.
-/

public section

namespace LinearMap

variable {R S M P : Type*} [Semiring R] [CommSemiring S] [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module S P] {I₁ I₂ : R →+* S}

/-- **A form definite off the origin separates vectors**: two vectors pairing identically against
every vector are equal, because their difference pairs to zero with itself.  Mathlib's
`LinearMap.SeparatingLeft` is the same separation stated as a property of the form; definiteness
off the origin is what supplies it here, and is the shape the callers carry it in. -/
theorem eq_of_forall_sesq_eq {B : M →ₛₗ[I₁] M →ₛₗ[I₂] P} (hdef : ∀ x : M, x ≠ 0 → B x x ≠ 0)
    {u v : M} (h : ∀ y : M, B u y = B v y) : u = v :=
  sub_eq_zero.1 <| not_not.1 fun hne ↦ hdef _ hne <| by simp [h]

end LinearMap
