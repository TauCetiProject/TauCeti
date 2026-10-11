/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Grassmannian

-- Proof-only: the body of `Module.Grassmannian.baseChangeMkQ` is not exposed.
import all Mathlib.RingTheory.Grassmannian

/-!
# Complements to Mathlib's Grassmannian

Let `M` be a module over a commutative ring `R`. Mathlib's `Module.Grassmannian R M k`, written
`G(k, M; R)`, is the set of submodules `N ≤ M` whose quotient `M ⧸ N` is finite projective of
constant rank `k`. This file adds two general facts about it: the kernel of a surjection onto a
finite projective module of constant rank `k` is a point of `G(k, M; R)`, and the evaluation of
`Module.Grassmannian.baseChangeMkQ`, the map underlying base change of points, on pure tensors.

## Main definitions

* `Module.Grassmannian.ofSurjective`: the kernel of a surjection onto a finite projective module
  of constant rank `k`, as a point of `G(k, M; R)`.

## Main results

* `Module.Grassmannian.baseChangeMkQ_tmul`: `baseChangeMkQ B N` sends `b ⊗ₜ m` to
  `b ⊗ₜ [1 ⊗ₜ m]`.

## References

* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
-/

public section

universe u v w

open TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}

section OfSurjective

variable {P : Type*} [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]

/-- The kernel of a surjection `φ : M → P` onto a finite projective module `P` of constant rank
`k`, as a point of `G(k, M; R)`. -/
noncomputable def ofSurjective (φ : M →ₗ[R] P) (hφ : Function.Surjective φ)
    (hP : ∀ p, rankAtStalk (R := R) P p = k) : G(k, M; R) where
  toSubmodule := LinearMap.ker φ
  finite_quotient := Module.Finite.equiv (φ.quotKerEquivOfSurjective hφ).symm
  projective_quotient := Module.Projective.of_equiv (φ.quotKerEquivOfSurjective hφ).symm
  rankAtStalk_eq p := by
    rw [rankAtStalk_eq_of_equiv (φ.quotKerEquivOfSurjective hφ)]
    exact hP p

@[simp]
theorem toSubmodule_ofSurjective (φ : M →ₗ[R] P) (hφ : Function.Surjective φ)
    (hP : ∀ p, rankAtStalk (R := R) P p = k) :
    (ofSurjective φ hφ hP).toSubmodule = LinearMap.ker φ :=
  (rfl)

end OfSurjective

@[simp]
theorem baseChangeMkQ_tmul {A B : Type w} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] (N : Submodule A (A ⊗[R] M)) (b : B) (m : M) :
    baseChangeMkQ B N (b ⊗ₜ m) = b ⊗ₜ Submodule.Quotient.mk (1 ⊗ₜ m) := by
  simp [baseChangeMkQ]

end Module.Grassmannian
