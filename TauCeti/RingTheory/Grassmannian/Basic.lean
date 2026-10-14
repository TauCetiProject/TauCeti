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
constant rank `k`. This file adds general facts about it: the kernel of a surjection onto a
finite projective module of constant rank `k` is a point of `G(k, M; R)`, and the behaviour of
`Module.Grassmannian.baseChangeMkQ`, the map underlying base change of points, on pure tensors and
on vectors coming from `A ⊗[R] M`. In particular a vector of a point maps into each of its base
changes, and, when `B` is an `A`-algebra, the base change of `N` along the structure map is the
kernel of `baseChangeMkQ B N` for the given algebra structure on `B`.

## Main definitions

* `Module.Grassmannian.ofSurjective`: the kernel of a surjection onto a finite projective module
  of constant rank `k`, as a point of `G(k, M; R)`.

## Main results

* `Module.Grassmannian.baseChangeMkQ_tmul`: `baseChangeMkQ B N` sends `b ⊗ₜ m` to
  `b ⊗ₜ [1 ⊗ₜ m]`.
* `Module.Grassmannian.baseChangeMkQ_rTensor`: `baseChangeMkQ B N` sends the image of
  `x ∈ A ⊗[R] M` to `1 ⊗ₜ [x]`.
* `Module.Grassmannian.map_toAlgHom_toSubmodule`: the base change of a point along the structure
  map of an `A`-algebra `B` is the kernel of `baseChangeMkQ B N`.
* `Module.Grassmannian.rTensor_mem_map`: a vector of a point maps into every base change of it.

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

section BaseChange

variable {A B : Type w} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- The base change map `B ⊗[R] M → B ⊗[A] ((A ⊗[R] M) ⧸ N)` sends the image of `x ∈ A ⊗[R] M`
to `1 ⊗ₜ [x]`. -/
@[simp]
theorem baseChangeMkQ_rTensor [Algebra A B] [IsScalarTower R A B] (N : Submodule A (A ⊗[R] M))
    (x : A ⊗[R] M) :
    baseChangeMkQ B N ((IsScalarTower.toAlgHom R A B).toLinearMap.rTensor M x) =
      (1 : B) ⊗ₜ N.mkQ x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Submodule.Quotient.mk_smul,
      TensorProduct.smul_tmul']
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, tmul_add]

/-- With an algebra structure in place, the base change `map f N` along the structure map
`f : A → B` is the kernel of `baseChangeMkQ B N`. -/
theorem map_toAlgHom_toSubmodule [Algebra A B] [IsScalarTower R A B] (N : G(k, A ⊗[R] M; A)) :
    (map (IsScalarTower.toAlgHom R A B) N).toSubmodule =
      LinearMap.ker (baseChangeMkQ B N.toSubmodule) := by
  have h : (IsScalarTower.toAlgHom R A B).toRingHom.toAlgebra = ‹Algebra A B› :=
    Algebra.algebra_ext _ _ fun _ ↦ rfl
  rw [map_toSubmodule]
  -- the two sides differ only in the algebra structure, `f.toAlgebra` against the given one, and
  -- in the proofs of `IsScalarTower` built on it
  congr 2 <;> first | rw [h] | exact proof_irrel_heq _ _

/-- A vector of `A ⊗[R] M` lying in a point `N` of the Grassmannian maps into every base change
of `N`. -/
theorem rTensor_mem_map (f : A →ₐ[R] B) {N : G(k, A ⊗[R] M; A)} {x : A ⊗[R] M}
    (hx : x ∈ N.toSubmodule) : f.toLinearMap.rTensor M x ∈ (map f N).toSubmodule := by
  algebraize [f.toRingHom]
  rw [map_toSubmodule, LinearMap.mem_ker]
  -- `algebraize` makes `f` the structure map of `B` as an `A`-algebra, so `f` is the map
  -- `IsScalarTower.toAlgHom R A B` that appears in `baseChangeMkQ_rTensor`
  have hf : IsScalarTower.toAlgHom R A B = f := AlgHom.ext fun _ ↦ rfl
  have := baseChangeMkQ_rTensor (B := B) N.toSubmodule x
  rw [hf] at this
  rw [this, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hx, tmul_zero]

end BaseChange

end Module.Grassmannian
