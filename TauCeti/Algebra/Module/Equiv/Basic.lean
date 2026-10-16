/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Linear equivalences and their underlying maps

Mathlib's `LinearEquiv.smulOfUnit` packages multiplication by a unit `u` of the base ring as a
linear equivalence, but records no lemma evaluating it at a vector. This file supplies that
evaluation lemma, in the `simp`-normal form that rewrites an application of
`LinearEquiv.smulOfUnit` to a scalar multiplication. It also records how a linear automorphism,
viewed as a permutation of the module through `MulAction.toPermHom`, moves the set underlying a
submodule.
Postcomposition with an isomorphism of targets also transports hom spaces over auxiliary
scalars, even when the ring defining the linear maps is noncommutative.
For coordinate transport, forgetting linearity gives the corresponding additive word
equivalence, with the same direction on coordinates.

## Main results

* `LinearEquiv.homCongrRight`: an isomorphism of targets induces an equivalence of hom spaces
  over the auxiliary scalar semiring.

* `LinearEquiv.map_ker_of_intertwine` and `LinearEquiv.map_range_of_intertwine`: transport of
  kernels and ranges across an intertwining semilinear equivalence.
* `LinearEquiv.toPermHom_smul_coe`: the permutation of the module underlying a linear
  automorphism moves the set underlying a submodule to the set underlying its image.
* `LinearEquiv.smulOfUnit_apply`: `LinearEquiv.smulOfUnit u` acts as multiplication by `u`.
* `LinearEquiv.funCongrLeft_toAddMonoidHom`: forgetting linearity in coordinate transport
  gives additive coordinate transport.
-/

public section

namespace LinearEquiv

section Coordinates

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] {ι κ : Type*}

/-- The additive homomorphism underlying linear coordinate transport is the one underlying
`AddEquiv.arrowCongr`, with the coordinate equivalence reversed. -/
@[simp]
theorem funCongrLeft_toAddMonoidHom (e : κ ≃ ι) :
    ((funCongrLeft R M e : (ι → M) →ₗ[R] κ → M) : (ι → M) →+ κ → M) =
      (AddEquiv.arrowCongr e.symm (AddEquiv.refl M)) := by
  ext x i
  simp

end Coordinates

section HomCongrRight

variable (k : Type*) {A : Type*} [CommSemiring k] [Semiring A] [Algebra k A]
variable {S : Type*} [AddCommMonoid S] [Module A S]
variable {N : Type*} [AddCommMonoid N] [Module A N] [Module k N] [IsScalarTower k A N]
variable {P : Type*} [AddCommMonoid P] [Module A P] [Module k P] [IsScalarTower k A P]

/-- **Isomorphic targets give isomorphic hom spaces.**  An `A`-linear isomorphism `e : N ≃ₗ[A] P`
carries `S →ₗ[A] N` to `S →ₗ[A] P` by postcomposition, `k`-linearly.

This is `LinearEquiv.congrRight` with the auxiliary scalars `k` in place of a commutativity
assumption on `A`: since `A` is not assumed commutative the hom spaces are not `A`-modules, and
`k`, acting on the targets compatibly with `A`, supplies the linear structure instead.  The two
directions are `LinearMap.compRight`. -/
def homCongrRight (e : N ≃ₗ[A] P) : (S →ₗ[A] N) ≃ₗ[k] (S →ₗ[A] P) :=
  LinearEquiv.ofLinearMap (LinearMap.compRight (M := S) k (e : N →ₗ[A] P))
    (LinearMap.compRight (M := S) k (e.symm : P →ₗ[A] N))
    (by ext f s; simp) (by ext f s; simp)

@[simp]
theorem homCongrRight_apply (e : N ≃ₗ[A] P) (f : S →ₗ[A] N) (s : S) :
    homCongrRight k (S := S) e f s = e (f s) :=
  (rfl)

@[simp]
theorem homCongrRight_symm_apply (e : N ≃ₗ[A] P) (f : S →ₗ[A] P) (s : S) :
    (homCongrRight k (S := S) e).symm f s = e.symm (f s) :=
  (rfl)

end HomCongrRight

section Intertwining

variable {R S M N : Type*} [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module S N] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ']
  [RingHomInvPair σ' σ]

/-- If a semilinear equivalence `e` intertwines two endomorphisms `f` and `g` pointwise
(`g (e d) = e (f d)`), it carries the kernel of `f` onto the kernel of `g`. -/
theorem map_ker_of_intertwine
    (e : M ≃ₛₗ[σ] N) (f : M →ₗ[R] M) (g : N →ₗ[S] N)
    (h : ∀ d, g (e d) = e (f d)) :
    Submodule.map (e : M →ₛₗ[σ] N) (LinearMap.ker f) = LinearMap.ker g := by
  ext c
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨d, hd, rfl⟩
    rw [h d, hd, map_zero]
  · intro hc
    refine ⟨e.symm c, ?_, e.apply_symm_apply c⟩
    have : e (f (e.symm c)) = 0 := by rw [← h, e.apply_symm_apply, hc]
    exact e.map_eq_zero_iff.mp this

/-- If a semilinear equivalence `e` intertwines two endomorphisms `f` and `g` pointwise
(`g (e d) = e (f d)`), it carries the range of `f` onto the range of `g`. -/
theorem map_range_of_intertwine
    (e : M ≃ₛₗ[σ] N) (f : M →ₗ[R] M) (g : N →ₗ[S] N)
    (h : ∀ d, g (e d) = e (f d)) :
    Submodule.map (e : M →ₛₗ[σ] N) (LinearMap.range f) = LinearMap.range g := by
  ext c
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨d, ⟨b, rfl⟩, rfl⟩
    exact ⟨e b, h b⟩
  · rintro ⟨b, rfl⟩
    exact ⟨f (e.symm b), ⟨e.symm b, rfl⟩, by rw [← h, e.apply_symm_apply]⟩

end Intertwining

section PermHom

open Pointwise

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- The permutation of the module underlying a linear automorphism moves the set underlying a
submodule to the set underlying its image. -/
theorem toPermHom_smul_coe (g : M ≃ₗ[R] M) (p : Submodule R M) :
    MulAction.toPermHom (M ≃ₗ[R] M) M g • (p : Set M) = (p.map (g : M →ₗ[R] M) : Set M) := by
  ext x
  simp only [Set.mem_smul_set, SetLike.mem_coe, Submodule.mem_map, MulAction.toPermHom_apply,
    Equiv.Perm.smul_def, MulAction.toPerm_apply, LinearEquiv.smul_def, LinearEquiv.coe_coe]

end PermHom

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Multiplication by a unit of the base ring, evaluated: `LinearEquiv.smulOfUnit u` sends `x` to
`u • x`. -/
@[simp]
theorem smulOfUnit_apply (u : Rˣ) (x : M) : (smulOfUnit u : M ≃ₗ[R] M) x = (u : R) • x :=
  (rfl)

end LinearEquiv
