/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Basic facts about monoid algebras

General facts about the monoid algebra `R[G]` that use only its basis elements `single g r`, and
none of the further theory built on it.

## Main results

* `TauCeti.single_sub_one_ne_zero`: over a nontrivial ring, the difference `single g 1 - 1`
  between the basis element at `g` and the unit is nonzero when `g ≠ 1`.
* The `IsMulCommutative (MonoidAlgebra R M)` instance: the monoid algebra of a commutative
  magma over a commutative semiring is commutative, as a mixin on the existing ring structure.
* `TauCeti.MonoidAlgebra.mem_ideal_smul_top_iff`: an element of `R[M]` lies in `I • R[M]` exactly
  when its coefficients lie in `I`, and `TauCeti.MonoidAlgebra.mapRingHom_eq_zero_iff`: the kernel
  of the coefficientwise map along `f : R →+* S` is `ker f • R[M]`.

## References

Injectivity of `single` in its index is Mathlib's `MonoidAlgebra.single_left_injective`.
-/

public section

namespace TauCeti

section Commutative

variable {R : Type*} [CommSemiring R] {M : Type*} [Mul M]

/-- The monoid algebra of a commutative magma over a commutative semiring is commutative. This is
the mixin form of Mathlib's `MonoidAlgebra.nonUnitalCommSemiring`, for a multiplication that is
commutative without carrying a `CommSemigroup` instance. -/
instance instIsMulCommutativeMonoidAlgebra [IsMulCommutative M] :
    IsMulCommutative (MonoidAlgebra R M) where
  is_comm.comm f g := by
    have hM := isMulCommutative_iff.mp (inferInstance : IsMulCommutative M)
    simp [MonoidAlgebra.mul_def, Finsupp.sum, mul_comm, hM, f.coeff.support.sum_comm]

end Commutative

variable {R : Type*} [Ring R] {G : Type*} [One G]

/-- Over a nontrivial ring, the difference `single g 1 - 1` between the basis element at `g` and the
unit is nonzero when `g ≠ 1`. -/
theorem single_sub_one_ne_zero [Nontrivial R] {g : G} (hg : g ≠ 1) :
    MonoidAlgebra.single g (1 : R) - 1 ≠ 0 := by
  rw [sub_ne_zero, MonoidAlgebra.one_def]
  intro h
  exact hg (MonoidAlgebra.single_left_injective one_ne_zero h)

namespace MonoidAlgebra

variable {R : Type*} [CommSemiring R] {M : Type*}

/-- An element of `R[M]` lies in `I • R[M]` exactly when all of its coefficients lie in `I`. -/
@[simp]
theorem mem_ideal_smul_top_iff {I : Ideal R} {x : MonoidAlgebra R M} :
    x ∈ I • (⊤ : Submodule R (MonoidAlgebra R M)) ↔ ∀ m, x.coeff m ∈ I := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · refine Submodule.smul_induction_on hx (fun r hr n _ m ↦ ?_) fun x y hx hy m ↦ ?_
    · simpa using I.mul_mem_right (n.coeff m) hr
    · simpa using I.add_mem (hx m) (hy m)
  · rw [← MonoidAlgebra.sum_coeff_single x, Finsupp.sum]
    refine Submodule.sum_mem _ fun m _ ↦ ?_
    simpa [MonoidAlgebra.smul_single'] using
      Submodule.smul_mem_smul (hx m) (Submodule.mem_top (x := MonoidAlgebra.single m (1 : R)))

/-- Applying a ring homomorphism `f` to the coefficients kills exactly `ker f • R[M]`. -/
@[simp]
theorem mapRingHom_eq_zero_iff [Monoid M] {S : Type*} [Semiring S] (f : R →+* S)
    {x : MonoidAlgebra R M} :
    MonoidAlgebra.mapRingHom M f x = 0 ↔
      x ∈ RingHom.ker f • (⊤ : Submodule R (MonoidAlgebra R M)) := by
  rw [mem_ideal_smul_top_iff, ← MonoidAlgebra.coeff_inj]
  simp [Finsupp.ext_iff, MonoidAlgebra.coeff_mapRingHom]

end MonoidAlgebra

end TauCeti
