/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.IsTensorProduct

import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Algebra homomorphisms out of a pushout over the base change

Let `S'` be the pushout of `R → S` along `R → R'`, as expressed by `Algebra.IsPushout R S R' S'`.
Mathlib's `Algebra.pushoutDesc` describes the `R`-algebra homomorphisms out of `S'`. This file
describes the `R'`-algebra homomorphisms out of `S'`: they are determined by their restrictions to
`S`, and every `R`-algebra homomorphism out of `S` extends to one. It also records the naturality
of `Algebra.IsPushout.cancelBaseChangeAlg` in the coefficient algebra.

## Main definitions

* `Algebra.IsPushout.lift f`: the `R'`-algebra homomorphism `S' →ₐ[R'] A` extending an
  `R`-algebra homomorphism `f : S →ₐ[R] A` along `S → S'`.

## Main results

* `Algebra.IsPushout.lift_algebraMap`: `lift f` restricts to `f` on `S`.
* `Algebra.IsPushout.algHom_ext'`: `R'`-algebra homomorphisms out of `S'` agreeing on `S` are
  equal.
* `Module.Finite.of_isPushout`, `Module.Projective.of_isPushout`,
  `Algebra.FinitePresentation.of_isPushout`: finiteness, projectivity and finite presentation are
  stable under pushout.
* `Algebra.IsPushout.cancelBaseChangeAlg_symm_lTensor`: the isomorphism
  `S ⊗[R] T ≃ₐ[S] S' ⊗[R'] T` is natural in the `R'`-algebra `T`.
-/

public section

open scoped TensorProduct

namespace Algebra.IsPushout

section CommSemiring

variable {R S R' S' : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring R'] [CommSemiring S']
  [Algebra R S] [Algebra R R'] [Algebra R' S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R R' S']
  [IsScalarTower R S S'] [IsPushout R S R' S']

section Lift

variable {A : Type*} [Semiring A] [Algebra R' A] [Algebra R A] [IsScalarTower R R' A]

variable (R') in
/-- The `R'`-algebra homomorphism out of the pushout `S'` extending an `R`-algebra homomorphism
`f : S →ₐ[R] A` along `S → S'`. -/
noncomputable def lift (f : S →ₐ[R] A) : S' →ₐ[R'] A :=
  { pushoutDesc S' f (IsScalarTower.toAlgHom R R' A) fun x y ↦ (Algebra.commutes y (f x)).symm with
    commutes' := pushoutDesc_right S' f _ _ }

/-- `lift R' f` restricts to `f` on `S`. -/
@[simp]
theorem lift_algebraMap (f : S →ₐ[R] A) (s : S) : lift R' f (algebraMap S S' s) = f s := by
  unfold lift
  exact pushoutDesc_left S' f _ _ s

/-- Two `R'`-algebra homomorphisms out of the pushout `S'` that agree on `S` are equal. -/
@[ext (iff := false)]
theorem algHom_ext' {f g : S' →ₐ[R'] A}
    (h : (f.restrictScalars R).comp (IsScalarTower.toAlgHom R S S') =
      (g.restrictScalars R).comp (IsScalarTower.toAlgHom R S S')) : f = g :=
  AlgHom.restrictScalars_injective R <| IsPushout.algHom_ext (R' := R') S' (by ext; simp) h

end Lift

section Finiteness

variable (R S R' S')

/-- Finiteness as a module is stable under pushout: if `S` is a finite `R`-module, then the pushout
`S'` is a finite `R'`-module. -/
theorem _root_.Module.Finite.of_isPushout [Module.Finite R S] : Module.Finite R' S' := by
  have := IsPushout.symm (inferInstance : IsPushout R S R' S')
  exact Module.Finite.equiv (IsPushout.equiv R R' S S').toLinearEquiv

/-- Projectivity as a module is stable under pushout: if `S` is a projective `R`-module, then the
pushout `S'` is a projective `R'`-module. -/
theorem _root_.Module.Projective.of_isPushout [Module.Projective R S] :
    Module.Projective R' S' := by
  have := IsPushout.symm (inferInstance : IsPushout R S R' S')
  exact Module.Projective.of_equiv (IsPushout.equiv R R' S S').toLinearEquiv

end Finiteness

end CommSemiring

section CommRing

variable {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R S]
  [Algebra R R'] [Algebra R' S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R R' S']
  [IsScalarTower R S S'] [IsPushout R S R' S']

variable (R S R' S') in
/-- Finite presentation is stable under pushout: if `S` is a finitely presented `R`-algebra, then
the pushout `S'` is a finitely presented `R'`-algebra. -/
theorem _root_.Algebra.FinitePresentation.of_isPushout [FinitePresentation R S] :
    FinitePresentation R' S' := by
  have := IsPushout.symm (inferInstance : IsPushout R S R' S')
  exact FinitePresentation.equiv (IsPushout.equiv R R' S S')

variable (S') in
/-- The isomorphism `S ⊗[R] T ≃ₐ[S] S' ⊗[R'] T` is natural in the `R'`-algebra `T`. -/
theorem cancelBaseChangeAlg_symm_lTensor {T T' : Type*} [CommRing T] [Algebra R' T]
    [Algebra R T] [IsScalarTower R R' T] [CommRing T'] [Algebra R' T'] [Algebra R T']
    [IsScalarTower R R' T'] (g : T →ₐ[R'] T') (z : S ⊗[R] T) :
    (cancelBaseChangeAlg R S R' S' T').symm
        (Algebra.TensorProduct.lTensor (S := S) S (g.restrictScalars R) z) =
      Algebra.TensorProduct.lTensor (S := S') S' g ((cancelBaseChangeAlg R S R' S' T).symm z) := by
  induction z <;> simp [*]

end CommRing

end Algebra.IsPushout
