/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Graded.Multilinear.Basic
public import TauCeti.Algebra.Module.GradedModule.Multilinear.Suspension
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Suspension of operations on composable paths

An arity-`n` operation of degree `2 - n` on a graded linear quiver corresponds to a degree-one
operation on its suspended Hom modules. `GradedLinearQuiver.pathSuspensionEquiv` implements
this correspondence for each composable string, including both round trips. Inputs retain
Keller's order `(aₙ, …, a₁)`.

Both sides are families of multilinear maps on homogeneous pieces. The construction extends
these families to total Hom modules, applies the dependent suspension equivalence, and restricts
back to pieces. No casts of multilinear maps along equalities of degrees are part of the API.
The evaluation formula measures the sign in the original degrees, so an input of suspended
degree `d` contributes `d + 1`. The unary and binary formulas pin the differential and
composition conventions used for higher categories.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.6 and 7.1.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
-/

public section

open scoped BigOperators

namespace TauCeti.GradedLinearQuiver

universe u v w

variable (R : Type w) [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]
  {n : ℕ} (X : Fin (n + 1) → C)

/-- Degree-one path operations on suspended Hom modules. An input of suspended degree `d i`
is an original morphism of degree `d i + 1`; the output has original degree `∑ i, d i + 2`. -/
abbrev SuspendedPathOperation := ∀ d : Fin n → ℤ,
  MultilinearMap R (fun i : Fin n ↦ grHom R (X i.rev.castSucc) (X i.rev.succ) (d i + 1))
    (grHom R (X 0) (X (Fin.last n)) (((∑ i, d i) + 1) + 1))

/-- Suspension and unsuspension give mutually inverse linear correspondences between
degree-`2 - n` path operations and degree-one operations on suspended Hom modules. -/
noncomputable def pathSuspensionEquiv :
    PathOperation R X (2 - n) ≃ₗ[R] SuspendedPathOperation R X := by
  let G := fun i : Fin n ↦ grading (R := R) (X i.rev.castSucc) (X i.rev.succ)
  let ℬ := (grading (R := R) (X 0) (X (Fin.last n))).piece
  exact (pathOperationEquiv R X (2 - n)).symm.trans
    ((InternalGrading.suspensionEquiv G ℬ 1).trans
      ((InternalGrading.homogeneousMultilinearEquiv
        (fun i ↦ (G i).shift 1) (Graded.shift ℬ 1) 1).trans
        (LinearEquiv.piCongrRight fun d ↦
          (LinearEquiv.multilinearMapCongrLeft fun i ↦
            (LinearEquiv.ofEq _ _ ((G i).shift_piece 1 (d i))).symm).trans
          (LinearEquiv.multilinearMapCongrRight R
            (LinearEquiv.ofEq _ _ (Graded.shift_apply ℬ 1 ((∑ i, d i) + 1)))))))

/-- The path suspension square has the Koszul sign of moving each suspension past the inputs
to its left. Degrees in the exponent are original, rather than suspended, degrees. -/
@[simp]
theorem coe_pathSuspensionEquiv_apply (f : PathOperation R X (2 - n))
    (d : Fin n → ℤ)
    (x : ∀ i : Fin n, grHom R (X i.rev.castSucc) (X i.rev.succ) (d i + 1)) :
    (pathSuspensionEquiv R X f d x : homModule (R := R) (X 0) (X (Fin.last n))) =
      negOnePowCast R (∑ i : Fin n, ((n : ℤ) - 1 - i) * (d i + 1)) •
        (f (fun i ↦ d i + 1) x : homModule (R := R) (X 0) (X (Fin.last n))) := by
  simp only [pathSuspensionEquiv, LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply,
    LinearEquiv.multilinearMapCongrLeft_apply, LinearEquiv.multilinearMapCongrRight_apply,
    LinearMap.compMultilinearMap_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.coe_ofEq_apply, MultilinearMap.compLinearMap_apply,
    InternalGrading.coe_homogeneousMultilinearEquiv_apply,
    LinearEquiv.ofEq_symm]
  rw [InternalGrading.suspensionEquiv_apply_of_mem _ _ _ _
    (fun i ↦ d i + 1) _ (fun i ↦ (x i).property)]
  rw [pathOperationEquiv_symm_apply]

/-- Unsuspension uses the same sign as suspension when evaluated on the same original
homogeneous morphisms. -/
@[simp]
theorem coe_pathSuspensionEquiv_symm_apply (b : SuspendedPathOperation R X)
    (d : Fin n → ℤ)
    (x : ∀ i : Fin n, grHom R (X i.rev.castSucc) (X i.rev.succ) (d i + 1)) :
    ((pathSuspensionEquiv R X).symm b (fun i ↦ d i + 1) x :
        homModule (R := R) (X 0) (X (Fin.last n))) =
      negOnePowCast R (∑ i : Fin n, ((n : ℤ) - 1 - i) * (d i + 1)) •
        (b d x : homModule (R := R) (X 0) (X (Fin.last n))) := by
  have h := coe_pathSuspensionEquiv_apply R X ((pathSuspensionEquiv R X).symm b) d x
  rw [LinearEquiv.apply_symm_apply] at h
  rw [h, negOnePowCast_smul_negOnePowCast_smul]

/-- Unary suspension introduces no sign: the suspended differential is the original operation
viewed on regraded pieces. -/
theorem coe_pathSuspensionEquiv_apply_one (X : Fin 2 → C)
    (f : PathOperation R X 1) (d : Fin 1 → ℤ)
    (x : ∀ i : Fin 1, grHom R (X i.rev.castSucc) (X i.rev.succ) (d i + 1)) :
    (pathSuspensionEquiv R X f d x : homModule (R := R) (X 0) (X (Fin.last 1))) =
      (f (fun i ↦ d i + 1) x : homModule (R := R) (X 0) (X (Fin.last 1))) := by
  rw [coe_pathSuspensionEquiv_apply]
  simp

/-- Binary suspension has sign `(-1)^|g|` on inputs `(g,f)`, where `|g|` is the original
degree of the first input. There is no change to the order of composable morphisms. -/
theorem coe_pathSuspensionEquiv_apply_two (X : Fin 3 → C)
    (f : PathOperation R X 0) (d : Fin 2 → ℤ)
    (x : ∀ i : Fin 2, grHom R (X i.rev.castSucc) (X i.rev.succ) (d i + 1)) :
    (pathSuspensionEquiv R X f d x : homModule (R := R) (X 0) (X (Fin.last 2))) =
      negOnePowCast R (d 0 + 1) •
        (f (fun i ↦ d i + 1) x : homModule (R := R) (X 0) (X (Fin.last 2))) := by
  rw [coe_pathSuspensionEquiv_apply]
  simp [Fin.sum_univ_two]

end TauCeti.GradedLinearQuiver
