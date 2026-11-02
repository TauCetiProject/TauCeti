/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.GraphAutomorphism.Diagonal.Basic
public import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Fixed diagonal matrices for the type-A graph automorphism

The actual intersection of the trace-zero diagonal submodule with the fixed submodule
of the pinned graph automorphism is identified with reversal-invariant coroot coordinates.
-/

public section

namespace TauCeti

open LieAlgebra.SpecialLinear

attribute [local instance 100] LieRing.ofAssociativeRing

variable (r : ℕ) (A : Type*) [CommRing A]

/-- Diagonal trace-zero matrices fixed by the pinned type-A graph automorphism. -/
def typeASpecialLinearFixedDiagonal : Submodule A (sl (Fin (r + 1)) A) :=
  specialLinearDiagonal r A ⊓
    (typeASpecialLinearGraphAutomorphism r A).toLinearEquiv.toLinearMap.fixedSubmodule

/-- Membership asserts diagonality and fixedness in the native special linear algebra. -/
@[simp]
theorem mem_typeASpecialLinearFixedDiagonal_iff (X : sl (Fin (r + 1)) A) :
    X ∈ typeASpecialLinearFixedDiagonal r A ↔
      X.val.IsDiag ∧ typeASpecialLinearGraphAutomorphism r A X = X := by
  simp only [typeASpecialLinearFixedDiagonal, Submodule.mem_inf,
    mem_specialLinearDiagonal_iff, LinearMap.mem_fixedSubmodule_iff,
    LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv]

/-- Simple-coroot coordinates identify the fixed diagonal submodule with fixed reversal tuples. -/
noncomputable def typeASpecialLinearFixedDiagonalEquiv :
    typeASpecialLinearFixedDiagonal r A ≃ₗ[A]
      (LinearEquiv.funCongrLeft A A
        (Fin.revPerm : Equiv.Perm (Fin r))).toLinearMap.fixedSubmodule where
  toFun X := ⟨specialLinearCorootEquiv r A ⟨X.val, X.property.1⟩, by
    apply LinearMap.mem_fixedSubmodule_iff.mpr
    funext i
    have h := (typeASpecialLinearGraphAutomorphism_eq_self_iff_coroot r A
      ⟨X.val, X.property.1⟩).mp X.property.2 i
    simpa only [LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply,
      LinearMap.funLeft_apply, Function.comp_apply, Fin.revPerm_apply] using h⟩
  invFun c := ⟨((specialLinearCorootEquiv r A).symm c.val).val, by
    constructor
    · exact ((specialLinearCorootEquiv r A).symm c.val).property
    · apply LinearMap.mem_fixedSubmodule_iff.mpr
      apply (typeASpecialLinearGraphAutomorphism_eq_self_iff_coroot r A _).mpr
      intro i
      have h := congrFun (LinearMap.mem_fixedSubmodule_iff.mp c.property) i
      simpa only [LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply,
        LinearMap.funLeft_apply, Function.comp_apply, Fin.revPerm_apply,
        LinearEquiv.apply_symm_apply] using h⟩
  left_inv X := by
    apply Subtype.ext
    exact congrArg (fun Y : specialLinearDiagonal r A ↦ Y.val)
      ((specialLinearCorootEquiv r A).symm_apply_apply
      ⟨X.val, X.property.1⟩)
  right_inv c := by
    apply Subtype.ext
    exact (specialLinearCorootEquiv r A).apply_symm_apply c.val
  map_add' X Y := by
    apply Subtype.ext
    exact (specialLinearCorootEquiv r A).map_add ⟨X.val, X.property.1⟩
      ⟨Y.val, Y.property.1⟩
  map_smul' a X := by
    apply Subtype.ext
    exact (specialLinearCorootEquiv r A).map_smul a ⟨X.val, X.property.1⟩

/-- Fixed coroot coordinates are the same initial diagonal sums as before restriction. -/
@[simp]
theorem typeASpecialLinearFixedDiagonalEquiv_apply
    (X : typeASpecialLinearFixedDiagonal r A) (i : Fin r) :
    (typeASpecialLinearFixedDiagonalEquiv r A X).val i =
      Fin.partialSum (fun j : Fin r ↦ X.val.val j.castSucc j.castSucc) i.succ := by
  exact specialLinearCorootEquiv_apply r A ⟨X.val, X.property.1⟩ i

/-- The inverse fixed-coordinate map retains the underlying native coroot reconstruction. -/
@[simp]
theorem typeASpecialLinearFixedDiagonalEquiv_symm_apply
    (c : (LinearEquiv.funCongrLeft A A
      (Fin.revPerm : Equiv.Perm (Fin r))).toLinearMap.fixedSubmodule) :
    ((typeASpecialLinearFixedDiagonalEquiv r A).symm c).val =
      ((specialLinearCorootEquiv r A).symm c.val).val :=
  (rfl)

end TauCeti
