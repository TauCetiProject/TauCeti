/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Off-diagonal coordinates in the special linear Lie algebra

The kernel of diagonal evaluation in the native special linear algebra has coordinates
indexed by unequal pairs. Its coordinate basis consists of the native off-diagonal
matrix units, over every commutative ring.
-/

public section

namespace TauCeti

open LieAlgebra.SpecialLinear

attribute [local instance 100] LieRing.ofAssociativeRing

variable (I : Type*) [Fintype I] [DecidableEq I] (A : Type*) [CommRing A]

/-- The zero-diagonal submodule of the native special linear algebra. -/
def specialLinearOffDiagonal : Submodule A (sl I A) :=
  LinearMap.ker ((Matrix.diagLinearMap I A A).comp (sl I A).toSubmodule.subtype)

/-- Membership means that every diagonal entry of the native matrix vanishes. -/
@[simp]
theorem mem_specialLinearOffDiagonal_iff (X : sl I A) :
    X ∈ specialLinearOffDiagonal I A ↔ ∀ i, X.val i i = 0 := by
  rw [specialLinearOffDiagonal, LinearMap.mem_ker]
  exact funext_iff

/-- Off-diagonal entries give coordinates on the zero-diagonal submodule. -/
def specialLinearOffDiagonalEquiv :
    specialLinearOffDiagonal I A ≃ₗ[A] ({p : I × I // p.1 ≠ p.2} → A) where
  toFun X p := X.val.val p.val.1 p.val.2
  invFun c := ⟨⟨Matrix.of (fun i j ↦ if h : i = j then 0 else c ⟨(i, j), h⟩), by
    apply LinearMap.mem_ker.mpr
    rw [Matrix.traceLinearMap_apply]
    simp [Matrix.trace, Matrix.diag]⟩, by
    rw [mem_specialLinearOffDiagonal_iff]
    intro i
    simp⟩
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    funext i j
    dsimp
    split_ifs with h
    · subst j
      exact ((mem_specialLinearOffDiagonal_iff I A X.val).mp X.property i).symm
    · rfl
  right_inv c := by
    funext p
    simp [p.property]
  map_add' X Y := by
    funext p
    rfl
  map_smul' a X := by
    funext p
    rfl

/-- The coordinate map reads the corresponding native matrix entry. -/
@[simp]
theorem specialLinearOffDiagonalEquiv_apply (X : specialLinearOffDiagonal I A)
    (p : {p : I × I // p.1 ≠ p.2}) :
    specialLinearOffDiagonalEquiv I A X p = X.val.val p.val.1 p.val.2 :=
  (rfl)

/-- Reconstruction inserts zeros on the diagonal and the given off-diagonal entries. -/
@[simp]
theorem specialLinearOffDiagonalEquiv_symm_apply
    (c : {p : I × I // p.1 ≠ p.2} → A) (i j : I) :
    ((specialLinearOffDiagonalEquiv I A).symm c).val.val i j =
      if h : i = j then 0 else c ⟨(i, j), h⟩ :=
  (rfl)

/-- The coordinate basis of the native zero-diagonal submodule. -/
noncomputable def specialLinearOffDiagonalBasis :
    Module.Basis {p : I × I // p.1 ≠ p.2} A (specialLinearOffDiagonal I A) :=
  Module.Basis.ofEquivFun (specialLinearOffDiagonalEquiv I A)

/-- Basis coordinates are the off-diagonal matrix entries. -/
@[simp]
theorem specialLinearOffDiagonalBasis_repr (X : specialLinearOffDiagonal I A)
    (p : {p : I × I // p.1 ≠ p.2}) :
    (specialLinearOffDiagonalBasis I A).repr X p = X.val.val p.val.1 p.val.2 := by
  rw [specialLinearOffDiagonalBasis, Module.Basis.ofEquivFun_repr_apply,
    specialLinearOffDiagonalEquiv_apply]

/-- Every native off-diagonal matrix unit lies in the zero-diagonal submodule. -/
theorem single_mem_specialLinearOffDiagonal (i j : I) (h : i ≠ j) (a : A) :
    single i j h a ∈ specialLinearOffDiagonal I A := by
  rw [mem_specialLinearOffDiagonal_iff]
  intro k
  by_cases hi : i = k
  · subst k
    simp [val_single, h, eq_comm]
  · simp [val_single, hi]

/-- The coordinate basis vectors are precisely the native matrix units. -/
@[simp]
theorem specialLinearOffDiagonalBasis_apply (p : {p : I × I // p.1 ≠ p.2}) :
    (specialLinearOffDiagonalBasis I A p).val =
      single p.val.1 p.val.2 p.property 1 := by
  rw [specialLinearOffDiagonalBasis, Module.Basis.coe_ofEquivFun]
  apply Subtype.ext
  ext i j
  rw [specialLinearOffDiagonalEquiv_symm_apply, val_single]
  by_cases hij : i = j
  · subst j
    by_cases hi : p.val.1 = i
    · subst i
      simp [p.property, eq_comm]
    · simp [hi]
  · simp [hij, Pi.single_apply, Matrix.single_apply, Subtype.ext_iff, Prod.ext_iff,
      eq_comm]

end TauCeti
