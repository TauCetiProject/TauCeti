/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAction.SubMulAction
public import TauCeti.LinearAlgebra.Matrix.NormTwoShell.Basic
public import TauCeti.LinearAlgebra.Matrix.ToQuadraticForm
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Action
public import Mathlib.Algebra.Group.Action.End
import Mathlib.Data.Fintype.Perm

/-!
# The orthogonal action on an integral norm-two shell

The integral orthogonal group of a matrix acts by permutations of its actual norm-two shell.
This representation is injective when the shell spans the lattice. Diagonal entries equal to
two suffice for spanning, since the coordinate vectors then belong to the shell.

Positive definiteness is used only to make the shell finite. Together with spanning, it gives
a finite orthogonal group, the finite permutation image needed for integral sign-cover lifts.
No symmetry or sign condition on off-diagonal entries is needed for the action or its faithfulness.
-/

public section

namespace Matrix

open QuadraticMap TauCeti.QuadraticMap

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The norm-two shell as an invariant subset for the integral orthogonal group. -/
def normTwoShellSubMulAction (B : Matrix I I ℤ) :
    SubMulAction (orthogonalGroup B.toQuadraticForm') (I → ℤ) :=
  (orthogonalLevelSet B.toQuadraticForm' 2).copy B.normTwoShell (by
    ext x
    rw [mem_normTwoShell, coe_orthogonalLevelSet, Set.mem_ofPred_eq,
      toQuadraticForm'_apply])

/-- The invariant subset has exactly the existing norm-two shell as its carrier. -/
@[simp]
theorem coe_normTwoShellSubMulAction (B : Matrix I I ℤ) :
    (normTwoShellSubMulAction B : Set (I → ℤ)) = B.normTwoShell := by
  simp only [normTwoShellSubMulAction, SubMulAction.coe_copy]

/-- Membership in the invariant subset is membership in the existing norm-two shell. -/
@[simp]
theorem mem_normTwoShellSubMulAction_iff (B : Matrix I I ℤ) (x : I → ℤ) :
    x ∈ normTwoShellSubMulAction B ↔ x ∈ B.normTwoShell :=
  Iff.rfl

/-- The integral orthogonal group acts by permutations of the norm-two shell. -/
def normTwoShellPermHom (B : Matrix I I ℤ) :
    orthogonalGroup B.toQuadraticForm' →* Equiv.Perm B.normTwoShell :=
  MulAction.toPermHom _ (normTwoShellSubMulAction B)

/-- On shell vectors, the permutation is the underlying integral linear equivalence. -/
@[simp]
theorem normTwoShellPermHom_apply (B : Matrix I I ℤ)
    (g : orthogonalGroup B.toQuadraticForm') (x : B.normTwoShell) :
    ↑(normTwoShellPermHom B g x) = (g : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)) x := by
  simp only [normTwoShellPermHom]
  rfl

/-- The inverse shell permutation is the restriction of the inverse linear equivalence. -/
@[simp]
theorem normTwoShellPermHom_symm_apply (B : Matrix I I ℤ)
    (g : orthogonalGroup B.toQuadraticForm') (x : B.normTwoShell) :
    ↑((normTwoShellPermHom B g).symm x) = (g : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)).symm x := by
  simp only [normTwoShellPermHom]
  rfl

/-- The kernel consists of orthogonal maps fixing every shell vector. -/
theorem mem_ker_normTwoShellPermHom_iff (B : Matrix I I ℤ)
    (g : orthogonalGroup B.toQuadraticForm') :
    g ∈ (normTwoShellPermHom B).ker ↔
      ∀ x ∈ B.normTwoShell, (g : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)) x = x := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h x hx
    simpa only [normTwoShellPermHom_apply, Equiv.Perm.one_apply] using
      congrArg Subtype.val (Equiv.congr_fun h ⟨x, hx⟩)
  · intro h
    apply Equiv.ext
    intro x
    apply Subtype.ext
    simpa only [normTwoShellPermHom_apply, Equiv.Perm.one_apply] using h x x.property

/-- A spanning norm-two shell determines every integral orthogonal map. -/
theorem normTwoShellPermHom_injective (B : Matrix I I ℤ)
    (hspan : Submodule.span ℤ B.normTwoShell = ⊤) :
    Function.Injective (normTwoShellPermHom B) := by
  have hs : Submodule.span ℤ (normTwoShellSubMulAction B : Set (I → ℤ)) = ⊤ := by
    simpa only [coe_normTwoShellSubMulAction] using hspan
  let := SubMulAction.faithfulSMul_of_span_eq_top (normTwoShellSubMulAction B) hs
  -- `copy` keeps the shell subtype while supplying its inherited action.
  change Function.Injective (MulAction.toPermHom _ (normTwoShellSubMulAction B))
  rw [MulAction.coe_toPermHom]
  exact MulAction.toPerm_injective

/-- Diagonal entries equal to two suffice for a faithful shell permutation representation. -/
theorem normTwoShellPermHom_injective_of_diagonal_eq_two (B : Matrix I I ℤ)
    (hdiag : ∀ i, B i i = 2) : Function.Injective (normTwoShellPermHom B) :=
  normTwoShellPermHom_injective B (span_normTwoShell_eq_top_of_diagonal_eq_two B hdiag)

/-- A positive definite integral form whose norm-two shell spans has finite orthogonal group. -/
theorem PosDef.finite_orthogonalGroup_of_span_normTwoShell_eq_top {B : Matrix I I ℤ}
    (hB : B.PosDef) (hspan : Submodule.span ℤ B.normTwoShell = ⊤) :
    Finite (orthogonalGroup B.toQuadraticForm') := by
  let : Finite B.normTwoShell := hB.finite_normTwoShell.to_subtype
  exact Finite.of_injective _ (normTwoShellPermHom_injective B hspan)

/-- Positive definiteness and diagonal two give a finite integral orthogonal group. -/
theorem PosDef.finite_orthogonalGroup_of_diagonal_eq_two {B : Matrix I I ℤ}
    (hB : B.PosDef) (hdiag : ∀ i, B i i = 2) :
    Finite (orthogonalGroup B.toQuadraticForm') :=
  hB.finite_orthogonalGroup_of_span_normTwoShell_eq_top
    (span_normTwoShell_eq_top_of_diagonal_eq_two B hdiag)

end Matrix
