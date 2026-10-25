/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.Diagonal
public import TauCeti.Algebra.Lie.SpecialLinear.GraphAutomorphism

/-!
# Diagonal coordinates for the type-A graph automorphism

The pinned special-linear graph automorphism reverses the simple-coroot coordinates
on the trace-zero diagonal submodule. All statements hold over any commutative ring.
-/

public section

namespace TauCeti

open LieAlgebra.SpecialLinear

attribute [local instance 100] LieRing.ofAssociativeRing

variable (r : ℕ) (A : Type*) [CommRing A]

/-- The graph automorphism reverses simple-coroot coordinates in the native Lie algebra. -/
theorem typeASpecialLinearGraphAutomorphism_corootEquiv_symm (c : Fin r → A) :
    typeASpecialLinearGraphAutomorphism r A ((specialLinearCorootEquiv r A).symm c).val =
      ((specialLinearCorootEquiv r A).symm (fun i ↦ c i.rev)).val := by
  rw [specialLinearCorootEquiv_symm_val, specialLinearCorootEquiv_symm_val, map_sum]
  simp only [map_smul, typeASpecialLinearGraphAutomorphism_coroot]
  simpa using (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin r))
    (fun i ↦ c i.rev • singleSubSingle i.castSucc i.succ (1 : A)))

/-- The pinned graph automorphism preserves the trace-zero diagonal submodule. -/
theorem typeASpecialLinearGraphAutomorphism_mem_diagonal (X : specialLinearDiagonal r A) :
    typeASpecialLinearGraphAutomorphism r A X.val ∈ specialLinearDiagonal r A := by
  have h := typeASpecialLinearGraphAutomorphism_corootEquiv_symm r A
    (specialLinearCorootEquiv r A X)
  rw [LinearEquiv.symm_apply_apply] at h
  rw [h]
  exact ((specialLinearCorootEquiv r A).symm
    (fun i ↦ specialLinearCorootEquiv r A X i.rev)).property

/-- A trace-zero diagonal matrix is fixed exactly when its coroot coordinates are symmetric. -/
theorem typeASpecialLinearGraphAutomorphism_eq_self_iff_coroot
    (X : specialLinearDiagonal r A) :
    typeASpecialLinearGraphAutomorphism r A X.val = X.val ↔
      ∀ i, specialLinearCorootEquiv r A X i.rev = specialLinearCorootEquiv r A X i := by
  have h := typeASpecialLinearGraphAutomorphism_corootEquiv_symm r A
    (specialLinearCorootEquiv r A X)
  rw [LinearEquiv.symm_apply_apply] at h
  rw [h]
  constructor
  · intro hX i
    have he : (specialLinearCorootEquiv r A).symm
        (fun i ↦ specialLinearCorootEquiv r A X i.rev) = X := Subtype.ext hX
    simpa only [LinearEquiv.apply_symm_apply] using
      congrFun (congrArg (specialLinearCorootEquiv r A) he) i
  · intro hc
    rw [funext hc, LinearEquiv.symm_apply_apply]

end TauCeti
