/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import TauCeti.RepresentationTheory.ClassicalGroups.Restriction
public import TauCeti.RepresentationTheory.Spin.HalfSpin.Basic
import TauCeti.RepresentationTheory.Intertwining

/-!
# Matrix models of the even half-spin representation

This file turns a matrix formula for the even half-spin action into an equivalence with the
standard representation of a special linear group. The comparison is independent of the
dimension of the quadratic space and the size of the matrices.

## Main result

* `TauCeti.nonempty_spinPlusSubrep_equiv_stdSLRep_of_matrix_action`: a matrix formula for the
  even half-spin action identifies it with the pulled-back standard representation.
-/

public section

open CliffordAlgebra Module

namespace TauCeti

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- A matrix formula for the even half-spin action identifies that representation with the
standard representation pulled back along a homomorphism to the special linear group. -/
theorem nonempty_spinPlusSubrep_equiv_stdSLRep_of_matrix_action
    {n : ℕ} {P : SpinPolarizationData Q} (hline : P.line = ⊥)
    (b : Basis (Fin n) K (spinPlus Q P))
    (f : spinGroup Q →* Matrix.SpecialLinearGroup (Fin n) K)
    (hmatrix : ∀ s : spinGroup Q,
      (f s : Matrix (Fin n) (Fin n) K) =
        LinearMap.toMatrix b b (spinPlusAction Q P hline (spinGroupToEven Q s))) :
    Nonempty ((spinPlusSubrep P hline).toRepresentation.Equiv
      ((stdSLRep K n).comp f)) := by
  let ep : spinPlus Q P ≃ₗ[K] (spinPlusSubrep P hline).toSubmodule :=
    LinearEquiv.ofEq _ _ (toSubmodule_spinPlusSubrep P hline).symm
  refine ⟨Representation.Equiv.ofBasisAction _ _ ep.symm b
    (fun s ↦ spinPlusAction Q P hline (spinGroupToEven Q s)) ?_ ?_⟩
  · intro s x
    apply Subtype.ext
    simpa only [ep, LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply] using
      (coe_spinPlusAction_spinGroupToEven_apply P hline s (ep.symm x)).symm
  · intro s x
    simp only [MonoidHom.comp_apply, stdSLRep_apply_apply]
    rw [hmatrix]
    exact LinearMap.toMatrix_mulVec_repr b b
      (spinPlusAction Q P hline (spinGroupToEven Q s)) x

end TauCeti

end
