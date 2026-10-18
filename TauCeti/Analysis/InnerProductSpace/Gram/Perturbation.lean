/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Perturbation of Gram operators

For bounded maps `A, B : E →L[𝕜] F` between real or complex Hilbert spaces, the source Gram
operators `A† A` and `B† B` satisfy

`‖A† A - B† B‖ ≤ (‖A‖ + ‖B‖) * ‖A - B‖`.

The same bound holds for the target Gram operators `A A†` and `B B†`. These estimates transfer
control of a rectangular operator perturbation to its positive Gram operators, whose spectra
determine the squared singular values. They apply in arbitrary dimension, including trivial
source or target spaces.

The identities expose the two terms linear in the perturbation `A - B`. The target-space
statements follow from the source-space statements by taking adjoints. The proofs use Mathlib's
isometric adjoint equivalence and the submultiplicativity of the operator norm.

## References

* G. W. Stewart and J.-G. Sun, *Matrix Perturbation Theory*, Academic Press (1990), Chapter I
  (norm estimates for matrix products).
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The difference of the source Gram operators is the sum of two products with the
perturbation `A - B`. -/
theorem adjoint_comp_self_sub_adjoint_comp_self (A B : E →L[𝕜] F) :
    A.adjoint ∘L A - B.adjoint ∘L B =
      A.adjoint ∘L (A - B) + (A - B).adjoint ∘L B := by
  simp only [map_sub, comp_sub, sub_comp]
  abel

/-- The difference of the target Gram operators is the sum of two products with the
perturbation `A - B`. -/
theorem self_comp_adjoint_sub_self_comp_adjoint (A B : E →L[𝕜] F) :
    A ∘L A.adjoint - B ∘L B.adjoint =
      A ∘L (A - B).adjoint + (A - B) ∘L B.adjoint := by
  simpa only [adjoint_adjoint, map_sub] using
    adjoint_comp_self_sub_adjoint_comp_self A.adjoint B.adjoint

/-- Perturbing an operator changes its source Gram operator by at most the norm of the
perturbation times the sum of the two operator norms. -/
theorem norm_adjoint_comp_self_sub_adjoint_comp_self_le (A B : E →L[𝕜] F) :
    ‖A.adjoint ∘L A - B.adjoint ∘L B‖ ≤ (‖A‖ + ‖B‖) * ‖A - B‖ := by
  rw [adjoint_comp_self_sub_adjoint_comp_self]
  calc
    ‖A.adjoint ∘L (A - B) + (A - B).adjoint ∘L B‖ ≤
        ‖A.adjoint ∘L (A - B)‖ + ‖(A - B).adjoint ∘L B‖ := norm_add_le _ _
    _ ≤ ‖A.adjoint‖ * ‖A - B‖ + ‖(A - B).adjoint‖ * ‖B‖ :=
      add_le_add (opNorm_comp_le _ _) (opNorm_comp_le _ _)
    _ = (‖A‖ + ‖B‖) * ‖A - B‖ := by
      rw [adjoint.norm_map, adjoint.norm_map]
      ring

/-- Perturbing an operator changes its target Gram operator by at most the norm of the
perturbation times the sum of the two operator norms. -/
theorem norm_self_comp_adjoint_sub_self_comp_adjoint_le (A B : E →L[𝕜] F) :
    ‖A ∘L A.adjoint - B ∘L B.adjoint‖ ≤ (‖A‖ + ‖B‖) * ‖A - B‖ := by
  simpa only [adjoint_adjoint, ← adjoint.map_sub, adjoint.norm_map] using
    norm_adjoint_comp_self_sub_adjoint_comp_self_le A.adjoint B.adjoint

end ContinuousLinearMap
