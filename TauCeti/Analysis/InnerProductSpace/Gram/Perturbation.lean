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
source or target spaces. In finite dimension, pointwise bounds on algebraic linear maps give a
corresponding pointwise source-Gram perturbation estimate.

The identities expose the two terms linear in the perturbation `A - B`. The target-space
statements follow from the source-space statements by taking adjoints. The proofs use Mathlib's
isometric adjoint equivalence and the submultiplicativity of the operator norm.

## Provenance

The pointwise source-Gram perturbation estimate for finite-dimensional linear maps is adapted
from `ForTauCeti/Analysis/InnerProductSpace/Singular/Subspace.lean` in the AIQ-Kitware DKPS
formalization (Kitware, Inc.; Apache-2.0), by Jon Crall and Claude Opus 4.8.

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

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **Pointwise source-Gram perturbation bound.** Bounds on two rectangular linear maps and
on their difference imply
`‖(A† A - B† B) x‖ ≤ (a + b) ε ‖x‖` for each `x` in the source. -/
theorem norm_adjoint_comp_self_sub_adjoint_comp_self_apply_le (A B : E →ₗ[𝕜] F)
    {a b ε : ℝ}
    (hA : ∀ x, ‖A x‖ ≤ a * ‖x‖) (hB : ∀ x, ‖B x‖ ≤ b * ‖x‖)
    (hAB : ∀ x, ‖(A - B) x‖ ≤ ε * ‖x‖) (x : E) :
    ‖((adjoint A ∘ₗ A) - (adjoint B ∘ₗ B)) x‖ ≤ (a + b) * ε * ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have ha : 0 ≤ a :=
    nonneg_of_mul_nonneg_left ((norm_nonneg (A x)).trans (hA x)) hxpos
  have hb : 0 ≤ b :=
    nonneg_of_mul_nonneg_left ((norm_nonneg (B x)).trans (hB x)) hxpos
  have hε : 0 ≤ ε :=
    nonneg_of_mul_nonneg_left ((norm_nonneg ((A - B) x)).trans (hAB x)) hxpos
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  have hAop : ‖A.toContinuousLinearMap‖ ≤ a :=
    A.toContinuousLinearMap.opNorm_le_bound ha hA
  have hBop : ‖B.toContinuousLinearMap‖ ≤ b :=
    B.toContinuousLinearMap.opNorm_le_bound hb hB
  have hABop : ‖A.toContinuousLinearMap - B.toContinuousLinearMap‖ ≤ ε :=
    (A.toContinuousLinearMap - B.toContinuousLinearMap).opNorm_le_bound hε hAB
  have hGram :
      ‖A.toContinuousLinearMap.adjoint ∘L A.toContinuousLinearMap -
        B.toContinuousLinearMap.adjoint ∘L B.toContinuousLinearMap‖ ≤ (a + b) * ε :=
    (ContinuousLinearMap.norm_adjoint_comp_self_sub_adjoint_comp_self_le
      A.toContinuousLinearMap B.toContinuousLinearMap).trans
      (mul_le_mul (add_le_add hAop hBop) hABop
        (norm_nonneg _) (add_nonneg ha hb))
  simpa only [_root_.sub_apply, ContinuousLinearMap.comp_apply,
    ← adjoint_toContinuousLinearMap, coe_toContinuousLinearMap',
    LinearMap.sub_apply, LinearMap.comp_apply] using
    (ContinuousLinearMap.le_of_opNorm_le _ hGram x)

end LinearMap
