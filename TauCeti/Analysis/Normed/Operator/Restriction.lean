/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Normed.Operator.ContinuousAlgEquiv
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-! # Norm and spectrum of restricted operators -/

public section

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Codomain restriction to a subspace containing the range preserves the
operator norm.  Completeness of the domain is not used, so the lemma also
applies when the domain is a bare subspace carrier. -/
theorem opNorm_codRestrict_eq
    (T : E →L[𝕜] F) (M : Submodule 𝕜 F)
    (hT : ∀ x, T x ∈ M) :
    ‖T.codRestrict M hT‖ = ‖T‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) ?_
    intro x
    exact T.le_opNorm x
  · refine ContinuousLinearMap.opNorm_le_bound _
      (norm_nonneg (T.codRestrict M hT)) ?_
    intro x
    have hx := (T.codRestrict M hT).le_opNorm x
    exact hx

/-- Restricting to the full subspace does not change the spectrum. -/
theorem spectrum_restrict_top (A : E →L[𝕜] E)
    (hInv : ∀ x ∈ (⊤ : Submodule 𝕜 E), A x ∈ (⊤ : Submodule 𝕜 E)) :
    spectrum 𝕜 (A.restrict hInv) = spectrum 𝕜 A := by
  have hconj :
      (Submodule.topContEquiv : (⊤ : Submodule 𝕜 E) ≃L[𝕜] E).conjContinuousAlgEquiv
        (A.restrict hInv) = A := by
    ext x
    rw [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply]
    change ((A.restrict hInv) ((Submodule.topContEquiv :
      (⊤ : Submodule 𝕜 E) ≃L[𝕜] E).symm x) : E) = A x
    rw [ContinuousLinearMap.coe_restrict_apply]
    rfl
  conv_rhs => rw [← hconj]
  exact (AlgEquiv.spectrum_eq
    ((Submodule.topContEquiv : (⊤ : Submodule 𝕜 E) ≃L[𝕜] E).conjContinuousAlgEquiv)
    (A.restrict hInv)).symm

end ContinuousLinearMap
