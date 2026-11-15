/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Alternating
public import TauCeti.Geometry.Manifold.Instances.Stiefel

/-!
# Attainment of comass on the Stiefel manifold

A continuous alternating map on a finite-dimensional real inner product space attains
its operator norm on an orthonormal frame whenever its degree is at most the dimension.
In particular, the comass of a real alternating form is a maximum, not merely a supremum.
The result includes degree zero, where the frame is empty. The restriction on the degree
is necessary because there are no orthonormal frames above the ambient dimension.

This uses compactness of the Stiefel manifold and the characterization of the operator
norm by orthonormal frames; no compactness assumption on the target is needed.
-/

public section

namespace ContinuousAlternatingMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- An alternating map attains its norm on an orthonormal frame whenever the degree
is at most the dimension. -/
theorem exists_orthonormal_norm_eq (ω : E [⋀^Fin k]→L[ℝ] F) (hk : k ≤ Module.finrank ℝ E) :
    ∃ v : Fin k → E, Orthonormal ℝ v ∧ ‖ω v‖ = ‖ω‖ := by
  obtain ⟨v, hv, hmax⟩ := (TauCeti.isCompact_stiefel E k).exists_isMaxOn
    (TauCeti.nonempty_stiefel.mpr hk) ω.cont.norm.continuousOn
  refine ⟨v, TauCeti.mem_stiefel_iff.mp hv, le_antisymm ?_ ?_⟩
  · exact (opNorm_le_iff_le_orthonormal (norm_nonneg ω)).mp le_rfl v
      (TauCeti.mem_stiefel_iff.mp hv)
  · exact (opNorm_le_iff_le_orthonormal (norm_nonneg (ω v))).mpr
      fun w hw ↦ hmax (TauCeti.mem_stiefel_iff.mpr hw)

end ContinuousAlternatingMap
