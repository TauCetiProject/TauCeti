/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Basic

/-!
# Signed coordinate evaluations of differential forms

Evaluating an `n`-form on the tuples obtained by omitting one of `n + 1` vectors gives its
signed coordinate coefficients. Summing the directional derivatives of these coefficients
recovers the actual exterior derivative. The within-set identity is shared by the full-space
and half-space Stokes proofs.
-/

public section

noncomputable section

namespace ContinuousAlternatingMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ}

/-- Signed evaluations on the tuples obtained by removing one vector, as a continuous linear
map on alternating forms. In a coordinate basis these are the vector-field coefficients used
in the divergence expression of the exterior derivative. -/
def signedRemoveNth (v : Fin (n + 1) → E) :
    (E [⋀^Fin n]→L[𝕜] F) →L[𝕜] (Fin (n + 1) → F) :=
  ContinuousLinearMap.pi fun i ↦ (-1 : 𝕜) ^ i.val • apply 𝕜 E F (i.removeNth v)

@[simp]
theorem signedRemoveNth_apply (v : Fin (n + 1) → E) (ω : E [⋀^Fin n]→L[𝕜] F)
    (i : Fin (n + 1)) : signedRemoveNth v ω i = (-1 : 𝕜) ^ i.val • ω (i.removeNth v) :=
  by simp [signedRemoveNth, ContinuousAlternatingMap.apply_apply]

/-- The sum of the directional derivatives of signed omission coefficients is the exterior
derivative on the original tuple. Only differentiability within the given set is required. -/
theorem _root_.DifferentiableWithinAt.sum_fderivWithin_signedRemoveNth {ω : E → E [⋀^Fin n]→L[𝕜] F}
    {s : Set E} {x : E} (hω : DifferentiableWithinAt 𝕜 ω s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) (v : Fin (n + 1) → E) :
    (∑ i : Fin (n + 1), fderivWithin 𝕜 (signedRemoveNth v ∘ ω) s x (v i) i) =
      extDerivWithin ω s x v := by
  have hd := ((signedRemoveNth (𝕜 := 𝕜) (F := F) v).hasFDerivAt.comp_hasFDerivWithinAt x
    hω.hasFDerivWithinAt).fderivWithin hs
  rw [hd, extDerivWithin, alternatizeUncurryFin_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [ContinuousLinearMap.comp_apply, signedRemoveNth_apply, ← Int.cast_smul_eq_zsmul 𝕜]

end ContinuousAlternatingMap
