/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import TauCeti.Analysis.Normed.Operator.Surjective

/-!
# Compactness of the critical points

A point is critical for a map when its Fréchet derivative there fails to be surjective. Since
surjectivity onto a finite-dimensional space is an open condition on continuous linear maps
(`TauCeti.isOpen_setOf_surjective`), the critical points in a compact set, where the derivative is
continuous, form a compact set, and so does their image.

## Main results

* `IsCompact.image_inter_setOf_not_surjective_fderiv`: the image of the critical points of `f`
  lying in a compact set `K` on which `f` and `Df` are continuous is compact.
-/

public section

open Function Set

namespace IsCompact

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The image of the critical points of `f` lying in a compact set `K` on which `f` and `Df` are
continuous is compact, since the critical points form a closed set. -/
theorem image_inter_setOf_not_surjective_fderiv {f : E → F} {K : Set E}
    (hK : IsCompact K) (hf : ContinuousOn f K) (hf' : ContinuousOn (fderiv 𝕜 f) K) :
    IsCompact (f '' ({x | ¬ Surjective (fderiv 𝕜 f x)} ∩ K)) := by
  have hCK : IsCompact ({x | ¬ Surjective (fderiv 𝕜 f x)} ∩ K) := by
    refine hK.of_isClosed_subset ?_ inter_subset_right
    have hclosed : IsClosed (K ∩ (fderiv 𝕜 f) ⁻¹' {A : E →L[𝕜] F | Surjective A}ᶜ) :=
      hf'.preimage_isClosed_of_isClosed hK.isClosed
        TauCeti.isOpen_setOf_surjective.isClosed_compl
    rwa [inter_comm] at hclosed
  exact hCK.image_of_continuousOn (hf.mono inter_subset_right)

end IsCompact
