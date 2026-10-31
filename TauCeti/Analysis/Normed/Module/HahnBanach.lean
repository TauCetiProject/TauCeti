/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Hahn–Banach extension along linear isometries

A continuous functional extends along a linear isometric embedding without changing its norm.
This form of Hahn–Banach allows the embedded space to be given by a map rather than a submodule,
for example when comparing injective tensor norms in different ambient spaces.

The construction applies Mathlib's `exists_extension_norm_eq` to the range of the embedding.
-/

public section

namespace LinearIsometry

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A continuous linear functional extends along a linear isometric embedding with the same
operator norm. No completeness or closed-range hypothesis is required. -/
theorem exists_extension_norm_eq (i : E →ₗᵢ[𝕜] F) (f : StrongDual 𝕜 E) :
    ∃ g : StrongDual 𝕜 F, g.comp i.toContinuousLinearMap = f ∧ ‖g‖ = ‖f‖ := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let e := i.equivRange
  obtain ⟨g, hg, hnorm⟩ := _root_.exists_extension_norm_eq i.toLinearMap.range
    (f.comp e.symm.toLinearIsometry.toContinuousLinearMap)
  refine ⟨g, ?_, hnorm.trans (ContinuousLinearMap.opNorm_comp_linearIsometryEquiv f e.symm)⟩
  ext x
  simpa [e] using hg (e x)

end LinearIsometry
