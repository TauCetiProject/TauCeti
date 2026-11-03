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
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A continuous linear functional extends along a linear isometric embedding with the same
operator norm. No completeness or closed-range hypothesis is required. -/
theorem exists_extension_norm_eq (i : E →ₗᵢ[𝕜] F) (f : StrongDual 𝕜 E) :
    ∃ g : StrongDual 𝕜 F, g.comp i.toContinuousLinearMap = f ∧ ‖g‖ = ‖f‖ := by
  let e := i.equivRange
  let f' : StrongDual 𝕜 i.toLinearMap.range :=
    f.comp e.symm.toLinearIsometry.toContinuousLinearMap
  -- The range is only seminormed, so Mathlib's normed-domain composition lemma does not apply.
  have hnorm' : ‖f'‖ = ‖f‖ := by
    apply le_antisymm
    · apply f'.opNorm_le_bound (norm_nonneg f)
      intro x
      calc
        ‖f' x‖ = ‖f (e.symm x)‖ := rfl
        _ ≤ ‖f‖ * ‖e.symm x‖ := f.le_opNorm _
        _ = ‖f‖ * ‖x‖ := by rw [e.symm.norm_map]
    · apply f.opNorm_le_bound (norm_nonneg f')
      intro x
      calc
        ‖f x‖ = ‖f' (e x)‖ := by
          -- Expose the composed functional to cancel the range equivalence without unfolding it.
          change ‖f x‖ = ‖f (e.symm (e x))‖
          rw [e.symm_apply_apply]
        _ ≤ ‖f'‖ * ‖e x‖ := f'.le_opNorm _
        _ = ‖f'‖ * ‖x‖ := by rw [e.norm_map]
  obtain ⟨g, hg, hnorm⟩ := _root_.exists_extension_norm_eq i.toLinearMap.range f'
  refine ⟨g, ?_, hnorm.trans hnorm'⟩
  ext x
  -- Expose composition and the range subtype at this point, without unfolding the equivalence.
  change g (i x) = f x
  have hx := hg (e x)
  change g (i x) = f (e.symm (e x)) at hx
  simpa only [e.symm_apply_apply] using hx

end LinearIsometry
