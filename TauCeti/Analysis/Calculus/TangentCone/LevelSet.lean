/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.Implicit

/-!
# Tangent cones of regular level sets

A map between Banach spaces with surjective strict derivative and complemented kernel has a
regular level set whose tangent cone at the base point is exactly that kernel. In particular,
the cone is already a linear subspace, so its span gives the same tangent space.

This needs only strict differentiability at the base point, over any nontrivially normed field.
It supplies the regular-level tangent-space calculation used in transverse intersections.
Mathlib's `HasStrictFDerivAt.to_implicitFunctionOfComplemented` provides the local parametrization
of the level set, with derivative equal to the kernel inclusion.

## Main results

* `HasStrictFDerivAt.tangentConeAt_preimage_singleton`: the tangent cone of a regular fiber is
  the derivative's kernel.
* `HasStrictFDerivAt.span_tangentConeAt_preimage_singleton`: the corresponding tangent-space
  calculation in terms of the span of the tangent cone.
-/

public section

open Filter Set Topology

namespace HasStrictFDerivAt

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {g : E → F} {g' : E →L[𝕜] F} {y : E}

/-- The tangent cone of a regular level set is the kernel of its surjective strict derivative,
provided that the kernel is complemented. -/
theorem tangentConeAt_preimage_singleton (hg : HasStrictFDerivAt g g' y) (hg' : g'.range = ⊤)
    (hker : g'.ker.ClosedComplemented) :
    tangentConeAt 𝕜 (g ⁻¹' {g y}) y = (g'.ker : Set E) := by
  refine Set.Subset.antisymm (fun v hv ↦ ?_) (fun v hv ↦ ?_)
  · have hv' := tangentConeAt_mono (image_preimage_subset g {g y})
      (hg.hasFDerivAt.hasFDerivWithinAt.mapsTo_tangent_cone hv)
    exact tangentConeAt_subset_zero (by rw [accPt_iff_frequently]; simp) hv'
  -- The implicit function parametrizes the fiber with derivative the kernel inclusion.
  · let φ := hg.implicitFunctionOfComplemented g g' hg' hker (g y)
    have hφ : HasFDerivAt φ g'.ker.subtypeL 0 :=
      (hg.to_implicitFunctionOfComplemented hg' hker).hasFDerivAt
    have hφmem : φ ⁻¹' (g ⁻¹' {g y}) ∈ 𝓝 0 :=
      (continuousAt_const.prodMk continuousAt_id).tendsto.eventually
        (hg.map_implicitFunctionOfComplemented_eq hg' hker)
    have hv' : (⟨v, hv⟩ : g'.ker) ∈ tangentConeAt 𝕜 (φ ⁻¹' (g ⁻¹' {g y})) 0 := by
      rw [tangentConeAt_of_mem_nhds hφmem]
      trivial
    have hm := tangentConeAt_mono (image_preimage_subset φ (g ⁻¹' {g y}))
      (hφ.hasFDerivWithinAt.mapsTo_tangent_cone hv')
    simpa only [φ, hg.implicitFunctionOfComplemented_apply_image hg' hker,
      Submodule.subtypeL_apply] using hm

/-- The tangent space of a regular level set, expressed as the span of its tangent cone, is the
kernel of its surjective strict derivative, provided that the kernel is complemented. -/
theorem span_tangentConeAt_preimage_singleton (hg : HasStrictFDerivAt g g' y)
    (hg' : g'.range = ⊤) (hker : g'.ker.ClosedComplemented) :
    Submodule.span 𝕜 (tangentConeAt 𝕜 (g ⁻¹' {g y}) y) = g'.ker := by
  rw [hg.tangentConeAt_preimage_singleton hg' hker, Submodule.span_eq]

end HasStrictFDerivAt
