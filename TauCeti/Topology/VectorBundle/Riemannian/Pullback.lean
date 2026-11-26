/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Riemannian
public import TauCeti.Topology.VectorBundle.Pullback

/-!
# Pullbacks of continuous Riemannian bundles

The fibres of the pullback `f *ᵖ E` of a vector bundle `E` along a continuous map `f` carry the
inner products of the fibres of `E` (`Bundle.Pullback.instInnerProductSpace`). This file shows that
these inner products depend continuously on the base point when those of `E` do: the pullback of
a continuous Riemannian bundle is a continuous Riemannian bundle
(`Bundle.Pullback.instIsContinuousRiemannianBundle`). A continuous family `g` of bilinear forms
defining the inner products of `E` pulls back to the family `x ↦ g (f x)`; in the pulled-back
chart at `x₀` it reads, near `x₀`, as `g` does in the chart of `E` at `f x₀`.

For the inclusion of an open subset `U` of a manifold, this makes the restrictions of Riemannian
bundles to `U` continuous Riemannian bundles, as needed to compare inner products and integrals of
sections over `U` with those over the whole manifold.
-/

public section

open Bundle ContinuousLinearMap Filter
open scoped Topology

namespace Bundle.Pullback

variable {B B' F : Type*} [TopologicalSpace B] [TopologicalSpace B']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
  {K : Type*} [FunLike K B' B] [ContinuousMapClass K B' B]

/-- The pullback of a continuous Riemannian bundle along a continuous map, with the fibre inner
products of the original bundle, is a continuous Riemannian bundle. -/
instance instIsContinuousRiemannianBundle [h : IsContinuousRiemannianBundle F E] (f : K) :
    IsContinuousRiemannianBundle F ((f : B' → B) *ᵖ E) := by
  obtain ⟨g, hg, hgi⟩ := h.exists_continuous
  refine ⟨⟨fun x ↦ g (f x), continuous_iff_continuousAt.2 fun x₀ ↦ ?_, fun x v w ↦ hgi (f x) v w⟩⟩
  have hc := (hg.continuousAt (x := f x₀)).comp (map_continuous f).continuousAt
  rw [continuousAt_hom_bundle] at hc ⊢
  refine ⟨continuousAt_id, hc.2.congr ?_⟩
  -- Near `x₀`, the image point `f x` lies in the base set of the chart of `E` at `f x₀`, whose
  -- pullback is the chart of `f *ᵖ E` at `x₀`; both coordinate expressions of `g (f x)` then
  -- evaluate `g (f x)` on the same vectors of `E (f x)`.
  filter_upwards [(map_continuous f).continuousAt.preimage_mem_nhds
    ((trivializationAt F E (f x₀)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' _))] with x hx
  have hx' : x ∈ (trivializationAt F ((f : B' → B) *ᵖ E) x₀).baseSet := hx
  ext v w
  dsimp only [Function.comp_apply]
  rw [inCoordinates_apply_eq₂ hx hx (by simp)]
  -- The fibres of `f *ᵖ E` carry the instances of the fibres of `E` only up to unfolding, so the
  -- coordinate formula for the pullback is applied with `erw`.
  erw [inCoordinates_apply_eq₂ (E₁ := (f : B' → B) *ᵖ E) (E₂ := (f : B' → B) *ᵖ E)
    (E₃ := fun _ : B' ↦ ℝ) hx' hx' (by simp)]
  simp only [trivializationAt, FiberBundle.pullback_trivializationAt']
  rw [Trivialization.symm_pullback _ f hx, Trivialization.symm_pullback _ f hx]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
    LinearMap.id_coe, id_eq]
  -- Unfolding `trivializationAt` left `FiberBundle.trivializationAt'` on one side only; it is
  -- `trivializationAt F E (f x₀)` by definition.
  rfl

end Bundle.Pullback
