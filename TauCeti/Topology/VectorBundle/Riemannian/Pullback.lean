/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Riemannian
public import TauCeti.Topology.VectorBundle.Pullback

/-!
# Pullbacks of continuous Riemannian metrics and bundles

The fibres of the pullback `f *ᵖ E` of a vector bundle `E` along a continuous map `f` carry the
inner products of the fibres of `E` (`Bundle.Pullback.instInnerProductSpace`). This file shows that
these inner products depend continuously on the base point when those of `E` do: an explicit
`Bundle.ContinuousRiemannianMetric` pulls back along `f`
(`Bundle.ContinuousRiemannianMetric.pullback`), and the pullback of a continuous Riemannian bundle
is a continuous Riemannian bundle (`Bundle.Pullback.instIsContinuousRiemannianBundle`). A
continuous family `g` of bilinear forms defining the inner products of `E` pulls back to the family
`x ↦ g (f x)`; in the pulled-back chart at `x₀` it reads, near `x₀`, as `g` does in the chart of
`E` at `f x₀` (`ContinuousLinearMap.inCoordinates_pullback_of_mem₂`).

For the inclusion of an open subset `U` of a manifold, this makes the restrictions of Riemannian
bundles to `U` continuous Riemannian bundles, as needed to compare inner products and integrals of
sections over `U` with those over the whole manifold.

## Main declarations

* `Bundle.ContinuousRiemannianMetric.pullback`: pullback of an explicit continuous Riemannian
  metric along a continuous map.
* `Bundle.Pullback.instIsContinuousRiemannianBundle`: pullback of a continuous Riemannian vector
  bundle along a continuous map is a continuous Riemannian vector bundle.

## References

* D. Husemoller, *Fibre Bundles*, third edition, Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 3 (pullbacks of vector bundles with metric structure).
-/

public section

noncomputable section

open Bundle ContinuousLinearMap Filter
open scoped Topology

namespace Bundle.ContinuousRiemannianMetric

variable {B B' F : Type*} [TopologicalSpace B] [TopologicalSpace B']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {K : Type*} [FunLike K B' B] [ContinuousMapClass K B' B]

/-- The pullback of a continuous Riemannian metric along a continuous map of bases. -/
def pullback (h : ContinuousRiemannianMetric F E) (f : K) :
    ContinuousRiemannianMetric F ((f : B' → B) *ᵖ E) where
  inner x := h.inner (f x)
  symm x := h.symm (f x)
  pos x := h.pos (f x)
  isVonNBounded x := h.isVonNBounded (f x)
  continuous := by
    refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
    have hc := (h.continuous.continuousAt (x := f x₀)).comp (map_continuous f).continuousAt
    rw [continuousAt_hom_bundle] at hc ⊢
    refine ⟨continuousAt_id, hc.2.congr ?_⟩
    have hmem := (trivializationAt F E (f x₀)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' (f x₀))
    filter_upwards [(map_continuous f).continuousAt.preimage_mem_nhds hmem] with x hx
    exact (inCoordinates_pullback_of_mem₂ f x₀ x (h.inner (f x)) hx hx).symm

@[simp]
theorem pullback_inner_apply (h : ContinuousRiemannianMetric F E) (f : K) (x : B') :
    (h.pullback f).inner x = h.inner (f x) :=
  (rfl)

end Bundle.ContinuousRiemannianMetric

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
  have hmem := (trivializationAt F E (f x₀)).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' (f x₀))
  filter_upwards [(map_continuous f).continuousAt.preimage_mem_nhds hmem] with x hx
  exact (inCoordinates_pullback_of_mem₂ f x₀ x (g (f x)) hx hx).symm

end Bundle.Pullback
