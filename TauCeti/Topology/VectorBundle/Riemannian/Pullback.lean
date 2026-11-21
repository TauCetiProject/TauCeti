/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Riemannian
public import TauCeti.Topology.VectorBundle.Pullback

/-!
# Pullback of continuous Riemannian metrics and bundles

Pulling back a continuous Riemannian vector bundle `E → B` along any continuous map `f : B' → B`
(bundled via `ContinuousMapClass`) preserves continuity of the fibrewise inner product
(`Bundle.Pullback.instIsContinuousRiemannianBundle`), using the original fibre inner products
supplied by `Bundle.Pullback.instInnerProductSpace` with no renorming or metric transport. An
explicit `Bundle.ContinuousRiemannianMetric` pulls back in the same way
(`Bundle.ContinuousRiemannianMetric.pullback`).

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

open Bundle TauCeti Topology
open scoped InnerProductSpace

namespace Bundle.ContinuousRiemannianMetric

variable {B B' F K : Type*} [TopologicalSpace B] [TopologicalSpace B']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  [FunLike K B' B] [ContinuousMapClass K B' B]

/-- The pullback of a continuous Riemannian metric along a continuous map of bases. -/
def pullback (h : ContinuousRiemannianMetric F E) (f : K) :
    ContinuousRiemannianMetric F ((f : B' → B) *ᵖ E) where
  inner x := h.inner (f x)
  symm x := h.symm (f x)
  pos x := h.pos (f x)
  isVonNBounded x := h.isVonNBounded (f x)
  continuous := continuous_bilinear_pullback f h.inner h.continuous

@[simp]
theorem pullback_inner_apply (h : ContinuousRiemannianMetric F E) (f : K) (x : B') :
    (h.pullback f).inner x = h.inner (f x) :=
  (rfl)

end Bundle.ContinuousRiemannianMetric

namespace Bundle.Pullback

section Riemannian

variable {B B' F K : Type*} [TopologicalSpace B] [TopologicalSpace B']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]
  [FunLike K B' B] [ContinuousMapClass K B' B]

/-- The pullback of a continuous Riemannian vector bundle along a continuous map is a continuous
Riemannian vector bundle, with the original fibre inner products. -/
instance instIsContinuousRiemannianBundle (f : K) :
    IsContinuousRiemannianBundle F ((f : B' → B) *ᵖ E) := by
  obtain ⟨g, hg, hinner⟩ := IsContinuousRiemannianBundle.exists_continuous (F := F) (E := E)
  exact ⟨⟨fun x ↦ g (f x), continuous_bilinear_pullback f g hg, fun x v w ↦ hinner (f x) v w⟩⟩

end Riemannian

end Bundle.Pullback
