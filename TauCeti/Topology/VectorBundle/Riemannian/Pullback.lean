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

Pulling back a continuous Riemannian vector bundle `E → B` along a continuous map `f : C(B', B)`
preserves continuity of the fibrewise inner product
(`Bundle.Pullback.instIsContinuousRiemannianBundle`), using the original fibre inner products
supplied by `Bundle.Pullback.instInnerProductSpace` with no renorming or metric transport. An
explicit `Bundle.ContinuousRiemannianMetric` pulls back in the same way
(`Bundle.ContinuousRiemannianMetric.pullback`).

## Main declarations

* `Bundle.Trivialization.pullback_symm_apply`: the fibrewise inverse of a pulled-back
  trivialization agrees with the original fibrewise inverse at the image point.
* `ContinuousLinearMap.inCoordinates_bilinear_pullback_of_mem`: reading a bilinear form on a
  pullback fibre in preferred charts agrees with reading it in the original charts at the image
  point.
* `Bundle.ContinuousRiemannianMetric.pullback`: pullback of an explicit continuous Riemannian
  metric along a continuous map.
* `Bundle.Pullback.instFiberBundleOfNormed`, `Bundle.Pullback.instVectorBundleOfNormed`: fibre and
  vector bundle instances on pullbacks of bundles with normed fibres.
* `Bundle.Pullback.instIsContinuousRiemannianBundle`: pullback of a continuous Riemannian vector
  bundle along a continuous map is a continuous Riemannian vector bundle.

## References

* D. Husemoller, *Fibre Bundles*, third edition, Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 3 (pullbacks of vector bundles with metric structure).
-/

public section

noncomputable section

open Bundle ContinuousLinearMap Filter Topology
open scoped InnerProductSpace

namespace Bundle.Trivialization

/-- Evaluating the fibrewise inverse of a pulled-back trivialization at `x` agrees with evaluating
the original fibrewise inverse at `f x` on the base set. -/
@[simp]
theorem pullback_symm_apply {B B' F K : Type*} [TopologicalSpace B] [TopologicalSpace B']
    [TopologicalSpace F] {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ b, Nonempty (V b)]
    [FunLike K B' B] [ContinuousMapClass K B' B]
    (e : Trivialization F (π F V)) (f : K) {x : B'} (hx : f x ∈ e.baseSet) (v : F) :
    (e.pullback f).symm x v = e.symm (f x) v :=
  (e.pullback f).toPretrivialization.symm_apply hx v

end Bundle.Trivialization

namespace ContinuousLinearMap

variable {𝕜 B X F : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B] [TopologicalSpace X]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module 𝕜 (V b)] [∀ b, TopologicalSpace (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Reading a scalar-valued bilinear form on a pullback fibre in the preferred hom-bundle charts
gives the same form on the model fibre as reading it in the preferred charts of the original bundle
at the image point. -/
theorem inCoordinates_bilinear_pullback_of_mem (f : C(X, B)) (x₀ x : X)
    (b : V (f x) →L[𝕜] V (f x) →L[𝕜] 𝕜)
    (hV : f x ∈ (trivializationAt F V (f x₀)).baseSet) :
    inCoordinates F ((f : X → B) *ᵖ V) (F →L[𝕜] 𝕜)
        (fun y ↦ ((f : X → B) *ᵖ V) y →L[𝕜] 𝕜) x₀ x x₀ x b =
      inCoordinates F V (F →L[𝕜] 𝕜) (fun y ↦ V y →L[𝕜] 𝕜) (f x₀) (f x) (f x₀) (f x) b := by
  have hV' : x ∈ (trivializationAt F ((f : X → B) *ᵖ V) x₀).baseSet := hV
  ext v w
  have hv := (trivializationAt F V (f x₀)).pullback_symm_apply f hV v
  have hw := (trivializationAt F V (f x₀)).pullback_symm_apply f hV w
  erw [inCoordinates_apply_eq₂ hV' hV' (by simp), inCoordinates_apply_eq₂ hV hV (by simp)]
  simp only [trivializationAt, FiberBundle.pullback_trivializationAt',
    Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization, LinearMap.id_coe,
    id_eq]
  erw [hv, hw]
  rfl

/-- A continuous section of the bundle of scalar-valued bilinear forms on `V` pulls back along a
continuous map `f` to a continuous section on `f *ᵖ V`. -/
theorem continuous_bilinear_pullback (f : C(X, B)) (g : ∀ b : B, V b →L[𝕜] V b →L[𝕜] 𝕜)
    (hg : Continuous fun b : B ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] 𝕜) b (g b)) :
    Continuous fun x : X ↦
      TotalSpace.mk' (F →L[𝕜] F →L[𝕜] 𝕜)
        (E := fun y ↦ ((f : X → B) *ᵖ V) y →L[𝕜] ((f : X → B) *ᵖ V) y →L[𝕜] 𝕜) x (g (f x)) := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  rw [continuousAt_hom_bundle (RingHom.id 𝕜)]
  have hg₀ := (continuousAt_hom_bundle (RingHom.id 𝕜) _).1
    (hg.continuousAt.comp f.continuous.continuousAt (x := x₀))
  have hmem : ∀ᶠ x in 𝓝 x₀, f x ∈ (trivializationAt F V (f x₀)).baseSet :=
    f.continuous.continuousAt
      ((trivializationAt F V (f x₀)).open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V _))
  refine ⟨continuousAt_id, hg₀.2.congr_of_eventuallyEq (hmem.mono fun x hx ↦ ?_)⟩
  dsimp only [Function.comp_apply]
  exact inCoordinates_bilinear_pullback_of_mem f x₀ x (g (f x)) hx

end ContinuousLinearMap

namespace Bundle.ContinuousRiemannianMetric

variable {B B' F : Type*} [TopologicalSpace B] [TopologicalSpace B']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- The pullback of a continuous Riemannian metric along a continuous map of bases. -/
def pullback (h : ContinuousRiemannianMetric F E) (f : C(B', B)) :
    ContinuousRiemannianMetric F ((f : B' → B) *ᵖ E) where
  inner x := h.inner (f x)
  symm x := h.symm (f x)
  pos x := h.pos (f x)
  isVonNBounded x := h.isVonNBounded (f x)
  continuous := continuous_bilinear_pullback f h.inner h.continuous

@[simp]
theorem pullback_inner_apply (h : ContinuousRiemannianMetric F E) (f : C(B', B)) (x : B') :
    (h.pullback f).inner x = h.inner (f x) :=
  (rfl)

end Bundle.ContinuousRiemannianMetric

namespace Bundle.Pullback

section Normed

variable {𝕜 B B' F K : Type*} [TopologicalSpace B] [TopologicalSpace B']
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [FunLike K B' B] [ContinuousMapClass K B' B]

/-- Pulling back a bundle with normed fibres along a continuous map gives a fibre bundle with
respect to the topology induced by `Bundle.Pullback.instNormedAddCommGroup`, matching
`FiberBundle.pullback` definitionally. -/
instance instFiberBundleOfNormed [TopologicalSpace F] [FiberBundle F E] (f : K) :
    @FiberBundle B' F _ _ ((f : B' → B) *ᵖ E) _ (fun _ ↦ UniformSpace.toTopologicalSpace) :=
  FiberBundle.pullback (F := F) (E := E) f

/-- Pulling back a vector bundle with normed fibres along a continuous map gives a vector bundle
with respect to the topology induced by `Bundle.Pullback.instNormedAddCommGroup`. -/
instance instVectorBundleOfNormed [NontriviallyNormedField 𝕜] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [∀ b, Module 𝕜 (E b)] [FiberBundle F E] [VectorBundle 𝕜 F E] (f : K) :
    @VectorBundle 𝕜 B' F ((f : B' → B) *ᵖ E) _ _ _ _ _ _ _
      (fun _ ↦ UniformSpace.toTopologicalSpace) (instFiberBundleOfNormed f) :=
  VectorBundle.pullback (F := F) (E := E) 𝕜 f

end Normed

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
  exact ⟨⟨fun x ↦ g (f x), continuous_bilinear_pullback ⟨f, map_continuous f⟩ g hg,
    fun x v w ↦ hinner (f x) v w⟩⟩

end Riemannian

end Bundle.Pullback
