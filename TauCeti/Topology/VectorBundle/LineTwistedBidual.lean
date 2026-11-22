/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.Coordinates
public import TauCeti.Topology.VectorBundle.Hom

/-!
# Bidual evaluation twisted by a line bundle

Let `V` be a vector bundle with model fibre `F` and let `D` be a line bundle, with model fibre the
scalar field. Evaluation `v ↦ (φ ↦ φ v)` maps each fibre `V x` to the space
`(V x →L D x) →L D x` of `D x`-valued linear functionals on `Hom(V x, D x)`. This is
`TauCeti.bundleLineTwistedBidual`. It is defined without choosing a norm on the fibres, a metric,
a generator of `D` or an orientation: a frame is used only to transport continuity, and the
evaluation formula `TauCeti.bundleLineTwistedBidual_apply` shows that the result does not depend
on it.

In the hom-bundle charts induced by any frames of `V` and `D`, the map is the constant map
`NormedSpace.inclusionInDoubleDual` of the model fibre, because the transition of the line `D`
cancels between the two hom factors (`TauCeti.bundleLineTwistedBidual_inCoordinates`). For a
finite-dimensional model fibre over a complete field, evaluation is an isomorphism
(`TauCeti.bundleLineTwistedBidualEquiv`), whose inverse is the inverse of the same constant map in
every frame.

For `D` the density line of a manifold and `V` its bundle of alternating `k`-forms, this is the
identification of `Hom(Hom(Λᵏ T*M, |Λ|), |Λ|)`, the bundle whose compactly supported sections are
tested by the distributional sections of `Hom(Λᵏ T*M, |Λ|)`, with `Λᵏ T*M` itself. Its fibrewise
algebra on tensor products is `TauCeti.lineTwistedBidualEquiv`; the trivial line gives
`TauCeti.bundleDoubleDual`.

## Main declarations

* `TauCeti.bundleLineTwistedBidual`: fibrewise evaluation `V x →L (V x →L D x) →L D x`.
* `TauCeti.bundleLineTwistedBidual_inCoordinates`: in every pair of frames it is
  `NormedSpace.inclusionInDoubleDual` of the model fibre.
* `TauCeti.bundleLineTwistedBidualEquiv`: the finite-dimensional isomorphism.
* `TauCeti.bundleLineTwistedBidualEquiv_symm_inCoordinates`: its inverse in every pair of frames.
-/

public section

noncomputable section

open Bundle FiberBundle Set
open scoped Topology

namespace TauCeti

variable {𝕜 M F : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace M] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  (D : M → Type*) [∀ x, AddCommGroup (D x)] [∀ x, Module 𝕜 (D x)]
  [∀ x, TopologicalSpace (D x)] [TopologicalSpace (TotalSpace 𝕜 D)]
  [FiberBundle 𝕜 D] [VectorBundle 𝕜 𝕜 D]
  [∀ x, IsTopologicalAddGroup (D x)] [∀ x, ContinuousSMul 𝕜 (D x)]

/-- Evaluation of `D x`-valued linear maps on `V x`, as a map into the `D x`-valued dual of
`Hom(V x, D x)`. No norm on the fibres is chosen: continuity is transported from the model
fibre through a frame, and `TauCeti.bundleLineTwistedBidual_apply` shows that the frame plays no
role. -/
def bundleLineTwistedBidual (x : M) : V x →L[𝕜] (V x →L[𝕜] D x) →L[𝕜] D x :=
  let e := (trivializationAt F V x).continuousLinearEquivAt 𝕜 x
    (mem_baseSet_trivializationAt F V x)
  let l := (trivializationAt 𝕜 D x).continuousLinearEquivAt 𝕜 x
    (mem_baseSet_trivializationAt 𝕜 D x)
  let dd := (e.arrowCongr l).arrowCongr l
  dd.symm.toContinuousLinearMap.comp
    ((NormedSpace.inclusionInDoubleDual 𝕜 F).comp e.toContinuousLinearMap)

/-- The line-twisted bidual map is evaluation. -/
@[simp]
theorem bundleLineTwistedBidual_apply (x : M) (v : V x) (φ : V x →L[𝕜] D x) :
    bundleLineTwistedBidual (F := F) V D x v φ = φ v := by
  simp [bundleLineTwistedBidual, ContinuousLinearEquiv.arrowCongr_apply,
    (trivializationAt F V x).symm_apply_apply_mk (mem_baseSet_trivializationAt F V x),
    (trivializationAt 𝕜 D x).symm_apply_apply_mk (mem_baseSet_trivializationAt 𝕜 D x)]

/-- In any pair of frames of `V` and `D`, line-twisted evaluation is the model-fibre evaluation
map: the transition of the line `D` cancels between the two hom factors. -/
theorem bundleLineTwistedBidual_inCoordinates (a : M) {x : M}
    (hxV : x ∈ (trivializationAt F V a).baseSet) (hxD : x ∈ (trivializationAt 𝕜 D a).baseSet) :
    ContinuousLinearMap.inCoordinates F V (StrongDual 𝕜 (StrongDual 𝕜 F))
      (fun y ↦ (V y →L[𝕜] D y) →L[𝕜] D y) a x a x (bundleLineTwistedBidual (F := F) V D x) =
      NormedSpace.inclusionInDoubleDual 𝕜 F := by
  ext v φ
  have hx : x ∈ (trivializationAt (F →L[𝕜] 𝕜) (fun y ↦ V y →L[𝕜] D y) a).baseSet :=
    ⟨hxV, hxD⟩
  -- The inverse chart of `Hom(V, D)` conjugates by the charts of `V` and `D`.
  have hsymm : (trivializationAt (F →L[𝕜] 𝕜) (fun y ↦ V y →L[𝕜] D y) a).symmL 𝕜 x φ =
      ((trivializationAt 𝕜 D a).symmL 𝕜 x).comp
        (φ.comp ((trivializationAt F V a).continuousLinearMapAt 𝕜 x)) :=
    Bundle.Trivialization.continuousLinearMap_symmL _ _ x φ
  rw [inCoordinates_apply_eq₂ (F₂ := F →L[𝕜] 𝕜) hxV hx hxD, bundleLineTwistedBidual_apply,
    ← Trivialization.symmL_apply (R := 𝕜) _ hx, hsymm]
  simp [hxV, hxD]

section FiniteDimensional

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

/-- For a finite-dimensional model fibre, evaluation identifies each fibre `V x` with the
`D x`-valued dual of `Hom(V x, D x)`. The equivalence is canonical, although its construction
uses a frame; its forward map is `TauCeti.bundleLineTwistedBidual`. -/
def bundleLineTwistedBidualEquiv (x : M) : V x ≃L[𝕜] (V x →L[𝕜] D x) →L[𝕜] D x :=
  let e := (trivializationAt F V x).continuousLinearEquivAt 𝕜 x
    (mem_baseSet_trivializationAt F V x)
  let l := (trivializationAt 𝕜 D x).continuousLinearEquivAt 𝕜 x
    (mem_baseSet_trivializationAt 𝕜 D x)
  let dd := (e.arrowCongr l).arrowCongr l
  let c : Module.Dual 𝕜 F ≃ₗ[𝕜] StrongDual 𝕜 F := LinearMap.toContinuousLinearMap
  let j := (Module.evalEquiv 𝕜 F).trans
    ((c.arrowCongr (LinearEquiv.refl 𝕜 𝕜)).trans LinearMap.toContinuousLinearMap)
  let j' := LinearEquiv.toContinuousLinearEquiv (𝕜 := 𝕜) (E := F)
    (F := StrongDual 𝕜 (StrongDual 𝕜 F)) j
  e.trans (j'.trans dd.symm)

/-- The line-twisted bidual equivalence is evaluation. -/
@[simp]
theorem bundleLineTwistedBidualEquiv_apply (x : M) (v : V x) (φ : V x →L[𝕜] D x) :
    bundleLineTwistedBidualEquiv (F := F) V D x v φ = φ v := by
  simp [bundleLineTwistedBidualEquiv, ContinuousLinearEquiv.arrowCongr_apply,
    (trivializationAt F V x).symm_apply_apply_mk (mem_baseSet_trivializationAt F V x),
    (trivializationAt 𝕜 D x).symm_apply_apply_mk (mem_baseSet_trivializationAt 𝕜 D x)]

/-- The equivalence extends the line-twisted bidual map. -/
@[simp]
theorem bundleLineTwistedBidualEquiv_toContinuousLinearMap (x : M) :
    (bundleLineTwistedBidualEquiv (𝕜 := 𝕜) (F := F) V D x).toContinuousLinearMap =
      bundleLineTwistedBidual (F := F) V D x := by
  ext v φ
  simp

/-- Applying a `D x`-valued map after the inverse identification is evaluation in the
line-twisted bidual. This characterizes the inverse. -/
@[simp]
theorem apply_bundleLineTwistedBidualEquiv_symm (x : M) (Φ : (V x →L[𝕜] D x) →L[𝕜] D x)
    (φ : V x →L[𝕜] D x) :
    φ ((bundleLineTwistedBidualEquiv (F := F) V D x).symm Φ) = Φ φ := by
  simpa using (bundleLineTwistedBidualEquiv_apply (F := F) V D x
    ((bundleLineTwistedBidualEquiv (F := F) V D x).symm Φ) φ).symm

/-- In any pair of frames, the inverse identification is the inverse of the model-fibre
evaluation map. This pins its behaviour under changes of frame of both `V` and `D`. -/
theorem bundleLineTwistedBidualEquiv_symm_inCoordinates (a : M) {x : M}
    (hxV : x ∈ (trivializationAt F V a).baseSet) (hxD : x ∈ (trivializationAt 𝕜 D a).baseSet) :
    ContinuousLinearMap.inCoordinates (StrongDual 𝕜 (StrongDual 𝕜 F))
      (fun y ↦ (V y →L[𝕜] D y) →L[𝕜] D y) F V a x a x
      (bundleLineTwistedBidualEquiv (F := F) V D x).symm.toContinuousLinearMap =
        (NormedSpace.inclusionInDoubleDual 𝕜 F).inverse := by
  have h := ContinuousLinearMap.inCoordinates_inverse (𝕜 := 𝕜) (F := F) (x₀ := a) (y₀ := a)
    (F' := StrongDual 𝕜 (StrongDual 𝕜 F))
    (W := fun y ↦ (V y →L[𝕜] D y) →L[𝕜] D y)
    (bundleLineTwistedBidualEquiv (F := F) V D x).toContinuousLinearMap
  rw [ContinuousLinearMap.inverse_equiv] at h
  simpa only [bundleLineTwistedBidualEquiv_toContinuousLinearMap,
    bundleLineTwistedBidual_inCoordinates V D a hxV hxD] using h

end FiniteDimensional

end TauCeti
