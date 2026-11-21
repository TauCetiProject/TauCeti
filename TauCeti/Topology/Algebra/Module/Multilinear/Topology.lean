/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Multilinear.Topology

/-!
# Injectivity of precomposition on continuous multilinear maps

Precomposing continuous multilinear maps with a coordinatewise dense-range family of continuous
linear maps is injective whenever the codomain is Hausdorff.

## Main results

* `ContinuousMultilinearMap.compContinuousLinearMap_injective`: precomposition with a family of
  continuous linear maps having dense range in each coordinate is injective.
* `ContinuousMultilinearMap.compContinuousLinearMapL_injective`: the bundled continuous linear
  map `compContinuousLinearMapL` is injective when each component map has dense range.
-/

public section

namespace ContinuousMultilinearMap

/-- Precomposition with a family of continuous linear maps having dense range in each coordinate is
injective on continuous multilinear maps into a Hausdorff space. -/
theorem compContinuousLinearMap_injective {R ι : Type*} {M₁ : ι → Type*} {M₁' : ι → Type*}
    {M₄ : Type*} [Semiring R] [∀ i, AddCommMonoid (M₁ i)] [∀ i, Module R (M₁ i)]
    [∀ i, TopologicalSpace (M₁ i)] [∀ i, AddCommMonoid (M₁' i)] [∀ i, Module R (M₁' i)]
    [∀ i, TopologicalSpace (M₁' i)] [AddCommMonoid M₄] [Module R M₄] [TopologicalSpace M₄]
    [T2Space M₄] {f : ∀ i, M₁ i →L[R] M₁' i} (hf : ∀ i, DenseRange (f i)) :
    Function.Injective fun g : ContinuousMultilinearMap R M₁' M₄ ↦ g.compContinuousLinearMap f :=
  fun g₁ g₂ hg ↦ ext <| congrFun <|
    (DenseRange.piMap hf).equalizer g₁.cont g₂.cont <| funext fun m ↦ by
      have hm : Pi.map (fun i ↦ (f i : M₁ i → M₁' i)) m = fun i ↦ f i (m i) :=
        funext fun i ↦ Pi.map_apply _ m i
      simpa only [Function.comp_apply, hm, compContinuousLinearMap_apply] using
        DFunLike.congr_fun hg m

/-- Precomposition `compContinuousLinearMapL` with a family of continuous linear maps having dense
range in each coordinate is injective when the codomain is Hausdorff. -/
theorem compContinuousLinearMapL_injective {𝕜 ι : Type*} {E : ι → Type*} {E₁ : ι → Type*}
    {F : Type*} [NormedField 𝕜] [∀ i, TopologicalSpace (E i)] [∀ i, AddCommGroup (E i)]
    [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E₁ i)] [∀ i, AddCommGroup (E₁ i)]
    [∀ i, Module 𝕜 (E₁ i)] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F] [T2Space F]
    {f : ∀ i, E i →L[𝕜] E₁ i} (hf : ∀ i, DenseRange (f i)) :
    Function.Injective (compContinuousLinearMapL (F := F) f) :=
  compContinuousLinearMap_injective hf

end ContinuousMultilinearMap
