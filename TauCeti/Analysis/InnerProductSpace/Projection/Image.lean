/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.RangeProjection
import TauCeti.Analysis.Normed.Operator.ImageInjectivity

/-!
# Orthogonal projections onto images of varying subspaces

For a continuous family of finite-rank idempotents `P x` and a continuous family of operators
`L x`, the orthogonal projection onto `L x (range (P x))` varies continuously wherever `L x`
is injective on the range of `P x`. In particular the ambient operator `L x` need not be
injective. This is the continuity of the image-plane map in projection coordinates, as used
in the differential pushforward of varifolds (Simon, *Lectures on Geometric Measure Theory*,
§39.1).

The fixed-source case is `ContinuousAt.starProjection_range`. The varying-source case uses
`ContinuousAt.eventually_bijective_rangeRestrict_comp_subtypeL` to reduce to it.
-/

public section

open ContinuousLinearMap Filter Function Set Topology

variable {𝕜 X E F : Type*} [RCLike 𝕜] [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  {L : X → E →L[𝕜] F} {P : X → E →L[𝕜] E} {x : X}

/-- Where `L x` is injective on the range of `P x`, the orthogonal projection onto the image of
this range under `L x` depends continuously on both operators. -/
theorem ContinuousAt.starProjection_map_range (hL : ContinuousAt L x) (hP : ContinuousAt P x)
    (hidem : ∀ᶠ y in 𝓝 x, IsIdempotentElem (P y)) [∀ y, FiniteDimensional 𝕜 (P y).range]
    (hinj : InjOn (L x) (P x).range) :
    ContinuousAt (fun y ↦ ((P y).range.map (L y).toLinearMap).starProjection) x := by
  let A (y : X) := L y ∘L (P y ∘L (P x).range.subtypeL)
  have hA : ContinuousAt A x := hL.clm_comp (hP.clm_comp continuousAt_const)
  have hx : IsIdempotentElem (P x) := hidem.self_of_nhds
  have hinj' : Injective (L x ∘L (P x).range.subtypeL) := hinj.injective
  have hinjA : Injective (A x) := by simpa only [A, hx.comp_subtypeL] using hinj'
  refine (hA.starProjection_range hinjA).congr_of_eventuallyEq ?_
  filter_upwards [hP.eventually_bijective_rangeRestrict_comp_subtypeL hidem] with y hbij
  have hrange : (A y).range = (P y).range.map (L y).toLinearMap := by
    let C := (P y).rangeRestrict ∘L (P x).range.subtypeL
    have hC : C.toLinearMap.range = ⊤ := LinearMap.range_eq_top.mpr hbij.surjective
    -- The source restriction factors through the surjective local chart `C`.
    have hAy : A y = (L y).domRestrict (P y).range ∘L C := rfl
    rw [hAy, toLinearMap_comp, LinearMap.range_comp_of_range_eq_top _ hC]
    exact LinearMap.range_domRestrict (P y).range (L y).toLinearMap
  simp only [hrange]
