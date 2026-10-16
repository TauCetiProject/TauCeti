/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Slope

/-!
# Convergence of slopes in topological modules

For a function with a derivative along a filter at a fixed base point, its slopes converge to
that derivative after removing the base point from the filter. This applies to topological
modules, including seminormed spaces where distinct points can have zero distance, and supplies
the difference-quotient limit used to identify metric speed with the norm of a derivative.
-/

public section

open Filter Set Topology

/-- The slopes of a function with a derivative along a filter converge to that derivative away
from the base point. -/
theorem HasDerivAtFilter.tendsto_slope {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [SeparatelyContinuousAdd E]
    [ContinuousSMul 𝕜 E]
    {γ : 𝕜 → E} {v : E} {t : 𝕜} {L : Filter 𝕜}
    (h : HasDerivAtFilter γ v (L ×ˢ pure t)) :
    Tendsto (slope γ t) (L ⊓ 𝓟 {t}ᶜ) (𝓝 v) := by
  have hlim := (h.hasFDerivAtFilter.isLittleOTVS.comp_tendsto
    (tendsto_id.prodMk (Filter.tendsto_const_pure (b := t)))).tendsto_inv_smul
  have hlim' := (hlim.mono_left (inf_le_left (a := L) (b := 𝓟 {t}ᶜ))).add_const v
  simp only [zero_add] at hlim'
  refine hlim'.congr' <| eventually_inf_principal.2 <| Eventually.of_forall fun s hs ↦ ?_
  simp [slope_def_module, smul_sub, inv_smul_smul₀ (sub_ne_zero.2 hs)]
