/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DSlope.Basic
import TauCeti.Analysis.Analytic.MultiIndex.CoordinateDivision

/-!
# Analytic coordinate divided differences

Coordinate divided differences extend analytically across their base hyperplane. Off that
hyperplane, analyticity is needed only for the function and its restriction to the hyperplane.

## Main results

* `AnalyticAt.dslope_update_of_ne`: analyticity away from the base hyperplane.
* `AnalyticAt.dslope_update_same`: analytic extension across the base hyperplane.
* `TauCeti.analyticAt_dslope_update`: the combined coordinate divided-difference theorem.
-/

public section

open Filter Topology

variable {𝕜 ι F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : (ι → 𝕜) → F} {x : ι → 𝕜} {i : ι} {ζ : 𝕜}

/-- Away from its base hyperplane, a coordinate divided difference is analytic wherever the
function and its restriction to that hyperplane are analytic. -/
theorem AnalyticAt.dslope_update_of_ne (hf : AnalyticAt 𝕜 f x)
    (hζ : AnalyticAt 𝕜 (fun z ↦ f (Function.update z i ζ)) x) (hne : x i ≠ ζ) :
    AnalyticAt 𝕜 (fun z ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)) x := by
  have hcoord : AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦ z i) x :=
    (ContinuousLinearMap.proj (R := 𝕜) i).analyticAt x
  have h := ((hcoord.sub analyticAt_const).inv (sub_ne_zero.mpr hne)).smul (hf.sub hζ)
  apply h.congr
  filter_upwards [hcoord.continuousAt.eventually_ne hne] with z hz
  simp only [dslope_of_ne _ hz, slope_def_module, Function.update_eq_self]
  rfl

/-- A coordinate divided difference extends analytically across its base hyperplane. -/
theorem AnalyticAt.dslope_update_same [CompleteSpace F] (hf : AnalyticAt 𝕜 f x) (i : ι) :
    AnalyticAt 𝕜 (fun z ↦ dslope (fun w ↦ f (Function.update z i w)) (x i) (z i)) x := by
  obtain ⟨g, hg, hfg⟩ := hf.exists_eventuallyEq_coord_sub_smul i
  apply hg.congr
  apply (TauCeti.eventuallyEq_dslope_update_of_factorization ?_ hfg).symm
  filter_upwards [hg.eventually_analyticAt] with z hgz hzi
  have huz : Function.update z i (x i) = z := by rw [← hzi, Function.update_eq_self]
  exact hgz.continuousAt.comp_of_eq (continuousAt_const.update i continuousAt_id) huz

/-- Coordinate divided differences are analytic wherever the function and its restriction to
the base hyperplane are analytic. -/
theorem TauCeti.analyticAt_dslope_update [CompleteSpace F] (i : ι) (ζ : 𝕜)
    (hf : AnalyticAt 𝕜 f x)
    (hζ : AnalyticAt 𝕜 (fun z ↦ f (Function.update z i ζ)) x) :
    AnalyticAt 𝕜 (fun z ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)) x := by
  by_cases hxi : x i = ζ
  · simpa only [hxi] using hf.dslope_update_same i
  · exact hf.dslope_update_of_ne hζ hxi
