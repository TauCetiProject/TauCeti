/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DSlope.Basic
import TauCeti.Analysis.Analytic.Constructions
import TauCeti.Analysis.Analytic.MultiIndex.CoordinateDivision

/-!
# Analytic coordinate divided differences

Off the base hyperplane, a coordinate divided difference is analytic exactly when its numerator
is analytic. At a hyperplane point, if the function is analytic there and the target is complete,
the divided difference extends analytically and takes the coordinate-slice derivative there.

## Main results

* `TauCeti.analyticWithinAt_dslope_update_iff_of_ne` and
  `TauCeti.analyticAt_dslope_update_iff_of_ne`: analyticity away from the base hyperplane.
* `AnalyticAt.dslope_update_same`: analytic extension across the base hyperplane.
* `TauCeti.analyticAt_dslope_update`: the combined coordinate divided-difference theorem.
* `AnalyticOnNhd.dslope_update`: coordinate divided differences preserve neighborhood
  analyticity on sets preserved by the base-coordinate update.
-/

public section

open Filter Topology

variable {𝕜 ι F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : (ι → 𝕜) → F} {x : ι → 𝕜} {i : ι} {ζ : 𝕜}

/-- Away from its base hyperplane, a coordinate divided difference is analytic within a set
exactly when its numerator is analytic there. No separate analyticity of the numerator's two
terms is needed. -/
theorem TauCeti.analyticWithinAt_dslope_update_iff_of_ne {s : Set (ι → 𝕜)}
    (hne : x i ≠ ζ) :
    AnalyticWithinAt 𝕜 (fun z ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)) s x ↔
      AnalyticWithinAt 𝕜 (fun z ↦ f z - f (Function.update z i ζ)) s x := by
  have hcoord : AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦ z i) x :=
    (ContinuousLinearMap.proj (R := 𝕜) i).analyticAt x
  constructor
  · intro h
    simpa only [Pi.sub_apply, sub_smul_dslope, Function.update_eq_self] using
      (hcoord.sub (analyticAt_const (v := ζ))).analyticWithinAt.smul h
  · intro h
    have hquot := ((hcoord.sub (analyticAt_const (v := ζ))).analyticWithinAt.inv
      (sub_ne_zero.mpr hne)).smul h
    have heq : (fun z ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)) =ᶠ[𝓝 x]
        (fun z ↦ (z i - ζ)⁻¹ • (f z - f (Function.update z i ζ))) := by
      filter_upwards [hcoord.continuousAt.eventually_ne hne] with z hz
      simp only [dslope_of_ne _ hz, slope_def_module, Function.update_eq_self]
    exact hquot.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds

/-- Away from its base hyperplane, a coordinate divided difference is analytic exactly when
its numerator is analytic. No separate analyticity of the numerator's two terms is needed. -/
theorem TauCeti.analyticAt_dslope_update_iff_of_ne (hne : x i ≠ ζ) :
    AnalyticAt 𝕜 (fun z ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)) x ↔
      AnalyticAt 𝕜 (fun z ↦ f z - f (Function.update z i ζ)) x := by
  simpa only [analyticWithinAt_univ] using
    (analyticWithinAt_dslope_update_iff_of_ne (f := f) (s := Set.univ) hne)

/-- If `f` is analytic at `x` with complete target, its coordinate divided difference extends
analytically across the hyperplane through `x`. On the hyperplane its value is the derivative of
the corresponding coordinate slice. -/
theorem AnalyticAt.dslope_update_same [CompleteSpace F] (hf : AnalyticAt 𝕜 f x) (i : ι) :
    AnalyticAt 𝕜 (fun z ↦ dslope (fun w ↦ f (Function.update z i w)) (x i) (z i)) x := by
  obtain ⟨g, hg, hfg⟩ := hf.exists_eventuallyEq_coord_sub_smul i
  apply hg.congr
  apply (TauCeti.eventuallyEq_dslope_update_of_factorization ?_ hfg).symm
  filter_upwards [hg.eventually_analyticAt] with z hgz hzi
  have huz : Function.update z i (x i) = z := by rw [← hzi, Function.update_eq_self]
  exact hgz.continuousAt.comp_of_eq (continuousAt_const.update i continuousAt_id) huz

/-- With complete target, a coordinate divided difference is analytic if `f` is analytic at the
point and at the corresponding updated point. At a hyperplane point its value is the
coordinate-slice derivative. -/
theorem TauCeti.analyticAt_dslope_update [CompleteSpace F] (i : ι) (ζ : 𝕜)
    (hf : AnalyticAt 𝕜 f x)
    (hres : AnalyticAt 𝕜 f (Function.update x i ζ)) :
    AnalyticAt 𝕜 (fun z ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)) x := by
  by_cases hxi : x i = ζ
  · simpa only [hxi] using hf.dslope_update_same i
  · apply (analyticAt_dslope_update_iff_of_ne hxi).2
    have hu : AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦ Function.update z i ζ) x :=
      analyticAt_id.update analyticAt_const
    exact hf.sub (hres.comp_of_eq hu rfl)

/-- If updating the coordinate to `ζ` preserves the set, the coordinate divided difference
preserves analyticity near the set. -/
theorem AnalyticOnNhd.dslope_update [CompleteSpace F] {s : Set (ι → 𝕜)}
    (hf : AnalyticOnNhd 𝕜 f s) (hupdate : Set.MapsTo (fun z ↦ Function.update z i ζ) s s) :
    AnalyticOnNhd 𝕜 (fun z ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)) s :=
  fun z hz ↦ TauCeti.analyticAt_dslope_update i ζ (hf z hz) (hf _ (hupdate hz))
