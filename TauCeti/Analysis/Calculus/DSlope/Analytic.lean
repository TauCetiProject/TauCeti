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
is analytic. With complete target, this criterion also holds across the hyperplane and near
arbitrary sets. On the hyperplane the divided difference takes the coordinate-slice derivative.

## Main results

* `AnalyticWithinAt.sub_update_of_dslope_update`: analyticity of the divided difference
  implies analyticity of its numerator, with no completeness or hyperplane restriction.
* `TauCeti.analyticWithinAt_dslope_update_iff_of_ne`,
  `TauCeti.analyticAt_dslope_update_iff_of_ne`, `TauCeti.analyticOn_dslope_update_iff_of_ne`,
  and `TauCeti.analyticOnNhd_dslope_update_iff_of_ne`: analyticity away from the base hyperplane.
* `TauCeti.analyticAt_dslope_update_iff` and `TauCeti.analyticOnNhd_dslope_update_iff`:
  numerator criteria with complete target, including the base hyperplane and arbitrary sets.
* `TauCeti.analyticAt_dslope_update`: the combined coordinate divided-difference theorem.
* `AnalyticOnNhd.dslope_update`: coordinate divided differences preserve neighborhood
  analyticity when the function is analytic near both the source and updated points.
-/

public section

open Filter Topology

variable {𝕜 ι F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : (ι → 𝕜) → F} {x : ι → 𝕜} {i : ι} {ζ : 𝕜}

/-- An analytic coordinate divided difference has analytic numerator within the same set,
including on the base hyperplane and without assuming the target is complete. -/
theorem AnalyticWithinAt.sub_update_of_dslope_update {s : Set (ι → 𝕜)}
    (h : AnalyticWithinAt 𝕜
      (fun z ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)) s x) :
    AnalyticWithinAt 𝕜 (fun z ↦ f z - f (Function.update z i ζ)) s x := by
  have hcoord : AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦ z i) x :=
    (ContinuousLinearMap.proj (R := 𝕜) i).analyticAt x
  simpa only [sub_smul_dslope, Function.update_eq_self] using
    (hcoord.fun_sub (analyticAt_const (v := ζ))).analyticWithinAt.smul h

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
  · exact AnalyticWithinAt.sub_update_of_dslope_update
  · intro h
    have hquot := ((hcoord.fun_sub (analyticAt_const (v := ζ))).analyticWithinAt.fun_inv
      (sub_ne_zero.mpr hne)).smul h
    have heq : (fun z ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)) =ᶠ[𝓝 x]
        (fun z ↦ (z i - ζ)⁻¹ • (f z - f (Function.update z i ζ))) := by
      filter_upwards [hcoord.continuousAt.eventually_ne hne] with z hz
      apply (eq_inv_smul_iff₀ (sub_ne_zero.mpr hz)).2
      simp only [sub_smul_dslope, Function.update_eq_self]
    exact hquot.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds

/-- Away from its base hyperplane, a coordinate divided difference is analytic exactly when
its numerator is analytic. No separate analyticity of the numerator's two terms is needed. -/
theorem TauCeti.analyticAt_dslope_update_iff_of_ne (hne : x i ≠ ζ) :
    AnalyticAt 𝕜 (fun z ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)) x ↔
      AnalyticAt 𝕜 (fun z ↦ f z - f (Function.update z i ζ)) x := by
  simpa only [analyticWithinAt_univ] using
    (analyticWithinAt_dslope_update_iff_of_ne (f := f) (s := Set.univ) hne)

/-- Away from the base hyperplane on a set, a coordinate divided difference is analytic
on the set exactly when its numerator is analytic there, without target completeness. -/
theorem TauCeti.analyticOn_dslope_update_iff_of_ne {s : Set (ι → 𝕜)}
    (hne : ∀ z ∈ s, z i ≠ ζ) :
    AnalyticOn 𝕜 (fun z ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)) s ↔
      AnalyticOn 𝕜 (fun z ↦ f z - f (Function.update z i ζ)) s :=
  forall₂_congr fun z hz ↦ analyticWithinAt_dslope_update_iff_of_ne (hne z hz)

/-- Away from the base hyperplane on a set, a coordinate divided difference is analytic
near the set exactly when its numerator is analytic there, without target completeness. -/
theorem TauCeti.analyticOnNhd_dslope_update_iff_of_ne {s : Set (ι → 𝕜)}
    (hne : ∀ z ∈ s, z i ≠ ζ) :
    AnalyticOnNhd 𝕜 (fun z ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)) s ↔
      AnalyticOnNhd 𝕜 (fun z ↦ f z - f (Function.update z i ζ)) s :=
  forall₂_congr fun z hz ↦ analyticAt_dslope_update_iff_of_ne (hne z hz)

/-- With complete target, a coordinate divided difference is analytic exactly when its
numerator is analytic, including on the base hyperplane. The two terms of the numerator need
not be separately analytic. -/
theorem TauCeti.analyticAt_dslope_update_iff [CompleteSpace F] (i : ι) (ζ : 𝕜) :
    AnalyticAt 𝕜 (fun z ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)) x ↔
      AnalyticAt 𝕜 (fun z ↦ f z - f (Function.update z i ζ)) x := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa only [analyticWithinAt_univ] using
      (h.analyticWithinAt (s := Set.univ)).sub_update_of_dslope_update
  by_cases hxi : x i = ζ
  · subst ζ
    obtain ⟨g, hg, hfactor⟩ := h.exists_eventuallyEq_coord_sub_smul i
      (Filter.Eventually.of_forall fun z ↦ by
        simp only [Function.update_idem, sub_self, Pi.zero_apply])
    apply hg.congr
    apply (TauCeti.eventuallyEq_dslope_update_of_factorization ?_ hfactor).symm
    filter_upwards [hg.eventually_analyticAt] with z hgz hzi
    have huz : Function.update z i (x i) = z := by rw [← hzi, Function.update_eq_self]
    exact hgz.continuousAt.comp_of_eq (continuousAt_const.update i continuousAt_id) huz
  · exact (analyticAt_dslope_update_iff_of_ne hxi).2 h

/-- With complete target, a coordinate divided difference is analytic near an arbitrary set
exactly when its numerator is analytic there. No preservation of the set by the base-coordinate
update is required. -/
theorem TauCeti.analyticOnNhd_dslope_update_iff [CompleteSpace F] (i : ι) (ζ : 𝕜)
    {s : Set (ι → 𝕜)} :
    AnalyticOnNhd 𝕜 (fun z ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)) s ↔
      AnalyticOnNhd 𝕜 (fun z ↦ f z - f (Function.update z i ζ)) s := by
  simp only [AnalyticOnNhd, analyticAt_dslope_update_iff i ζ]

/-- With complete target, a coordinate divided difference is analytic if `f` is analytic at the
point and at the corresponding updated point. At a hyperplane point its value is the
coordinate-slice derivative. -/
@[fun_prop]
theorem TauCeti.analyticAt_dslope_update [CompleteSpace F] (i : ι) (ζ : 𝕜)
    (hf : AnalyticAt 𝕜 f x)
    (hres : AnalyticAt 𝕜 f (Function.update x i ζ)) :
    AnalyticAt 𝕜 (fun z ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)) x := by
  apply (analyticAt_dslope_update_iff i ζ).2
  exact hf.fun_sub hres.comp_update

/-- A coordinate divided difference is analytic near a source set if the function is analytic
near that set and near a target set containing its base-coordinate updates. -/
@[fun_prop]
theorem AnalyticOnNhd.dslope_update [CompleteSpace F] {s t : Set (ι → 𝕜)}
    (hf : AnalyticOnNhd 𝕜 f s) (ht : AnalyticOnNhd 𝕜 f t)
    (hupdate : Set.MapsTo (fun z ↦ Function.update z i ζ) s t) :
    AnalyticOnNhd 𝕜 (fun z ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)) s := by
  intro x hx
  exact TauCeti.analyticAt_dslope_update i ζ (hf x hx) (ht _ (hupdate hx))
