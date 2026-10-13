/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.PolygonalApproximation
public import TauCeti.Analysis.Green.WindingWeight.Convergence
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Proximity
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Polygonal approximation preserving an index domain

Uniformly close closed absolutely continuous curves have the same index outside any open
neighborhood of the original trace. Endpoint-preserving polygonal approximation therefore
preserves an index-vanishing domain eventually, while the winding weights converge in `L¹`.
-/

public section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace TauCeti.Green

variable {γ : ℝ → ℂ} {a b : ℝ} {U : Set ℂ}

/-- Uniform approximation of closed AC curves preserves the trace domain and every index outside
that domain once the approximation is sufficiently close. -/
theorem eventually_windingNumber_eq_on_compl_of_tendstoUniformlyOn
    {γn : ℕ → ℝ → ℂ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hγn : ∀ n, AbsolutelyContinuousOnInterval (γn n) a b)
    (hclosed : γ a = γ b) (hclosedn : ∀ n, γn n a = γn n b)
    (hconv : TendstoUniformlyOn γn γ atTop (uIcc a b))
    (hU : IsOpen U) (htrace : γ '' uIcc a b ⊆ U) :
    ∀ᶠ n in atTop, γn n '' uIcc a b ⊆ U ∧
      ∀ z ∉ U, Contour.windingNumber (γn n) a b z = Contour.windingNumber γ a b z := by
  obtain ⟨ε, hε, hεU⟩ :=
    (isCompact_uIcc.image_of_continuousOn hγ.continuousOn).exists_thickening_subset_open hU htrace
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv ε hε] with n hn
  have hnear (t) (ht : t ∈ uIcc a b) : dist (γn n t) (γ t) < ε := by
    simpa only [dist_comm] using hn t ht
  constructor
  · rintro z ⟨t, ht, rfl⟩
    exact hεU (mem_thickening_iff.mpr ⟨γ t, ⟨t, ht, rfl⟩, hnear t ht⟩)
  · intro z hz
    apply Contour.windingNumber_eq_of_dist_lt_dist_of_absolutelyContinuousOnInterval
      hγ (hγn n) hclosed (hclosedn n)
    intro t ht
    have hdist : ε ≤ dist (γ t) z := by
      by_contra h
      exact hz (hεU (mem_thickening_iff.mpr ⟨γ t, ⟨t, ht, rfl⟩,
        by simpa only [dist_comm] using lt_of_not_ge h⟩))
    exact (hnear t ht).trans_le hdist

/-- A closed AC curve with index vanishing outside its field domain has closed polygonal
approximants converging uniformly, in derivative `L¹`, and in winding-weight `L¹`. Eventually
their traces lie in the domain and their indices also vanish outside it. -/
theorem exists_polygonal_approximation_winding (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hU : IsOpen U) (htrace : γ '' uIcc a b ⊆ U)
    (hindex : ∀ z ∉ U, Contour.windingNumber γ a b z = 0) :
    ∃ γn : ℕ → ℝ → ℂ,
      (∀ n, IsPolygonalOnInterval (γn n) a b ∧ AbsolutelyContinuousOnInterval (γn n) a b ∧
        γn n a = γ a ∧ γn n b = γ b ∧ γn n a = γn n b) ∧
      TendstoUniformlyOn γn γ atTop (Icc a b) ∧
      Tendsto (fun n ↦ ∫ t in a..b, ‖deriv (γn n) t - deriv γ t‖) atTop (nhds 0) ∧
      Tendsto (fun n ↦ ∫ z : ℂ, |windingWeight (γn n) a b z - windingWeight γ a b z|)
        atTop (nhds 0) ∧
      ∀ᶠ n in atTop, γn n '' uIcc a b ⊆ U ∧
        ∀ z ∉ U, Contour.windingNumber (γn n) a b z = 0 := by
  obtain ⟨γn, hn, hu, hd⟩ := hγ.exists_polygonal_approximation hab
  have hAC (n) := (hn n).2.1
  have hcl (n) : γn n a = γn n b := (hn n).2.2.1.trans (hclosed.trans (hn n).2.2.2.symm)
  refine ⟨γn, fun n ↦ ⟨(hn n).1, hAC n, (hn n).2.2.1, (hn n).2.2.2, hcl n⟩,
    hu, hd, tendsto_integral_abs_windingWeight_sub hab.le hAC hγ hcl hclosed hu hd, ?_⟩
  have hu' : TendstoUniformlyOn γn γ atTop (uIcc a b) := by
    rwa [uIcc_of_le hab.le]
  filter_upwards [eventually_windingNumber_eq_on_compl_of_tendstoUniformlyOn
    hγ hAC hclosed hcl hu' hU htrace] with n hn
  exact ⟨hn.1, fun z hz ↦ (hn.2 z hz).trans (hindex z hz)⟩

end TauCeti.Green
