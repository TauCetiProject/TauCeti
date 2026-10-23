/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.PolygonalApproximation
public import TauCeti.Analysis.Green.WindingWeight.Convergence
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Proximity

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
  have hAC (n) := (hn n).1.absolutelyContinuousOnInterval
  have hcl (n) : γn n a = γn n b := (hn n).2.1.trans (hclosed.trans (hn n).2.2.symm)
  refine ⟨γn, fun n ↦ ⟨(hn n).1, hAC n, (hn n).2.1, (hn n).2.2, hcl n⟩,
    hu, hd, tendsto_integral_abs_windingWeight_sub hab.le hAC hγ hcl hclosed hu hd, ?_⟩
  have hu' : TendstoUniformlyOn γn γ atTop (uIcc a b) := by
    rwa [uIcc_of_le hab.le]
  filter_upwards [AbsolutelyContinuousOnInterval.eventually_windingNumber_eq_on_compl
    hγ hAC hclosed hcl hu' hU htrace] with n hn
  exact ⟨hn.1, fun z hz ↦ (hn.2 z hz).trans (hindex z hz)⟩

end TauCeti.Green
