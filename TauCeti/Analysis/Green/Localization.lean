/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.WindingWeight.Basic
public import TauCeti.Analysis.Green.Basic
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.LocallyConstant

/-!
# Localization of planar Green fields

If the index of a closed absolutely continuous curve vanishes outside an open field domain,
its trace and the topological support of its winding weight lie in a compact subset of that
domain. Smooth cutoffs then give globally `C¹` fields preserving both the circulation integral
and the winding-weighted curl integral.
-/

public section

noncomputable section

open MeasureTheory Set Function
open scoped Topology

namespace TauCeti.Green

variable {γ : ℝ → ℂ} {a b : ℝ} {U : Set ℂ}

/-- Local constancy prevents the winding support from accumulating at an excluded point away
from the trace. Thus an index-vanishing domain containing the trace contains the topological
support of the winding weight. -/
theorem tsupport_windingWeight_subset
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (htrace : γ '' uIcc a b ⊆ U)
    (hindex : ∀ z ∉ U, Contour.windingNumber γ a b z = 0) :
    tsupport (windingWeight γ a b) ⊆ U := by
  intro z hz
  by_contra hzU
  have hzK : z ∉ γ '' uIcc a b := fun h ↦ hzU (htrace h)
  have hzero : windingWeight γ a b =ᶠ[nhds z] 0 := by
    simpa only [windingWeight_eq_of_notMem hzK, hindex z hzU, Complex.zero_re, Pi.zero_def]
      using windingWeight_eventuallyEq_of_notMem hγ hclosed hzK
  exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hz

/-- The trace and winding support fit together in a compact subset of the index-vanishing
field domain. -/
theorem isCompact_trace_union_tsupport_windingWeight
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b) :
    IsCompact (γ '' uIcc a b ∪ tsupport (windingWeight γ a b)) :=
  (isCompact_uIcc.image_of_continuousOn hγ.continuousOn).union
    (hasCompactSupport_windingWeight hγ hclosed)

/-- A locally `C¹` field can be cut off to a globally `C¹`, compactly supported field without
changing circulation or the winding-weighted curl integral. -/
theorem exists_contDiff_localization {P Q : ℂ → ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hU : IsOpen U) (htrace : γ '' uIcc a b ⊆ U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U)
    (hindex : ∀ z ∉ U, Contour.windingNumber γ a b z = 0) :
    ∃ P' Q' : ℂ → ℝ,
      ContDiff ℝ 1 P' ∧ ContDiff ℝ 1 Q' ∧ HasCompactSupport P' ∧ HasCompactSupport Q' ∧
      tsupport P' ⊆ U ∧ tsupport Q' ⊆ U ∧
      EqOn P' P (γ '' uIcc a b) ∧ EqOn Q' Q (γ '' uIcc a b) ∧
      (∀ z, windingWeight γ a b z * curl P' Q' z = windingWeight γ a b z * curl P Q z) ∧
      (∫ t in a..b, circulationFun P' Q' γ t) =
        (∫ t in a..b, circulationFun P Q γ t) ∧
      (∫ z in U, windingWeight γ a b z * curl P' Q' z) =
        (∫ z in U, windingWeight γ a b z * curl P Q z) := by
  let K := γ '' uIcc a b ∪ tsupport (windingWeight γ a b)
  have hK : IsCompact K := isCompact_trace_union_tsupport_windingWeight hγ hclosed
  have hKU : K ⊆ U := union_subset htrace (tsupport_windingWeight_subset hγ hclosed htrace hindex)
  obtain ⟨P', hP', hcP, hsP, heP⟩ := hP.exists_contDiff_eventuallyEq_on_isCompact hK hU hKU
  obtain ⟨Q', hQ', hcQ, hsQ, heQ⟩ := hQ.exists_contDiff_eventuallyEq_on_isCompact hK hU hKU
  have hPt : EqOn P' P (γ '' uIcc a b) := fun z hz ↦ (heP z (Or.inl hz)).eq_of_nhds
  have hQt : EqOn Q' Q (γ '' uIcc a b) := fun z hz ↦ (heQ z (Or.inl hz)).eq_of_nhds
  have hw : ∀ z, windingWeight γ a b z * curl P' Q' z =
      windingWeight γ a b z * curl P Q z := by
    intro z
    by_cases hz : windingWeight γ a b z = 0
    · simp only [hz, zero_mul]
    · have hzK : z ∈ K := Or.inr (subset_tsupport _ hz)
      rw [curl_def, curl_def, (heP z hzK).fderiv_eq, (heQ z hzK).fderiv_eq]
  refine ⟨P', Q', hP', hQ', hcP, hcQ, hsP, hsQ, hPt, hQt, hw, ?_, ?_⟩
  · apply intervalIntegral.integral_congr
    intro t ht
    rw [circulationFun_def, circulationFun_def, hPt ⟨t, ht, rfl⟩, hQt ⟨t, ht, rfl⟩]
  · exact setIntegral_congr_fun hU.measurableSet (fun z _ ↦ hw z)

end TauCeti.Green
