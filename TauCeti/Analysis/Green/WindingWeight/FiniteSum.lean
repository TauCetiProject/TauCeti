/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Localization
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Basic.Complex.BigOperators

/-!
# Finite weighted winding supports

Finite integer-weighted families of closed absolutely continuous curves have integrable,
compactly supported total winding weight. If the total index vanishes outside a field domain
containing every trace, the total weight's topological support lies in that domain. Individual
indices may cancel there.
-/

public section

noncomputable section

open MeasureTheory Set Function
open scoped Topology

namespace TauCeti.Green

variable {ι : Type*} {s : Finset ι} {γ : ι → ℝ → ℂ} {a b : ι → ℝ} {w : ι → ℤ}
  {U : Set ℂ}

/-- A finite weighted sum of closed absolutely continuous winding weights is integrable. -/
theorem integrable_sum_windingWeight
    (hγ : ∀ i ∈ s, AbsolutelyContinuousOnInterval (γ i) (a i) (b i))
    (hclosed : ∀ i ∈ s, γ i (a i) = γ i (b i)) :
    Integrable (fun z ↦ ∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) z) := by
  exact integrable_finsetSum _ fun i hi ↦
    (integrable_windingWeight (hγ i hi) (hclosed i hi)).const_mul _

/-- Finite weighted winding families have compact support without a bounded-index assumption. -/
theorem hasCompactSupport_sum_windingWeight
    (hγ : ∀ i ∈ s, AbsolutelyContinuousOnInterval (γ i) (a i) (b i))
    (hclosed : ∀ i ∈ s, γ i (a i) = γ i (b i)) :
    HasCompactSupport (fun z ↦ ∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) z) := by
  have h := HasCompactSupport.finset_sum (s := s)
    (f := fun i z ↦ (w i : ℝ) * windingWeight (γ i) (a i) (b i) z)
    (fun i hi ↦ (hasCompactSupport_windingWeight (hγ i hi) (hclosed i hi)).mul_left)
  convert h using 1
  ext z
  simp only [Finset.sum_apply]

/-- Vanishing of the total index outside a domain suffices to localize the total winding weight.
No vanishing condition is imposed on the individual curves. -/
theorem tsupport_sum_windingWeight_subset
    (hγ : ∀ i ∈ s, AbsolutelyContinuousOnInterval (γ i) (a i) (b i))
    (hclosed : ∀ i ∈ s, γ i (a i) = γ i (b i))
    (htrace : ∀ i ∈ s, γ i '' uIcc (a i) (b i) ⊆ U)
    (hindex : ∀ z ∉ U, ∑ i ∈ s, (w i : ℂ) * Contour.windingNumber (γ i) (a i) (b i) z = 0) :
    tsupport (fun z ↦ ∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) z) ⊆ U := by
  intro z hz
  by_contra hzU
  have hzK (i) (hi : i ∈ s) : z ∉ γ i '' uIcc (a i) (b i) :=
    fun h ↦ hzU (htrace i hi h)
  have he : ∀ᶠ y in nhds z, ∀ i ∈ s,
      windingWeight (γ i) (a i) (b i) y = windingWeight (γ i) (a i) (b i) z :=
    (Filter.eventually_all_finset s).mpr fun i hi ↦
      windingWeight_eventuallyEq_of_notMem (hγ i hi) (hclosed i hi) (hzK i hi)
  have hsum : ∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) z = 0 := by
    have h := congrArg Complex.re (hindex z hzU)
    simp only [Complex.re_sum, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
      zero_mul, sub_zero, Complex.zero_re] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [windingWeight_eq_of_notMem (hzK i hi)]
  have hzero : (fun y ↦ ∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) y) =ᶠ[nhds z] 0 := by
    filter_upwards [he] with y hy
    simp only [Pi.zero_apply]
    rw [Finset.sum_congr rfl (fun i hi ↦ congrArg ((w i : ℝ) * ·) (hy i hi)), hsum]
  exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hz

/-- All traces and the total weighted winding support form a compact subset of the domain
under the total-index vanishing condition. -/
theorem isCompact_traces_union_tsupport_sum_windingWeight
    (hγ : ∀ i ∈ s, AbsolutelyContinuousOnInterval (γ i) (a i) (b i))
    (hclosed : ∀ i ∈ s, γ i (a i) = γ i (b i)) :
    IsCompact ((⋃ i ∈ s, γ i '' uIcc (a i) (b i)) ∪
      tsupport (fun z ↦ ∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) z)) :=
  (s.isCompact_biUnion fun i hi ↦ isCompact_uIcc.image_of_continuousOn
    (hγ i hi).continuousOn).union (hasCompactSupport_sum_windingWeight hγ hclosed)

/-- Finite weighted cycles can be localized using their total index and every trace. The
localized fields preserve every boundary integral and the total winding-weighted area integral. -/
theorem exists_contDiff_localization_sum {P Q : ℂ → ℝ}
    (hγ : ∀ i ∈ s, AbsolutelyContinuousOnInterval (γ i) (a i) (b i))
    (hclosed : ∀ i ∈ s, γ i (a i) = γ i (b i)) (hU : IsOpen U)
    (htrace : ∀ i ∈ s, γ i '' uIcc (a i) (b i) ⊆ U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U)
    (hindex : ∀ z ∉ U, ∑ i ∈ s, (w i : ℂ) * Contour.windingNumber (γ i) (a i) (b i) z = 0) :
    ∃ P' Q' : ℂ → ℝ,
      ContDiff ℝ 1 P' ∧ ContDiff ℝ 1 Q' ∧ HasCompactSupport P' ∧ HasCompactSupport Q' ∧
      tsupport P' ⊆ U ∧ tsupport Q' ⊆ U ∧
      (∀ i ∈ s, EqOn P' P (γ i '' uIcc (a i) (b i))) ∧
      (∀ i ∈ s, EqOn Q' Q (γ i '' uIcc (a i) (b i))) ∧
      (∀ z, (∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) z) * curl P' Q' z =
        (∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) z) * curl P Q z) ∧
      (∀ i ∈ s, (∫ t in a i..b i, circulationFun P' Q' (γ i) t) =
        ∫ t in a i..b i, circulationFun P Q (γ i) t) ∧
      (∫ z in U, (∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) z) * curl P' Q' z) =
        ∫ z in U, (∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) z) * curl P Q z := by
  let W := fun z ↦ ∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) z
  let K := (⋃ i ∈ s, γ i '' uIcc (a i) (b i)) ∪ tsupport W
  have hK : IsCompact K := isCompact_traces_union_tsupport_sum_windingWeight hγ hclosed
  have hKU : K ⊆ U := union_subset (iUnion_subset fun i ↦ iUnion_subset (htrace i))
    (tsupport_sum_windingWeight_subset hγ hclosed htrace hindex)
  obtain ⟨P', hP', hcP, hsP, heP⟩ := hP.exists_contDiff_eventuallyEq_on_isCompact hK hU hKU
  obtain ⟨Q', hQ', hcQ, hsQ, heQ⟩ := hQ.exists_contDiff_eventuallyEq_on_isCompact hK hU hKU
  have htK (i) (hi : i ∈ s) {z} (hz : z ∈ γ i '' uIcc (a i) (b i)) : z ∈ K :=
    Or.inl (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hz⟩⟩)
  have hPt : ∀ i ∈ s, EqOn P' P (γ i '' uIcc (a i) (b i)) :=
    fun i hi z hz ↦ (heP z (htK i hi hz)).eq_of_nhds
  have hQt : ∀ i ∈ s, EqOn Q' Q (γ i '' uIcc (a i) (b i)) :=
    fun i hi z hz ↦ (heQ z (htK i hi hz)).eq_of_nhds
  have hw : ∀ z, W z * curl P' Q' z = W z * curl P Q z := by
    intro z
    by_cases hz : W z = 0
    · simp only [hz, zero_mul]
    · have hzK : z ∈ K := Or.inr (subset_tsupport W hz)
      rw [curl_def, curl_def, (heP z hzK).fderiv_eq, (heQ z hzK).fderiv_eq]
  refine ⟨P', Q', hP', hQ', hcP, hcQ, hsP, hsQ, hPt, hQt, hw, ?_, ?_⟩
  · intro i hi
    apply intervalIntegral.integral_congr
    intro t ht
    rw [circulationFun_def, circulationFun_def,
      hPt i hi ⟨t, ht, rfl⟩, hQt i hi ⟨t, ht, rfl⟩]
  · exact setIntegral_congr_fun hU.measurableSet (fun z _ ↦ hw z)

end TauCeti.Green
