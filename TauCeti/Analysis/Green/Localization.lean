/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.WindingWeight.FiniteSum
public import TauCeti.Analysis.Green.Basic
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Localization of planar Green fields

The union of a closed absolutely continuous curve's trace and winding support is compact.
The same holds for finitely many closed AC traces and their total weighted winding support,
without any index-vanishing assumption. If every trace lies in an open field domain and the
single or total index vanishes outside that domain, the compact union is contained in the
domain. Smooth cutoffs then give globally `C¹` fields preserving circulation along each curve
and the single or total winding-weighted curl integral.
-/

public section

noncomputable section

open MeasureTheory Set Function
open scoped Topology

namespace TauCeti.Green

section

variable {ι : Type*} {s : Finset ι} {γ : ι → ℝ → ℂ} {a b : ι → ℝ} {w : ι → ℤ}
  {U : Set ℂ}

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
      rw [curl, curl, (heP z hzK).fderiv_eq, (heQ z hzK).fderiv_eq]
  refine ⟨P', Q', hP', hQ', hcP, hcQ, hsP, hsQ, hPt, hQt, hw, ?_, ?_⟩
  · intro i hi
    apply intervalIntegral.integral_congr
    intro t ht
    rw [circulationFun, circulationFun,
      hPt i hi ⟨t, ht, rfl⟩, hQt i hi ⟨t, ht, rfl⟩]
  · exact setIntegral_congr_fun hU.measurableSet (fun z _ ↦ hw z)

end

variable {γ : ℝ → ℂ} {a b : ℝ} {U : Set ℂ}

/-- A locally `C¹` field can be cut off to a globally `C¹`, compactly supported field without
changing circulation or the winding-weighted curl integral. -/
theorem _root_.AbsolutelyContinuousOnInterval.exists_contDiff_localization {P Q : ℂ → ℝ}
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
  have h := exists_contDiff_localization_sum (s := {()}) (γ := fun _ : Unit ↦ γ)
    (a := fun _ ↦ a) (b := fun _ ↦ b) (w := fun _ ↦ (1 : ℤ))
    (fun _ _ ↦ hγ) (fun _ _ ↦ hclosed) hU (fun _ _ ↦ htrace) hP hQ
    (by simpa only [Finset.sum_singleton, Int.cast_one, one_mul] using hindex)
  simpa only [Finset.sum_singleton, Int.cast_one, one_mul, Finset.mem_singleton,
    forall_eq, forall_const, true_implies] using h

end TauCeti.Green
