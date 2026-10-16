/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Polygonal.Basic
public import TauCeti.Analysis.Green.Polygonal.Geometry
import TauCeti.Analysis.Complex.PlaneSeparation.Segment
public import Mathlib.Basic.Real.Sign
import TauCeti.Analysis.Contour.Winding.Number.Segment.Bounds
import TauCeti.Analysis.Contour.Winding.Number.Concat
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Measure.OpenPos
import TauCeti.Analysis.Contour.Winding.Continuity

/-!
# The winding number of an oriented triangle

The triangle winding number is positive or negative on the interior according to the ordered
orientation and vanishes outside the convex hull, including for degenerate triangles away from
their edges. These signed certificates supply the triangle indicators in finite fan identities.
-/

public section

open Set MeasureTheory Complex

namespace TauCeti.Green

/-- Away from the three edges, the triangle winding number is the sum of the edge windings. -/
theorem windingNumber_triangleCurve_eq_sum {c p q z : ℂ}
    (hz : z ∉ segment ℝ c p ∪ segment ℝ p q ∪ segment ℝ q c) :
    Contour.windingNumber (triangleCurve c p q) 0 3 z =
      Contour.windingNumber (fun t : ℝ ↦ c + t • (p - c)) 0 1 z +
      Contour.windingNumber (fun t : ℝ ↦ p + t • (q - p)) 0 1 z +
      Contour.windingNumber (fun t : ℝ ↦ q + t • (c - q)) 0 1 z := by
  have hAC := absolutelyContinuousOnInterval_triangleCurve c p q
  have havoid : z ∉ triangleCurve c p q '' uIcc 0 3 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3), image_triangleCurve] using hz
  have hpv (s t : ℝ) (hs : s ∈ uIcc (0 : ℝ) 3) (ht : t ∈ uIcc (0 : ℝ) 3) :
      Contour.CauchyPVExistsAt (triangleCurve c p q) s t (fun w ↦ (w - z)⁻¹) z := by
    have hsub := uIcc_subset_uIcc hs ht
    have hAC' := hAC.mono hsub
    have havoid' : z ∉ triangleCurve c p q '' uIcc s t :=
      fun h ↦ havoid (image_mono hsub h)
    exact Contour.cauchyPVExistsAt_of_avoidance hAC'.continuousOn
      (fun v hv he ↦ havoid' ⟨v, hv, he⟩)
      (hAC'.intervalIntegrable_inv_sub_mul_deriv havoid')
  have h0 : (0 : ℝ) ∈ uIcc 0 3 := left_mem_uIcc
  have h1 : (1 : ℝ) ∈ uIcc 0 3 := by norm_num [uIcc_of_le]
  have h2 : (2 : ℝ) ∈ uIcc 0 3 := by norm_num [uIcc_of_le]
  have h3 : (3 : ℝ) ∈ uIcc 0 3 := right_mem_uIcc
  rw [Contour.windingNumber_concat (hpv 0 1 h0 h1) (hpv 1 3 h1 h3),
    Contour.windingNumber_concat (hpv 1 2 h1 h2) (hpv 2 3 h2 h3)]
  have hfirst : Contour.windingNumber (triangleCurve c p q) 0 1 z =
      Contour.windingNumber (fun t : ℝ ↦ c + t • (p - c)) 0 1 z := by
    apply Contour.windingNumber_congr_curve
    intro t ht
    apply triangleCurve_eq_first
    simpa only [uIcc_of_le zero_le_one] using uIoo_subset_uIcc_self ht
  have hsecond : Contour.windingNumber (triangleCurve c p q) 1 2 z =
      Contour.windingNumber (fun t : ℝ ↦ p + t • (q - p)) 0 1 z := by
    calc
      _ = Contour.windingNumber (fun t : ℝ ↦ p + (t - 1) • (q - p)) 1 2 z := by
        apply Contour.windingNumber_congr_curve
        intro t ht
        apply triangleCurve_eq_second
        simpa only [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using uIoo_subset_uIcc_self ht
      _ = _ := by
        have hlength : (2 : ℝ) - 1 = 1 := by norm_num
        simpa only [hlength, div_one] using
          Contour.windingNumber_segment_interval (p := p) (q := q) (a := 1) (b := 2)
            (by norm_num) (fun h ↦ hz (Or.inl (Or.inr h)))
  have hthird : Contour.windingNumber (triangleCurve c p q) 2 3 z =
      Contour.windingNumber (fun t : ℝ ↦ q + t • (c - q)) 0 1 z := by
    calc
      _ = Contour.windingNumber (fun t : ℝ ↦ q + (t - 2) • (c - q)) 2 3 z := by
        apply Contour.windingNumber_congr_curve
        intro t ht
        apply triangleCurve_eq_third
        simpa only [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using uIoo_subset_uIcc_self ht
      _ = _ := by
        have hlength : (3 : ℝ) - 2 = 1 := by norm_num
        simpa only [hlength, div_one] using
          Contour.windingNumber_segment_interval (p := q) (q := c) (a := 2) (b := 3)
            (by norm_num) (fun h ↦ hz (Or.inr h))
  rw [hfirst, hsecond, hthird]
  abel

private theorem interior_edge_heights {c p q z : ℂ} (hdet : 0 < triangleDet c p q)
    (hz : z ∈ interior (convexHull ℝ {c, p, q})) :
    0 < ((z - c) / (p - c)).im ∧ 0 < ((z - p) / (q - p)).im ∧
      0 < ((z - q) / (c - q)).im := by
  have hdet₁ : 0 < triangleDet p q c := by rwa [triangleDet_cyclic]
  have hdet₂ : 0 < triangleDet q c p := by rwa [triangleDet_cyclic, triangleDet_cyclic]
  have hset₁ : ({p, q, c} : Set ℂ) = {c, p, q} := by
    ext x
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto
  have hset₂ : ({q, c, p} : Set ℂ) = {c, p, q} := by
    ext x
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto
  exact ⟨im_div_pos_of_mem_interior_convexHull_triangle
      (sub_ne_zero_of_triangleDet_pos hdet) (im_div_sub_pos_of_triangleDet_pos hdet).le hz,
    im_div_pos_of_mem_interior_convexHull_triangle
      (sub_ne_zero_of_triangleDet_pos hdet₁) (im_div_sub_pos_of_triangleDet_pos hdet₁).le
      (hset₁.symm ▸ hz),
    im_div_pos_of_mem_interior_convexHull_triangle
      (sub_ne_zero_of_triangleDet_pos hdet₂) (im_div_sub_pos_of_triangleDet_pos hdet₂).le
      (hset₂.symm ▸ hz)⟩

/-- A positively oriented triangle winds once around every point in its interior. -/
theorem windingNumber_triangleCurve_eq_one {c p q z : ℂ} (hdet : 0 < triangleDet c p q)
    (hz : z ∈ interior (convexHull ℝ {c, p, q})) :
    Contour.windingNumber (triangleCurve c p q) 0 3 z = 1 := by
  obtain ⟨h₁, h₂, h₃⟩ := interior_edge_heights hdet hz
  have havoid : z ∉ segment ℝ c p ∪ segment ℝ p q ∪ segment ℝ q c := by
    rintro ((h | h) | h)
    exacts [TauCeti.notMem_segment_of_im_div_sub_pos h₁ h,
      TauCeti.notMem_segment_of_im_div_sub_pos h₂ h,
      TauCeti.notMem_segment_of_im_div_sub_pos h₃ h]
  obtain ⟨n, hn⟩ := AbsolutelyContinuousOnInterval.exists_int_windingNumber
    (absolutelyContinuousOnInterval_triangleCurve c p q)
    (by simp) (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3), image_triangleCurve]
      using havoid)
  have hsum := congrArg Complex.re (windingNumber_triangleCurve_eq_sum havoid)
  simp only [Complex.add_re, hn, Complex.intCast_re] at hsum
  have he₁ := Contour.windingNumber_segment_re_mem_Ioo h₁
  have he₂ := Contour.windingNumber_segment_re_mem_Ioo h₂
  have he₃ := Contour.windingNumber_segment_re_mem_Ioo h₃
  have hnp : (0 : ℝ) < n := by linarith [he₁.1, he₂.1, he₃.1]
  have hnl : (n : ℝ) < 2 := by linarith [he₁.2, he₂.2, he₃.2]
  have hnp' : (0 : ℤ) < n := by exact_mod_cast hnp
  have hnl' : n < (2 : ℤ) := by exact_mod_cast hnl
  have hne : n = 1 := by omega
  rw [hn, hne]
  norm_num

private theorem triangle_edges_swap (c p q : ℂ) :
    segment ℝ c q ∪ segment ℝ q p ∪ segment ℝ p c =
      segment ℝ c p ∪ segment ℝ p q ∪ segment ℝ q c := by
  rw [segment_symm ℝ c q, segment_symm ℝ q p, segment_symm ℝ p c]
  ext z
  simp only [mem_union]
  tauto

/-- Reversing the ordered vertices negates the actual triangle winding number off its edges. -/
theorem windingNumber_triangleCurve_swap {c p q z : ℂ}
    (hz : z ∉ segment ℝ c p ∪ segment ℝ p q ∪ segment ℝ q c) :
    Contour.windingNumber (triangleCurve c p q) 0 3 z =
      -Contour.windingNumber (triangleCurve c q p) 0 3 z := by
  have hz' : z ∉ segment ℝ c q ∪ segment ℝ q p ∪ segment ℝ p c := by
    rwa [triangle_edges_swap]
  rw [windingNumber_triangleCurve_eq_sum hz, windingNumber_triangleCurve_eq_sum hz',
    Contour.windingNumber_segment_swap (fun h ↦ hz (Or.inr h)),
    Contour.windingNumber_segment_swap (fun h ↦ hz (Or.inl (Or.inr h))),
    Contour.windingNumber_segment_swap (fun h ↦ hz (Or.inl (Or.inl h)))]
  ring

/-- A negatively oriented triangle winds negatively once around every interior point. -/
theorem windingNumber_triangleCurve_eq_neg_one {c p q z : ℂ} (hdet : triangleDet c p q < 0)
    (hz : z ∈ interior (convexHull ℝ {c, p, q})) :
    Contour.windingNumber (triangleCurve c p q) 0 3 z = -1 := by
  have hdet' : 0 < triangleDet c q p := by rw [triangleDet_swap]; exact neg_pos.mpr hdet
  have hset : ({c, q, p} : Set ℂ) = {c, p, q} := by ext; simp [or_comm]
  have hz' : z ∈ interior (convexHull ℝ {c, q, p}) := hset.symm ▸ hz
  obtain ⟨h₁, h₂, h₃⟩ := interior_edge_heights hdet' hz'
  have havoid' : z ∉ segment ℝ c q ∪ segment ℝ q p ∪ segment ℝ p c := by
    rintro ((h | h) | h)
    exacts [TauCeti.notMem_segment_of_im_div_sub_pos h₁ h,
      TauCeti.notMem_segment_of_im_div_sub_pos h₂ h,
      TauCeti.notMem_segment_of_im_div_sub_pos h₃ h]
  have havoid : z ∉ segment ℝ c p ∪ segment ℝ p q ∪ segment ℝ q c := by
    rwa [← triangle_edges_swap]
  rw [windingNumber_triangleCurve_swap havoid, windingNumber_triangleCurve_eq_one hdet' hz']

/-- The winding number of a triangle vanishes outside its convex hull. -/
theorem windingNumber_triangleCurve_eq_zero_of_notMem_convexHull {c p q z : ℂ}
    (hz : z ∉ convexHull ℝ {c, p, q}) :
    Contour.windingNumber (triangleCurve c p q) 0 3 z = 0 := by
  have hconv := convex_convexHull ℝ ({c, p, q} : Set ℂ)
  have hc : c ∈ convexHull ℝ {c, p, q} := subset_convexHull ℝ _ (by simp)
  have hp : p ∈ convexHull ℝ {c, p, q} := subset_convexHull ℝ _ (by simp)
  have hq : q ∈ convexHull ℝ {c, p, q} := subset_convexHull ℝ _ (by simp)
  have htrace : triangleCurve c p q '' uIcc 0 3 ⊆ convexHull ℝ {c, p, q} := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3), image_triangleCurve]
    exact union_subset (union_subset (hconv.segment_subset hc hp) (hconv.segment_subset hp hq))
      (hconv.segment_subset hq hc)
  have hfill : filledHull (triangleCurve c p q '' uIcc 0 3) ⊆ convexHull ℝ {c, p, q} :=
    (filledHull_subset_closedConvexHull (K := triangleCurve c p q '' uIcc 0 3)
      ⟨c, 0, left_mem_uIcc, triangleCurve_zero c p q⟩).trans
      (closedConvexHull_min htrace hconv
        ((Set.toFinite ({c, p, q} : Set ℂ)).isClosed_convexHull ℝ))
  apply AbsolutelyContinuousOnInterval.windingNumber_eq_zero_of_unbounded_component
    (absolutelyContinuousOnInterval_triangleCurve c p q) (by simp)
  intro hbounded
  exact hz (hfill (mem_filledHull_iff.mpr hbounded))

/-- Almost everywhere, a triangle's actual winding weight is its orientation times the indicator
of its interior. Degenerate triangles contribute zero. -/
theorem windingWeight_triangleCurve_ae_eq (c p q : ℂ) :
    windingWeight (triangleCurve c p q) 0 3 =ᵐ[volume]
      fun z ↦ Real.sign (triangleDet c p q) *
        (interior (convexHull ℝ {c, p, q})).indicator (fun _ : ℂ ↦ (1 : ℝ)) z := by
  have hclosed : IsClosed (convexHull ℝ {c, p, q}) :=
    (Set.toFinite ({c, p, q} : Set ℂ)).isClosed_convexHull ℝ
  have hfront : ∀ᵐ z : ℂ ∂volume, z ∉ frontier (convexHull ℝ {c, p, q}) := by
    rw [ae_iff]
    simpa only [not_not, ofPred_mem_eq] using
      (convex_convexHull ℝ ({c, p, q} : Set ℂ)).addHaar_frontier volume
  have hedge : ∀ᵐ z : ℂ ∂volume, z ∉ segment ℝ c p ∪ segment ℝ p q ∪ segment ℝ q c := by
    rw [ae_iff]
    simpa only [not_not, ofPred_mem_eq] using volume_triangle_edges c p q
  filter_upwards [hfront, hedge] with z hzfront hzedge
  have hztrace : z ∉ triangleCurve c p q '' uIcc 0 3 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3), image_triangleCurve] using hzedge
  rw [windingWeight_eq_of_notMem hztrace]
  by_cases hi : z ∈ interior (convexHull ℝ {c, p, q})
  · rw [Set.indicator_of_mem hi, mul_one]
    rcases lt_trichotomy (triangleDet c p q) 0 with hneg | hzero | hpos
    · rw [windingNumber_triangleCurve_eq_neg_one hneg hi, Real.sign_of_neg hneg]
      simp
    · rw [interior_convexHull_triangle_eq_empty hzero] at hi
      exact hi.elim
    · rw [windingNumber_triangleCurve_eq_one hpos hi, Real.sign_of_pos hpos]
      simp
  · rw [Set.indicator_of_notMem hi, mul_zero]
    have hout : z ∉ convexHull ℝ {c, p, q} := by
      intro hz
      exact hzfront (by rw [frontier, hclosed.closure_eq]; exact ⟨hz, hi⟩)
    rw [windingNumber_triangleCurve_eq_zero_of_notMem_convexHull hout, Complex.zero_re]

/-- A degenerate triangle has winding number zero at every point off its three edges. -/
theorem windingNumber_triangleCurve_eq_zero_of_degenerate {c p q z : ℂ}
    (hdet : triangleDet c p q = 0)
    (hz : z ∉ segment ℝ c p ∪ segment ℝ p q ∪ segment ℝ q c) :
    Contour.windingNumber (triangleCurve c p q) 0 3 z = 0 := by
  have hAC := absolutelyContinuousOnInterval_triangleCurve c p q
  have hAE : windingWeight (triangleCurve c p q) 0 3 =ᵐ[volume] fun _ ↦ (0 : ℝ) := by
    simpa only [hdet, Real.sign_zero, zero_mul] using windingWeight_triangleCurve_ae_eq c p q
  let U := (triangleCurve c p q '' uIcc 0 3)ᶜ
  have hU : IsOpen U :=
    (isCompact_uIcc.image_of_continuousOn hAC.continuousOn).isClosed.isOpen_compl
  have hcont : ContinuousOn (windingWeight (triangleCurve c p q) 0 3) U := by
    have hW : ContinuousOn (fun w ↦ (Contour.windingNumber (triangleCurve c p q) 0 3 w).re) U := by
      intro w hw
      exact (Complex.continuous_re.continuousAt.comp
        (Contour.continuousAt_windingNumber_of_avoidance hAC.continuousOn
        (fun t ht he ↦ hw ⟨t, ht, he⟩)
        (hAC.intervalIntegrable_inv_sub_mul_deriv hw))).continuousWithinAt
    exact hW.congr fun w hw ↦ windingWeight_eq_of_notMem hw
  have hzU : z ∈ U := by
    simpa only [U, mem_compl_iff, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3), image_triangleCurve]
      using hz
  have hzero := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hAE) hU hcont
    continuousOn_const hzU
  obtain ⟨n, hn⟩ := hAC.exists_int_windingNumber
    (by simp) hzU
  rw [windingWeight_eq_of_notMem hzU, hn, Complex.intCast_re] at hzero
  -- The real part of the integer winding number is its real coercion.
  change (n : ℝ) = 0 at hzero
  have hnzero : n = 0 := by exact_mod_cast hzero
  rw [hn, hnzero]
  norm_num

end TauCeti.Green
