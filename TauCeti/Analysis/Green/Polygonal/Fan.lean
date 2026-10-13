/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Polygonal.Index
public import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.PolygonalApproximation
import TauCeti.Analysis.Contour.Winding.Number.Segment.Bounds
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Trace
import TauCeti.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Basic.Complex.BigOperators
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.FiniteGluing

/-!
# Winding weights of polygonal triangle fans

The actual winding number of a raw polygonal curve is the sum of the windings of its finite
straight edges. Adding the two radial edges of each triangle leaves this sum unchanged for a
closed polygon. Triangle edges have planar area zero, so this gives the almost-everywhere signed
indicator identity, with no hypothesis bounding the winding number.
-/

public section

noncomputable section

open Set MeasureTheory Complex

namespace TauCeti.Green

/-- The winding number of an absolutely continuous raw polygonal curve is the sum of its
successive straight-edge winding numbers, on its given nonuniform subdivision. -/
theorem windingNumber_eq_sum_polygon_segments {γ : ℝ → ℂ} {a b : ℝ} {N : ℕ}
    {s : Fin (N + 1) → ℝ} (hs : StrictMono s) (ha : s 0 = a) (hb : s (Fin.last N) = b)
    (hsegments : ∀ i : Fin N, ∀ t ∈ Icc (s i.castSucc) (s i.succ),
      γ t = γ (s i.castSucc) + ((t - s i.castSucc) / (s i.succ - s i.castSucc)) •
        (γ (s i.succ) - γ (s i.castSucc)))
    {z : ℂ} (hz : z ∉ γ '' uIcc a b) :
    Contour.windingNumber γ a b z =
      ∑ i : Fin N, Contour.windingNumber
        (fun t : ℝ ↦ γ (s i.castSucc) + t • (γ (s i.succ) - γ (s i.castSucc))) 0 1 z := by
  have hγ := AbsolutelyContinuousOnInterval.of_affine_subdivision hs ha hb hsegments
  have hab : a ≤ b := by rw [← ha, ← hb]; exact hs.monotone (Fin.zero_le _)
  have hmem (i : Fin (N + 1)) : s i ∈ uIcc a b := by
    rw [uIcc_of_le hab, ← ha, ← hb]
    exact ⟨hs.monotone (Fin.zero_le _), hs.monotone (Fin.le_last _)⟩
  have hint := Contour.intervalIntegrable_inv_sub_mul_deriv_of_absolutelyContinuousOnInterval hγ hz
  let F : Fin (N + 1) → ℂ := fun i ↦
    (2 * (Real.pi : ℂ) * I)⁻¹ * ∫ t in a..s i, (γ t - z)⁻¹ * deriv γ t
  have hstep (i : Fin N) : Contour.windingNumber
      (fun t : ℝ ↦ γ (s i.castSucc) + t • (γ (s i.succ) - γ (s i.castSucc))) 0 1 z =
      F i.succ - F i.castSucc := by
    have hic : s i.castSucc < s i.succ := hs i.castSucc_lt_succ
    have hsub := uIcc_subset_uIcc (hmem i.castSucc) (hmem i.succ)
    have hcell : AbsolutelyContinuousOnInterval γ (s i.castSucc) (s i.succ) := hγ.mono hsub
    have hzcell : z ∉ γ '' uIcc (s i.castSucc) (s i.succ) :=
      fun h ↦ hz (image_mono hsub h)
    have hzedge : z ∉ segment ℝ (γ (s i.castSucc)) (γ (s i.succ)) := by
      rw [segment_eq_image']
      rintro ⟨t, ht, heq⟩
      let u := s i.castSucc + t * (s i.succ - s i.castSucc)
      have hu : u ∈ Icc (s i.castSucc) (s i.succ) := by
        dsimp [u]
        constructor <;> nlinarith [ht.1, ht.2]
      have hratio : (u - s i.castSucc) / (s i.succ - s i.castSucc) = t := by
        dsimp [u]
        rw [add_sub_cancel_left, mul_div_cancel_right₀ _ (sub_pos.mpr hic).ne']
      apply hzcell
      refine ⟨u, (uIcc_of_le hic.le).symm ▸ hu, ?_⟩
      rw [hsegments i u hu, hratio]
      exact heq
    have hw : Contour.windingNumber γ (s i.castSucc) (s i.succ) z =
        Contour.windingNumber (fun t : ℝ ↦ γ (s i.castSucc) +
          ((t - s i.castSucc) / (s i.succ - s i.castSucc)) •
            (γ (s i.succ) - γ (s i.castSucc))) (s i.castSucc) (s i.succ) z := by
      apply Contour.windingNumber_congr_curve
      intro t ht
      exact hsegments i t (by simpa only [uIcc_of_le hic.le] using uIoo_subset_uIcc_self ht)
    rw [← Contour.windingNumber_segment_interval hic hzedge, ← hw,
      Contour.windingNumber_eq_integral_of_absolutelyContinuousOnInterval hcell hzcell]
    dsimp [F]
    rw [← mul_sub]
    congr 1
    exact (intervalIntegral.integral_interval_sub_left
      (hint.mono_set (uIcc_subset_uIcc left_mem_uIcc (hmem i.succ)))
      (hint.mono_set (uIcc_subset_uIcc left_mem_uIcc (hmem i.castSucc)))).symm
  simp_rw [hstep]
  rw [Fin.sum_univ_succ_sub_castSucc]
  simp only [F, ha, hb, intervalIntegral.integral_same, mul_zero, sub_zero]
  exact Contour.windingNumber_eq_integral_of_absolutelyContinuousOnInterval hγ hz

/-- For a closed raw polygon, the actual winding weight is almost everywhere the sum of the
actual winding weights of the triangles in any fan. -/
theorem windingWeight_eq_sum_triangleCurve {γ : ℝ → ℂ} {a b : ℝ} {N : ℕ}
    {s : Fin (N + 1) → ℝ} (hs : StrictMono s) (ha : s 0 = a) (hb : s (Fin.last N) = b)
    (hsegments : ∀ i : Fin N, ∀ t ∈ Icc (s i.castSucc) (s i.succ),
      γ t = γ (s i.castSucc) + ((t - s i.castSucc) / (s i.succ - s i.castSucc)) •
        (γ (s i.succ) - γ (s i.castSucc)))
    (hclosed : γ a = γ b) (c : ℂ) :
    windingWeight γ a b =ᵐ[volume] fun z ↦
      ∑ i : Fin N, windingWeight (triangleCurve c (γ (s i.castSucc)) (γ (s i.succ))) 0 3 z := by
  have hγ := AbsolutelyContinuousOnInterval.of_affine_subdivision hs ha hb hsegments
  have htrace : ∀ᵐ z : ℂ ∂volume, z ∉ γ '' uIcc a b := by
    rw [ae_iff]
    simpa only [not_not, ofPred_mem_eq] using hγ.measure_image_uIcc_eq_zero volume
      (by norm_num [Complex.finrank_real_complex])
  have hfan : ∀ᵐ z : ℂ ∂volume, ∀ i : Fin N,
      z ∉ segment ℝ c (γ (s i.castSucc)) ∪ segment ℝ (γ (s i.castSucc)) (γ (s i.succ)) ∪
        segment ℝ (γ (s i.succ)) c := by
    apply ae_all_iff.mpr
    intro i
    rw [ae_iff]
    simpa only [not_not, ofPred_mem_eq] using
      volume_triangle_edges c (γ (s i.castSucc)) (γ (s i.succ))
  filter_upwards [htrace, hfan] with z hz hzi
  rw [windingWeight_eq_of_notMem hz]
  have htriangle (i : Fin N) :
      windingWeight (triangleCurve c (γ (s i.castSucc)) (γ (s i.succ))) 0 3 z =
        (Contour.windingNumber (fun t : ℝ ↦ c + t • (γ (s i.castSucc) - c)) 0 1 z +
          Contour.windingNumber (fun t : ℝ ↦ γ (s i.castSucc) +
            t • (γ (s i.succ) - γ (s i.castSucc))) 0 1 z -
          Contour.windingNumber (fun t : ℝ ↦ c + t • (γ (s i.succ) - c)) 0 1 z).re := by
    have hzi' : z ∉ triangleCurve c (γ (s i.castSucc)) (γ (s i.succ)) '' uIcc 0 3 := by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3), image_triangleCurve] using hzi i
    rw [windingWeight_eq_of_notMem hzi', windingNumber_triangleCurve_eq_sum (hzi i)]
    rw [Contour.windingNumber_segment_swap (p := c) (q := γ (s i.succ)) (z := z) (by
      rw [segment_symm]
      exact fun h ↦ hzi i (Or.inr h))]
    simp only [sub_eq_add_neg]
  simp_rw [htriangle]
  rw [← Complex.re_sum]
  have htelescope : (∑ i : Fin N,
      (Contour.windingNumber (fun t : ℝ ↦ c + t • (γ (s i.castSucc) - c)) 0 1 z +
        Contour.windingNumber (fun t : ℝ ↦ γ (s i.castSucc) +
          t • (γ (s i.succ) - γ (s i.castSucc))) 0 1 z -
        Contour.windingNumber (fun t : ℝ ↦ c + t • (γ (s i.succ) - c)) 0 1 z)) =
      ∑ i : Fin N, Contour.windingNumber
        (fun t : ℝ ↦ γ (s i.castSucc) + t • (γ (s i.succ) - γ (s i.castSucc))) 0 1 z := by
    let R : Fin (N + 1) → ℂ := fun i ↦
      Contour.windingNumber (fun t : ℝ ↦ c + t • (γ (s i) - c)) 0 1 z
    have hR : R (Fin.last N) = R 0 := by simp only [R, ha, hb, hclosed]
    have he (i : Fin N) : R i.castSucc +
        Contour.windingNumber (fun t : ℝ ↦ γ (s i.castSucc) +
          t • (γ (s i.succ) - γ (s i.castSucc))) 0 1 z - R i.succ =
        Contour.windingNumber (fun t : ℝ ↦ γ (s i.castSucc) +
          t • (γ (s i.succ) - γ (s i.castSucc))) 0 1 z + (R i.castSucc - R i.succ) := by ring
    change (∑ i : Fin N, (R i.castSucc + _ - R i.succ)) = _
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    have hdiff : (∑ i : Fin N, (R i.castSucc - R i.succ)) = 0 := by
      rw [Fin.sum_univ_castSucc_sub_succ, hR, sub_self]
    rw [hdiff, add_zero]
  rw [htelescope]
  exact congrArg Complex.re (windingNumber_eq_sum_polygon_segments hs ha hb hsegments hz)

/-- The winding weight of a closed raw polygon is almost everywhere the signed indicator sum
of the interiors of its fan triangles, including degenerate and overlapping triangles. -/
theorem windingWeight_eq_triangle_fan {γ : ℝ → ℂ} {a b : ℝ} {N : ℕ}
    {s : Fin (N + 1) → ℝ} (hs : StrictMono s) (ha : s 0 = a) (hb : s (Fin.last N) = b)
    (hsegments : ∀ i : Fin N, ∀ t ∈ Icc (s i.castSucc) (s i.succ),
      γ t = γ (s i.castSucc) + ((t - s i.castSucc) / (s i.succ - s i.castSucc)) •
        (γ (s i.succ) - γ (s i.castSucc)))
    (hclosed : γ a = γ b) (c : ℂ) :
    windingWeight γ a b =ᵐ[volume] fun z ↦ ∑ i : Fin N,
      Real.sign (triangleDet c (γ (s i.castSucc)) (γ (s i.succ))) *
        (interior (convexHull ℝ {c, γ (s i.castSucc), γ (s i.succ)})).indicator
          (fun _ : ℂ ↦ (1 : ℝ)) z := by
  apply (windingWeight_eq_sum_triangleCurve hs ha hb hsegments hclosed c).trans
  have h : ∀ᵐ z : ℂ ∂volume, ∀ i : Fin N,
      windingWeight (triangleCurve c (γ (s i.castSucc)) (γ (s i.succ))) 0 3 z =
        Real.sign (triangleDet c (γ (s i.castSucc)) (γ (s i.succ))) *
          (interior (convexHull ℝ {c, γ (s i.castSucc), γ (s i.succ)})).indicator
            (fun _ : ℂ ↦ (1 : ℝ)) z :=
    ae_all_iff.mpr fun i ↦ windingWeight_triangleCurve_ae_eq c (γ (s i.castSucc)) (γ (s i.succ))
  filter_upwards [h] with z hz
  exact Finset.sum_congr rfl fun i _ ↦ hz i

end TauCeti.Green
