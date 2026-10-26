/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Polygonal.Index
public import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.PolygonalApproximation
import TauCeti.Analysis.Contour.Winding.Number.Segment.Bounds
import TauCeti.Analysis.Contour.Winding.Number.Partition
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Trace
import TauCeti.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Basic.Complex.BigOperators
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Gluing

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
  have hpv (i : Fin N) : Contour.CauchyPVExistsAt γ (s i.castSucc) (s i.succ)
      (fun w ↦ (w - z)⁻¹) z := by
    have hsub := uIcc_subset_uIcc (hmem i.castSucc) (hmem i.succ)
    have hcell := hγ.mono hsub
    have hzcell : z ∉ γ '' uIcc (s i.castSucc) (s i.succ) :=
      fun h ↦ hz (image_mono hsub h)
    exact Contour.cauchyPVExistsAt_of_avoidance hcell.continuousOn
      (fun t ht he ↦ hzcell ⟨t, ht, he⟩) (hcell.intervalIntegrable_inv_sub_mul_deriv hzcell)
  let t : ℕ → ℝ := fun k ↦ s (Fin.ofNat (N + 1) k)
  have ht (i : Fin (N + 1)) : t i = s i := by simp [t]
  have hcast (i : Fin N) : t i = s i.castSucc := ht i.castSucc
  have hsucc (i : Fin N) : t (i + 1) = s i.succ := ht i.succ
  have ht0 : t 0 = a := (ht 0).trans ha
  have htN : t N = b := (ht (Fin.last N)).trans hb
  have hsum := Contour.windingNumber_eq_sum_range (n := N) (t := t) (by
    intro k hk
    simpa only [← hcast, ← hsucc, Fin.val_mk] using hpv ⟨k, hk⟩)
  rw [← Fin.sum_univ_eq_sum_range] at hsum
  rw [ht0, htN] at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hcast i, hsucc i]
  have hic : s i.castSucc < s i.succ := hs i.castSucc_lt_succ
  have hsub := uIcc_subset_uIcc (hmem i.castSucc) (hmem i.succ)
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
  rw [← Contour.windingNumber_segment_interval hic hzedge, ← hw]

/-- Away from the polygon trace and all fan edges, the actual complex winding number of a
closed raw polygon is the sum of the actual triangle winding numbers. -/
theorem windingNumber_eq_sum_triangleCurve {γ : ℝ → ℂ} {a b : ℝ} {N : ℕ}
    {s : Fin (N + 1) → ℝ} (hs : StrictMono s) (ha : s 0 = a) (hb : s (Fin.last N) = b)
    (hsegments : ∀ i : Fin N, ∀ t ∈ Icc (s i.castSucc) (s i.succ),
      γ t = γ (s i.castSucc) + ((t - s i.castSucc) / (s i.succ - s i.castSucc)) •
        (γ (s i.succ) - γ (s i.castSucc)))
    (hclosed : γ a = γ b) (c : ℂ) {z : ℂ} (hz : z ∉ γ '' uIcc a b)
    (hzi : ∀ i : Fin N,
      z ∉ segment ℝ c (γ (s i.castSucc)) ∪ segment ℝ (γ (s i.castSucc)) (γ (s i.succ)) ∪
        segment ℝ (γ (s i.succ)) c) :
    Contour.windingNumber γ a b z =
      ∑ i : Fin N, Contour.windingNumber
        (triangleCurve c (γ (s i.castSucc)) (γ (s i.succ))) 0 3 z := by
  let R : Fin (N + 1) → ℂ := fun i ↦
    Contour.windingNumber (fun t : ℝ ↦ c + t • (γ (s i) - c)) 0 1 z
  have htriangle (i : Fin N) :
      Contour.windingNumber (triangleCurve c (γ (s i.castSucc)) (γ (s i.succ))) 0 3 z =
        Contour.windingNumber (fun t : ℝ ↦ γ (s i.castSucc) +
          t • (γ (s i.succ) - γ (s i.castSucc))) 0 1 z + (R i.castSucc - R i.succ) := by
    rw [windingNumber_triangleCurve_eq_sum (hzi i),
      Contour.windingNumber_segment_swap (p := c) (q := γ (s i.succ)) (z := z) (by
        rw [segment_symm]
        exact fun h ↦ hzi i (Or.inr h))]
    dsimp [R]
    ring
  simp_rw [htriangle]
  have htel : ∑ i : Fin N, (R i.castSucc - R i.succ) = R 0 - R (Fin.last N) := by
    exact Fin.sum_univ_castSucc_sub_succ R
  rw [Finset.sum_add_distrib, htel]
  have hR : R (Fin.last N) = R 0 := by simp only [R, ha, hb, hclosed]
  rw [hR, sub_self, add_zero]
  exact windingNumber_eq_sum_polygon_segments hs ha hb hsegments hz

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
    simpa only [not_not, ofPred_mem_eq] using hγ.addHaar_image_uIcc_eq_zero volume
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
        (Contour.windingNumber (triangleCurve c (γ (s i.castSucc)) (γ (s i.succ))) 0 3 z).re := by
    apply windingWeight_eq_of_notMem
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3), image_triangleCurve] using hzi i
  simp_rw [htriangle]
  rw [← Complex.re_sum]
  exact congrArg Complex.re (windingNumber_eq_sum_triangleCurve hs ha hb hsegments hclosed c hz hzi)

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
