/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Examples.Shoelace
import TauCeti.Analysis.Green.Polygonal.Fan
import Mathlib.Analysis.Convex.Combination

/-!
# A self-intersecting polygon

The closed polygon `(0,0) → (1,1) → (0,1) → (1,0) → (0,0)` crosses itself at `(1/2,1/2)`.
Its signed shoelace area is zero: the two lobes have opposite winding orientation.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green.Examples

/-- A raw four-edge self-intersecting polygon on the interval `[0,4]`. -/
def bowTieCurve (t : ℝ) : ℂ :=
  if t ≤ 1 then ⟨t, t⟩ else if t ≤ 2 then ⟨2 - t, 1⟩
    else if t ≤ 3 then ⟨t - 2, 3 - t⟩ else ⟨4 - t, 0⟩

/-- The two crossing parameters are distinct interior points with equal images. -/
theorem bowTieCurve_crossing :
    bowTieCurve (1 / 2) = bowTieCurve (5 / 2) ∧
      (1 / 2 : ℝ) ≠ 5 / 2 ∧ (1 / 2 : ℝ) ∈ Ioo 0 4 ∧ (5 / 2 : ℝ) ∈ Ioo 0 4 := by
  norm_num [bowTieCurve]

/-- The four affine edges are exactly the integer-node subdivision. -/
theorem bowTieCurve_subdivision (i : Fin 4) (t : ℝ)
    (ht : t ∈ Icc (i : ℝ) (i + 1 : ℝ)) :
    bowTieCurve t = bowTieCurve (i : ℝ) +
      (t - (i : ℝ)) • (bowTieCurve (i + 1 : ℝ) - bowTieCurve (i : ℝ)) := by
  fin_cases i <;> norm_num [bowTieCurve] at ht ⊢ <;>
    split_ifs <;> apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im] <;> linarith

/-- The crossing polygon is polygonal on `[0,4]`. -/
theorem isPolygonalOnInterval_bowTieCurve : IsPolygonalOnInterval bowTieCurve 0 4 := by
  refine ⟨4, by decide, (fun i ↦ (i : ℝ)), ?_, by norm_num, by norm_num, ?_⟩
  · intro i j hij
    -- Expose the underlying natural indices of the Fin-to-real coercions for exact_mod_cast.
    change (i.val : ℝ) < j.val
    exact_mod_cast hij
  · intro i t ht
    have h := bowTieCurve_subdivision i t (by simpa using ht)
    simpa using h

/-- The polygon is closed. -/
theorem bowTieCurve_closed : bowTieCurve 0 = bowTieCurve 4 := by
  norm_num [bowTieCurve]

private theorem bowTieCurve_avoids (y : ℝ) (hy : y = 3 / 4 ∨ y = 1 / 4) :
    (⟨1 / 2, y⟩ : ℂ) ∉ bowTieCurve '' uIcc 0 4 := by
  rintro ⟨t, _, heq⟩
  rcases hy with rfl | rfl
  all_goals
    unfold bowTieCurve at heq
    split_ifs at heq
    all_goals
      have hr := congrArg Complex.re heq
      have hi := congrArg Complex.im heq
      norm_num at *
      all_goals linarith

private theorem bowTieFan_avoids (y : ℝ) (hy : y = 3 / 4 ∨ y = 1 / 4) (i : Fin 4) :
    (⟨1 / 2, y⟩ : ℂ) ∉
      segment ℝ 0 (bowTieCurve (i.castSucc : ℝ)) ∪
        segment ℝ (bowTieCurve (i.castSucc : ℝ)) (bowTieCurve (i.succ : ℝ)) ∪
          segment ℝ (bowTieCurve (i.succ : ℝ)) 0 := by
  rcases hy with rfl | rfl
  all_goals
    fin_cases i <;> norm_num [bowTieCurve]
    all_goals
      refine ⟨⟨?_, ?_⟩, ?_⟩
      all_goals
        intro h
        rw [segment_eq_image'] at h
        obtain ⟨t, ht, heq⟩ := h
        have hr := congrArg Complex.re heq
        have hi := congrArg Complex.im heq
        norm_num [Complex.smul_re, Complex.smul_im, Complex.mul_re, Complex.mul_im]
          at *
        all_goals linarith

private theorem bowTie_index_eq_two_triangles {z : ℂ}
    (hz : z ∉ bowTieCurve '' uIcc 0 4)
    (hf : ∀ i : Fin 4, z ∉
      segment ℝ 0 (bowTieCurve (i.castSucc : ℝ)) ∪
        segment ℝ (bowTieCurve (i.castSucc : ℝ)) (bowTieCurve (i.succ : ℝ)) ∪
          segment ℝ (bowTieCurve (i.succ : ℝ)) 0) :
    Contour.windingNumber bowTieCurve 0 4 z =
      Contour.windingNumber (triangleCurve 0 (1 + Complex.I) Complex.I) 0 3 z +
        Contour.windingNumber (triangleCurve 0 Complex.I 1) 0 3 z := by
  have hs : StrictMono (fun i : Fin 5 ↦ (i : ℝ)) := by
    intro i j hij
    -- Expose the underlying natural indices of the Fin-to-real coercions for exact_mod_cast.
    change (i.val : ℝ) < j.val
    exact_mod_cast hij
  have hseg (i : Fin 4) (t : ℝ) (ht : t ∈ Icc (i.castSucc : ℝ) (i.succ : ℝ)) :
      bowTieCurve t = bowTieCurve (i.castSucc : ℝ) +
        ((t - (i.castSucc : ℝ)) / ((i.succ : ℝ) - (i.castSucc : ℝ))) •
          (bowTieCurve (i.succ : ℝ) - bowTieCurve (i.castSucc : ℝ)) := by
    simpa using bowTieCurve_subdivision i t (by simpa using ht)
  have h := windingNumber_eq_sum_triangleCurve (a := 0) (b := 4)
    hs (by norm_num) (by norm_num) hseg bowTieCurve_closed 0 hz hf
  have hv : (⟨1, 1⟩ : ℂ) = 1 + Complex.I := by apply Complex.ext <;> simp
  have hI : (⟨0, 1⟩ : ℂ) = Complex.I := by apply Complex.ext <;> simp
  have h1 : (⟨1, 0⟩ : ℂ) = 1 := by apply Complex.ext <;> simp
  have h0 : (⟨0, 0⟩ : ℂ) = 0 := rfl
  have hd₀ : Contour.windingNumber (triangleCurve 0 0 (1 + Complex.I)) 0 3 z = 0 := by
    apply windingNumber_triangleCurve_eq_zero_of_degenerate (by simp [triangleDet_def])
    simpa [bowTieCurve, hv, hI, h1, h0] using hf 0
  have hd₃ : Contour.windingNumber (triangleCurve 0 1 0) 0 3 z = 0 := by
    apply windingNumber_triangleCurve_eq_zero_of_degenerate (by simp [triangleDet_def])
    have hh := hf 3
    norm_num [bowTieCurve, hv, hI, h1, h0] at hh ⊢
    tauto
  norm_num [Fin.sum_univ_succ, bowTieCurve, hv, hI, h1, h0, hd₀, hd₃] at h
  exact h

private theorem bowTie_upper_interior :
    (⟨1 / 2, 3 / 4⟩ : ℂ) ∈ interior (convexHull ℝ {0, 1 + Complex.I, Complex.I}) := by
  let S : Set ℂ := {z | 0 < z.re ∧ z.re < z.im ∧ z.im < 1}
  have hS : IsOpen S :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const))
  have hsub : S ⊆ convexHull ℝ {0, 1 + Complex.I, Complex.I} := by
    intro z hz
    exact mem_convexHull_of_exists_fintype
      ![1 - z.im, z.re, z.im - z.re] ![0, 1 + Complex.I, Complex.I]
      (by intro i; fin_cases i <;> simp <;> linarith [hz.1, hz.2.1, hz.2.2])
      (by simp [Fin.sum_univ_succ])
      (by intro i; fin_cases i <;> simp)
      (by apply Complex.ext <;> simp [Fin.sum_univ_succ])
  have hpoint : (⟨1 / 2, 3 / 4⟩ : ℂ) ∈ S := by norm_num [S]
  exact interior_mono hsub (hS.interior_eq.symm ▸ hpoint)

private theorem bowTie_lower_interior :
    (⟨1 / 2, 1 / 4⟩ : ℂ) ∈ interior (convexHull ℝ {0, Complex.I, 1}) := by
  let S : Set ℂ := {z | 0 < z.re ∧ 0 < z.im ∧ z.re + z.im < 1}
  have hS : IsOpen S :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt (Complex.continuous_re.add Complex.continuous_im) continuous_const))
  have hsub : S ⊆ convexHull ℝ {0, Complex.I, 1} := by
    intro z hz
    exact mem_convexHull_of_exists_fintype
      ![1 - z.re - z.im, z.im, z.re] ![0, Complex.I, 1]
      (by intro i; fin_cases i <;> simp <;> linarith [hz.1, hz.2.1, hz.2.2])
      (by simp [Fin.sum_univ_succ]; ring)
      (by intro i; fin_cases i <;> simp)
      (by apply Complex.ext <;> simp [Fin.sum_univ_succ])
  have hpoint : (⟨1 / 2, 1 / 4⟩ : ℂ) ∈ S := by norm_num [S]
  exact interior_mono hsub (hS.interior_eq.symm ▸ hpoint)

/-- The upper lobe has positive index one at an explicit interior point. -/
theorem windingNumber_bowTieCurve_upper :
    Contour.windingNumber bowTieCurve 0 4 ⟨1 / 2, 3 / 4⟩ = 1 := by
  rw [bowTie_index_eq_two_triangles (bowTieCurve_avoids _ (Or.inl rfl))
    (bowTieFan_avoids _ (Or.inl rfl)),
    windingNumber_triangleCurve_eq_one (by norm_num [triangleDet_def]) bowTie_upper_interior]
  have hout : (⟨1 / 2, 3 / 4⟩ : ℂ) ∉ convexHull ℝ {0, Complex.I, 1} := by
    have hsub : convexHull ℝ {0, Complex.I, 1} ⊆ {z : ℂ | z.re + z.im ≤ 1} :=
      convexHull_min (by simp [insert_subset_iff])
        ((convex_Iic (1 : ℝ)).linear_preimage (Complex.reCLM + Complex.imCLM).toLinearMap)
    intro hz
    have h := hsub hz
    norm_num at h
  rw [windingNumber_triangleCurve_eq_zero_of_notMem_convexHull hout, add_zero]

/-- The lower lobe has negative index one at an explicit interior point. -/
theorem windingNumber_bowTieCurve_lower :
    Contour.windingNumber bowTieCurve 0 4 ⟨1 / 2, 1 / 4⟩ = -1 := by
  rw [bowTie_index_eq_two_triangles (bowTieCurve_avoids _ (Or.inr rfl))
    (bowTieFan_avoids _ (Or.inr rfl)),
    windingNumber_triangleCurve_eq_neg_one (by norm_num [triangleDet_def]) bowTie_lower_interior]
  have hout : (⟨1 / 2, 1 / 4⟩ : ℂ) ∉ convexHull ℝ {0, 1 + Complex.I, Complex.I} := by
    have hsub : convexHull ℝ {0, 1 + Complex.I, Complex.I} ⊆ {z : ℂ | z.re - z.im ≤ 0} :=
      convexHull_min (by simp [insert_subset_iff])
        ((convex_Iic (0 : ℝ)).linear_preimage (Complex.reCLM - Complex.imCLM).toLinearMap)
    intro hz
    have h := hsub hz
    norm_num at h
  rw [windingNumber_triangleCurve_eq_zero_of_notMem_convexHull hout, zero_add]

/-- The winding-weighted area of the crossing polygon is an ordinary integrable function. -/
theorem integrable_windingWeight_bowTieCurve : Integrable (windingWeight bowTieCurve 0 4) :=
  isPolygonalOnInterval_bowTieCurve.absolutelyContinuousOnInterval.integrable_windingWeight
    bowTieCurve_closed

/-- The signed circulation of this self-intersecting polygon is zero. -/
theorem integral_circulationFun_area_bowTieCurve :
    (∫ t in (0 : ℝ)..4, circulationFun areaP areaQ bowTieCurve t) = 0 := by
  have hs : StrictMono (fun i : Fin 5 ↦ (i : ℝ)) := by
    intro i j hij
    -- Expose the underlying natural indices of the Fin-to-real coercions for exact_mod_cast.
    change (i.val : ℝ) < j.val
    exact_mod_cast hij
  have hseg (i : Fin 4) (t : ℝ) (ht : t ∈ Icc (i.castSucc : ℝ) (i.succ : ℝ)) :
      bowTieCurve t = bowTieCurve (i.castSucc : ℝ) +
        ((t - (i.castSucc : ℝ)) / ((i.succ : ℝ) - (i.castSucc : ℝ))) •
          (bowTieCurve (i.succ : ℝ) - bowTieCurve (i.castSucc : ℝ)) := by
    simpa using bowTieCurve_subdivision i t (by simpa using ht)
  have h := integral_circulationFun_area_shoelace (a := 0) (b := 4)
    hs (by norm_num) (by norm_num)
    hseg
  norm_num [Fin.sum_univ_succ, bowTieCurve] at h
  exact h

/-- Green's theorem counts the two lobes with opposite signs, yielding zero weighted area. -/
theorem integral_windingWeight_bowTieCurve :
    (∫ z : ℂ, windingWeight bowTieCurve 0 4 z) = 0 := by
  have h := (green_polygonal isPolygonalOnInterval_bowTieCurve bowTieCurve_closed
    (contDiff_areaP (n := 1)) (contDiff_areaQ (n := 1))).2.2
  simp only [curl_area, mul_one] at h
  rw [← h, integral_circulationFun_area_bowTieCurve]

end TauCeti.Green.Examples
