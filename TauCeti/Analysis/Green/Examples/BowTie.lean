/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Examples.Shoelace

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
  refine IsPolygonalOnInterval.of_subdivision (N := 4) (s := fun i ↦ (i : ℝ))
    (by decide) ?_ (by norm_num) (by norm_num) ?_
  · intro i j hij
    change (i.val : ℝ) < j.val
    exact_mod_cast hij
  · intro i t ht
    have h := bowTieCurve_subdivision i t (by simpa using ht)
    simpa using h

/-- The polygon is closed. -/
theorem bowTieCurve_closed : bowTieCurve 0 = bowTieCurve 4 := by
  norm_num [bowTieCurve]

/-- The signed circulation of this self-intersecting polygon is zero. -/
theorem integral_circulationFun_area_bowTieCurve :
    (∫ t in (0 : ℝ)..4, circulationFun areaP areaQ bowTieCurve t) = 0 := by
  have hs : StrictMono (fun i : Fin 5 ↦ (i : ℝ)) := by
    intro i j hij
    change (i.val : ℝ) < j.val
    exact_mod_cast hij
  have hseg (i : Fin 4) (t : ℝ) (ht : t ∈ Icc (i.castSucc : ℝ) (i.succ : ℝ)) :
      bowTieCurve t = bowTieCurve (i.castSucc : ℝ) +
        ((t - (i.castSucc : ℝ)) / ((i.succ : ℝ) - (i.castSucc : ℝ))) •
          (bowTieCurve (i.succ : ℝ) - bowTieCurve (i.castSucc : ℝ)) := by
    simpa using bowTieCurve_subdivision i t (by simpa using ht)
  have h := integral_circulationFun_area_shoelace hs (by norm_num) (by norm_num)
    hseg isPolygonalOnInterval_bowTieCurve.absolutelyContinuousOnInterval
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
