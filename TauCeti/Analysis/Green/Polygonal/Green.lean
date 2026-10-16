/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.DegenerateTriangle
public import TauCeti.Analysis.Green.Polygonal.Fan
public import TauCeti.Analysis.Green.Polygonal.Circulation
import Mathlib.Analysis.Convex.Measure
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Gluing

/-!
# Winding-weighted Green for polygonal cycles

Every finite polygonal subdivision gives a triangle fan about any chosen center. Actual
triangle Green identities sum because the radial path generators cancel. The signed indicator
formula for the winding weight identifies this sum with the winding-weighted area integral.
Both integrabilities are proved, including for self-intersections, repeated vertices, and
degenerate or overlapping fan triangles. The fields are `C¹` on the whole plane.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green

/-- Circulation around a closed raw polygon on a nonuniform subdivision equals its
winding-weighted curl integral. Both the boundary integrand and weighted curl are integrable. -/
theorem green_polygon_of_subdivision {γ : ℝ → ℂ} {a b : ℝ} {N : ℕ}
    {s : Fin (N + 1) → ℝ} (hs : StrictMono s) (ha : s 0 = a) (hb : s (Fin.last N) = b)
    (hsegments : ∀ i : Fin N, ∀ t ∈ Icc (s i.castSucc) (s i.succ),
      γ t = γ (s i.castSucc) + ((t - s i.castSucc) / (s i.succ - s i.castSucc)) •
        (γ (s i.succ) - γ (s i.castSucc)))
    (hclosed : γ a = γ b)
    {P Q : ℂ → ℝ} (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q) :
    IntervalIntegrable (circulationFun P Q γ) volume a b ∧
      Integrable (fun z ↦ windingWeight γ a b z * curl P Q z) ∧
      (∫ t in a..b, circulationFun P Q γ t) =
        ∫ z : ℂ, windingWeight γ a b z * curl P Q z := by
  have hγ := AbsolutelyContinuousOnInterval.of_affine_subdivision hs ha hb hsegments
  let c : ℂ := 0
  let v : Fin (N + 1) → ℂ := γ ∘ s
  let T : Fin N → Set ℂ := fun i ↦ convexHull ℝ {c, v i.castSucc, v i.succ}
  let σ : Fin N → ℝ := fun i ↦ Real.sign (triangleDet c (v i.castSucc) (v i.succ))
  let F : Fin N → ℂ → ℝ := fun i z ↦ σ i * (interior (T i)).indicator (curl P Q) z
  have htri (i : Fin N) := green_triangle c (v i.castSucc) (v i.succ)
    isOpen_univ (subset_univ _) hP.contDiffOn hQ.contDiffOn
  have hF (i : Fin N) : Integrable (F i) :=
    ((htri i).1.mono_set interior_subset).integrable_indicator isOpen_interior.measurableSet
      |>.const_mul (σ i)
  have hFan := windingWeight_eq_triangle_fan hs ha hb hsegments hclosed c
  have hweight : (fun z ↦ windingWeight γ a b z * curl P Q z) =ᵐ[volume]
      fun z ↦ ∑ i : Fin N, F i z := by
    filter_upwards [hFan] with z hz
    rw [hz, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    -- The fan theorem displays the determinant and vertices explicitly; σ, T and F
    -- abbreviate that same summand in the local integrability argument.
    change σ i * (interior (T i)).indicator (fun _ : ℂ ↦ (1 : ℝ)) z * curl P Q z = F i z
    by_cases hzi : z ∈ interior (T i)
    · simp only [F, indicator_of_mem hzi, mul_one]
    · simp only [F, indicator_of_notMem hzi, mul_zero, zero_mul]
  have harea : Integrable (fun z ↦ windingWeight γ a b z * curl P Q z) :=
    (integrable_finsetSum _ (fun i _ ↦ hF i)).congr hweight.symm
  have hFI (i : Fin N) : (∫ z : ℂ, F i z) =
      Finsupp.linearCombination ℤ (fun η : Arc ↦ curveIntegral (oneForm P Q) η.2.2)
        (BoundaryChain.triangle c (v i.castSucc) (v i.succ)) := by
    have hi : interior (T i) =ᵐ[volume] T i :=
      interior_ae_eq_of_null_frontier ((convex_convexHull ℝ _).addHaar_frontier volume)
    simp only [F, integral_const_mul, integral_indicator isOpen_interior.measurableSet]
    rw [setIntegral_congr_set hi]
    simpa only [BoundaryChain.triangle_def, map_sub, map_add, BoundaryChain.ofPath_def,
      Finsupp.linearCombination_single, one_smul] using (htri i).2.symm
  refine ⟨hγ.intervalIntegrable_circulationFun hP.continuous.continuousOn
    hQ.continuous.continuousOn, harea, ?_⟩
  rw [integral_congr_ae hweight, integral_finsetSum _ (fun i _ ↦ hF i)]
  simp_rw [hFI]
  rw [← map_sum, BoundaryChain.sum_triangle_of_closed v (by
    simp only [v, Function.comp_apply, ha, hb, hclosed]) c]
  exact integral_circulationFun_eq_polygon hs ha hb hsegments
    hP.continuous.continuousOn hQ.continuous.continuousOn

/-- Winding-weighted Green for a closed raw polygonal curve and globally `C¹` fields.
The boundary integrand and winding-weighted curl are integrable, and their integrals agree. -/
theorem green_polygonal {γ : ℝ → ℂ} {a b : ℝ}
    (hpoly : IsPolygonalOnInterval γ a b)
    (hclosed : γ a = γ b) {P Q : ℂ → ℝ} (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q) :
    IntervalIntegrable (circulationFun P Q γ) volume a b ∧
      Integrable (fun z ↦ windingWeight γ a b z * curl P Q z) ∧
      (∫ t in a..b, circulationFun P Q γ t) =
        ∫ z : ℂ, windingWeight γ a b z * curl P Q z := by
  obtain ⟨N, _, s, hs, ha, hb, hsegments⟩ := hpoly
  exact green_polygon_of_subdivision hs ha hb hsegments hclosed hP hQ

end TauCeti.Green
