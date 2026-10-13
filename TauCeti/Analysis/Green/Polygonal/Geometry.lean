/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Supporting halfplanes of a planar triangle

The interior of a convex triangle lies strictly on the side of each edge containing the third
vertex. The determinant records the orientation of the ordered triple.
-/

public section

open Complex Set

namespace TauCeti.Green

/-- The real determinant of the two edges based at the first vertex. -/
def triangleDet (c p q : ℂ) : ℝ :=
  (p - c).re * (q - c).im - (p - c).im * (q - c).re

/-- The oriented determinant in real and imaginary coordinates. -/
theorem triangleDet_def (c p q : ℂ) : triangleDet c p q =
    (p - c).re * (q - c).im - (p - c).im * (q - c).re := (rfl)

/-- The imaginary height relative to an edge is its oriented determinant divided by norm squared. -/
theorem im_div_sub_eq_triangleDet (p q z : ℂ) :
    ((z - p) / (q - p)).im = triangleDet p q z / Complex.normSq (q - p) := by
  simp only [Complex.div_im, triangleDet]
  ring

/-- Cyclically relabelling vertices preserves the oriented determinant. -/
theorem triangleDet_cyclic (c p q : ℂ) : triangleDet p q c = triangleDet c p q := by
  simp only [triangleDet, Complex.sub_re, Complex.sub_im]
  ring

/-- Interchanging two vertices negates the oriented determinant. -/
theorem triangleDet_swap (c p q : ℂ) : triangleDet c q p = -triangleDet c p q := by
  simp only [triangleDet]
  ring

/-- A positive determinant ensures that the first edge is nondegenerate. -/
theorem sub_ne_zero_of_triangleDet_pos {p q r : ℂ} (h : 0 < triangleDet p q r) : q - p ≠ 0 := by
  intro heq
  simp only [triangleDet, heq, Complex.zero_re, Complex.zero_im, zero_mul, sub_zero] at h
  exact h.false

/-- A positive oriented determinant places the third vertex strictly left of the first edge. -/
theorem im_div_sub_pos_of_triangleDet_pos {p q r : ℂ} (h : 0 < triangleDet p q r) :
    0 < ((r - p) / (q - p)).im := by
  rw [im_div_sub_eq_triangleDet]
  exact div_pos h (Complex.normSq_pos.mpr (sub_ne_zero_of_triangleDet_pos h))

/-- An interior point lies strictly on the side of an edge containing the third vertex. -/
theorem im_div_pos_of_mem_interior_convexHull_triangle {p q r z : ℂ} (hpq : q - p ≠ 0)
    (hr : 0 ≤ ((r - p) / (q - p)).im)
    (hz : z ∈ interior (convexHull ℝ {p, q, r})) : 0 < ((z - p) / (q - p)).im := by
  let L : ℂ →L[ℝ] ℝ := Complex.imCLM.comp ((ContinuousLinearMap.mul ℝ ℂ).flip (q - p)⁻¹)
  have hL (w : ℂ) : L w = (w / (q - p)).im := by
    simp [L, div_eq_mul_inv]
    ring
  have hsurj : Function.Surjective L := by
    intro x
    refine ⟨((x : ℂ) * I) * (q - p), ?_⟩
    rw [hL, mul_div_cancel_right₀ _ hpq]
    simp
  let F := fun w : ℂ ↦ L (w - p)
  have hconv : Convex ℝ {w : ℂ | 0 ≤ F w} := by
    intro x hx y hy a b ha hb hab
    change 0 ≤ L (a • x + b • y - p)
    have he : a • x + b • y - p = a • (x - p) + b • (y - p) := by
      rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hab, one_smul]
    rw [he, map_add, map_smul, map_smul]
    exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  have hsubset : convexHull ℝ {p, q, r} ⊆ {w : ℂ | 0 ≤ F w} := by
    apply convexHull_min _ hconv
    intro w hw
    simp only [mem_insert_iff, mem_singleton_iff] at hw
    rcases hw with hw | hw | hw
    · subst w
      simp [F]
    · subst w
      change 0 ≤ L (q - p)
      rw [hL, div_self hpq]
      simp
    · subst w
      change 0 ≤ L (r - p)
      rwa [hL]
  have hopen : IsOpenMap F := (L.isOpenMap hsurj).comp (isOpenMap_sub_right p)
  have h := hopen.interior_preimage_subset_preimage_interior (s := Ici (0 : ℝ))
    (interior_mono hsubset hz)
  simpa only [interior_Ici, mem_preimage, mem_Ioi, F, hL] using h

private theorem im_div_combo (p q x y : ℂ) (a b : ℝ) (hab : a + b = 1) :
    ((a • x + b • y - p) / (q - p)).im =
      a * ((x - p) / (q - p)).im + b * ((y - p) / (q - p)).im := by
  have he : a • x + b • y - p = a • (x - p) + b • (y - p) := by
    rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hab, one_smul]
  rw [he, add_div, smul_div_assoc, smul_div_assoc, Complex.add_im,
    Complex.smul_im, Complex.smul_im]
  rfl

private theorem interior_triangle_eq_empty_of_height_eq_zero {c p q : ℂ}
    (hpc : p - c ≠ 0) (hq : ((q - c) / (p - c)).im = 0) :
    interior (convexHull ℝ {c, p, q}) = ∅ := by
  have hconv : Convex ℝ {z : ℂ | ((z - c) / (p - c)).im = 0} := by
    intro x hx y hy a b _ _ hab
    rw [mem_ofPred_eq, im_div_combo c p x y a b hab, hx, hy]
    simp
  have hsub : convexHull ℝ {c, p, q} ⊆ {z : ℂ | ((z - c) / (p - c)).im = 0} := by
    apply convexHull_min _ hconv
    intro z hz
    simp only [mem_insert_iff, mem_singleton_iff] at hz
    rcases hz with hz | hz | hz
    · subst z; simp
    · subst z; simp [hpc]
    · subst z; exact hq
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hpos := im_div_pos_of_mem_interior_convexHull_triangle hpc hq.ge hz
  exact hpos.ne' (hsub (interior_subset hz))

/-- A degenerate planar triangle has empty interior. -/
theorem interior_convexHull_triangle_eq_empty {c p q : ℂ} (hdet : triangleDet c p q = 0) :
    interior (convexHull ℝ {c, p, q}) = ∅ := by
  by_cases hpc : p - c = 0
  · have hp : p = c := sub_eq_zero.mp hpc
    subst p
    by_cases hqc : q - c = 0
    · have hq : q = c := sub_eq_zero.mp hqc
      subst q
      simp
    · have hset : ({c, q, c} : Set ℂ) = {c, c, q} := by ext; simp [or_comm]
      exact hset ▸ interior_triangle_eq_empty_of_height_eq_zero hqc (by simp)
  · apply interior_triangle_eq_empty_of_height_eq_zero hpc
    rw [im_div_sub_eq_triangleDet, hdet, zero_div]

/-- A degenerate planar triangle has area zero. -/
theorem volume_convexHull_triangle_eq_zero {c p q : ℂ} (hdet : triangleDet c p q = 0) :
    MeasureTheory.volume (convexHull ℝ {c, p, q}) = 0 := by
  have hclosed := (Set.toFinite ({c, p, q} : Set ℂ)).isClosed_convexHull ℝ
  have h := (convex_convexHull ℝ ({c, p, q} : Set ℂ)).addHaar_frontier MeasureTheory.volume
  rw [frontier, hclosed.closure_eq, interior_convexHull_triangle_eq_empty hdet, sdiff_empty] at h
  exact h

end TauCeti.Green
