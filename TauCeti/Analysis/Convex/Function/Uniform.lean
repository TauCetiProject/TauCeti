/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Strong

import Mathlib.Analysis.Normed.Affine.AddTorsor
import TauCeti.Algebra.Order.Field.Basic

/-!
# Affine-segment bounds for uniformly convex functions

The affine-segment inequality gives a lower bound in terms of the modulus at
a constrained minimizer, and controls the midpoint gap above a lower bound.
-/

public section

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : Set E} {f : E → ℝ} {φ : ℝ → ℝ} {μ : ℝ} {x y : E}

/-- A uniformly convex function satisfies the modulus interpolation bound along an
affine segment contained in its domain. -/
theorem UniformConvexOn.map_lineMap_le (hf : UniformConvexOn s φ f) (hx : x ∈ s) (hy : y ∈ s)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    f (AffineMap.lineMap x y t) ≤ (1 - t) * f x + t * f y - t * (1 - t) * φ ‖x - y‖ := by
  rw [AffineMap.lineMap_apply_module, mul_comm t (1 - t)]
  simpa only [smul_eq_mul] using hf.2 hx hy (sub_nonneg.2 ht.2) ht.1 (sub_add_cancel 1 t)

/-- At a constrained minimizer, the objective gap is bounded below by the uniform modulus
evaluated at the distance to any other feasible point. -/
theorem UniformConvexOn.add_le_of_isMinOn (hf : UniformConvexOn s φ f) (hx : x ∈ s)
    (hmin : IsMinOn f s x) (hy : y ∈ s) :
    f x + φ ‖x - y‖ ≤ f y := by
  refine TauCeti.add_le_of_le_affine_sub fun t ht ↦ ?_
  exact ((isMinOn_iff.mp hmin) _ (hf.1.lineMap_mem hx hy (Ioo_subset_Icc_self ht))).trans
    (hf.map_lineMap_le hx hy (Ioo_subset_Icc_self ht))

/-- At a constrained minimizer `x`, the objective gap `f y - f x` for any feasible `y` is at least
`μ / 2 * ‖x - y‖ ^ 2`. This gives quadratic growth when `0 < μ`. -/
theorem StrongConvexOn.mul_norm_sub_sq_le_sub_of_isMinOn (hf : StrongConvexOn s μ f)
    (hx : x ∈ s) (hmin : IsMinOn f s x) (hy : y ∈ s) :
    μ / 2 * ‖x - y‖ ^ 2 ≤ f y - f x :=
  le_sub_iff_add_le'.2 (UniformConvexOn.add_le_of_isMinOn hf hx hmin hy)

/-- A lower bound at the midpoint gives an upper bound on one quarter of the modulus
at the distance between the endpoints. -/
theorem UniformConvexOn.div_four_le_sub (hf : UniformConvexOn s φ f)
    {a : ℝ} (hlower : a ≤ f (AffineMap.lineMap x y (1 / 2 : ℝ))) (hx : x ∈ s) (hy : y ∈ s) :
    φ ‖x - y‖ / 4 ≤ (f x + f y) / 2 - a := by
  have ht : (1 / 2 : ℝ) ∈ Icc 0 1 := by norm_num
  linarith [hlower.trans (hf.map_lineMap_le hx hy ht)]

/-- If two feasible points are at distance at least `ε > 0`, their maximum objective gap
above a common lower bound controls a quarter of the modulus at radius `ε`.
The argument uses a subsegment of length `ε` and needs no monotonicity of the modulus. -/
theorem UniformConvexOn.div_four_le_max_sub (hf : UniformConvexOn s φ f)
    {a ε : ℝ} (hlower : ∀ z ∈ s, a ≤ f z) (hx : x ∈ s) (hy : y ∈ s)
    (hφ : 0 ≤ φ ‖x - y‖) (hε : 0 < ε) (hd : ε ≤ dist x y) :
    φ ε / 4 ≤ max (f x) (f y) - a := by
  have hdpos : 0 < dist x y := hε.trans_le hd
  let t := ε / dist x y
  have ht : t ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hε.le hdpos.le, (div_le_one hdpos).2 hd⟩
  let z := AffineMap.lineMap x y t
  have hz : z ∈ s := hf.1.lineMap_mem hx hy ht
  have hnorm : ‖x - z‖ = ε := by
    rw [← dist_eq_norm, dist_left_lineMap, Real.norm_of_nonneg ht.1]
    exact div_mul_cancel₀ ε hdpos.ne'
  have hpen := mul_nonneg (mul_nonneg ht.1 (sub_nonneg.2 ht.2)) hφ
  have hcombo := Convex.combo_le_max (f x) (f y) (sub_nonneg.2 ht.2) ht.1 (sub_add_cancel 1 t)
  have hzle : f z ≤ max (f x) (f y) :=
    (hf.map_lineMap_le hx hy ht).trans <|
      (sub_le_self _ hpen).trans (by simpa only [smul_eq_mul] using hcombo)
  have hmid := hf.div_four_le_sub
    (hlower _ (hf.1.lineMap_mem hx hz (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1))) hx hz
  rw [hnorm] at hmid
  linarith [le_max_left (f x) (f y)]
