/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Strong

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

/-- The average objective gap above a common lower bound controls one quarter of the
modulus at the distance between the two points. -/
theorem UniformConvexOn.div_four_le_sub (hf : UniformConvexOn s φ f)
    {a : ℝ} (hlower : ∀ z ∈ s, a ≤ f z) (hx : x ∈ s) (hy : y ∈ s) :
    φ ‖x - y‖ / 4 ≤ (f x + f y) / 2 - a := by
  have ht : (1 / 2 : ℝ) ∈ Icc 0 1 := by norm_num
  exact TauCeti.div_four_le_sub_of_le_midpoint_sub
    ((hlower _ (hf.1.lineMap_mem hx hy ht)).trans (hf.map_lineMap_le hx hy ht))
