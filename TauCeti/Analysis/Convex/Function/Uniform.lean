/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Strong
public import TauCeti.Analysis.Convex.Along

/-!
# Affine-segment bounds for uniformly convex functions

The affine-segment inequality gives a lower bound in terms of the modulus at
a constrained minimizer, and controls the midpoint gap above a lower bound.
For strong convexity the same interpolation inequality yields metric convexity
along the segment.
-/

public section

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : Set E} {f : E → ℝ} {φ : ℝ → ℝ} {μ : ℝ} {x y : E}

/-- A uniformly convex function satisfies the modulus interpolation bound along an
affine segment contained in its domain. -/
theorem UniformConvexOn.lineMap_le (hf : UniformConvexOn s φ f) (hx : x ∈ s) (hy : y ∈ s)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    f (AffineMap.lineMap x y t) ≤ (1 - t) * f x + t * f y - t * (1 - t) * φ ‖x - y‖ := by
  rw [AffineMap.lineMap_apply_module, mul_comm t (1 - t)]
  simpa only [smul_eq_mul] using hf.2 hx hy (sub_nonneg.2 ht.2) ht.1 (sub_add_cancel 1 t)

/-- The quadratic interpolation bound for a strongly convex function along an affine segment. -/
theorem StrongConvexOn.lineMap_le (hf : StrongConvexOn s μ f) (hx : x ∈ s) (hy : y ∈ s)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    f (AffineMap.lineMap x y t) ≤
      (1 - t) * f x + t * f y - μ / 2 * t * (1 - t) * dist x y ^ 2 := by
  have hu : UniformConvexOn s (fun r ↦ μ / 2 * r ^ 2) f := hf
  rw [dist_eq_norm]
  convert hu.lineMap_le hx hy ht using 1
  ring

/-- The real-to-extended-real embedding of a strongly convex function is convex along
the affine segment between any two points in its domain, with the same modulus. -/
theorem StrongConvexOn.convexAlong_lineMap (hf : StrongConvexOn s μ f) (hx : x ∈ s) (hy : y ∈ s) :
    TauCeti.ConvexAlong μ (fun z ↦ (f z : EReal)) (AffineMap.lineMap x y) := by
  rw [TauCeti.convexAlong_def]
  intro t ht
  simp only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
  exact_mod_cast hf.lineMap_le hx hy ht

/-- At a constrained minimizer, the objective increases by at least the uniform modulus
evaluated at the distance to any other feasible point. -/
theorem UniformConvexOn.add_le_of_isMinOn (hf : UniformConvexOn s φ f) (hx : x ∈ s)
    (hmin : IsMinOn f s x) (hy : y ∈ s) :
    f x + φ ‖x - y‖ ≤ f y := by
  refine TauCeti.add_le_of_le_affine_sub fun t ht ↦ ?_
  exact ((isMinOn_iff.mp hmin) _ (hf.1.lineMap_mem hx hy (Ioo_subset_Icc_self ht))).trans
    (hf.lineMap_le hx hy (Ioo_subset_Icc_self ht))

/-- The average objective gap above a common lower bound controls one quarter of the
modulus at the distance between the two points. -/
theorem UniformConvexOn.div_four_le_sub (hf : UniformConvexOn s φ f)
    {a : ℝ} (hlower : ∀ z ∈ s, a ≤ f z) (hx : x ∈ s) (hy : y ∈ s) :
    φ ‖x - y‖ / 4 ≤ (f x + f y) / 2 - a := by
  have ht : (1 / 2 : ℝ) ∈ Icc 0 1 := by norm_num
  exact TauCeti.div_four_le_sub_of_le_midpoint
    ((hlower _ (hf.1.lineMap_mem hx hy ht)).trans (hf.lineMap_le hx hy ht))
