/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import Mathlib.Topology.MetricSpace.Holder
import TauCeti.Analysis.Normed.Module.RCLike.Basic
import TauCeti.Topology.MetricSpace.Holder

/-!
# Hölder bounds for Wirtinger derivatives

Taking the complex-linear or complex-antilinear part of a real derivative does not increase
its Hölder constant. The estimates compare derivatives at two points directly and do not
require a second derivative.
-/

public section

open Complex
open scoped NNReal

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {g : V → W}

/-- The difference of two Wirtinger derivatives is bounded by the difference of the real
derivatives, with the same operator bound. -/
theorem norm_wirtingerDeriv_apply_sub_le (x y : V) (v : V) :
    ‖wirtingerDeriv g x v - wirtingerDeriv g y v‖ ≤
      ‖fderiv ℝ g x - fderiv ℝ g y‖ * ‖v‖ := by
  rw [wirtingerDeriv_apply, wirtingerDeriv_apply]
  have heq : (2 : ℂ)⁻¹ • (fderiv ℝ g x v - I • fderiv ℝ g x (I • v)) -
      (2 : ℂ)⁻¹ • (fderiv ℝ g y v - I • fderiv ℝ g y (I • v)) =
      (2 : ℂ)⁻¹ • ((fderiv ℝ g x - fderiv ℝ g y) v +
        -(I • (fderiv ℝ g x - fderiv ℝ g y) (I • v))) := by
    simp only [sub_apply]
    module
  rw [heq]
  apply norm_two_inv_smul_add_le ((fderiv ℝ g x - fderiv ℝ g y).le_opNorm v)
  simpa only [norm_neg, norm_smul, norm_I, one_mul] using
    (fderiv ℝ g x - fderiv ℝ g y).le_opNorm (I • v)

/-- A `K`-Hölder bound for the real derivative gives a `K ‖v‖`-Hölder bound for its
complex-linear part applied to `v`. -/
theorem _root_.HolderOnWith.wirtingerDeriv_apply {K α : ℝ≥0} {s : Set V}
    (h : HolderOnWith K α (fderiv ℝ g) s) (v : V) :
    HolderOnWith (K * ‖v‖₊) α (fun x ↦ wirtingerDeriv g x v) s := by
  apply HolderOnWith.of_dist_le
  intro x hx y hy
  rw [dist_eq_norm]
  calc
    _ ≤ ‖fderiv ℝ g x - fderiv ℝ g y‖ * ‖v‖ := norm_wirtingerDeriv_apply_sub_le x y v
    _ ≤ (K * dist x y ^ (α : ℝ)) * ‖v‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
      simpa only [dist_eq_norm] using h.dist_le hx hy
    _ = _ := by push_cast; ring

end TauCeti
