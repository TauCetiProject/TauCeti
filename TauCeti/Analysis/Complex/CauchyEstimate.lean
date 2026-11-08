/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Cauchy's estimate for Taylor terms and divided differences

Cauchy's estimate bounds the `n`-th derivative of a holomorphic function at the centre of a disc by
its size on the boundary circle, so the terms of its Taylor series decay geometrically inside the
disc. The divided difference `dslope f a` of a holomorphic function is again holomorphic, and on the
boundary circle it is controlled by `f` and the distance from `a` to that circle, so the same
estimate applies to it.

## Main results

* `TauCeti.norm_taylor_term_le_of_forall_mem_sphere_norm_le`: Cauchy's estimate for the `n`-th term
  of a Taylor series.
* `Differentiable.dslope`, `DiffContOnCl.dslope`: divided differences stay holomorphic.
* `TauCeti.norm_dslope_le_of_mem_sphere`: the bound for a divided difference on the boundary circle.
-/

public section

open Metric Nat

/-- The divided difference of an entire function is entire. -/
theorem Differentiable.dslope {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} (hf : Differentiable ℂ f) (a : ℂ) :
    Differentiable ℂ (_root_.dslope f a) :=
  differentiableOn_univ.mp
    ((Complex.differentiableOn_dslope Filter.univ_mem).mpr hf.differentiableOn)

/-- The divided difference at a point `a` interior to `s` of a function that is differentiable on
`s` and continuous on its closure is again differentiable on `s` and continuous on its closure. -/
theorem DiffContOnCl.dslope {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} {s : Set ℂ} {a : ℂ} (hf : DiffContOnCl ℂ f s)
    (hs : s ∈ nhds a) : DiffContOnCl ℂ (_root_.dslope f a) s :=
  ⟨(Complex.differentiableOn_dslope hs).mpr hf.differentiableOn,
    (continuousOn_dslope (Filter.mem_of_superset hs subset_closure)).mpr
      ⟨hf.continuousOn, hf.differentiableOn.differentiableAt hs⟩⟩

namespace TauCeti

/-- **Cauchy's estimate for Taylor terms.** If `f` is differentiable on the open disc of radius `R`
about `c`, continuous on its closure and bounded by `C` on the boundary circle, then the `n`-th term
of its Taylor series at `c`, evaluated at `z`, has norm at most `C (|z - c| / R) ^ n`. -/
theorem norm_taylor_term_le_of_forall_mem_sphere_norm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {c : ℂ} {R C : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hC : ∀ w ∈ sphere c R, ‖f w‖ ≤ C) (z : ℂ) (n : ℕ) :
    ‖(n ! : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c‖ ≤ C * (‖z - c‖ / R) ^ n := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hf hC
  have hfac : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  simp only [norm_smul, norm_inv, Complex.norm_natCast, norm_pow]
  calc (n ! : ℝ)⁻¹ * (‖z - c‖ ^ n * ‖iteratedDeriv n f c‖)
      ≤ (n ! : ℝ)⁻¹ * (‖z - c‖ ^ n * (n ! * C / R ^ n)) := by gcongr
    _ = C * (‖z - c‖ / R) ^ n := by
      rw [div_pow]
      field_simp

/-- On the circle of radius `R` about `c`, the divided difference of `f` at a point `a` inside the
disc is at most twice a bound for `f` on the closed disc, over the distance from `a` to the
circle. -/
theorem norm_dslope_le_of_mem_sphere {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {a c z : 𝕜} {R B : ℝ}
    (ha : a ∈ ball c R) (hB : ∀ w ∈ closedBall c R, ‖f w‖ ≤ B) (hz : z ∈ sphere c R) :
    ‖dslope f a z‖ ≤ 2 * B / (R - ‖a - c‖) := by
  have hd : 0 < R - ‖a - c‖ := sub_pos.mpr (mem_ball_iff_norm.mp ha)
  have hza : R - ‖a - c‖ ≤ ‖z - a‖ := by
    have h := norm_sub_norm_le (z - c) (a - c)
    rwa [sub_sub_sub_cancel_right, mem_sphere_iff_norm.mp hz] at h
  have hne : z ≠ a := fun h ↦ by
    rw [h, sub_self, norm_zero] at hza
    linarith
  have hfz := hB z (sphere_subset_closedBall hz)
  have hfa := hB a (ball_subset_closedBall ha)
  rw [dslope_of_ne f hne, slope_def_module, norm_smul, norm_inv, div_eq_inv_mul]
  have hfsub : ‖f z - f a‖ ≤ 2 * B := by linarith [norm_sub_le (f z) (f a)]
  gcongr

end TauCeti
