/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Sard.EqualDimension
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Critical values of radial Lipschitz functions

A radial Lipschitz real-valued function on a real inner product space
has a null set of critical values. Here critical points include nondifferentiability points,
since the Fréchet derivative is totalized to zero. This is stronger than the nullity of the
critical part of almost every level surface: outside a null set of values, the whole level
contains no critical points at all.

The radial profile has a one-dimensional null set of critical values. Away from the origin,
a vanishing ambient derivative forces the profile derivative to vanish. The origin contributes
only one additional value. This is the critical-value input for identifying the derivative of
a radial distribution function with its reciprocal-gradient level integral.

## References

* Bianchi–Gardner–Gronchi–Kiderlen, *The Pólya–Szegő inequality for smoothing rearrangements*,
  arXiv:2206.09833, proof of Theorem 5.8 (the one-dimensional radial critical-value argument).
-/

public section

open Function MeasureTheory Module Set
open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Away from the origin, a vanishing totalized derivative of a radial function forces its
one-dimensional profile derivative to vanish. The profile need not be differentiable. -/
theorem deriv_eq_zero_of_fderiv_comp_norm_eq_zero {v : ℝ → ℝ} {x : E} (hx : x ≠ 0)
    (hcrit : fderiv ℝ (fun y : E ↦ v ‖y‖) x = 0) : deriv v ‖x‖ = 0 := by
  have : Nontrivial E := ⟨⟨x, 0, hx⟩⟩
  by_contra hv
  have hvd := differentiableAt_of_deriv_ne_zero hv
  have hn : DifferentiableAt ℝ (fun y : E ↦ ‖y‖) x := differentiableAt_id.norm ℝ hx
  have hd := hvd.hasDerivAt.comp_hasFDerivAt x hn.hasFDerivAt
  have hz : deriv v ‖x‖ • fderiv ℝ (fun y : E ↦ ‖y‖) x = 0 := hd.fderiv.symm.trans hcrit
  have hnorm := norm_fderiv_norm hn
  rw [(smul_eq_zero.mp hz).resolve_left hv, norm_zero] at hnorm
  exact zero_ne_one hnorm

/-- The critical values of a radial function with a Lipschitz profile form a Lebesgue-null set.
No finite-dimensionality or measurability structure on the ambient inner product space is needed;
the exceptional value at the origin is included. -/
theorem _root_.LipschitzWith.volume_image_setOf_fderiv_comp_norm_eq_zero
    {K : ℝ≥0} {v : ℝ → ℝ} (hv : LipschitzWith K v) :
    volume ((fun x : E ↦ v ‖x‖) ''
      {x | fderiv ℝ (fun y : E ↦ v ‖y‖) x = 0}) = 0 := by
  apply measure_mono_null (t := {v 0} ∪ v '' {r | deriv v r = 0})
  · rintro _ ⟨x, hx, rfl⟩
    rcases eq_or_ne x 0 with rfl | hx0
    · exact Or.inl (by simp)
    · exact Or.inr ⟨‖x‖, deriv_eq_zero_of_fderiv_comp_norm_eq_zero hx0 hx, rfl⟩
  · exact measure_union_null (measure_singleton _) hv.volume_image_setOf_deriv_eq_zero

/-- A radial Lipschitz real-valued function has a Lebesgue-null set of totalized critical values.
Radiality is expressed by equality at points with the same norm. The ambient inner product space
may be infinite-dimensional. -/
theorem _root_.LipschitzWith.volume_image_setOf_fderiv_eq_zero_of_norm_eq
    {K : ℝ≥0} {h : E → ℝ} (hh : LipschitzWith K h)
    (hrad : ∀ x y, ‖x‖ = ‖y‖ → h x = h y) :
    volume (h '' {x | fderiv ℝ h x = 0}) = 0 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · apply measure_mono_null (t := {h 0})
    · rintro _ ⟨x, _, rfl⟩
      simp [Subsingleton.elim x 0]
    · exact measure_singleton _
  obtain ⟨e, he⟩ := exists_norm_eq E zero_le_one
  let v : ℝ → ℝ := fun r ↦ h (r • e)
  have hv : LipschitzWith K v := by
    simpa only [Function.comp_def, LinearIsometry.toSpanSingleton_apply, mul_one] using
      hh.comp (LinearIsometry.toSpanSingleton ℝ E he).isometry.lipschitzWith
  have hrep : h = fun x ↦ v ‖x‖ := by
    funext x
    exact hrad x (‖x‖ • e) (by simp [norm_smul, he])
  rw [hrep]
  exact hv.volume_image_setOf_fderiv_comp_norm_eq_zero

end TauCeti
