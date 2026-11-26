/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteBeta.Kernel
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Examples: the side of crossing matters on the diagonal

On the diagonal `v₁ = v₂` the integrand of the incomplete beta kernel is `z⁻¹`, and the defining
path from `conj ξ` to `ξ` crosses the real axis in `(0, 1)`, at `1/2`; the kernel is
`arg ξ / π`, which is `s` at `ξ = ξ(s, t)` (`TauCeti.incompleteBetaKernel_self`). Crossing in
`(-∞, 0)` instead, through `-1`, gives `(2πi)⁻¹ ∫ z⁻¹ dz = arg (-ξ) / π`, which is `-(1 - s)` at
`ξ = ξ(s, t)`: the two values differ by `1`, the winding number of the closed path about `0`. So
the definition must fix the side of crossing.
-/

public section

open Complex Set
open scoped Real ComplexConjugate

namespace TauCeti.IncompleteBetaDiagonalExample

/-- Crossing the real axis in `(-∞, 0)`, through `-1`, the integral of `z⁻¹` from `conj ξ` to `ξ`
is `2πi · arg (-ξ) / π`, for `ξ` off `[0, ∞)`. The primitive is `log (-z)`. -/
theorem curveIntegral_inv_through_neg_one {ξ : ℂ} (hξ : -ξ ∈ slitPlane) :
    (2 * π * I)⁻¹ * ((∫ᶜ z in Path.segment (conj ξ) (-1 : ℂ),
        ContinuousLinearMap.toSpanSingleton ℂ z⁻¹) +
      ∫ᶜ z in Path.segment (-1 : ℂ) ξ, ContinuousLinearMap.toSpanSingleton ℂ z⁻¹) =
      ((arg (-ξ) / π : ℝ) : ℂ) := by
  have h0 {z : ℂ} (hz : -z ∈ slitPlane) : z ≠ 0 := fun h => slitPlane_ne_zero hz (by simp [h])
  have hint := curveIntegral_conj_neg_one_add_eq_sub
    (F := fun z => log (-z)) (f := fun z => z⁻¹) hξ (fun z hz => ?_)
    (continuousOn_inv₀.mono fun z hz => h0 hz)
  · rw [hint]
    have e : log (-conj ξ) = conj (log (-ξ)) := by
      rw [← map_neg, log_conj _ (mem_slitPlane_iff_arg.1 hξ).1]
    rw [e, sub_conj, log_im]
    push_cast
    field_simp
  · have := h0 hz
    convert (hasDerivAt_neg z).clog hz using 1
    field_simp

/-- At the complex slope, crossing in `(-∞, 0)` gives `-(1 - s)`. -/
theorem curveIntegral_inv_through_neg_one_complexSlope {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hst : s + t < 1) :
    (2 * π * I)⁻¹ * ((∫ᶜ z in Path.segment (conj (complexSlope s t)) (-1 : ℂ),
        ContinuousLinearMap.toSpanSingleton ℂ z⁻¹) +
      ∫ᶜ z in Path.segment (-1 : ℂ) (complexSlope s t), ContinuousLinearMap.toSpanSingleton ℂ z⁻¹) =
      ((-(1 - s) : ℝ) : ℂ) := by
  have hξ := im_complexSlope_pos hs ht hst
  rw [curveIntegral_inv_through_neg_one (mem_slitPlane_iff.2 (Or.inr (by simpa using hξ.ne'))),
    arg_neg_eq_arg_sub_pi_of_im_pos hξ, arg_complexSlope hs ht hst]
  congr 1
  field_simp
  ring

/-- **The side of crossing matters.** At the complex slope, the diagonal kernel `s`, defined by
crossing in `(0, 1)`, differs from the value `-(1 - s)` obtained by crossing in `(-∞, 0)`. -/
theorem incompleteBetaKernel_self_ne_curveIntegral_inv_through_neg_one {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) (hst : s + t < 1) (v : ℤ × ℤ) :
    incompleteBetaKernel (complexSlope s t) v v ≠
      (2 * π * I)⁻¹ * ((∫ᶜ z in Path.segment (conj (complexSlope s t)) (-1 : ℂ),
        ContinuousLinearMap.toSpanSingleton ℂ z⁻¹) +
      ∫ᶜ z in Path.segment (-1 : ℂ) (complexSlope s t),
        ContinuousLinearMap.toSpanSingleton ℂ z⁻¹) := by
  have hξ := im_complexSlope_pos hs ht hst
  rw [incompleteBetaKernel_self (mem_slitPlane_iff.2 (Or.inr hξ.ne')) v,
    arg_complexSlope hs ht hst, curveIntegral_inv_through_neg_one_complexSlope hs ht hst]
  intro h
  have h' : s = -(1 - s) := by
    have := congrArg re h
    simp only [div_ofReal_re, ofReal_re] at this
    rw [← this]
    field_simp
  linarith

end TauCeti.IncompleteBetaDiagonalExample
