/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Boundary.Function
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.Analysis.Complex.RadialUniqueness
import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley

/-!
# Uniqueness for boundary functions of bounded holomorphic functions on the half-plane

If the boundary function `F*` of a bounded holomorphic function `F` on the upper half-plane `ℂ₊`
vanishes on a set of positive measure, then `F` vanishes on `ℂ₊`
(`TauCeti.eqOn_zero_of_upperHalfPlaneBoundaryFun_eq_zero`); more generally, if `F* = c` on a set of
positive measure then `F = c` (`TauCeti.eqOn_const_of_upperHalfPlaneBoundaryFun_eq`).

The proof transports the F. and M. Riesz uniqueness theorem on the disc,
`TauCeti.eqOn_const_ball_of_tendsto_circleMap`, through the Cayley transform. The inverse Cayley
transform `w ↦ i (1 + w) / (1 - w)` maps the radius of the unit disc ending at
`ζ = (x - i) / (x + i)` to an arc ending at `x`, inside every cone at `x` near `x`
(`TauCeti.tendsto_nontangentialFilter_I_mul_one_add_div_one_sub`): along it
`|Re z - x| = |x| (1 - r) / (1 + r) · Im z`. So the radial limits of `F` transported to the disc
are the nontangential limits of `F`. The point `ζ` is `e^{iθ}` for `θ = π + 2 arctan x`
(`TauCeti.exp_pi_add_two_mul_arctan_mul_I`), and `θ ↦ tan ((θ - π) / 2)` is differentiable on
`(0, 2π)`, so these angles form a set of positive measure when the points `x` do.
-/

public section

noncomputable section

open Complex MeasureTheory Filter Metric Set Topology
open scoped Real
open UpperHalfPlane (upperHalfPlaneSet)

namespace TauCeti

/-- The boundary point `(x - i) / (x + i)` of the Cayley transform is `e^{iθ}` for
`θ = π + 2 arctan x`. -/
theorem exp_pi_add_two_mul_arctan_mul_I (x : ℝ) :
    exp ((π + 2 * Real.arctan x : ℝ) * I) = ((x : ℂ) - I) / ((x : ℂ) + I) := by
  have hxI : (x : ℂ) + I ≠ 0 := add_I_ne_zero_of_im_nonneg (by simp)
  have hs : (0 : ℝ) < √(1 + x ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hsq : ((√(1 + x ^ 2) : ℝ) : ℂ) ^ 2 = 1 + (x : ℂ) ^ 2 := by
    rw [← ofReal_pow, Real.sq_sqrt (by positivity)]
    push_cast
    ring
  have hs' : ((√(1 + x ^ 2) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hs.ne'
  rw [show ((π + 2 * Real.arctan x : ℝ) : ℂ) * I =
      π * I + ((Real.arctan x : ℂ) * I + (Real.arctan x : ℂ) * I) by push_cast; ring,
    exp_add, exp_add, exp_pi_mul_I, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_arctan,
    Real.sin_arctan, eq_div_iff hxI]
  push_cast
  field_simp
  rw [hsq]
  linear_combination (-2 * (x : ℂ) - (x : ℂ) ^ 3 - (x : ℂ) ^ 2 * I) * I_sq

/-- The inverse Cayley transform of a point `r ζ` on the radius ending at `ζ = (x - i) / (x + i)`,
in closed form. -/
private theorem I_mul_one_add_div_one_sub_eq (x : ℝ) {r : ℝ} (hr0 : -1 < r) (hr1 : r < 1) :
    I * (1 + r * (((x : ℂ) - I) / ((x : ℂ) + I))) / (1 - r * (((x : ℂ) - I) / ((x : ℂ) + I))) =
      ((1 + r) * x * I - (1 - r) : ℂ) / ((1 - r) * x + (1 + r) * I) := by
  have hxI : (x : ℂ) + I ≠ 0 := add_I_ne_zero_of_im_nonneg (by simp)
  have hq : ((1 - r) * x : ℂ) + (1 + r) * I ≠ 0 := by
    intro h
    have := congrArg im h
    simp only [add_im, mul_im, sub_re, one_re, ofReal_re, sub_im, one_im, ofReal_im, mul_zero,
      add_zero, I_im, mul_one, add_re, I_re, zero_im, zero_mul, zero_add, sub_zero] at this
    have : ((1 + r : ℂ)).re = 0 := by simpa using this
    simp at this
    linarith
  have hrζ : (1 : ℂ) - r * (((x : ℂ) - I) / ((x : ℂ) + I)) ≠ 0 := by
    intro h
    have h' : ‖(r : ℂ) * (((x : ℂ) - I) / ((x : ℂ) + I))‖ = 1 := by
      rw [← sub_eq_zero.1 h, norm_one]
    rw [norm_mul, norm_div, norm_sub_I_div_norm_add_I_ofReal, mul_one, norm_real,
      Real.norm_eq_abs] at h'
    exact (abs_lt.2 ⟨hr0, hr1⟩).ne h'
  rw [div_eq_div_iff hrζ hq]
  field_simp
  linear_combination (I * (1 - (r : ℂ) ^ 2) + x * (1 - r) ^ 2) * I_sq

/-- Along the radius ending at `ζ = (x - i) / (x + i)`, the inverse Cayley transform
`z = i (1 + r ζ) / (1 - r ζ)` lies in `ℂ₊` and satisfies `Re z - x = -x (1 - r)/(1 + r) Im z`. -/
theorem im_pos_and_re_sub_eq_of_mem_Ioo (x : ℝ) {r : ℝ} (hr0 : -1 < r) (hr1 : r < 1) :
    0 < (I * (1 + r * (((x : ℂ) - I) / ((x : ℂ) + I))) /
        (1 - r * (((x : ℂ) - I) / ((x : ℂ) + I)))).im ∧
      (I * (1 + r * (((x : ℂ) - I) / ((x : ℂ) + I))) /
        (1 - r * (((x : ℂ) - I) / ((x : ℂ) + I)))).re - x =
      -(x * ((1 - r) / (1 + r))) * (I * (1 + r * (((x : ℂ) - I) / ((x : ℂ) + I))) /
        (1 - r * (((x : ℂ) - I) / ((x : ℂ) + I)))).im := by
  rw [I_mul_one_add_div_one_sub_eq x hr0 hr1]
  set N : ℝ := (1 - r) ^ 2 * x ^ 2 + (1 + r) ^ 2
  have hN : 0 < N := by nlinarith [sq_nonneg ((1 - r) * x)]
  have hnq : normSq (((1 - r) * x : ℂ) + (1 + r) * I) = N := by
    rw [normSq_apply]
    simp only [add_re, mul_re, mul_im, add_im, sub_re, sub_im, ofReal_re, ofReal_im, one_re,
      one_im, I_re, I_im, N]
    ring
  rw [div_re, div_im, hnq]
  simp only [sub_re, add_re, mul_re, mul_im, add_im, sub_im, ofReal_re, ofReal_im, one_re,
    one_im, I_re, I_im]
  refine ⟨?_, ?_⟩
  · have : 0 < (1 - r ^ 2) * (1 + x ^ 2) / N :=
      div_pos (mul_pos (by nlinarith) (by positivity)) hN
    convert this using 1
    field_simp
    ring
  · have : 1 + r ≠ 0 := by linarith
    field_simp
    ring

/-- **Radii of the disc end nontangentially.** The inverse Cayley transform `w ↦ i (1 + w)/(1 - w)`
maps the radius `r ↦ r ζ` of the unit disc ending at `ζ = (x - i) / (x + i)` to a curve tending to
`x` inside the cone of any aperture `α > 0` at `x`: along it
`|Re z - x| = |x| (1 - r)/(1 + r) Im z`. -/
theorem tendsto_nontangentialFilter_I_mul_one_add_div_one_sub (x : ℝ) {α : ℝ} (hα : 0 < α) :
    Tendsto (fun r : ℝ ↦ I * (1 + r * (((x : ℂ) - I) / ((x : ℂ) + I))) /
        (1 - r * (((x : ℂ) - I) / ((x : ℂ) + I))))
      (𝓝[<] 1) (nontangentialFilter α x) := by
  set ζ : ℂ := ((x : ℂ) - I) / ((x : ℂ) + I) with hζ
  have hxI : (x : ℂ) + I ≠ 0 := add_I_ne_zero_of_im_nonneg (by simp)
  have hζ1 : (1 : ℂ) - ζ ≠ 0 := by
    rw [hζ, one_sub_sub_I_div_add_I hxI]
    exact div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) hxI
  rw [nontangentialFilter_def]
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · -- the curve tends to `x`
    have hc : ContinuousAt (fun r : ℝ ↦ I * (1 + r * ζ) / (1 - r * ζ)) 1 := by
      refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
      simpa using hζ1
    have h1 : I * (1 + ((1 : ℝ) : ℂ) * ζ) / (1 - ((1 : ℝ) : ℂ) * ζ) = x := by
      simpa [hζ] using I_mul_one_add_sub_I_div_add_I_div_one_sub hxI
    rw [← h1]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  · -- and lies in the cone for `r` close to `1`
    have hsmall : ∀ᶠ r : ℝ in 𝓝[<] 1, |x| * ((1 - r) / (1 + r)) < α := by
      have : Tendsto (fun r : ℝ ↦ |x| * ((1 - r) / (1 + r))) (𝓝 1)
          (𝓝 (|x| * ((1 - 1) / (1 + 1)))) :=
        tendsto_const_nhds.mul ((tendsto_const_nhds.sub tendsto_id).div
          (tendsto_const_nhds.add tendsto_id) (by norm_num))
      rw [sub_self, zero_div, mul_zero] at this
      exact nhdsWithin_le_nhds (this.eventually (gt_mem_nhds hα))
    filter_upwards [hsmall, Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr hr01
    obtain ⟨hpos, heq⟩ := im_pos_and_re_sub_eq_of_mem_Ioo x (by linarith [hr01.1]) hr01.2
    refine mem_nontangentialCone.2 ⟨hpos, ?_, ENNReal.ofReal_lt_top⟩
    have hq : (0 : ℝ) < (1 - r) / (1 + r) := div_pos (by linarith [hr01.2]) (by linarith [hr01.1])
    rw [heq, abs_mul, abs_neg, abs_mul, abs_of_pos hpos, abs_of_pos hq]
    exact mul_lt_mul_of_pos_right hr hpos

/-- **Uniqueness for boundary functions.** If `F` is holomorphic and bounded on `ℂ₊` and its
boundary function `F*` equals `c` almost everywhere on a set `A` of positive measure, then `F` is
the constant `c` on `ℂ₊`. -/
theorem eqOn_const_of_upperHalfPlaneBoundaryFun_eq {F : ℂ → ℂ} {S : ℝ} {A : Set ℝ} {c : ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (hS : ∀ z ∈ upperHalfPlaneSet, ‖F z‖ ≤ S)
    (hA : volume A ≠ 0) (hFA : ∀ᵐ x, x ∈ A → upperHalfPlaneBoundaryFun F x = c) :
    EqOn F (fun _ ↦ c) upperHalfPlaneSet := by
  -- the good boundary points of `A`
  set A' := {x ∈ A | ∀ α : ℝ, Tendsto F (nontangentialFilter α x) (𝓝 c)}
  have hA' : volume A' ≠ 0 := by
    have hgood : ∀ᵐ x, x ∈ A → x ∈ A' := by
      filter_upwards [hFA, ae_tendsto_nontangentialFilter_upperHalfPlaneBoundaryFun hF hS]
        with x hx hlim hxA
      exact ⟨hxA, fun α ↦ hx hxA ▸ hlim α⟩
    intro h0
    refine hA (measure_mono_null (fun x hx ↦ ?_) (measure_union_null h0 (ae_iff.1 hgood)))
    by_cases hxA' : x ∈ A'
    · exact Or.inl hxA'
    · exact Or.inr fun h ↦ hxA' (h hx)
  -- the corresponding angles
  set θ : ℝ → ℝ := fun x ↦ π + 2 * Real.arctan x
  have hE : volume (θ '' A') ≠ 0 := by
    intro h0
    have hsub : A' ⊆ (fun t ↦ Real.tan ((t - π) / 2)) '' (θ '' A') :=
      fun x hx ↦ ⟨θ x, mem_image_of_mem θ hx, by simp [θ]⟩
    have hdiff : DifferentiableOn ℝ (fun t ↦ Real.tan ((t - π) / 2)) (θ '' A') := by
      rintro _ ⟨y, -, rfl⟩
      refine (Real.differentiableAt_tan.2 ?_).comp _ (by fun_prop) |>.differentiableWithinAt
      simpa [θ] using (Real.cos_arctan_pos y).ne'
    exact hA' (measure_mono_null hsub
      (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff h0))
  -- the transported function on the disc
  set g : ℂ → ℂ := fun w ↦ F (I * (1 + w) / (1 - w))
  have hmaps := bijOn_I_mul_one_add_div_one_sub_ball.mapsTo
  have hg : DifferentiableOn ℂ g (ball 0 1) := by
    refine hF.comp (fun w hw ↦ ?_) hmaps
    have hw1 : (1 : ℂ) - w ≠ 0 := by
      rintro h
      rw [← sub_eq_zero.1 h] at hw
      simp at hw
    exact ((differentiableAt_const _).mul ((differentiableAt_const _).add differentiableAt_id)).div
      ((differentiableAt_const _).sub differentiableAt_id) hw1 |>.differentiableWithinAt
  have hgS : ∀ w ∈ ball (0 : ℂ) 1, ‖g w‖ ≤ S := fun w hw ↦ hS _ (hmaps hw)
  have hlim : ∀ t ∈ θ '' A', Tendsto (fun r ↦ g (circleMap 0 r t)) (𝓝[<] 1) (𝓝 c) := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [g, circleMap_zero, θ, exp_pi_add_two_mul_arctan_mul_I]
    exact (hx.2 1).comp (tendsto_nontangentialFilter_I_mul_one_add_div_one_sub x one_pos)
  have hgc := eqOn_const_ball_of_tendsto_circleMap hg hgS hE hlim
  intro z hz
  have hzI : z + I ≠ 0 := add_I_ne_zero_of_im_nonneg (le_of_lt hz)
  have := hgc (bijOn_sub_I_div_add_I_upperHalfPlaneSet.mapsTo hz)
  simpa [g, I_mul_one_add_sub_I_div_add_I_div_one_sub hzI] using this

/-- **Uniqueness for boundary functions** (roadmap form). If `F` is holomorphic and bounded on
`ℂ₊` and its boundary function `F*` vanishes almost everywhere on a set of positive measure, then
`F ≡ 0` on `ℂ₊`. -/
theorem eqOn_zero_of_upperHalfPlaneBoundaryFun_eq_zero {F : ℂ → ℂ} {S : ℝ} {A : Set ℝ}
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (hS : ∀ z ∈ upperHalfPlaneSet, ‖F z‖ ≤ S)
    (hA : volume A ≠ 0) (hFA : ∀ᵐ x, x ∈ A → upperHalfPlaneBoundaryFun F x = 0) :
    EqOn F 0 upperHalfPlaneSet :=
  eqOn_const_of_upperHalfPlaneBoundaryFun_eq hF hS hA hFA

end TauCeti
