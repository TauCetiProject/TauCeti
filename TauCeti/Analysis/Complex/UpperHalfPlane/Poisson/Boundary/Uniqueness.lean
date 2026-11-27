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
(`TauCeti.tendsto_I_mul_one_add_div_one_sub_nontangentialFilter`): along it
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

/-- **Radii of the disc end nontangentially.** The inverse Cayley transform `w ↦ i (1 + w)/(1 - w)`
maps the radius `r ↦ r ζ` of the unit disc ending at `ζ = (x - i) / (x + i)` to a curve tending to
`x` inside the cone of any aperture `α > 0` at `x`: along it
`|Re z - x| = |x| (1 - r)/(1 + r) Im z`. -/
theorem tendsto_I_mul_one_add_div_one_sub_nontangentialFilter (x : ℝ) {α : ℝ} (hα : 0 < α) :
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
    have hrζ : (r : ℂ) * ζ ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, norm_mul, hζ, norm_div, norm_sub_I_div_norm_add_I_ofReal, mul_one,
        norm_real, Real.norm_eq_abs]
      exact abs_lt.2 ⟨by linarith [hr01.1], hr01.2⟩
    have hpos : 0 < (I * (1 + r * ζ) / (1 - r * ζ)).im :=
      bijOn_I_mul_one_add_div_one_sub_ball.mapsTo hrζ
    have heq := re_I_mul_one_add_div_one_sub_ofReal_mul_sub_I_div_add_I x
      (show r ≠ -1 by linarith [hr01.1])
    refine mem_nontangentialCone.2 ⟨hpos, ?_, ENNReal.ofReal_lt_top⟩
    have hq : (0 : ℝ) < (1 - r) / (1 + r) := div_pos (by linarith [hr01.2]) (by linarith [hr01.1])
    rw [← hζ] at heq
    rw [heq, sub_sub_cancel_left, abs_neg, abs_mul, abs_mul, abs_of_pos hpos, abs_of_pos hq]
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
    have hw1 : w ≠ 1 := by
      rintro rfl
      simp at hw
    exact (hasDerivAt_I_mul_one_add_div_one_sub hw1).differentiableAt.differentiableWithinAt
  have hgS : ∀ w ∈ ball (0 : ℂ) 1, ‖g w‖ ≤ S := fun w hw ↦ hS _ (hmaps hw)
  have hlim : ∀ t ∈ θ '' A', Tendsto (fun r ↦ g (circleMap 0 r t)) (𝓝[<] 1) (𝓝 c) := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [g, circleMap_zero, θ, exp_pi_add_two_mul_arctan_mul_I]
    exact (hx.2 1).comp (tendsto_I_mul_one_add_div_one_sub_nontangentialFilter x one_pos)
  have hgc := eqOn_const_ball_of_tendsto_circleMap hg hgS hE hlim
  intro z hz
  have hzI : z + I ≠ 0 := add_I_ne_zero_of_im_nonneg (le_of_lt hz)
  have := hgc (bijOn_sub_I_div_add_I_upperHalfPlaneSet.mapsTo hz)
  simpa [g, I_mul_one_add_sub_I_div_add_I_div_one_sub hzI] using this

/-- **Uniqueness for boundary functions**, the case `c = 0`. If `F` is holomorphic and bounded on
`ℂ₊` and its boundary function `F*` vanishes almost everywhere on a set of positive measure, then
`F ≡ 0` on `ℂ₊`. -/
theorem eqOn_zero_of_upperHalfPlaneBoundaryFun_eq_zero {F : ℂ → ℂ} {S : ℝ} {A : Set ℝ}
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (hS : ∀ z ∈ upperHalfPlaneSet, ‖F z‖ ≤ S)
    (hA : volume A ≠ 0) (hFA : ∀ᵐ x, x ∈ A → upperHalfPlaneBoundaryFun F x = 0) :
    EqOn F 0 upperHalfPlaneSet :=
  eqOn_const_of_upperHalfPlaneBoundaryFun_eq hF hS hA hFA

end TauCeti
