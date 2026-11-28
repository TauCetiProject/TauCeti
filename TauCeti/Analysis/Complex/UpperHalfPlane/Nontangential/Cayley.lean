/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Nontangential.Limit
import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley

/-!
# Radii of the disc and nontangential approach

The inverse Cayley transform `w ↦ i (1 + w) / (1 - w)` carries the radius of the unit disc ending at
`ζ = (x - i) / (x + i)` to a curve tending to `x ∈ ℝ` inside every cone at `x`
(`TauCeti.tendsto_I_mul_one_add_div_one_sub_nontangentialFilter`). So radial limits of a function
transported from the upper half-plane to the disc are nontangential limits of the original
function.

## Main results

* `TauCeti.tendsto_I_mul_one_add_div_one_sub_nontangentialFilter`: radii of the disc end
  nontangentially under the inverse Cayley transform.

## References

* J. B. Garnett, *Bounded Analytic Functions*, revised 1st ed., Springer (2007), Chapter II.
-/

public section

noncomputable section

open Complex Filter Metric Set Topology

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
      have hc : ContinuousAt (fun r : ℝ ↦ |x| * ((1 - r) / (1 + r))) 1 := by
        fun_prop (disch := norm_num)
      exact nhdsWithin_le_nhds (hc.eventually_lt continuousAt_const (by simpa using hα))
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
    rw [heq]
    simpa [abs_mul, abs_of_pos hpos, abs_of_pos hq] using mul_lt_mul_of_pos_right hr hpos

end TauCeti
