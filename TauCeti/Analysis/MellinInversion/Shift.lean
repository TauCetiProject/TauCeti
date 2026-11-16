/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Residue.Basic
public import TauCeti.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import TauCeti.Analysis.Contour.Residue.Rectangle

/-!
# Contour shifts for the inverse Mellin transform

Shifting the vertical contour of `Complex.mellinInv` across a closed strip `Icc a b ×ℂ univ`
applies the vertical-line contour shift formula
`TauCeti.Contour.integral_add_mul_I_sub_integral_add_mul_I_eq_two_pi_mul_sum_residue` to
`z ↦ (x : ℂ) ^ (-z) * f z`. When `f` is differentiable on the strip away from a finite set `S`
of poles in the open strip `a < Re s < b`, vertically integrable on `Re s = a` and `Re s = b`,
and its horizontal `L¹` integrals at heights `±T` vanish as `T → ∞`, the difference
`mellinInv b f x - mellinInv a f x` equals the sum of the residues of `z ↦ (x : ℂ) ^ (-z) * f z`
at the points of `S`.

## Main results

* `TauCeti.Contour.mellinInv_sub_mellinInv_eq_sum_residue`: shifting `mellinInv` between two
  abscissae under `L¹` decay on horizontal segments.

## References

* E. C. Titchmarsh, *The Theory of Functions*, §3.1 and §9.5.
* H. Davenport, *Multiplicative Number Theory*, the chapter on Siegel's theorem.
-/

public section

open Set Complex MeasureTheory Filter
open scoped Real Topology Interval

namespace TauCeti.Contour

variable {f : ℂ → ℂ} {S : Finset ℂ}

private theorem tendsto_integral_cpow_neg_mul_of_tendsto_integral_norm {a b x sgn : ℝ}
    (hab : a ≤ b) (hx : 0 < x) (hsgn : |sgn| = 1)
    (hf : DifferentiableOn ℂ f ((Icc a b ×ℂ univ) \ (↑S : Set ℂ)))
    (hL1 : Tendsto (fun T : ℝ ↦ ∫ σ : ℝ in a..b, ‖f (σ + ((sgn * T : ℝ) : ℂ) * I)‖) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ ↦ ∫ σ : ℝ in a..b,
      (x : ℂ) ^ (-((σ : ℂ) + ((sgn * T : ℝ) : ℂ) * I)) * f (σ + ((sgn * T : ℝ) : ℂ) * I))
      atTop (𝓝 0) := by
  set g : ℂ → ℂ := fun z ↦ (x : ℂ) ^ (-z) * f z
  have hg_diff : DifferentiableOn ℂ g ((Icc a b ×ℂ univ) \ (↑S : Set ℂ)) :=
    DifferentiableOn.mul (fun z _ ↦ (analyticAt_const.cpow analyticAt_id.neg
      (ofReal_mem_slitPlane.mpr hx)).differentiableAt.differentiableWithinAt) hf
  set M : ℝ := max (x ^ (-a)) (x ^ (-b))
  have hpow {σ : ℝ} (hσ : σ ∈ Icc a b) (y : ℝ) : ‖(x : ℂ) ^ (-((σ : ℂ) + y * I))‖ ≤ M := by
    rw [norm_cpow_eq_rpow_re_of_pos hx, show (-((σ : ℂ) + y * I)).re = -σ by simp]
    rcases le_total 1 x with hx1 | hx1
    · exact (Real.rpow_le_rpow_of_exponent_le hx1 (neg_le_neg hσ.1)).trans (le_max_left _ _)
    · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1 (neg_le_neg hσ.2)).trans (le_max_right _ _)
  refine squeeze_zero_norm'
    (a := fun T ↦ M * ∫ σ : ℝ in a..b, ‖f (σ + ((sgn * T : ℝ) : ℂ) * I)‖) ?_
    (by simpa using hL1.const_mul M)
  filter_upwards [eventually_ge_atTop ((∑ s ∈ S, |s.im|) + 1)] with T hT
  have hmaps : MapsTo (fun σ : ℝ ↦ (σ : ℂ) + ((sgn * T : ℝ) : ℂ) * I) (Icc a b)
      ((Icc a b ×ℂ univ) \ (↑S : Set ℂ)) := fun σ hσ ↦ by
    refine ⟨⟨by simpa using hσ, trivial⟩, fun hmem ↦ ?_⟩
    have hle : |((σ : ℂ) + ((sgn * T : ℝ) : ℂ) * I).im| ≤ ∑ p ∈ S, |p.im| :=
      Finset.single_le_sum (f := fun p : ℂ ↦ |p.im|) (fun p _ ↦ abs_nonneg p.im) hmem
    have hsum0 : 0 ≤ ∑ p ∈ S, |p.im| := Finset.sum_nonneg fun p _ ↦ abs_nonneg p.im
    have him : |((σ : ℂ) + ((sgn * T : ℝ) : ℂ) * I).im| = T := by
      simp [abs_mul, hsgn, abs_of_nonneg (by linarith : 0 ≤ T)]
    linarith
  have hcont_f := hf.continuousOn.comp (continuous_ofReal.add continuous_const).continuousOn hmaps
  have hcont_g :=
    hg_diff.continuousOn.comp (continuous_ofReal.add continuous_const).continuousOn hmaps
  calc ‖∫ σ : ℝ in a..b, g (σ + ((sgn * T : ℝ) : ℂ) * I)‖
      ≤ ∫ σ : ℝ in a..b, ‖g (σ + ((sgn * T : ℝ) : ℂ) * I)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ σ : ℝ in a..b, M * ‖f (σ + ((sgn * T : ℝ) : ℂ) * I)‖ := by
        refine intervalIntegral.integral_mono_on hab
          (hcont_g.norm.intervalIntegrable_of_Icc hab)
          ((continuousOn_const.mul hcont_f.norm).intervalIntegrable_of_Icc hab) fun σ hσ ↦ ?_
        simpa [g, norm_mul] using mul_le_mul_of_nonneg_right (hpow hσ (sgn * T)) (norm_nonneg _)
    _ = M * ∫ σ : ℝ in a..b, ‖f (σ + ((sgn * T : ℝ) : ℂ) * I)‖ :=
        intervalIntegral.integral_const_mul _ _

/-- **Shifting `mellinInv` across poles in a strip.** Suppose `a ≤ b`, `0 < x`, `f` is
differentiable on `(Icc a b ×ℂ univ) \ S` and meromorphic at each `s ∈ S`, every `s ∈ S` has real
part strictly between `a` and `b`, `f` is vertically integrable on `Re s = a` and `Re s = b`, and
the horizontal `L¹` integrals `∫ σ in a..b, ‖f (σ ± T * I)‖` tend to `0` as `T → ∞`. Then
`mellinInv b f x - mellinInv a f x = ∑_{s ∈ S} Res_s (z ↦ x⁻ᶻ f(z))`. -/
theorem mellinInv_sub_mellinInv_eq_sum_residue {a b x : ℝ} (hab : a ≤ b) (hx : 0 < x)
    (hf : DifferentiableOn ℂ f ((Icc a b ×ℂ univ) \ (↑S : Set ℂ)))
    (hmero : ∀ s ∈ S, MeromorphicAt f s)
    (hS : ∀ s ∈ S, s.re ∈ Ioo a b)
    (ha : VerticalIntegrable f a) (hb : VerticalIntegrable f b)
    (htop : Tendsto (fun T : ℝ ↦ ∫ σ : ℝ in a..b, ‖f (σ + T * I)‖) atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ ↦ ∫ σ : ℝ in a..b, ‖f (σ - T * I)‖) atTop (𝓝 0)) :
    mellinInv b f x - mellinInv a f x =
      ∑ s ∈ S, residue (fun z ↦ (x : ℂ) ^ (-z) * f z) s := by
  set g : ℂ → ℂ := fun z ↦ (x : ℂ) ^ (-z) * f z
  have hx_an (z : ℂ) : AnalyticAt ℂ (fun w : ℂ ↦ (x : ℂ) ^ (-w)) z :=
    analyticAt_const.cpow analyticAt_id.neg (ofReal_mem_slitPlane.mpr hx)
  have hg_diff : DifferentiableOn ℂ g ((Icc a b ×ℂ univ) \ (↑S : Set ℂ)) :=
    DifferentiableOn.mul (fun z _ ↦ (hx_an z).differentiableAt.differentiableWithinAt) hf
  have hg_mero : ∀ s ∈ S, MeromorphicAt g s := fun s hs ↦ (hx_an s).meromorphicAt.mul (hmero s hs)
  have htop_g : Tendsto (fun T : ℝ ↦ ∫ σ : ℝ in a..b, g (σ + T * I)) atTop (𝓝 0) := by
    simpa [g, one_mul] using tendsto_integral_cpow_neg_mul_of_tendsto_integral_norm hab hx
      (sgn := 1) (by norm_num) hf (by simpa [one_mul] using htop)
  have hbot_g : Tendsto (fun T : ℝ ↦ ∫ σ : ℝ in a..b, g (σ - T * I)) atTop (𝓝 0) := by
    simpa [g, sub_eq_add_neg, neg_mul] using tendsto_integral_cpow_neg_mul_of_tendsto_integral_norm
      hab hx (sgn := -1) (by norm_num) hf (by simpa [sub_eq_add_neg, neg_mul] using hbot)
  have hshift := integral_add_mul_I_sub_integral_add_mul_I_eq_two_pi_mul_sum_residue hab hg_diff
    hg_mero hS (by simpa [g] using ha.integrable_cpow_smul hx)
    (by simpa [g] using hb.integrable_cpow_smul hx) htop_g hbot_g
  simp only [mellinInv, real_smul, smul_eq_mul, ← mul_sub]
  dsimp only [g] at hshift ⊢
  rw [hshift]
  push_cast
  field_simp [Real.pi_ne_zero]

end TauCeti.Contour
