/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.AbsolutelyContinuous
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Winding numbers of absolutely continuous curves

For an absolutely continuous curve avoiding a point, exponentiating its winding integral gives
the endpoint ratio. Consequently the winding number of a closed absolutely continuous curve is
an integer.
-/

public section

open Complex MeasureTheory Set

namespace TauCeti.Contour

/-- The endpoint-ratio identity for an absolutely continuous curve, with either orientation of
its parameter interval. -/
theorem _root_.AbsolutelyContinuousOnInterval.exp_two_pi_I_mul_windingNumber
    {γ : ℝ → ℂ} {a b : ℝ} {z : ℂ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hz : z ∉ γ '' uIcc a b) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b z) =
      (γ b - z) / (γ a - z) := by
  let f : ℝ → ℂ := fun t ↦ (γ t - z)⁻¹ * deriv γ t
  let A : ℝ → ℂ := fun t ↦ ∫ v in a..t, f v
  have hf : IntervalIntegrable f volume a b :=
    hγ.intervalIntegrable_inv_sub_mul_deriv hz
  have hA : AbsolutelyContinuousOnInterval A a b :=
    hf.absolutelyContinuousOnInterval_intervalIntegral' left_mem_uIcc
  have hexp : AbsolutelyContinuousOnInterval (fun t ↦ Complex.exp (-A t)) a b :=
    hA.neg.comp_of_contDiffAt fun _ _ ↦ (Complex.contDiff_exp (𝕜 := ℝ) (n := 1)).contDiffAt
  have hsub : AbsolutelyContinuousOnInterval (fun t ↦ γ t - z) a b :=
    hγ.fun_sub (LipschitzWith.const (α := ℝ) z).lipschitzOnWith.absolutelyContinuousOnInterval
  have hfactor : AbsolutelyContinuousOnInterval
      (fun t ↦ (γ t - z) * Complex.exp (-A t)) a b := hsub.smul hexp
  have hzero : ∀ᵐ t, t ∈ uIcc a b →
      HasDerivAt (fun t ↦ (γ t - z) * Complex.exp (-A t)) 0 t := by
    filter_upwards [hγ.boundedVariationOn.ae_differentiableAt_of_mem_uIcc,
      hf.ae_hasDerivAt_integral]
      with t hdt hAt ht
    have hne : γ t - z ≠ 0 := sub_ne_zero.mpr (fun heq ↦ hz ⟨t, ht, heq⟩)
    convert ((hdt ht).hasDerivAt.sub_const z).mul ((hAt ht a left_mem_uIcc).neg.cexp) using 1
    dsimp [f]
    field_simp
    ring
  obtain ⟨C, hC⟩ := hfactor.const_of_ae_hasDerivAt_zero hzero
  have ha := hC a left_mem_uIcc
  have hb := hC b right_mem_uIcc
  have ha0 : A a = 0 := by simp [A]
  rw [ha0, neg_zero, Complex.exp_zero, mul_one] at ha
  have hratio : Complex.exp (A b) = (γ b - z) / (γ a - z) := by
    have hne : γ a - z ≠ 0 := sub_ne_zero.mpr (fun heq ↦ hz ⟨a, left_mem_uIcc, heq⟩)
    rw [← ha, Complex.exp_neg] at hb
    rw [eq_div_iff hne]
    calc
      Complex.exp (A b) * (γ a - z) =
          Complex.exp (A b) * ((γ b - z) * (Complex.exp (A b))⁻¹) := by rw [hb]
      _ = γ b - z := by field_simp
  rw [hγ.windingNumber_eq_integral hz,
    ← mul_assoc, mul_inv_cancel₀ Complex.two_pi_I_ne_zero, one_mul]
  exact hratio

/-- The winding number of a closed absolutely continuous curve is an integer off its trace. -/
theorem _root_.AbsolutelyContinuousOnInterval.exists_int_windingNumber
    {γ : ℝ → ℂ} {a b : ℝ} {z : ℂ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) (hz : z ∉ γ '' uIcc a b) :
    ∃ n : ℤ, windingNumber γ a b z = n := by
  have h := hγ.exp_two_pi_I_mul_windingNumber hz
  rw [← hclosed, div_self (sub_ne_zero.mpr (fun heq ↦ hz ⟨a, left_mem_uIcc, heq⟩))] at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  refine ⟨n, mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_⟩
  rw [hn, mul_comm]

end TauCeti.Contour
