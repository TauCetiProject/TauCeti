/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.AbsolutelyContinuous
public import TauCeti.MeasureTheory.Integral.CurveIntegral.Reparam
import TauCeti.Analysis.Contour.Winding.Number.Reverse

/-!
# Winding numbers under absolutely continuous reparametrizations

Monotone or antitone absolutely continuous changes of parameter preserve the winding integral
with its oriented image interval. Increasing parameters onto a given interval preserve its index;
decreasing parameters onto that interval negate its index. Constant pieces and unbounded speeds
are allowed.
-/

public section

open MeasureTheory Set

namespace TauCeti.Contour

/-- An absolutely continuous monotone or antitone change of parameter preserves the off-trace
winding number when the image interval carries its induced orientation. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_comp
    {γ : ℝ → ℂ} {θ : ℝ → ℝ} {a b : ℝ} {z : ℂ}
    (hγ : AbsolutelyContinuousOnInterval γ (θ a) (θ b))
    (hθ : AbsolutelyContinuousOnInterval θ a b) (hab : a ≤ b)
    (horder : MonotoneOn θ (Icc a b) ∨ AntitoneOn θ (Icc a b))
    (hz : z ∉ γ '' uIcc (θ a) (θ b)) :
    windingNumber (γ ∘ θ) a b z = windingNumber γ (θ a) (θ b) z := by
  have horderu : MonotoneOn θ (uIcc a b) ∨ AntitoneOn θ (uIcc a b) := by
    simpa only [uIcc_of_le hab] using horder
  have hmap : MapsTo θ (uIcc a b) (uIcc (θ a) (θ b)) :=
    horderu.elim MonotoneOn.mapsTo_uIcc AntitoneOn.mapsTo_uIcc
  have hcomp : AbsolutelyContinuousOnInterval (γ ∘ θ) a b := by
    rcases horderu with hmono | hanti
    · exact hγ.comp_monotoneOn hθ hmono hmap
    · exact hγ.comp_antitoneOn hθ hanti hmap
  have hzcomp : z ∉ (γ ∘ θ) '' uIcc a b := by
    rintro ⟨t, ht, heq⟩
    exact hz ⟨θ t, hmap ht, heq⟩
  let ω : ℂ → ℂ →L[ℝ] ℂ := fun u ↦ (u - z)⁻¹ • ContinuousLinearMap.id ℝ ℂ
  have hω : IntervalIntegrable (fun t ↦ ω (γ t) (deriv γ t)) volume (θ a) (θ b) := by
    simpa only [ω, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
      using hγ.intervalIntegrable_inv_sub_mul_deriv hz
  have hint : (∫ t in a..b, ((γ ∘ θ) t - z)⁻¹ * deriv (γ ∘ θ) t) =
      ∫ u in θ a..θ b, (γ u - z)⁻¹ * deriv γ u := by
    simpa only [ω, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
      using hγ.integral_oneForm_comp hθ hab horder hω
  rw [hcomp.windingNumber_eq_integral hzcomp,
    hγ.windingNumber_eq_integral hz, hint]

/-- An increasing absolutely continuous parameter onto the original interval preserves the
winding number of an absolutely continuous curve away from its trace. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_comp_of_monotoneOn
    {γ : ℝ → ℂ} {θ : ℝ → ℝ} {a b c d : ℝ} {z : ℂ}
    (hγ : AbsolutelyContinuousOnInterval γ c d)
    (hθ : AbsolutelyContinuousOnInterval θ a b) (hab : a ≤ b)
    (hmono : MonotoneOn θ (Icc a b)) (ha : θ a = c) (hb : θ b = d)
    (hz : z ∉ γ '' uIcc c d) :
    windingNumber (γ ∘ θ) a b z = windingNumber γ c d z := by
  have hγθ : AbsolutelyContinuousOnInterval γ (θ a) (θ b) := by simpa only [ha, hb] using hγ
  have hzθ : z ∉ γ '' uIcc (θ a) (θ b) := by simpa only [ha, hb] using hz
  simpa only [ha, hb] using
    hγθ.windingNumber_comp hθ hab (Or.inl hmono) hzθ

/-- A decreasing absolutely continuous parameter onto the original interval negates the
winding number of an absolutely continuous curve away from its trace. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_comp_of_antitoneOn
    {γ : ℝ → ℂ} {θ : ℝ → ℝ} {a b c d : ℝ} {z : ℂ}
    (hγ : AbsolutelyContinuousOnInterval γ c d)
    (hθ : AbsolutelyContinuousOnInterval θ a b) (hab : a ≤ b)
    (hanti : AntitoneOn θ (Icc a b)) (ha : θ a = d) (hb : θ b = c)
    (hz : z ∉ γ '' uIcc c d) :
    windingNumber (γ ∘ θ) a b z = -windingNumber γ c d z := by
  have hγθ : AbsolutelyContinuousOnInterval γ (θ a) (θ b) := by
    simpa only [ha, hb] using hγ.symm
  have hzθ : z ∉ γ '' uIcc (θ a) (θ b) := by simpa only [ha, hb, uIcc_comm d c] using hz
  have hcomp := hγθ.windingNumber_comp hθ hab
    (Or.inr hanti) hzθ
  rw [ha, hb] at hcomp
  refine hcomp.trans (windingNumber_symm ?_)
  exact cauchyPVExistsAt_of_avoidance hγ.continuousOn
    (fun t ht heq ↦ hz ⟨t, ht, heq⟩)
    (hγ.intervalIntegrable_inv_sub_mul_deriv hz)

end TauCeti.Contour
