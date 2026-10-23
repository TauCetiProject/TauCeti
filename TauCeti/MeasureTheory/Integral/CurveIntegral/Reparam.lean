/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.DerivComp

/-!
# Reparametrizing integrals of 1-forms along absolutely continuous curves

An absolutely continuous change of parameter that is monotone or antitone preserves the integral
of a 1-form along an absolutely continuous curve. Integrability on the original interval implies
integrability on the new interval. The oriented image interval records reversal of orientation.
The statements use the raw-curve integral `∫ t in a..b, ω (γ t) (deriv γ t)`.
For a `Path`, Mathlib's `curveIntegral_eq_intervalIntegral_deriv` gives this representation.
The 1-form needs only the integrability of its pairing with the original velocity.
-/

public section

open MeasureTheory Set

namespace AbsolutelyContinuousOnInterval

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {γ : ℝ → E} {θ : ℝ → ℝ} {a b : ℝ}
  {ω : E → E →L[ℝ] F}

/-- The a.e. reparametrization formula for a 1-form paired with the canonical derivative. -/
private theorem ae_oneForm_comp (hγ : AbsolutelyContinuousOnInterval γ (θ a) (θ b))
    (hθ : AbsolutelyContinuousOnInterval θ a b) (hab : a ≤ b)
    (horder : MonotoneOn θ (Icc a b) ∨ AntitoneOn θ (Icc a b)) :
    ∀ᵐ t, t ∈ uIoc a b → ω ((γ ∘ θ) t) (deriv (γ ∘ θ) t) =
      deriv θ t • ω (γ (θ t)) (deriv γ (θ t)) := by
  have hmap : MapsTo θ (Icc a b) (uIcc (θ a) (θ b)) := by
    have horderu : MonotoneOn θ (uIcc a b) ∨ AntitoneOn θ (uIcc a b) := by
      simpa only [uIcc_of_le hab] using horder
    rw [← uIcc_of_le hab]
    exact horderu.elim MonotoneOn.mapsTo_uIcc AntitoneOn.mapsTo_uIcc
  have hd : ∀ᵐ t, t ∈ uIcc a b → deriv (γ ∘ θ) t = deriv θ t • deriv γ (θ t) := by
    rcases horder with hmono | hanti
    · exact hγ.ae_deriv_comp_of_monotoneOn hθ hab hmono hmap
    · exact hγ.ae_deriv_comp_of_antitoneOn hθ hab hanti hmap
  filter_upwards [hd] with t ht hmem
  simp only [ht (uIoc_subset_uIcc hmem), Function.comp_apply, map_smul]

/-- The integrability of a 1-form paired with an absolutely continuous curve's velocity is
preserved by monotone or antitone absolutely continuous changes of parameter. -/
theorem intervalIntegrable_oneForm_comp (hγ : AbsolutelyContinuousOnInterval γ (θ a) (θ b))
    (hθ : AbsolutelyContinuousOnInterval θ a b) (hab : a ≤ b)
    (horder : MonotoneOn θ (Icc a b) ∨ AntitoneOn θ (Icc a b))
    (hω : IntervalIntegrable (fun t ↦ ω (γ t) (deriv γ t)) volume (θ a) (θ b)) :
    IntervalIntegrable (fun t ↦ ω ((γ ∘ θ) t) (deriv (γ ∘ θ) t)) volume a b := by
  have hint : IntervalIntegrable (fun t ↦ deriv θ t • ω (γ (θ t)) (deriv γ (θ t))) volume a b := by
    rcases horder with hmono | hanti
    · exact hθ.intervalIntegrable_deriv_smul_comp_of_monotoneOn hab hmono hω
    · exact hθ.intervalIntegrable_deriv_smul_comp_of_antitoneOn hab hanti hω
  apply hint.congr_ae
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [hγ.ae_oneForm_comp (ω := ω) hθ hab horder] with t ht hmem
  exact (ht hmem).symm

/-- A monotone or antitone absolutely continuous change of parameter preserves the integral of
the raw integral `∫ t in a..b, ω (γ t) (deriv γ t)`, with its oriented image interval. -/
theorem integral_oneForm_comp (hγ : AbsolutelyContinuousOnInterval γ (θ a) (θ b))
    (hθ : AbsolutelyContinuousOnInterval θ a b) (hab : a ≤ b)
    (horder : MonotoneOn θ (Icc a b) ∨ AntitoneOn θ (Icc a b))
    (hω : IntervalIntegrable (fun t ↦ ω (γ t) (deriv γ t)) volume (θ a) (θ b)) :
    ∫ t in a..b, ω ((γ ∘ θ) t) (deriv (γ ∘ θ) t) =
      ∫ u in θ a..θ b, ω (γ u) (deriv γ u) := by
  refine Eq.trans
    (intervalIntegral.integral_congr_ae (hγ.ae_oneForm_comp (ω := ω) hθ hab horder)) ?_
  rcases horder with hmono | hanti
  · exact hθ.integral_deriv_smul_comp_of_monotoneOn hab hmono hω
  · exact hθ.integral_deriv_smul_comp_of_antitoneOn hab hanti hω

end AbsolutelyContinuousOnInterval
