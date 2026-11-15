/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousSubstitution.Basic
public import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Reparam
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Substitution by decreasing absolutely continuous parameters

Change of variables holds for antitone absolutely continuous substitutions, including constant
pieces and unbounded speeds. Reflecting the parameter interval reduces the results to increasing
substitutions. The oriented image interval records the sign reversal.
-/

public section

open MeasureTheory Set

namespace AbsolutelyContinuousOnInterval

variable {θ : ℝ → ℝ} {a b : ℝ}

/-- Reflecting the source interval turns an antitone absolutely continuous parameter into a
monotone absolutely continuous parameter. -/
private theorem comp_reflection_of_antitoneOn (hθ : AbsolutelyContinuousOnInterval θ a b)
    (hab : a ≤ b) (hanti : AntitoneOn θ (Icc a b)) :
    AbsolutelyContinuousOnInterval (fun t ↦ θ (a + b - t)) a b ∧
      MonotoneOn (fun t ↦ θ (a + b - t)) (Icc a b) := by
  have hmem {t : ℝ} (ht : t ∈ Icc a b) : a + b - t ∈ Icc a b := by
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨?_, fun t ht u hu htu ↦ hanti (hmem hu) (hmem ht) (by linarith)⟩
  have hR : ContDiff ℝ 1 (fun t : ℝ ↦ a + b - t) := contDiff_const.sub contDiff_id
  apply hθ.comp_antitoneOn hR.contDiffOn.absolutelyContinuousOnInterval
  · rw [uIcc_of_le hab]
    exact fun _ _ _ _ htu ↦ by dsimp; linarith
  · rw [uIcc_of_le hab]
    exact fun _ ht ↦ hmem ht

/-- An antitone absolutely continuous substitution preserves integrability after multiplication
by its derivative. -/
theorem intervalIntegrable_deriv_smul_comp_of_antitoneOn
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F}
    (hθ : AbsolutelyContinuousOnInterval θ a b) (hab : a ≤ b)
    (hanti : AntitoneOn θ (Icc a b)) (hf : IntervalIntegrable f volume (θ a) (θ b)) :
    IntervalIntegrable (fun t ↦ deriv θ t • f (θ t)) volume a b := by
  obtain ⟨hR, hmono⟩ := comp_reflection_of_antitoneOn hθ hab hanti
  have hfR : IntervalIntegrable f volume (θ (a + b - a)) (θ (a + b - b)) := by
    simpa using hf.symm
  have hi := hR.intervalIntegrable_deriv_smul_comp_of_monotoneOn hab hmono hfR
  simp only [deriv_comp_const_sub, neg_smul] at hi
  have href := hi.neg.comp_sub_left (a + b)
  simpa using href.symm

/-- Change of variables for an antitone absolutely continuous substitution and an integrable
vector-valued integrand. The decreasing oriented image interval records the sign reversal. -/
theorem integral_deriv_smul_comp_of_antitoneOn
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F}
    (hθ : AbsolutelyContinuousOnInterval θ a b) (hab : a ≤ b)
    (hanti : AntitoneOn θ (Icc a b)) (hf : IntervalIntegrable f volume (θ a) (θ b)) :
    ∫ t in a..b, deriv θ t • f (θ t) = ∫ u in θ a..θ b, f u := by
  obtain ⟨hR, hmono⟩ := comp_reflection_of_antitoneOn hθ hab hanti
  have hfR : IntervalIntegrable f volume (θ (a + b - a)) (θ (a + b - b)) := by
    simpa using hf.symm
  have hi := hR.integral_deriv_smul_comp_of_monotoneOn hab hmono hfR
  simp only [deriv_comp_const_sub, neg_smul] at hi
  have href : (∫ t in a..b, deriv θ (a + b - t) • f (θ (a + b - t))) =
      ∫ t in a..b, deriv θ t • f (θ t) := by
    simpa using intervalIntegral.integral_comp_sub_left
      (a := a) (b := b) (fun t ↦ deriv θ t • f (θ t)) (a + b)
  rw [intervalIntegral.integral_neg, href] at hi
  have hi' : -(∫ t in a..b, deriv θ t • f (θ t)) = ∫ u in θ b..θ a, f u := by
    simpa using hi
  rw [intervalIntegral.integral_symm (θ a) (θ b)] at hi'
  exact neg_injective hi'

end AbsolutelyContinuousOnInterval
