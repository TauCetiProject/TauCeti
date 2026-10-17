/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoxIntegral.Oriented.Basic
public import TauCeti.Analysis.BoxIntegral.Substitution
import TauCeti.Analysis.Calculus.Deriv.Projection

/-!
# Fundamental theorem and substitution for oriented Henstock intervals

The genuine gauge FTC and substitution theorems hold for arbitrary endpoint order, including
zero intervals and backtracking parametrizations. Neither theorem assumes Bochner integrability
of the derivative. Constant real projections have zero integral, without curve regularity.
-/

public section

open MeasureTheory Set

open BoxIntegral

namespace TauCeti.BoxIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The oriented Henstock fundamental theorem for a continuous primitive differentiable
outside a countable exceptional set in the interval interior. -/
theorem hasHenstockIntervalIntegral_of_hasDerivAt_off_countable {a b : ℝ} {f f' : ℝ → E} {s : Set ℝ}
    (hs : s.Countable) (hc : ContinuousOn f (uIcc a b))
    (hd : ∀ x ∈ uIoo a b \ s, HasDerivAt f (f' x) x) :
    HasHenstockIntervalIntegral f' a b (f b - f a) := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · rw [hasHenstockIntervalIntegral_iff_of_lt hab]
    exact hasIntegral_Henstock_of_hasDerivAt_off_countable hab hs
      (by simpa only [uIcc_of_le hab.le] using hc)
      (by simpa only [uIoo_of_le hab.le] using hd)
  · simp
  · rw [hasHenstockIntervalIntegral_iff_of_gt hba, neg_sub]
    exact hasIntegral_Henstock_of_hasDerivAt_off_countable hba hs
      (by simpa only [uIcc_of_ge hba.le] using hc)
      (by simpa only [uIoo_of_ge hba.le] using hd)

/-- Oriented substitution for continuous integrands and continuous scalar parametrizations
with countably many derivative exceptions. The parameter may reverse direction or backtrack. -/
theorem hasHenstockIntervalIntegral_deriv_smul_comp {a b : ℝ} {f : ℝ → E} {θ θ' : ℝ → ℝ}
    {s : Set ℝ} (hs : s.Countable) (hθ : ContinuousOn θ (uIcc a b))
    (hdθ : ∀ t ∈ uIoo a b \ s, HasDerivAt θ (θ' t) t)
    (hf : ContinuousOn f (θ '' uIcc a b)) :
    HasHenstockIntervalIntegral (fun t ↦ θ' t • f (θ t)) a b (∫ x in θ a..θ b, f x) := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · rw [hasHenstockIntervalIntegral_iff_of_lt hab]
    exact hasIntegral_Henstock_deriv_smul_comp hab hs
      (by simpa only [uIcc_of_le hab.le] using hθ)
      (by simpa only [uIoo_of_le hab.le] using hdθ)
      (by simpa only [uIcc_of_le hab.le] using hf)
  · simp
  · rw [hasHenstockIntervalIntegral_iff_of_gt hba, ← intervalIntegral.integral_symm]
    exact hasIntegral_Henstock_deriv_smul_comp hba hs
      (by simpa only [uIcc_of_ge hba.le] using hθ)
      (by simpa only [uIoo_of_ge hba.le] using hdθ)
      (by simpa only [uIcc_of_ge hba.le] using hf)

/-- A raw curve with constant projection contributes zero to that coordinate one-form.
No regularity of its other coordinate or of the field is needed. -/
theorem hasHenstockIntervalIntegral_of_projection_constant {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) {a b c : ℝ}
    {γ : ℝ → V} (hγ : ∀ t, L (γ t) = c) (P : V → ℝ) :
    TauCeti.BoxIntegral.HasHenstockIntervalIntegral (fun t ↦ P (γ t) * L (deriv γ t)) a b 0 := by
  have hd (t : ℝ) : L (deriv γ t) = 0 := L.apply_deriv_eq_zero_of_forall_eq hγ t
  simpa only [hd, mul_zero, Pi.zero_def] using
    TauCeti.BoxIntegral.hasHenstockIntervalIntegral_zero (E := ℝ) a b

end TauCeti.BoxIntegral
