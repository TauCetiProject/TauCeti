/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Pow.Windows
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Upper power bounds on scale windows

Increasing the power in an upper bound on arbitrarily large scale windows preserves the
window ratio. A strict increase also absorbs any constant multiplying the power. Thus to
obtain unit-coefficient window bounds at every exponent above a threshold, it suffices to
have bounds with constants at exponents arbitrarily close to the threshold.
-/

public section

open Filter

namespace TauCeti

/-- Increasing the exponent of a unit-coefficient upper bound preserves the window ratio. -/
theorem HasWindows.rpow_bound_mono {f : ℝ → ℝ} {L a b : ℝ}
    (h : HasWindows {y | f y ≤ y ^ a} L) (hab : a ≤ b) :
    HasWindows {y | f y ≤ y ^ b} L :=
  h.mono_of_inter_subset (x₀ := 1) fun _ ⟨hy, hy₁⟩ ↦
    hy.trans (Real.rpow_le_rpow_of_exponent_le hy₁ hab)

/-- A strict increase in the exponent absorbs any real coefficient in a window bound,
without changing the window ratio. -/
theorem HasWindows.rpow_bound_of_lt {f : ℝ → ℝ} {L C a b : ℝ}
    (h : HasWindows {y | f y ≤ C * y ^ a} L) (hab : a < b) :
    HasWindows {y | f y ≤ y ^ b} L := by
  have hsmall := ((isLittleO_rpow_rpow_atTop hab).const_mul_left C).bound one_pos
  obtain ⟨Y, hY⟩ := (hsmall.and (eventually_ge_atTop (0 : ℝ))).exists_forall_of_atTop
  refine h.mono_of_inter_subset (x₀ := Y) fun y ⟨hy, hyY⟩ ↦ ?_
  obtain ⟨hb, hy₀⟩ := hY y hyY
  have hnonneg : 0 ≤ y ^ b := Real.rpow_nonneg hy₀ _
  exact hy.trans ((le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg, one_mul] using hb))

/-- Scaling the bounded function by a nonnegative factor preserves its windows at every
strictly larger exponent, with coefficient one. -/
theorem HasWindows.rpow_bound_mul_of_lt {f : ℝ → ℝ} {L C c a b : ℝ}
    (h : HasWindows {y | f y ≤ C * y ^ a} L) (hc : 0 ≤ c) (hab : a < b) :
    HasWindows {y | c * f y ≤ y ^ b} L := by
  have hmul : HasWindows {y | c * f y ≤ (c * C) * y ^ a} L :=
    h.mono fun _ hy ↦ (mul_le_mul_of_nonneg_left hy hc).trans_eq (mul_assoc _ _ _).symm
  exact hmul.rpow_bound_of_lt hab

/-- An eventual upper bound gives windows of any ratio at each strictly larger exponent. -/
theorem hasWindows_rpow_bound_of_eventually_le {f : ℝ → ℝ} {C a b : ℝ}
    (h : ∀ᶠ y in atTop, f y ≤ C * y ^ a) (hab : a < b) (L : ℝ) :
    HasWindows {y | f y ≤ y ^ b} L := by
  obtain ⟨Y, hY⟩ := h.exists_forall_of_atTop
  have hwindow : HasWindows {y | f y ≤ C * y ^ a} L := (hasWindows_Ici Y L).mono hY
  exact hwindow.rpow_bound_of_lt hab

/-- Normalized window bounds at every exponent above `σ` are equivalent to window bounds
with arbitrary coefficients at all exponents in any fixed interval `(σ, σ + δ)`. On both
sides the ratio may depend on the exponent. -/
theorem forall_exists_hasWindows_rpow_iff {f : ℝ → ℝ} {σ δ : ℝ} (hδ : 0 < δ) :
    (∀ ε > 0, ∃ L > 1, HasWindows {y | f y ≤ y ^ (σ + ε)} L) ↔
      ∀ ε > 0, ε < δ → ∃ L > 1, ∃ C : ℝ, HasWindows {y | f y ≤ C * y ^ (σ + ε)} L := by
  constructor
  · intro h ε hε _
    obtain ⟨L, hL, hw⟩ := h ε hε
    exact ⟨L, hL, 1, by simpa only [one_mul] using hw⟩
  · intro h ε hε
    obtain ⟨η, hη, hη'⟩ := exists_between (lt_min hε hδ)
    obtain ⟨L, hL, C, hw⟩ := h η hη (hη'.trans_le (min_le_right _ _))
    exact ⟨L, hL, hw.rpow_bound_of_lt (add_lt_add_right (hη'.trans_le (min_le_left _ _)) _)⟩

end TauCeti
