/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.DedekindEta.Kronecker
public import TauCeti.NumberTheory.ModularForms.DedekindEta.ScaledTransformation
import TauCeti.NumberTheory.ModularForms.Degeneracy.ConjScale

/-!
# Kronecker-symbol formulas for scaled eta multipliers

This module evaluates `TauCeti.ModularForm.etaMultiplier` on the `diag(δ, 1)`-conjugate
`TauCeti.conjScaleGamma0 hδ γ` of a matrix `γ ∈ Γ₀(N)` in terms of `TauCeti.kroneckerSym` and
`TauCeti.ModularForm.e24`.
-/

public section

open CongruenceSubgroup
open scoped MatrixGroups

namespace TauCeti.ModularForm

/-- For `γ = (a b; c d) ∈ Γ₀(N)` with `c = N t ≥ 0`, odd `d`, and `δ ∣ N`, the eta multiplier
of the conjugate `γ_δ = (a, δ b; (N / δ) t, d)` is
`((N / δ) t / d) · e(((a + d) (N / δ) t - b δ d (((N / δ) t)² - 1) + 3 d - 3 - 3 (N / δ) t d)`
`/ 24)`. -/
theorem etaMultiplier_conjScaleGamma0_of_c_nonneg_of_odd_d {N δ : ℕ} (hδ : δ ∣ N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) {t : ℤ} (ht : γ 1 0 = N * t) (hc : 0 ≤ γ 1 0) (hdo : Odd (γ 1 1)) :
    etaMultiplier (conjScaleGamma0 hδ ⟨γ, hγ⟩) =
      (kroneckerSym ((N / δ : ℕ) * t) (γ 1 1) : ℂ) *
        e24 ((γ 0 0 + γ 1 1) * ((N / δ : ℕ) * t) -
          γ 0 1 * δ * γ 1 1 * (((N / δ : ℕ) * t) ^ 2 - 1) + 3 * γ 1 1 - 3 -
          3 * ((N / δ : ℕ) * t) * γ 1 1) := by
  obtain ⟨h00, h01, h10, h11⟩ := conjScaleGamma0_entries_of_c_eq_mul hδ hγ ht
  have hc' : 0 ≤ ((N / δ : ℕ) : ℤ) * t := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · exact mul_nonneg (Int.natCast_nonneg _)
        (nonneg_of_mul_nonneg_right (ht ▸ hc) (Int.natCast_pos.mpr hN))
  rw [etaMultiplier_eq_kroneckerSym_mul_of_c_nonneg_of_odd_d _
    (by rw [h10]; exact hc') (by rw [h11]; exact hdo), h00, h01, h10, h11, e24_def]

end TauCeti.ModularForm
