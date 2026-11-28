/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Degeneracy

/-!
# Entry formulas for `conjScaleGamma0`

This module records entrywise formulas for the `diag(δ, 1)`-conjugate `TauCeti.conjScaleGamma0`
when the lower-left entry of `γ ∈ Γ₀(N)` is written explicitly as `N * t`.
-/

public section

open CongruenceSubgroup
open scoped MatrixGroups

namespace TauCeti

/-- The entries of `conjScaleGamma0 hδ γ = (a, δ b; (N / δ) t, d)` when `c = N t` and `δ ∣ N`. -/
lemma conjScaleGamma0_entries_of_c_eq_mul {N δ : ℕ} (hδ : δ ∣ N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) {t : ℤ} (ht : γ 1 0 = N * t) :
    conjScaleGamma0 hδ ⟨γ, hγ⟩ 0 0 = γ 0 0 ∧
      conjScaleGamma0 hδ ⟨γ, hγ⟩ 0 1 = γ 0 1 * δ ∧
      conjScaleGamma0 hδ ⟨γ, hγ⟩ 1 0 = (N / δ : ℕ) * t ∧
      conjScaleGamma0 hδ ⟨γ, hγ⟩ 1 1 = γ 1 1 := by
  rcases eq_or_ne δ 0 with rfl | hδ0
  · obtain rfl := Nat.eq_zero_of_zero_dvd hδ
    simp [ht]
  · have hmul : (δ : ℤ) * (N / δ : ℕ) = N := by exact_mod_cast Nat.mul_div_cancel' hδ
    have hc : γ 1 0 = δ * ((N / δ : ℕ) * t) := by rw [ht, ← mul_assoc, hmul]
    refine ⟨by simp, by simp [mul_comm],
      by simp [hc, Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr hδ0)], by simp⟩

end TauCeti
