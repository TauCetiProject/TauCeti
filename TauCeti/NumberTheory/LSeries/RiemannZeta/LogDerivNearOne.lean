/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The logarithmic derivative of the Riemann zeta function near `s = 1`

The function `ζ′/ζ(s) + (s - 1)⁻¹` is bounded on every compact subset of the closed half-plane
`1 ≤ re s`, punctured at `s = 1`. In particular there is one absolute constant `C` with
`‖-ζ′/ζ(1 + η) - η⁻¹‖ ≤ C` for all `0 < η ≤ 1`.

The proof identifies `ζ′/ζ(s) + (s - 1)⁻¹` with the logarithmic derivative of the regularized
function `(s - 1) ζ(s)`, which is Mathlib's `DirichletCharacter.LFunctionTrivChar₁` at level one.
Its negative logarithmic derivative is continuous wherever `ζ` does not vanish, including at `s = 1`
(`DirichletCharacter.continuousOn_neg_logDeriv_LFunctionTrivChar₁`), and `ζ` has no zero on
`1 ≤ re s` (`riemannZeta_ne_zero_of_one_le_re`).
-/

public section

open Complex DirichletCharacter

namespace TauCeti

/-- Away from `s = 1` and the zeros of `ζ`, `ζ′/ζ(s) + (s - 1)⁻¹` is the logarithmic derivative of
the regularized function `(s - 1) ζ(s)`. -/
theorem logDeriv_riemannZeta_add_inv_sub_one {s : ℂ} (hs : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    logDeriv riemannZeta s + (s - 1)⁻¹ = logDeriv (LFunctionTrivChar₁ 1) s := by
  have hs' : s - 1 ≠ 0 := sub_ne_zero_of_ne hs
  rw [logDeriv_apply, logDeriv_apply, deriv_LFunctionTrivChar₁_apply_of_ne_one _ hs,
    LFunctionTrivChar₁, Function.update_of_ne hs, LFunctionTrivChar, LFunction_modOne_eq]
  field_simp

end TauCeti

/-- On a compact subset of the closed half-plane `1 ≤ re s`, the function `ζ′/ζ(s) + (s - 1)⁻¹`
is bounded away from `s = 1`. -/
theorem IsCompact.exists_norm_logDeriv_riemannZeta_add_inv_sub_one_le {K : Set ℂ}
    (hK : IsCompact K) (hK₁ : K ⊆ {s | 1 ≤ s.re}) :
    ∃ C, ∀ s ∈ K, s ≠ 1 → ‖logDeriv riemannZeta s + (s - 1)⁻¹‖ ≤ C := by
  have hcont := (continuousOn_neg_logDeriv_LFunctionTrivChar₁ 1).mono fun s hs ↦ by
    rcases eq_or_ne s 1 with rfl | _
    · exact .inl rfl
    · refine .inr ?_
      rw [LFunctionTrivChar, LFunction_modOne_eq]
      exact riemannZeta_ne_zero_of_one_le_re (hK₁ hs)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨C, fun s hs hs₁ ↦ ?_⟩
  have := hC s hs
  rwa [neg_div, norm_neg, ← logDeriv_apply, ← TauCeti.logDeriv_riemannZeta_add_inv_sub_one hs₁
    (riemannZeta_ne_zero_of_one_le_re (hK₁ hs))] at this

namespace TauCeti

/-- **The pole of `-ζ′/ζ` at `s = 1`.** One absolute constant `C` satisfies
`‖-ζ′/ζ(1 + η) - η⁻¹‖ ≤ C` for every `0 < η ≤ 1`. -/
theorem exists_norm_neg_logDeriv_riemannZeta_one_add_sub_inv_le :
    ∃ C, ∀ η : ℝ, 0 < η → η ≤ 1 → ‖-logDeriv riemannZeta (1 + η) - (η : ℂ)⁻¹‖ ≤ C := by
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).image
    (continuous_const.add continuous_ofReal)).exists_norm_logDeriv_riemannZeta_add_inv_sub_one_le
      (K := (fun η : ℝ ↦ 1 + (η : ℂ)) '' Set.Icc 0 1) (by
        rintro _ ⟨η, hη, rfl⟩
        simpa using hη.1)
  refine ⟨C, fun η hη hη₁ ↦ ?_⟩
  have := hC _ ⟨η, ⟨hη.le, hη₁⟩, rfl⟩ (by simpa using hη.ne')
  rwa [add_sub_cancel_left, ← norm_neg, neg_add] at this

end TauCeti
