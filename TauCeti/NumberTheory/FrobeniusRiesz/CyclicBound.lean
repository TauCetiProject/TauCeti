/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.FrobeniusRiesz.ErrorBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Restoring discarded characters in the Frobenius Riesz bound

The averaged Frobenius comparison controls the weighted remainder of the cyclic family
minus the absolute remainders of the discarded characters. If those characters each satisfy
a square-root bound with a small exponent loss, restoring them costs one further exponent
loss, at a cutoff independent of the host and its sizes.

This is the last estimation step of Levent Alpöge's `Deduction.ch_core` in
`Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean` and
`UpperTheory.Comparison₂.sigA_le` in `Development/AutomorphicArithmetic/PrimitiveCosets/SigALe.lean`
in the [published formalization][alpoege].

[alpoege]: https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005
-/

public section

open Filter Real

namespace TauCeti

/-- A Frobenius error bracket for the weighted family sum `Y` minus the discarded costs `R i`
gives `Y ≤ x ^ (1/2 + (C + 4) * ε)`. Each cost (in the application, the norm of a discarded
character's remainder) is at most `x ^ (1/2 + ε)`, and there are at most `D` costs.
The cutoff depends only on `D` and `ε`, not on the chain sizes or its loss exponent `C`.
Here `N`, `P`, and `T` count the ambient group, the tops, and the thick set, and `m` is the length
of the chain. The scale normalizer is `b`, the order bound is `a`, and the auxiliary rank is `k`. -/
theorem cyclic_bound_of_frobenius_error_bracket (D : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, 3 ≤ x₀ ∧ ∀ x ≥ x₀,
      ∀ {ι : Type*} (s : Finset ι) (R : ι → ℝ) (_ : s.card ≤ D)
      (_ : ∀ i ∈ s, R i ≤ x ^ (1 / 2 + ε))
      {C N P T m b a k Y : ℝ} (_ : 0 ≤ C) (_ : 0 < N) (_ : 0 < b)
      (_ : x ^ (1 / 2 - ε) ≤ m) (_ : m ≤ x ^ (1 / 2 + ε / 2))
      (_ : x * m ≤ k) (_ : k ≤ N ^ 2 * x ^ (1 / 2 - ε))
      (_ : x ^ (-ε / 8) * N / 2 ≤ P) (_ : x ^ (-ε) * N ≤ T) (_ : a ≤ 2 * x * b),
      P * m * b * (T / N / 2) * (Y - (∑ i ∈ s, R i) - 4 * x ^ (1 / 2 + ε)) ≤
        x ^ (C * ε) * (P * a * (1 + m ^ 2 / k) +
          m * (2 * N * m * b * x ^ ε + T * k * b * x ^ (2 * ε) / N ^ 2)) +
        2 * P * m * b / x →
      Y ≤ x ^ (1 / 2 + (C + 4) * ε) := by
  have hlarge := (tendsto_rpow_atTop (show 0 < 3 * ε / 8 by positivity)).eventually_ge_atTop 26
  have hcount := (tendsto_rpow_atTop hε).eventually_ge_atTop (1 + (D : ℝ))
  obtain ⟨x₀, hx₀⟩ := (hlarge.and hcount).exists_forall_of_atTop
  refine ⟨max 3 x₀, le_max_left .., fun x hx ι s R hs hR C N P T m b a k Y hC hN hb
    hmlo hmhi hklo hkhi hP hT ha h ↦ ?_⟩
  have hx₁ : 1 ≤ x := (by norm_num : (1 : ℝ) ≤ 3).trans ((le_max_left ..).trans hx)
  obtain ⟨hxlarge, hxcount⟩ := hx₀ x ((le_max_right ..).trans hx)
  have hcore := le_rpow_of_frobenius_error_bracket hx₁ hxlarge hC hN hb hmlo hmhi
    hklo hkhi hP hT ha h
  have hdiscard : (∑ i ∈ s, R i) ≤ (D : ℝ) * x ^ (1 / 2 + ε) := by
    have hsum := Finset.sum_le_card_nsmul s R _ hR
    have hcard := nsmul_le_nsmul_left (rpow_nonneg (zero_le_one.trans hx₁) (1 / 2 + ε)) hs
    simpa only [nsmul_eq_mul] using hsum.trans hcard
  calc
    Y ≤ x ^ (1 / 2 + (C + 3) * ε) + D * x ^ (1 / 2 + ε) := by linarith
    _ ≤ x ^ (1 / 2 + (C + 3) * ε) + D * x ^ (1 / 2 + (C + 3) * ε) := by
      gcongr
      nlinarith
    _ = (1 + (D : ℝ)) * x ^ (1 / 2 + (C + 3) * ε) := by ring
    _ ≤ x ^ ε * x ^ (1 / 2 + (C + 3) * ε) := by gcongr
    _ = x ^ (1 / 2 + (C + 4) * ε) := by
      rw [← rpow_add (zero_lt_one.trans_le hx₁)]
      congr 1
      ring

end TauCeti
