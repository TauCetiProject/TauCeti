/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Basic

/-!
# Reverse martingale infrastructure (finite horizon)

Reversing time on a finite horizon `N` turns an antitone family of σ-algebras `𝔽` into a
*forward* filtration `revFiltration`, on which the time-reversed conditional-expectation process
`n ↦ μ[f | 𝔽 (N - n)]` is a genuine forward martingale (via Mathlib's `martingale_condExp`). This
finite-horizon reversal is the base step of the reverse (Lévy-downward) martingale convergence
argument.

## Main definitions

- `revFiltration`: the time-reversed filtration on a finite horizon `N` (`k ↦ 𝔽 (N - k)`).

Adapted from `cameronfreer/exchangeability` (`Probability/Martingale/Reverse.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`). Written Mathlib-shaped for eventual upstreaming.
-/

public section

noncomputable section

open MeasureTheory

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- Reverse filtration on a finite horizon `N`: its level `n` is `𝔽 (N - n)`. Used for
finite-horizon time reversal of an antitone family `𝔽`. -/
def revFiltration (𝔽 : ℕ → MeasurableSpace Ω) (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ m0)
    (N : ℕ) : Filtration ℕ m0 where
  seq n := 𝔽 (N - n)
  mono' := Antitone.comp h_antitone antitone_const_tsub
  le' _ := h_le _

/-- Levels of the reverse filtration: `revFiltration 𝔽 … N` at `n` is `𝔽 (N - n)`. -/
@[simp]
lemma revFiltration_apply (𝔽 : ℕ → MeasurableSpace Ω) (h_antitone : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ m0) (N n : ℕ) : (revFiltration 𝔽 h_antitone h_le N) n = 𝔽 (N - n) :=
  (rfl)

end MeasureTheory
