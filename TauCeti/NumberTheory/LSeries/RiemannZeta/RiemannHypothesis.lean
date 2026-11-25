/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import TauCeti.NumberTheory.LSeries.RiemannZeta.Meromorphic
import TauCeti.NumberTheory.LSeries.RiemannZeta.FunctionalEquation

/-!
# The Riemann hypothesis as a zero-free half-plane

Mathlib's `RiemannHypothesis` says that every zero of `riemannZeta` other than a trivial zero
`-2(n + 1)` and the point `1` has real part `1/2`. This file proves that it says exactly that
`riemannZeta` is zero-free right of `1/2`, in the order form `TauCeti.ZeroFreeRightOf (1 / 2)`
and in the value form `∀ s, 1/2 < re s → riemannZeta s ≠ 0`.

The value form needs no exception `s ≠ 1`, because Mathlib's junk value `riemannZeta 1` is not
`0`; the order form never reads it, since `riemannZeta` has order `-1` at `1`
(`TauCeti.meromorphicOrderAt_riemannZeta_one`). The two forms agree right of every `σ`
(`TauCeti.zeroFreeRightOf_riemannZeta_iff`).

To pass from a zero-free half-plane to the Riemann hypothesis, the functional equation reflects
a zero `s` that is not a trivial zero to the zero `1 - s` (`TauCeti.riemannZeta_one_sub_eq_zero`).
So ruling out zeros right of the critical line also rules out nontrivial zeros left of it.

The divisor form of the same hypothesis, through the completed zeta function, is
`TauCeti.LFunctions.allOnCriticalLine_completedRiemannZeta_iff`.

## Main results

* `TauCeti.riemannHypothesis_iff_riemannZeta_ne_zero`:
  `RiemannHypothesis ↔ ∀ s, 1/2 < re s → riemannZeta s ≠ 0`.
* `TauCeti.riemannHypothesis_iff_zeroFreeRightOf`:
  `RiemannHypothesis ↔ ZeroFreeRightOf (1 / 2) riemannZeta`.

## References

* Levent Alpöge, Lean formalization of the Riemann hypothesis,
  https://github.com/leanprover-community/riemann-hypothesis (commit
  40e56bab026552e089d7afcfeff08d2defb9c005), `Formalism.VW.rh_of_right` in
  `src/Formalism/GammaFactorNonvanishing/RhOfRight.lean`: the source of the statement of the
  direction to `RiemannHypothesis` from the value form. The Lean proof here, by the reflection
  route described above, was written independently of it.
* David Loeffler, `RiemannHypothesis` in `Mathlib.NumberTheory.LSeries.RiemannZeta`.
-/

public section

open Complex

namespace TauCeti

/-- **The Riemann hypothesis**, value form: it holds exactly when `riemannZeta` has no zero with
real part greater than `1/2`. No exception `s ≠ 1` is needed, as Mathlib's junk value
`riemannZeta 1` is not `0`. -/
theorem riemannHypothesis_iff_riemannZeta_ne_zero :
    RiemannHypothesis ↔ ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0 := by
  refine ⟨fun h s hre hs => ?_, fun h s hs htriv _ => ?_⟩
  · have hs1 : s ≠ 1 := by
      rintro rfl
      exact riemannZeta_one_ne_zero hs
    -- a trivial zero `-2(n + 1)` has negative real part
    have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := fun ⟨n, hn⟩ => by
      have : s.re = -2 * (n + 1) := by simp [hn]
      linarith [n.cast_nonneg (α := ℝ)]
    linarith [h s hs htriv hs1]
  · refine le_antisymm (not_lt.mp fun hgt => h s hgt hs) (not_lt.mp fun hlt => ?_)
    -- a zero left of the line is reflected to the zero `1 - s` right of it
    exact h (1 - s) (by simp only [sub_re, one_re]; linarith) (riemannZeta_one_sub_eq_zero hs htriv)

/-- **The Riemann hypothesis**, order form: it holds exactly when `riemannZeta` is zero-free right
of `1/2`, that is, when its meromorphic order is at most `0` at every `s` with `1/2 < re s`.
The pole at `1`, of order `-1`, is allowed. -/
theorem riemannHypothesis_iff_zeroFreeRightOf :
    RiemannHypothesis ↔ ZeroFreeRightOf (1 / 2) riemannZeta := by
  rw [riemannHypothesis_iff_riemannZeta_ne_zero, zeroFreeRightOf_riemannZeta_iff]

end TauCeti
