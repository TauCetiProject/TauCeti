/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.HilbertSamuel

/-!
# Hilbert–Samuel stabilization in resolution of singularities

This module provides `TauCeti.hsLexStabilization`, specializing
`TauCeti.exists_forall_ge_localQuotientHilbertSamuel_eq_of_toLex_le` to sequences of ideals in a
fixed multivariate formal power series ring `MvPowerSeries (Fin n) K`, with the lexicographic
hypothesis expressed using `Pi.Lex`.

## Main results

* `TauCeti.hsLexStabilization`: lexicographic stabilization of realized Hilbert–Samuel functions in
  `MvPowerSeries (Fin n) K`.

## References

* Edward Bierstone and Pierre D. Milman, *Uniformization of analytic spaces*, J. Amer. Math. Soc.
  2 (1989), 801–836, Theorem 5.2.1, pp. 820–821.
* Edward Bierstone, Pierre D. Milman, and Michael Temkin, *𝒬-universal desingularization*,
  Asian J. Math. 15 (2011), 229–250, §6.1.
-/

public section

namespace TauCeti

/-- **Lexicographic Hilbert–Samuel stabilization** in `MvPowerSeries (Fin n) K`: every
lexicographically nonincreasing sequence of realized Hilbert–Samuel functions stabilizes. -/
theorem hsLexStabilization (K : Type*) [Field K] (n : ℕ)
    (I : ℕ → Ideal (MvPowerSeries (Fin n) K))
    (h : ∀ j, (I (j + 1)).localQuotientHilbertSamuel = (I j).localQuotientHilbertSamuel ∨
      Pi.Lex (· < ·) (· < ·) (I (j + 1)).localQuotientHilbertSamuel
        (I j).localQuotientHilbertSamuel) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      (I j).localQuotientHilbertSamuel = (I j₀).localQuotientHilbertSamuel :=
  exists_forall_ge_localQuotientHilbertSamuel_eq_of_toLex_le I fun j ↦
    le_iff_eq_or_lt.mpr ((h j).imp (congrArg toLex) id)

end TauCeti
