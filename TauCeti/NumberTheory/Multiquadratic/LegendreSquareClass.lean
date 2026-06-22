/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.NumberTheory.LegendreSymbol.SquareClass

/-!
# Square-class changes of multiquadratic radicands

The prime-splitting law for multiquadratic fields is naturally stated for square classes:
replacing each radicand `d i` by `d i * u i ^ 2`, with `p ∤ u i`, changes neither its Legendre
symbol modulo `p` nor whether `p` divides it. This file packages the single-variable invariance
of `TauCeti.NumberTheory.LegendreSymbol.SquareClass` as indexed-family wrappers in the form
consumed by the multiquadratic splitting theorem, where each radicand is given by an equation
`e i = d i * u i ^ 2`.

The main point is `forall_legendreSym_eq_of_forall_eq_mul_sq`; the residue-condition and
unramifiedness companions show that `legendreSym p (d i) = 1` and `p ∤ d i` are likewise
invariant under the same square-class change.
-/

namespace TauCeti.Multiquadratic

variable {p : ℕ} [Fact p.Prime]

/-- Replacing each radicand in a family by `d i * u i ^ 2` with `p ∤ u i` preserves all the
Legendre symbols pointwise. -/
theorem forall_legendreSym_eq_of_forall_eq_mul_sq {ι : Type*} {d e u : ι → ℤ}
    (he : ∀ i, e i = d i * u i ^ 2) (hu : ∀ i, ¬ (p : ℤ) ∣ u i) :
    ∀ i, legendreSym p (e i) = legendreSym p (d i) := fun i => by
  rw [he i, legendreSym_mul_sq (hu i)]

/-- The quadratic-residue conditions of a family are unchanged by replacing each radicand by
`d i * u i ^ 2` with `p ∤ u i`. -/
theorem forall_legendreSym_eq_one_iff_of_forall_eq_mul_sq {ι : Type*} {d e u : ι → ℤ}
    (he : ∀ i, e i = d i * u i ^ 2) (hu : ∀ i, ¬ (p : ℤ) ∣ u i) :
    (∀ i, legendreSym p (e i) = 1) ↔ ∀ i, legendreSym p (d i) = 1 := by
  simp_rw [he, legendreSym_mul_sq (p := p) (hu _)]

/-- The unramifiedness conditions of a family are unchanged by replacing each radicand by
`d i * u i ^ 2` with `p ∤ u i`. -/
theorem forall_not_dvd_iff_of_forall_eq_mul_sq {ι : Type*} {d e u : ι → ℤ}
    (he : ∀ i, e i = d i * u i ^ 2) (hu : ∀ i, ¬ (p : ℤ) ∣ u i) :
    (∀ i, ¬ (p : ℤ) ∣ e i) ↔ ∀ i, ¬ (p : ℤ) ∣ d i := by
  simp_rw [he, not_dvd_mul_sq_iff (p := p) (hu _)]

end TauCeti.Multiquadratic
