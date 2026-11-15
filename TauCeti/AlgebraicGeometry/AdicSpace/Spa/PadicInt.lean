/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.DiscreteValuationRing
public import TauCeti.RingTheory.Huber.Padic.Basic

import Mathlib.NumberTheory.Padics.RingHoms

/-!
# The adic spectrum of `ℤ_p`

The `p`-adic integers form a Huber ring that is not Tate
(`TauCeti.Huber.PadicInt.not_isTateRing`), and their adic spectrum shows the difference: it has
a non-analytic point. Precisely, `Cont ℤ_p` has exactly two points, the `p`-adic valuation `η`
(the adic valuation `intValuation` of the maximal ideal `pℤ_p`) and the trivial valuation `s` of
the maximal ideal, the first analytic and the second not. Since `ℤ` is dense in `ℤ_p`, every
continuous valuation is at most `1` on `ℤ_p`, so `Spa (ℤ_p, A⁺) = Cont ℤ_p` for every plus ring
`A⁺`. These are the discrete valuation ring results of
`TauCeti.AlgebraicGeometry.AdicSpace.Spa.DiscreteValuationRing` for `R = ℤ_p`.

## Main results

* `TauCeti.ValuationSpectrum.cont_padicInt`: `Cont ℤ_p = {η, s}`.
* `TauCeti.ValuationSpectrum.spa_padicInt`: `Spa (ℤ_p, A⁺) = {η, s}` for every subring `A⁺`.
* `TauCeti.ValuationSpectrum.spaAnalytic_padicInt`: the analytic locus of `Spa (ℤ_p, A⁺)` is `{η}`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 7.23 for `Spa` and
  Definition 7.39 for analytic points.
-/

public section

namespace TauCeti.ValuationSpectrum

open IsLocalRing

variable {p : ℕ} [Fact p.Prime]

/-- **The continuous valuations on `ℤ_p`**: `Cont ℤ_p` consists of the `p`-adic valuation and the
trivial valuation of the maximal ideal. -/
theorem cont_padicInt :
    cont ℤ_[p] = {ofValuation (_root_.IsDiscreteValuationRing.maximalIdeal ℤ_[p]).intValuation,
      trivialSection (⊤ : PrimeSpectrum ℤ_[p])} := by
  rw [← spa_eq_cont_of_denseRange_intCast PadicInt.denseRange_intCast ⊤,
    IsDiscreteValuationRing.spa_top_eq Huber.PadicInt.isAdic_maximalIdeal]

/-- **The adic spectrum of `ℤ_p`**: for every plus ring `A⁺`, `Spa (ℤ_p, A⁺)` consists of the
`p`-adic valuation and the trivial valuation of the maximal ideal. -/
theorem spa_padicInt (Aplus : Subring ℤ_[p]) :
    spa Aplus = {ofValuation (_root_.IsDiscreteValuationRing.maximalIdeal ℤ_[p]).intValuation,
      trivialSection (⊤ : PrimeSpectrum ℤ_[p])} := by
  rw [spa_eq_cont_of_denseRange_intCast PadicInt.denseRange_intCast, cont_padicInt]

/-- **The analytic locus of `Spa (ℤ_p, A⁺)`** is the single point of the `p`-adic valuation, for
every plus ring `A⁺`; the trivial valuation of the maximal ideal is a non-analytic point. -/
theorem spaAnalytic_padicInt (Aplus : Subring ℤ_[p]) :
    spaAnalytic Aplus =
      {ofValuation (_root_.IsDiscreteValuationRing.maximalIdeal ℤ_[p]).intValuation} := by
  have hR := Huber.PadicInt.isAdic_maximalIdeal (p := p)
  rw [spaAnalytic_def, spa_padicInt, ← IsDiscreteValuationRing.spa_top_eq hR, ← spaAnalytic_def,
    IsDiscreteValuationRing.spaAnalytic_top_eq hR]

end TauCeti.ValuationSpectrum
