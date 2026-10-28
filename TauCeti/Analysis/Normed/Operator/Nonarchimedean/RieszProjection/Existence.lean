/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Basic
public import TauCeti.RingTheory.PowerSeries.Entire.GoodZero.Field

/-!
# Riesz projectors at arbitrary scalars over a field

Over a complete ultrametric field, the Fredholm series of a row-compact operator
is nonzero and entire. Its order at every scalar is therefore finite, so the
Riesz projector construction applies without a supplied good-zero hypothesis.
The order is positive exactly at zeros of the Fredholm series.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS 12 (1962), §7, Proposition 12.
-/

public section

open scoped ZeroAtInfty

namespace ContinuousLinearMap

variable {K I : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  {u : C₀(I, K) →L[K] C₀(I, K)}

/-- At every scalar, a row-compact operator over a field has a Riesz projector
at the uniquely determined finite order of its Fredholm series. Away from its
zeros this order is zero and the finite spectral summand is zero. -/
theorem IsRowCompact.exists_isRieszProjection (hu : u.IsRowCompact) (a : K) :
    ∃ h : ℕ, u.matrixCoeff.charPowerSeries.IsGoodZero a h ∧
      IsRieszProjection u a h (u.rieszProjection a h) := by
  have hne : u.matrixCoeff.charPowerSeries ≠ 0 := by
    intro hzero
    have := Matrix.constantCoeff_charPowerSeries u.matrixCoeff
    rw [hzero, map_zero] at this
    exact zero_ne_one this
  obtain ⟨h, hh, _⟩ := hu.isEntire_charPowerSeries.existsUnique_isGoodZero hne a
  exact ⟨h, hh, hu.isRieszProjection_rieszProjection
    (fun j hj ↦ hh.evalAt_hasseDeriv_eq_zero hj) hh.isUnit_evalAt_hasseDeriv⟩

end ContinuousLinearMap
