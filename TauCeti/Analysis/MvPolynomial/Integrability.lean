/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import TauCeti.Analysis.MvPolynomial.PolynomialSpace
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Integrability of bounded-degree polynomial functions

Every real polynomial function of bounded total degree on finite-dimensional `EuclideanSpace ℝ ι`
is continuous, hence bounded on the compact closure of any bounded set `Ω`. Consequently it lies
in `Lᵖ(μ.restrict Ω)` for every exponent `p : ℝ≥0∞` and every Borel measure `μ` that is finite on
compact sets (`TauCeti.memLp_restrict_of_mem_polynomialsDegLE_of_isBounded`), without requiring
`Ω` itself to be measurable.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

/-- Every bounded-degree polynomial function belongs to `Lᵖ(μ.restrict Ω)` on any bounded set `Ω`
under any Borel measure `μ` finite on compact sets and any exponent `p : ℝ≥0∞`. -/
theorem memLp_restrict_of_mem_polynomialsDegLE_of_isBounded
    {ι : Type*} [Finite ι] {μ : Measure (EuclideanSpace ℝ ι)} [IsFiniteMeasureOnCompacts μ]
    {m : ℕ} {q : EuclideanSpace ℝ ι → ℝ} (hq : q ∈ polynomialsDegLE ι m)
    {Ω : Set (EuclideanSpace ℝ ι)} (hΩ : Bornology.IsBounded Ω) (p : ℝ≥0∞) :
    MemLp q p (μ.restrict Ω) := by
  have := Fintype.ofFinite ι
  exact ((contDiff_of_mem_polynomialsDegLE hq (n := 0)).continuous.continuousOn
    |>.memLp_restrict_of_subset_isCompact hΩ.isCompact_closure measurableSet_closure
    Subset.rfl p).mono_measure (Measure.restrict_mono subset_closure le_rfl)

end TauCeti
