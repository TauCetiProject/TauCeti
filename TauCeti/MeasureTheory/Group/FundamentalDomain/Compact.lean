/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import TauCeti.Topology.Algebra.GroupAction.Quotient

/-!
# Finite measure of fundamental domains with compact orbit space

For a countable group acting by measurable homeomorphisms on a weakly locally compact space,
compactness of the orbit space forces every fundamental domain to have finite measure for any
invariant measure finite on compact sets. No discreteness or separation assumption is needed,
and the fundamental domain need only be null-measurable.

A compact set `K` meets every orbit by
`TauCeti.MulAction.compactSpace_orbitRelQuotient_iff_exists_isCompact`. Its translates cover the
fundamental domain `D`, and Mathlib's `MeasureTheory.IsFundamentalDomain.measure_eq_tsum` gives
`μ D ≤ ∑' g, μ (g • K ∩ D) = μ K < ∞`. This supplies finiteness independently of how `D` is
constructed, in particular for discrete subgroups acting by left multiplication.

## Main statements

* `MeasureTheory.IsFundamentalDomain.measure_lt_top_of_compactSpace`: every fundamental domain
  has finite measure when the orbit space is compact.

## Provenance

The statement is adapted from `New.isFiniteMeasure_quotMeasure_of_cocompact`
(file `src/Lib/Adelic/QuotientMeasure/Basic.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
There finiteness concerns a cutoff-weighted quotient measure of a discrete subgroup; here it
concerns any fundamental domain of a countable group action. The proof is new here.

## References

* Dave Witte Morris, *Introduction to Arithmetic Groups*, Deductive Press, 2015,
  Proposition 4.1.18.
-/

public section

open MeasureTheory Measure Set
open scoped ENNReal Pointwise

namespace MeasureTheory.IsFundamentalDomain

variable {G X : Type*} [Group G] [Countable G] [MulAction G X] [TopologicalSpace X]
  [WeaklyLocallyCompactSpace X] [ContinuousConstSMul G X] [MeasurableSpace X]
  [MeasurableConstSMul G X] {μ : Measure X} [SMulInvariantMeasure G X μ]
  [IsFiniteMeasureOnCompacts μ] [CompactSpace (MulAction.orbitRel.Quotient G X)] {D : Set X}

/-- Every fundamental domain of a countable group action with compact orbit space has finite
measure for an invariant measure finite on compact sets, on a weakly locally compact space. -/
theorem measure_lt_top_of_compactSpace (hD : IsFundamentalDomain G D μ) : μ D < ∞ := by
  obtain ⟨K, hK, hKG⟩ :=
    TauCeti.MulAction.compactSpace_orbitRelQuotient_iff_exists_isCompact.mp ‹_›
  refine lt_of_le_of_lt ?_ (hK.measure_lt_top (μ := μ))
  -- The translates `g • K` cover `D`, and the pieces `g • K ∩ D` add up to `μ K`.
  calc μ D ≤ μ (⋃ g : G, g • K ∩ D) := measure_mono fun x hx ↦ by
          obtain ⟨g, hg⟩ := hKG x
          exact mem_iUnion.mpr ⟨g⁻¹, ⟨g • x, hg, inv_smul_smul g x⟩, hx⟩
    _ ≤ ∑' g : G, μ (g • K ∩ D) := measure_iUnion_le _
    _ = μ K := (hD.measure_eq_tsum K).symm

end MeasureTheory.IsFundamentalDomain
