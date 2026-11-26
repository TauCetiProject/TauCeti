/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.ProperlyDiscontinuous
public import TauCeti.Topology.Algebra.GroupAction.Quotient

/-!
# Fundamental domains for discrete subgroups

A discrete subgroup of a second countable locally compact Hausdorff group has a measurable
fundamental domain for its left action, by
`MeasureTheory.Measure.exists_isFundamentalDomain_of_properlyDiscontinuousSMul`: translation is
free, so every point belongs to the free locus. If the orbit quotient is compact, a compact set
`K` meets every orbit, and the fundamental domain has measure at most `μ K` for any invariant
measure `μ` that is finite on compact sets.

## Main statements

* `Subgroup.exists_isFundamentalDomain_mul_left`: a measurable fundamental domain for the left
  action of a discrete subgroup, for every measure.
* `Subgroup.exists_isFundamentalDomain_measure_lt_top`: a measurable fundamental domain of finite
  measure when the quotient is compact and the invariant measure is finite on compact sets.

## Provenance

The statement of `Subgroup.exists_isFundamentalDomain_measure_lt_top` is adapted from
`New.isFiniteMeasure_quotMeasure_of_cocompact` (file `src/Lib/Adelic/QuotientMeasure/Basic.lean`)
in grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
There finiteness is stated for a quotient measure built from a cutoff weight; here it is stated
for a measurable fundamental domain. The proofs are new here.

## References

* Dave Witte Morris, *Introduction to Arithmetic Groups*, Deductive Press, 2015,
  Proposition 4.1.18.
-/

public section

open MeasureTheory Measure Set
open scoped ENNReal Pointwise

namespace Subgroup

variable {T : Type*} [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
  [SecondCountableTopology T] [T2Space T] (Λ : Subgroup T) [DiscreteTopology Λ]

/-- A discrete subgroup `Λ` of a second countable locally compact Hausdorff group `T` has a
measurable fundamental domain for its left action on `T`, for every measure. -/
theorem exists_isFundamentalDomain_mul_left [MeasurableSpace T] [OpensMeasurableSpace T]
    (μ : Measure T) :
    ∃ D : Set T, MeasurableSet D ∧ IsFundamentalDomain Λ D μ := by
  have : Countable Λ := countable_of_Lindelof_of_discrete
  have := Λ.properlyDiscontinuousSMul_of_tendsto_cofinite
    (Λ.tendsto_coe_cofinite_of_isDiscrete (isDiscrete_iff_discreteTopology.mpr ‹_›))
  -- Left multiplication is free, so every point lies in the free locus.
  have hfree : (TauCeti.freeLocus Λ T : Set T) = univ := by
    ext x
    simp [TauCeti.mem_freeLocus]
  obtain ⟨D, hDm, -, hD⟩ :=
    exists_isFundamentalDomain_of_properlyDiscontinuousSMul (G := Λ) μ (by simp [hfree])
  exact ⟨D, hDm, hD⟩

variable [CompactSpace (MulAction.orbitRel.Quotient Λ T)]

/-- A discrete subgroup `Λ` of a second countable locally compact Hausdorff group, with compact
quotient `Λ\T`, has a measurable fundamental domain of finite measure for its left action, for
every `Λ`-invariant measure that is finite on compact sets. -/
theorem exists_isFundamentalDomain_measure_lt_top [MeasurableSpace T] [BorelSpace T]
    (μ : Measure T) [SMulInvariantMeasure Λ T μ] [IsFiniteMeasureOnCompacts μ] :
    ∃ D : Set T, MeasurableSet D ∧ IsFundamentalDomain Λ D μ ∧ μ D < ∞ := by
  have : Countable Λ := countable_of_Lindelof_of_discrete
  obtain ⟨D, hDm, hD⟩ := Λ.exists_isFundamentalDomain_mul_left μ
  obtain ⟨K, hK, hKΛ⟩ :=
    TauCeti.MulAction.compactSpace_orbitRelQuotient_iff_exists_isCompact.mp ‹_›
  refine ⟨D, hDm, hD, lt_of_le_of_lt ?_ (hK.measure_lt_top (μ := μ))⟩
  -- The translates `g • K` cover `D`, and the pieces `g • K ∩ D` add up to `μ K`.
  calc μ D ≤ μ (⋃ g : Λ, g • K ∩ D) := measure_mono fun x hx ↦ by
          obtain ⟨g, hg⟩ := hKΛ x
          exact mem_iUnion.mpr ⟨g⁻¹, ⟨g • x, hg, inv_smul_smul g x⟩, hx⟩
    _ ≤ ∑' g : Λ, μ (g • K ∩ D) := measure_iUnion_le _
    _ = μ K := (hD.measure_eq_tsum K).symm

end Subgroup
