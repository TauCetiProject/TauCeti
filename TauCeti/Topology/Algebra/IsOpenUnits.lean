/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Topology.Algebra.IsOpenUnits
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Rings with open units: the inverse and embeddings

A topological monoid `M` has open units (`IsOpenUnits M`) when `Units.val : Mˣ → M` is an open
embedding: the units are open and inversion is continuous on them for the subspace topology.
In a monoid with zero with open units, `Ring.inverse` is therefore continuous at every unit.
The property passes along embeddings: a monoid embedded in one with open units has open units as
soon as its own units form an open subset.

In a topological ring with open units, a topologically nilpotent element `x`, one whose powers
tend to zero, has `1 - x` invertible, and the partial geometric sums `1 + x + ⋯ + x ^ (n - 1)`
tend to the inverse of `1 - x`. No norm is assumed. For square
matrices over `ℝ` or `ℂ` this is the Neumann series of a matrix whose powers tend to zero, which
governs the limit of a stationary iteration `x ↦ G x + c`.

## Main declarations

* `IsOpenUnits.continuousAt_ringInverse`: `Ring.inverse` is continuous at every unit of a ring
  with open units.
* `IsOpenUnits.of_isEmbedding`: a monoid embedding into a monoid with open units whose units
  form an open subset has open units.
* `Units.instLocallyPathConnectedSpace`: the units of a locally path-connected monoid with open
  units are locally path connected; for instance the units of a real Banach algebra.
* `IsTopologicallyNilpotent.isUnit_one_sub_of_isOpenUnits`: if `x ^ n → 0`, then `1 - x` is a
  unit.
* `IsTopologicallyNilpotent.tendsto_geom_sum_of_isOpenUnits`: if `x ^ n → 0`, then the partial
  geometric sums of `x` tend to `Ring.inverse (1 - x)`.
-/

public section

open Filter Finset Topology

/-- A topological monoid `M` has open units if it embeds, by a monoid homomorphism that is a
topological embedding, into a monoid with open units, and its units form an open subset of `M`.
For instance, the valuation ring of a field whose topology is defined by its valuation. -/
theorem IsOpenUnits.of_isEmbedding {M N : Type*} [Monoid M] [TopologicalSpace M] [Monoid N]
    [TopologicalSpace N] [IsOpenUnits N] {f : M →* N} (hf : IsEmbedding f)
    (h : IsOpen {x : M | IsUnit x}) : IsOpenUnits M where
  isOpenEmbedding_unitsVal := by
    refine ⟨?_, h⟩
    have e : (f : M → N) ∘ Units.val = Units.val ∘ Units.map f :=
      funext fun u ↦ (Units.coe_map f u).symm
    have : IsEmbedding ((f : M → N) ∘ Units.val) := by
      rw [e]
      exact IsOpenUnits.isOpenEmbedding_unitsVal.isEmbedding.comp hf.units_map
    exact this.of_comp Units.continuous_val hf.continuous

/-- The units of a locally path-connected topological monoid with open units are locally path
connected, being an open subspace. For instance, the units of a real Banach algebra. -/
instance Units.instLocallyPathConnectedSpace {M : Type*} [Monoid M] [TopologicalSpace M]
    [IsOpenUnits M] [LocallyPathConnectedSpace M] : LocallyPathConnectedSpace Mˣ :=
  IsOpenUnits.isOpenEmbedding_unitsVal.locallyPathConnectedSpace

variable {R : Type*} [MonoidWithZero R] [TopologicalSpace R] [IsOpenUnits R]

/-- In a monoid with zero whose units are open with continuous inversion, `Ring.inverse` is
continuous at every unit. -/
theorem IsOpenUnits.continuousAt_ringInverse (u : Rˣ) : ContinuousAt Ring.inverse (u : R) := by
  rw [← IsOpenUnits.isOpenEmbedding_unitsVal.continuousAt_iff]
  have : (Ring.inverse ∘ Units.val : Rˣ → R) = fun v ↦ ↑v⁻¹ := by
    funext v
    exact Ring.inverse_unit v
  rw [this]
  exact Units.continuous_coe_inv.continuousAt

section Ring

variable {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] [IsOpenUnits R] {x : R}

/-- In a topological ring with open units, if `x` is topologically nilpotent, then `1 - x` is a
unit. -/
theorem IsTopologicallyNilpotent.isUnit_one_sub_of_isOpenUnits
    (hx : IsTopologicallyNilpotent x) : IsUnit (1 - x) := by
  have h1 : Tendsto (fun n ↦ 1 - x ^ n) atTop (𝓝 (1 : R)) := by
    simpa using tendsto_const_nhds.sub hx
  obtain ⟨m, hm⟩ := (h1.eventually
    (IsOpenUnits.isOpenEmbedding_unitsVal.isOpen_range.mem_nhds ⟨1, rfl⟩)).exists
  have hcomm : Commute (1 - x) (∑ i ∈ range m, x ^ i) :=
    (mul_neg_geom_sum x m).trans (geom_sum_mul_neg x m).symm
  rw [← mul_neg_geom_sum x m] at hm
  obtain ⟨u, hu⟩ := hm
  exact (hcomm.isUnit_mul_iff.1 ⟨u, hu⟩).1

/-- In a topological ring with open units, if `x` is topologically nilpotent, then the partial
geometric sums `∑ i ∈ range n, x ^ i` tend to the inverse of `1 - x`. -/
theorem IsTopologicallyNilpotent.tendsto_geom_sum_of_isOpenUnits
    (hx : IsTopologicallyNilpotent x) :
    Tendsto (fun n ↦ ∑ i ∈ range n, x ^ i) atTop (𝓝 (Ring.inverse (1 - x))) := by
  obtain ⟨u, hu⟩ := hx.isUnit_one_sub_of_isOpenUnits
  have hsum (n : ℕ) : ∑ i ∈ range n, x ^ i = Ring.inverse (1 - x) * (1 - x ^ n) := by
    rw [← mul_neg_geom_sum x n, ← mul_assoc, ← hu, Ring.inverse_mul_cancel _ u.isUnit, one_mul]
  simp_rw [hsum]
  simpa using ((tendsto_const_nhds (x := (1 : R))).sub hx).const_mul (Ring.inverse (1 - x))

end Ring
