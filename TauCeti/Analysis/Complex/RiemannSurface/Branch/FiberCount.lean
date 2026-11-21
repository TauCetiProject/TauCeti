/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Branch.Values
public import TauCeti.GroupTheory.Perm.OrbitCount.Basic

/-!
# Counting the points removed above branch values

For a finite holomorphic map `f` from a compact Riemann surface to a connected
Riemann surface, the preimage of a finite set `S` has `degree f * S.ncard` points counted
with multiplicity. Its ordinary cardinality is smaller by the sum of `e_x - 1` over that
preimage, where `e_x` is the local multiplicity. If `S` contains all branch values, this
sum is the entire ramification degree:

`(f ⁻¹' S).ncard + ramificationDegree f = degree f * S.ncard`.

In particular this counts the points deleted in the source when the branch values are
deleted from the target. Together with the covering over the complement of the branch
values, it supplies the numerical correction in the branched-cover Euler-characteristic
formula. Allowing a finite superset of the branch values also permits additional punctures
when choosing a topological decomposition.

## Main results

* `FiniteHolomorphicMap.ncard_preimage_add_ramificationDegree`: the count over a finite set
  containing every branch value.
* `FiniteHolomorphicMap.ncard_preimage_branchValues_add_ramificationDegree`: the count over
  the branch values themselves.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §17 (the topological proof of the Riemann–Hurwitz formula).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter II §4.
-/

public section

open Set
open scoped Manifold

namespace TauCeti.RiemannSurface.FiniteHolomorphicMap

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- If the local multiplicities of `f` on the fibre over `y` match `fullCycleType σ`, the fibre
finset has cardinality `orbitCount σ`. -/
theorem card_finite_fiber_eq_orbitCount (f : FiniteHolomorphicMap X Y) {α : Type*}
    [Fintype α] [DecidableEq α] {y : Y} {σ : Equiv.Perm α}
    (h : (f.finite_fiber y).toFinset.val.map (localMultiplicity f) = Equiv.Perm.fullCycleType σ) :
    (f.finite_fiber y).toFinset.card = orbitCount σ := by
  have hc := congrArg Multiset.card h
  rwa [Multiset.card_map, Finset.card_val, Equiv.Perm.fullCycleType_def,
    ← Equiv.Perm.orbitCount_eq_card_parts_partition] at hc

/-- If the local multiplicities of `f` on the fibre over `y` match `fullCycleType σ`, then
`(f ⁻¹' {y}).ncard` equals `orbitCount σ`. -/
theorem ncard_preimage_singleton_eq_orbitCount (f : FiniteHolomorphicMap X Y) {α : Type*}
    [Fintype α] [DecidableEq α] {y : Y} {σ : Equiv.Perm α}
    (h : (f.finite_fiber y).toFinset.val.map (localMultiplicity f) = Equiv.Perm.fullCycleType σ) :
    (f ⁻¹' {y}).ncard = orbitCount σ :=
  (ncard_eq_toFinset_card _ (f.finite_fiber y)).trans (f.card_finite_fiber_eq_orbitCount h)

variable [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]
  [CompactSpace X] [T2Space X] [T2Space Y] [PreconnectedSpace Y]

/-- Above a finite set containing all branch values, the defect in the number of distinct
points is exactly the total ramification degree. Extra unramified values do not change the
defect. -/
theorem ncard_preimage_add_ramificationDegree (f : FiniteHolomorphicMap X Y)
    {S : Set Y} (hS : S.Finite) (hbranch : f.branchValues ⊆ S) :
    (f ⁻¹' S).ncard + ramificationDegree f = degree f * S.ncard := by
  have hsupp : Function.support (fun x ↦ localMultiplicity f x - 1) ⊆ f ⁻¹' S := by
    intro x hx
    exact hbranch ((f.mem_branchValues_iff (f x)).2
      ⟨x, rfl, Nat.lt_of_sub_ne_zero hx⟩)
  have hram : (∑ᶠ x ∈ f ⁻¹' S, (localMultiplicity f x - 1)) = ramificationDegree f := by
    rw [ramificationDegree_def]
    exact (finsum_mem_inter_support_eq' _ (f ⁻¹' S) univ fun x hx ↦
      ⟨fun _ ↦ mem_univ x, fun _ ↦ hsupp hx⟩).trans (finsum_mem_univ _)
  rw [← hram]
  exact f.ncard_preimage_add_finsum_localMultiplicity_sub_one hS

/-- The number of points deleted above the branch values plus the ramification degree is
the degree times the number of branch values. This is the correction term when passing from
the unbranched covering of punctured surfaces back to the whole surfaces. -/
theorem ncard_preimage_branchValues_add_ramificationDegree (f : FiniteHolomorphicMap X Y) :
    (f ⁻¹' f.branchValues).ncard + ramificationDegree f = degree f * f.branchValues.ncard :=
  f.ncard_preimage_add_ramificationDegree f.finite_branchValues Subset.rfl

/-- If the local multiplicities of `f` on the fibre over `y` match `fullCycleType σ`, the local
ramification indices `e_x - 1` on that fibre sum to `Fintype.card α - orbitCount σ`. -/
theorem sum_localMultiplicity_sub_one_fiber_eq (f : FiniteHolomorphicMap X Y) {α : Type*}
    [Fintype α] [DecidableEq α] {y : Y} {σ : Equiv.Perm α}
    (h : (f.finite_fiber y).toFinset.val.map (localMultiplicity f) = Equiv.Perm.fullCycleType σ) :
    ∑ x ∈ (f.finite_fiber y).toFinset, (localMultiplicity f x - 1) =
      Fintype.card α - orbitCount σ := by
  have hdeg : degree f = Fintype.card α := by
    simpa [← degree_eq_fiber_sum f y, Finset.sum_eq_multiset_sum,
      Equiv.Perm.sum_fullCycleType] using congrArg Multiset.sum h
  have hcard := card_fiber_add_sum_localMultiplicity_sub_one f y
  rw [f.card_finite_fiber_eq_orbitCount h, hdeg] at hcard; omega

end TauCeti.RiemannSurface.FiniteHolomorphicMap

end
