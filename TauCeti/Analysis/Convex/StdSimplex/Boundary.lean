/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Order.Compact
public import TauCeti.Geometry.Convex.ConvexSpace.Defs
import Mathlib.Topology.Algebra.Monoid

/-!
# The relative boundary of the standard simplex

The relative boundary `TauCeti.stdSimplexBoundary R ι` of the standard simplex consists of the
weight vectors of `Convexity.StdSimplex R ι` with some vanishing coordinate. Every other point of
the simplex has all coordinates positive. For finitely many vertices, over an ordered additive
monoid with one, continuous addition, closed points and compact closed intervals, such as `ℝ`,
the relative boundary is compact.

## Main results

* `TauCeti.stdSimplexBoundary`: the relative boundary of the standard simplex.
* `TauCeti.mem_stdSimplexBoundary_or_forall_pos`: a point of the standard simplex lies on its
  relative boundary or has all coordinates positive.
* `TauCeti.isCompact_stdSimplexBoundary`: the relative boundary is compact.
-/

public section

open Set Finset Convexity

namespace TauCeti

variable {R ι : Type*}

variable (R ι) in
/-- The relative boundary of the standard simplex: its points with some vanishing coordinate. -/
def stdSimplexBoundary [LE R] [AddCommMonoid R] [One R] : Set (ι → R) :=
  {y ∈ (range fun s : StdSimplex R ι => ⇑s.weights) | ∃ i, y i = 0}

variable (R ι) in
/-- The relative boundary of the standard simplex is the set of its points with some vanishing
coordinate. -/
theorem stdSimplexBoundary_def [LE R] [AddCommMonoid R] [One R] :
    stdSimplexBoundary R ι = {y ∈ (range fun s : StdSimplex R ι => ⇑s.weights) | ∃ i, y i = 0} :=
  (rfl)

/-- Membership in the relative boundary of the standard simplex. -/
@[simp]
theorem mem_stdSimplexBoundary [LE R] [AddCommMonoid R] [One R] {x : ι → R} :
    x ∈ stdSimplexBoundary R ι ↔
      x ∈ (range fun s : StdSimplex R ι => ⇑s.weights) ∧ ∃ i, x i = 0 :=
  Iff.rfl

/-- The relative boundary lies in the standard simplex. -/
theorem stdSimplexBoundary_subset [LE R] [AddCommMonoid R] [One R] :
    stdSimplexBoundary R ι ⊆ range fun s : StdSimplex R ι => ⇑s.weights :=
  fun _ hx => (mem_stdSimplexBoundary.mp hx).1

/-- A point of the standard simplex lies on its relative boundary or in its open part. -/
theorem mem_stdSimplexBoundary_or_forall_pos [PartialOrder R] [AddCommMonoid R] [One R]
    {x : ι → R} (hx : x ∈ range fun s : StdSimplex R ι => ⇑s.weights) :
    x ∈ stdSimplexBoundary R ι ∨ ∀ i, 0 < x i := by
  refine or_iff_not_imp_left.2 fun h i => ?_
  obtain ⟨s, rfl⟩ := hx
  exact (s.nonneg i).lt_of_ne' fun h0 =>
    h (mem_stdSimplexBoundary.mpr ⟨mem_range_self s, i, h0⟩)

/-- The relative boundary of the standard simplex over an ordered additive monoid with one,
continuous addition, closed points and compact closed intervals, such as `ℝ`, is compact. -/
theorem isCompact_stdSimplexBoundary [Finite ι] [PartialOrder R] [AddCommMonoid R] [One R]
    [IsOrderedAddMonoid R] [TopologicalSpace R] [ContinuousAdd R] [CompactIccSpace R]
    [T1Space R] :
    IsCompact (stdSimplexBoundary R ι) := by
  have := Fintype.ofFinite ι
  -- The boundary is the intersection of the unit cube with a closed set.
  have hC : IsClosed
      ((fun y : ι → R => ∑ i, y i) ⁻¹' {1} ∩ ⋃ i, (fun y : ι → R => y i) ⁻¹' {0}) :=
    (isClosed_singleton.preimage (continuous_finsetSum _ fun i _ => continuous_apply i)).inter
      (isClosed_iUnion_of_finite fun i => isClosed_singleton.preimage (continuous_apply i))
  convert (isCompact_Icc (a := (0 : ι → R)) (b := 1)).inter_right hC using 1
  ext y
  simp only [mem_stdSimplexBoundary, StdSimplex.mem_range_toFun_comp_weights_iff, mem_inter_iff,
    Set.mem_Icc, Pi.le_def, Pi.zero_apply, Pi.one_apply, Set.mem_preimage, mem_singleton_iff,
    mem_iUnion]
  constructor
  · rintro ⟨⟨h0, h1⟩, hz⟩
    exact ⟨⟨h0, fun i => h1 ▸ single_le_sum (fun j _ => h0 j) (mem_univ i)⟩, h1, hz⟩
  · rintro ⟨⟨h0, -⟩, h1, hz⟩
    exact ⟨⟨h0, h1⟩, hz⟩

end TauCeti
