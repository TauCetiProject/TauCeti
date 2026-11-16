/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.LinearAlgebra.Dimension.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Topology.Algebra.Module.PerfectSpace
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.Connected
import TauCeti.Topology.Perfect

/-!
# Adjoining discrete sets to filled-in subsets of manifolds

In a topological manifold modelled on a real normed space `E` of dimension greater than one,
adjoining a closed discrete set `s` (for instance a finite set, or a single point) to a closed set
`K` that is filled in an open set `Ω` preserves `TauCeti.IsFilledIn`: each open connected component
`C` of `Ω \ K` stays preconnected when `s` is deleted
(`TauCeti.isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank`), and loses no closure
points because the manifold is a perfect space (`ChartedSpace.perfectSpace`).

This enters point-separation characterizations of Runge sets: to separate a point `a ∈ Ω \ K` from
a filled compact set `K ⊆ Ω` by a function holomorphic on `Ω`, one applies Runge approximation on
`insert a K` to the indicator that is `0` near `K` and `1` near `a`.

## Main results

* `TauCeti.IsFilledIn.union_of_isDiscrete`: adjoining a closed discrete set to a closed set `K`
  preserves filledness in an open set, in dimension greater than one.
* `TauCeti.IsFilledIn.union_of_finite`: the special case of adjoining a finite set to a closed set
  `K`.
* `TauCeti.IsFilledIn.insert`: adjoining a single point to a closed set `K` preserves filledness in
  an open set.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 11.1.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.3.9.
-/

public section

open Set Topology

namespace TauCeti

variable {E X : Type*} [TopologicalSpace X]

section Seminormed

variable [SeminormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E X]

/-- **Adjoining a closed discrete set to a closed set preserves filledness in an open set**, on a
manifold modelled on a real seminormed space of dimension greater than one. -/
theorem IsFilledIn.union_of_isDiscrete {K Ω s : Set X} (hfill : IsFilledIn K Ω)
    (h : 1 < Module.rank ℝ E) (hK : IsClosed K) (hΩ : IsOpen Ω) (hs : IsClosed s)
    (hd : IsDiscrete s) : IsFilledIn (K ∪ s) Ω := by
  have := ChartedSpace.locallyConnectedSpace E X
  have : Nontrivial E := (rank_pos_iff_nontrivial (R := ℝ)).1 (zero_lt_one.trans h)
  have : PerfectSpace E := perfectSpace_of_module ℝ E
  have : PerfectSpace X := ChartedSpace.perfectSpace (H := E)
  rw [isFilledIn_iff] at hfill ⊢
  rintro x ⟨hxΩ, hxKs⟩
  have hxK : x ∈ Ω \ K := ⟨hxΩ, fun hxK => hxKs (Or.inl hxK)⟩
  have hxs : x ∉ s := fun hxs => hxKs (Or.inr hxs)
  set C := connectedComponentIn (Ω \ K) x
  have hCopen : IsOpen C := (hΩ.sdiff hK).connectedComponentIn
  have hcomp : connectedComponentIn (Ω \ (K ∪ s)) x = C \ s := by
    refine Subset.antisymm ?_ ?_
    · exact fun y hy => ⟨connectedComponentIn_mono x
          (sdiff_subset_sdiff Subset.rfl subset_union_left) hy,
        fun hys => (connectedComponentIn_subset _ _ hy).2 (Or.inr hys)⟩
    · exact (isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank h hCopen
        isPreconnected_connectedComponentIn hs hd).subset_connectedComponentIn
        ⟨mem_connectedComponentIn hxK, hxs⟩
        fun y ⟨hyC, hys⟩ => ⟨(connectedComponentIn_subset _ _ hyC).1,
          fun hyKs => hyKs.elim (connectedComponentIn_subset _ _ hyC).2 hys⟩
  have hcl : closure (C \ s) = closure C :=
    Subset.antisymm (closure_mono sdiff_subset)
      (closure_minimal (hCopen.subset_closure_sdiff_of_isDiscrete (hd.mono inter_subset_right))
        isClosed_closure)
  rw [hcomp, hcl]
  exact hfill x hxK

end Seminormed

section Normed

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E X]

/-- **Adjoining a finite set to a closed set preserves filledness in an open set**, on a manifold
modelled on a real normed space of dimension greater than one. -/
theorem IsFilledIn.union_of_finite {K Ω s : Set X} (hfill : IsFilledIn K Ω)
    (h : 1 < Module.rank ℝ E) (hK : IsClosed K) (hΩ : IsOpen Ω) (hs : s.Finite) :
    IsFilledIn (K ∪ s) Ω :=
  have := ChartedSpace.t1Space E X
  hfill.union_of_isDiscrete h hK hΩ hs.isClosed hs.isDiscrete

/-- **Adjoining a point to a closed set preserves filledness in an open set**, on a manifold
modelled on a real normed space of dimension greater than one. -/
theorem IsFilledIn.insert {K Ω : Set X} (hfill : IsFilledIn K Ω) (h : 1 < Module.rank ℝ E)
    (hK : IsClosed K) (hΩ : IsOpen Ω) (a : X) : IsFilledIn (insert a K) Ω := by
  rw [insert_eq, union_comm]
  exact hfill.union_of_finite h hK hΩ (finite_singleton a)

end Normed

end TauCeti
