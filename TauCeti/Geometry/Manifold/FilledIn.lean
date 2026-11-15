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
import Mathlib.Geometry.Manifold.HasGroupoid
import TauCeti.Geometry.Manifold.Connected

/-!
# Adjoining discrete sets to filled-in subsets of manifolds

In a topological manifold modelled on a real normed space `E` of dimension greater than one,
adjoining a closed discrete set `s` (for instance a finite set, or a single point) to a closed set
`K` that is filled in an open set `Ω` preserves `TauCeti.IsFilledIn`: each open connected component
`C` of `Ω \ K` stays preconnected when `s` is deleted
(`TauCeti.isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank`), and loses no closure
points because punctured neighbourhoods in `E` are nonempty.

This enters point-separation characterizations of Runge sets: to separate a point `a ∈ Ω \ K` from
a filled compact set `K ⊆ Ω` by a function holomorphic on `Ω`, one applies Runge approximation on
`insert a K` to the indicator that is `0` near `K` and `1` near `a`.

## Main results

* `TauCeti.IsFilledIn.union_of_isDiscrete`: adjoining a closed discrete set preserves filledness in
  an open set, in dimension greater than one.
* `TauCeti.IsFilledIn.union_of_finite`: the special case of a finite set.
* `TauCeti.IsFilledIn.insert`: adjoining a single point preserves filledness in an open set.

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

/-- **Adjoining a closed discrete set preserves filledness in an open set**, on a manifold modelled
on a real seminormed space of dimension greater than one. -/
theorem IsFilledIn.union_of_isDiscrete {K Ω s : Set X} (hfill : IsFilledIn K Ω)
    (h : 1 < Module.rank ℝ E) (hK : IsClosed K) (hΩ : IsOpen Ω) (hs : IsClosed s)
    (hd : IsDiscrete s) : IsFilledIn (K ∪ s) Ω := by
  have := ChartedSpace.locallyConnectedSpace E X
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
  have hcl : closure (C \ s) = closure C := by
    refine Subset.antisymm (closure_mono sdiff_subset)
      (closure_minimal (fun y hyC => ?_) isClosed_closure)
    by_cases hys : y ∈ s
    · obtain ⟨u, hu, hus⟩ := isDiscrete_iff_forall_mem_exists_isOpen.1 hd y hys
      have hyu : y ∈ u := (hus.symm ▸ mem_singleton y : y ∈ u ∩ s).1
      refine mem_closure_iff_nhds.2 fun W hW => ?_
      obtain ⟨V, -, hV, hc⟩ := exists_mem_nhds_subset_isConnected_sdiff_singleton h y
        (Filter.inter_mem hW ((hCopen.inter hu).mem_nhds ⟨hyC, hyu⟩))
      obtain ⟨z, hzV, hzy⟩ := hc.nonempty
      refine ⟨z, (hV hzV).1, (hV hzV).2.1, fun hzs => hzy ?_⟩
      have : z ∈ u ∩ s := ⟨(hV hzV).2.2, hzs⟩
      rwa [hus] at this
    · exact subset_closure ⟨hyC, hys⟩
  rw [hcomp, hcl]
  exact hfill x hxK

end Seminormed

section Normed

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E X]

/-- **Adjoining a finite set preserves filledness in an open set**, on a manifold modelled on a
real normed space of dimension greater than one. -/
theorem IsFilledIn.union_of_finite {K Ω s : Set X} (hfill : IsFilledIn K Ω)
    (h : 1 < Module.rank ℝ E) (hK : IsClosed K) (hΩ : IsOpen Ω) (hs : s.Finite) :
    IsFilledIn (K ∪ s) Ω :=
  have := ChartedSpace.t1Space E X
  hfill.union_of_isDiscrete h hK hΩ hs.isClosed hs.isDiscrete

/-- **Adjoining a point preserves filledness in an open set**, on a manifold modelled on a real
normed space of dimension greater than one. -/
theorem IsFilledIn.insert {K Ω : Set X} (hfill : IsFilledIn K Ω) (h : 1 < Module.rank ℝ E)
    (hK : IsClosed K) (hΩ : IsOpen Ω) (a : X) : IsFilledIn (insert a K) Ω := by
  rw [insert_eq, union_comm]
  exact hfill.union_of_finite h hK hΩ (finite_singleton a)

end Normed

end TauCeti
