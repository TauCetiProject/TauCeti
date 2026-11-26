/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CriticalPoints

/-!
# The topology of sublevels at a regular value

Let `f : M → ℝ` be a continuous function on a boundaryless manifold and `c` a regular value of
`f`. A point of the level `f⁻¹(c)` is neither a local maximum nor a local minimum of `f`, by
Fermat's theorem (`IsLocalExtr.mem_criticalPoints`), so it is a limit both of points where
`f < c` and of points where `f > c`. Hence the topological interior of the sublevel `{f ≤ c}` in
`M` is the strict sublevel `{f < c}`, the closure of `{f < c}` is `{f ≤ c}`, and the frontier of
`{f ≤ c}` is the level `f⁻¹(c)`. No differentiability of `f` is needed: at a point where `f` is not
differentiable its derivative is zero, so a regular point of a real function is a point of
differentiability.

When `f` is `C¹`, `M` is modelled on a space of dimension `n + 1` and the model `I` is
boundaryless (`I.Boundaryless`), the sublevel `{f ≤ c}` is a manifold with boundary for the atlas
`TauCeti.scalarRegularSublevelChartedSpace` (`TauCeti.isManifold_scalarRegularSublevel`), whose
manifold interior and boundary are `{f < c}` and `f⁻¹(c)` (`TauCeti.interior_scalarRegularSublevel`,
`TauCeti.boundary_scalarRegularSublevel`). The results here say that these are also its topological
interior and frontier in `M`, so the sublevel is a regular domain: a closed codimension-zero
submanifold with boundary.

## Main results

* `TauCeti.IsRegularValue.interior_setOfPred_le`, `TauCeti.IsRegularValue.closure_setOfPred_lt` and
  `TauCeti.IsRegularValue.frontier_setOfPred_le`: the interior, closure and frontier of the
  sublevels at a regular value.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 5.47 (regular sublevel sets are regular domains).
-/

public section

open Filter Set
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

section Topology

variable [BoundarylessManifold I M] {f : M → ℝ} {c : ℝ}

/-- **The interior of a regular sublevel.** On a boundaryless manifold, the interior of the
sublevel `{f ≤ c}` of a continuous function at a regular value `c` is the strict sublevel
`{f < c}`: a point of the level `f⁻¹(c)` in that interior would be a local maximum of `f`, hence a
critical point. -/
theorem IsRegularValue.interior_setOfPred_le (hreg : IsRegularValue I 𝓘(ℝ) f c)
    (hf : Continuous f) : interior {x | f x ≤ c} = {x | f x < c} := by
  refine Subset.antisymm (fun x hx ↦ ?_)
    (interior_maximal (fun _ hx ↦ mem_ofPred.2 (mem_ofPred.1 hx).le)
      (isOpen_lt hf continuous_const))
  refine (mem_ofPred.1 (interior_subset hx)).lt_of_ne fun hxc ↦ ?_
  refine isRegularPoint_iff_notMem_criticalPoints.1 (hreg.isRegularPoint hxc)
    (IsLocalMax.mem_criticalPoints ?_ BoundarylessManifold.isInteriorPoint)
  filter_upwards [mem_interior_iff_mem_nhds.1 hx] with y (hy : f y ≤ c)
  exact hy.trans hxc.ge

/-- **The closure of a regular strict sublevel.** On a boundaryless manifold, the closure of the
strict sublevel `{f < c}` of a continuous function at a regular value `c` is the sublevel
`{f ≤ c}`: a point of the level `f⁻¹(c)` outside that closure would be a local minimum of `f`,
hence a critical point. -/
theorem IsRegularValue.closure_setOfPred_lt (hreg : IsRegularValue I 𝓘(ℝ) f c)
    (hf : Continuous f) : closure {x | f x < c} = {x | f x ≤ c} := by
  refine (closure_lt_subset_le hf continuous_const).antisymm fun x (hx : f x ≤ c) ↦ ?_
  refine hx.lt_or_eq.elim (fun h ↦ subset_closure h) fun hxc ↦ ?_
  by_contra hcl
  rw [mem_closure_iff_frequently, not_frequently] at hcl
  refine isRegularPoint_iff_notMem_criticalPoints.1 (hreg.isRegularPoint hxc)
    (IsLocalMin.mem_criticalPoints ?_ BoundarylessManifold.isInteriorPoint)
  filter_upwards [hcl] with y (hy : ¬ f y < c)
  exact hxc.trans_le (not_lt.1 hy)

/-- **The frontier of a regular sublevel is the level.** On a boundaryless manifold, the frontier
of the sublevel `{f ≤ c}` of a continuous function at a regular value `c` is the level
`f⁻¹(c)`. -/
theorem IsRegularValue.frontier_setOfPred_le (hreg : IsRegularValue I 𝓘(ℝ) f c)
    (hf : Continuous f) : frontier {x | f x ≤ c} = {x | f x = c} := by
  rw [frontier, (isClosed_le hf continuous_const).closure_eq, hreg.interior_setOfPred_le hf]
  ext x
  simp only [Set.mem_sdiff, mem_ofPred, not_lt, le_antisymm_iff]

end Topology

end TauCeti
