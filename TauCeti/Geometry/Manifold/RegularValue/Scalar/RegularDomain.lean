/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Exhaustion
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import TauCeti.Geometry.Manifold.Sard.Basic

/-!
# Regular sublevels as regular domains

Let `f : M → ℝ` be a continuous function on a boundaryless manifold and `c` a regular value of
`f`. A point of the level `f⁻¹(c)` is neither a local maximum nor a local minimum of `f`, by
Fermat's theorem (`IsLocalExtr.mem_criticalPoints`), so it is a limit both of points where
`f < c` and of points where `f > c`. Hence the topological interior of the sublevel `{f ≤ c}` in
`M` is the strict sublevel `{f < c}`, the closure of `{f < c}` is `{f ≤ c}`, and the frontier of
`{f ≤ c}` is the level `f⁻¹(c)`. No differentiability of `f` is needed: at a point where `f` is not
differentiable its derivative is zero, so a regular point of a real function is a point of
differentiability.

When `f` is `C¹` and `M` is modelled on a space of dimension `n + 1`, the sublevel `{f ≤ c}` is a
manifold with boundary for the atlas `TauCeti.scalarRegularSublevelChartedSpace`
(`TauCeti.isManifold_scalarRegularSublevel`), whose manifold interior and boundary are `{f < c}`
and `f⁻¹(c)` (`TauCeti.interior_scalarRegularSublevel`, `TauCeti.boundary_scalarRegularSublevel`).
The results here say that these are also its topological interior and frontier in `M`, so the
sublevel is a regular domain: a closed codimension-zero submanifold with boundary.

Every compact subset `K` of a Hausdorff, σ-compact (for instance second-countable),
finite-dimensional smooth manifold without boundary lies in the interior of a compact regular
domain of this kind (`IsCompact.exists_isRegularValue_isCompact_setOf_le`). The manifold carries a
smooth proper exhaustion function `f ≥ 0` (`TauCeti.exists_contMDiffMap_isProperMap_nonneg`).
By Sard's theorem (`ContMDiff.dense_isRegularValue`) the regular values of `f` are dense, so one of
them, `c`, exceeds the maximum of `f` on `K`. Properness makes `{f ≤ c}` compact. Such compact
neighbourhoods with smooth boundary are the compact pieces on which doubling arguments run, for
instance to reduce approximation and transversality into a non-compact target to a compact one.

In dimension zero every point is critical, so a regular value `c` is not a value of `f` and the
sublevel `{f ≤ c}` is open and closed. The existence theorem holds in every dimension; only the
manifold structure with boundary needs positive dimension.

## Main results

* `TauCeti.IsRegularValue.interior_setOf_le`, `TauCeti.IsRegularValue.closure_setOf_lt` and
  `TauCeti.IsRegularValue.frontier_setOf_le`: the interior, closure and frontier of the sublevels
  at a regular value.
* `IsCompact.exists_isRegularValue_isCompact_setOf_le`: every compact set lies in the strict
  sublevel of a smooth function at a regular value whose sublevel is compact.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 2.28 (smooth exhaustion functions), Proposition 5.47 (regular
  sublevel sets are regular domains) and Theorem 6.10 (Sard).
-/

public section

open Filter Module Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

section Topology

variable [BoundarylessManifold I M] {f : M → ℝ} {c : ℝ}

/-- **The interior of a regular sublevel.** On a boundaryless manifold, the interior of the
sublevel `{f ≤ c}` of a continuous function at a regular value `c` is the strict sublevel
`{f < c}`: a point of the level `f⁻¹(c)` in that interior would be a local maximum of `f`, hence a
critical point. -/
theorem IsRegularValue.interior_setOf_le (hreg : IsRegularValue I 𝓘(ℝ) f c)
    (hf : Continuous f) : interior {x | f x ≤ c} = {x | f x < c} := by
  refine Subset.antisymm (fun x hx ↦ ?_)
    (interior_maximal (fun _ hx ↦ mem_ofPred.2 (mem_ofPred.1 hx).le)
      (isOpen_lt hf continuous_const))
  refine (mem_ofPred.1 (interior_subset hx)).lt_of_ne fun hxc ↦ ?_
  refine isRegularPoint_iff_notMem_criticalPoints.1 (hreg.isRegularPoint hxc)
    (IsLocalMax.mem_criticalPoints ?_)
  filter_upwards [mem_interior_iff_mem_nhds.1 hx] with y (hy : f y ≤ c)
  exact hy.trans hxc.ge

/-- **The closure of a regular strict sublevel.** On a boundaryless manifold, the closure of the
strict sublevel `{f < c}` of a continuous function at a regular value `c` is the sublevel
`{f ≤ c}`: a point of the level `f⁻¹(c)` outside that closure would be a local minimum of `f`,
hence a critical point. -/
theorem IsRegularValue.closure_setOf_lt (hreg : IsRegularValue I 𝓘(ℝ) f c)
    (hf : Continuous f) : closure {x | f x < c} = {x | f x ≤ c} := by
  refine (closure_lt_subset_le hf continuous_const).antisymm fun x (hx : f x ≤ c) ↦ ?_
  refine hx.lt_or_eq.elim (fun h ↦ subset_closure h) fun hxc ↦ ?_
  by_contra hcl
  rw [mem_closure_iff_frequently, not_frequently] at hcl
  refine isRegularPoint_iff_notMem_criticalPoints.1 (hreg.isRegularPoint hxc)
    (IsLocalMin.mem_criticalPoints ?_)
  filter_upwards [hcl] with y (hy : ¬ f y < c)
  exact hxc.trans_le (not_lt.1 hy)

/-- **The frontier of a regular sublevel is the level.** On a boundaryless manifold, the frontier
of the sublevel `{f ≤ c}` of a continuous function at a regular value `c` is the level
`f⁻¹(c)`. -/
theorem IsRegularValue.frontier_setOf_le (hreg : IsRegularValue I 𝓘(ℝ) f c)
    (hf : Continuous f) : frontier {x | f x ≤ c} = {x | f x = c} := by
  rw [frontier, (isClosed_le hf continuous_const).closure_eq, hreg.interior_setOf_le hf]
  ext x
  simp only [Set.mem_sdiff, mem_ofPred, not_lt, le_antisymm_iff]

end Topology

section Neighbourhood

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]

/-- **Compact regular neighbourhoods.** Every compact subset `K` of a Hausdorff, σ-compact,
finite-dimensional smooth manifold without boundary, for instance a second-countable one, lies in
the strict sublevel `{f < c}` of a smooth function `f` at a regular value `c` whose sublevel
`{f ≤ c}` is compact. When `M` is
modelled on a space of dimension `n + 1`, this sublevel is a compact manifold with boundary
`f⁻¹(c)` for `TauCeti.scalarRegularSublevelChartedSpace`, and `K` lies in its interior
(`TauCeti.IsRegularValue.interior_setOf_le`). -/
theorem _root_.IsCompact.exists_isRegularValue_isCompact_setOf_le {K : Set M} (hK : IsCompact K) :
    ∃ (f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (c : ℝ), IsRegularValue I 𝓘(ℝ) f c ∧
      IsCompact {x | f x ≤ c} ∧ K ⊆ {x | f x < c} := by
  obtain ⟨f, hp, hf0⟩ := exists_contMDiffMap_isProperMap_nonneg I (M := M)
  obtain ⟨b, hb⟩ := (hK.image f.contMDiff.continuous).bddAbove
  obtain ⟨c, hreg, hbc, -⟩ := (f.contMDiff.dense_isRegularValue (by simp)).exists_between
    (lt_add_one b)
  refine ⟨f, c, hreg, ?_, fun x hx ↦ (hb (mem_image_of_mem f hx)).trans_lt hbc⟩
  exact (hp.isCompact_preimage isCompact_Icc).of_isClosed_subset
    (isClosed_le f.contMDiff.continuous continuous_const) fun x (hx : f x ≤ c) ↦ ⟨hf0 x, hx⟩

end Neighbourhood

end TauCeti
