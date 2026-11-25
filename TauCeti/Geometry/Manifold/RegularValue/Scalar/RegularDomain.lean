/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Exhaustion
public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Sublevel.Topology
import TauCeti.Geometry.Manifold.Sard.Basic

/-!
# Compact regular sublevels around a compact set

Let `f : M → ℝ` be a continuous function on a boundaryless manifold and `c` a regular value of
`f`. The interior of the sublevel `{f ≤ c}` is the strict sublevel `{f < c}` and its frontier is
the level `f⁻¹(c)` (`TauCeti.IsRegularValue.interior_setOfPred_le`,
`TauCeti.IsRegularValue.frontier_setOfPred_le`). When moreover `f` is `C¹`, `M` is modelled on a
space of dimension `n + 1` and the model `I` is boundaryless (`I.Boundaryless`), the atlas
`TauCeti.scalarRegularSublevelChartedSpace` makes the sublevel a regular domain: a closed
codimension-zero submanifold with boundary.

Every compact subset `K` of a Hausdorff, σ-compact (for instance second-countable),
finite-dimensional smooth manifold without boundary lies in the strict sublevel `{f < c}` of a
smooth function `f` at a regular value `c` whose sublevel `{f ≤ c}` is compact
(`IsCompact.exists_isRegularValue_isCompact_setOfPred_le`). In positive dimension and on a
boundaryless model, this sublevel is a compact regular domain of the kind above with `K` in its
interior. The manifold carries a smooth proper exhaustion function `f ≥ 0`
(`TauCeti.exists_contMDiffMap_isProperMap_nonneg`). By Sard's theorem
(`ContMDiff.dense_isRegularValue`) the regular values of `f` are dense, so one of them, `c`,
exceeds the maximum of `f` on `K`. Properness makes `{f ≤ c}` compact. Such compact neighbourhoods
with smooth boundary are the compact pieces on which doubling arguments run, for instance to
reduce approximation and transversality into a non-compact target to a compact one.

In dimension zero every point is critical, so a regular value `c` is not a value of `f` and the
sublevel `{f ≤ c}` is open and closed. The existence theorem holds in every dimension; only the
manifold structure with boundary needs positive dimension and a boundaryless model.

## Main results

* `IsCompact.exists_isRegularValue_isCompact_setOfPred_le`: every compact set lies in the strict
  sublevel of a smooth function at a regular value whose sublevel is compact.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 2.28 (smooth exhaustion functions) and Theorem 6.10 (Sard).
-/

public section

open Filter Module Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

section Neighbourhood

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]

/-- **Compact regular neighbourhoods.** Every compact subset `K` of a Hausdorff, σ-compact,
finite-dimensional smooth manifold without boundary, for instance a second-countable one, lies in
the strict sublevel `{f < c}` of a smooth function `f` at a regular value `c` whose sublevel
`{f ≤ c}` is compact. When `M` is modelled on a space of dimension `n + 1` and the model `I` is
boundaryless (`I.Boundaryless`), this sublevel is a compact manifold with boundary `f⁻¹(c)` for
`TauCeti.scalarRegularSublevelChartedSpace`, and `K` lies in its interior
(`TauCeti.IsRegularValue.interior_setOfPred_le`). -/
theorem _root_.IsCompact.exists_isRegularValue_isCompact_setOfPred_le {K : Set M}
    (hK : IsCompact K) :
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
