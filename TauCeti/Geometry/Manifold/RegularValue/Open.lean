/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Rank

/-!
# Regular points form an open set

A point is a regular point of a map when its manifold derivative there is surjective
(`TauCeti.IsRegularPoint`). For a `C¹` map into a manifold modelled on a finite-dimensional space,
regularity is an open condition: the regular points are the points of maximal rank
(`TauCeti.isRegularPoint_iff_mfderivRank_eq`), and the rank of a `C¹` map can only go up near a
point (`TauCeti.eventually_mfderivRank_le_mfderivRank`). So the set of regular points of a `C¹` map
is open, and a dense set of regular points is a dense open set.

For a closed map the image of the closed critical-point set is closed, so the regular values
also form an open set. In particular, this applies to proper maps.

## Main results

* `TauCeti.IsRegularPoint.eventually_isRegularPoint`: the points near a regular point of a `C¹`
  map are regular.
* `TauCeti.isOpen_setOf_isRegularPoint`: the regular points of a `C¹` map form an open set.
* `TauCeti.isOpen_setOf_isRegularValue_of_isClosedMap`: the regular values of a closed `C¹`
  map form an open set, in particular for a proper map.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 4.1 (submersion points form an open set).
-/

public section

open Function Set Filter
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  {f : M → N} {x : M} {n : ℕ∞ω}

/-- **Regularity is an open condition.** Every point near a regular point of a map which is `C¹`
there is a regular point. -/
theorem IsRegularPoint.eventually_isRegularPoint (h : IsRegularPoint I J f x)
    (hf : ContMDiffAt I J n f x) (hn : 1 ≤ n) : ∀ᶠ y in 𝓝 x, IsRegularPoint I J f y := by
  filter_upwards [eventually_mfderivRank_le_mfderivRank hf hn] with y hy
  rw [isRegularPoint_iff_mfderivRank_eq] at h ⊢
  exact mfderivRank_le_finrank_target.antisymm (h ▸ hy)

/-- **The regular points of a `C¹` map form an open set.** -/
theorem isOpen_setOf_isRegularPoint (hf : ContMDiff I J n f) (hn : 1 ≤ n) :
    IsOpen {x | IsRegularPoint I J f x} :=
  isOpen_iff_mem_nhds.2 fun _ hx ↦ hx.eventually_isRegularPoint (hf _) hn

/-- The regular values of a closed `C¹` map form an open set. This applies in particular to
proper maps, including continuous maps from compact spaces to Hausdorff spaces. -/
theorem isOpen_setOf_isRegularValue_of_isClosedMap (hf : ContMDiff I J n f) (hn : 1 ≤ n)
    (hclosed : IsClosedMap f) : IsOpen {y | IsRegularValue I J f y} := by
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hclosed _ (isOpen_setOf_isRegularPoint hf hn).isClosed_compl).isOpen_compl

end TauCeti
