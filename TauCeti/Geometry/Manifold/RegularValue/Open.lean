/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Regular points form an open set

A point is a regular point of a map when its manifold derivative there is surjective
(`TauCeti.IsRegularPoint`). For a `C¹` map into a manifold modelled on a finite-dimensional space,
regularity is an open condition: the coordinate derivative depends continuously on the point, and a
surjective linear map onto a finite-dimensional space stays surjective under small perturbations,
since surjectivity is the condition that the rank reaches the dimension of the target. So the set of
regular points of a `C¹` map is open, and a dense set of regular points is a dense open set.

## Main results

* `ContinuousLinearMap.isOpen_setOf_surjective`: surjective continuous linear maps onto a
  finite-dimensional space form an open set.
* `TauCeti.IsRegularPoint.eventually_isRegularPoint`: the points near a regular point of a `C¹`
  map are regular.
* `TauCeti.isOpen_setOf_isRegularPoint`: the regular points of a `C¹` map form an open set.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 4.1 (submersion points form an open set).
-/

public section

open Function Set Filter
open scoped Manifold Topology ContDiff

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- The surjective continuous linear maps onto a finite-dimensional space form an open set: a
linear map is surjective exactly when its rank is the dimension of the target, and maps of rank at
least a given number form an open set. -/
theorem isOpen_setOf_surjective : IsOpen {L : E →L[𝕜] F | Surjective L} := by
  convert isOpen_setOfPred_nat_le_rank (𝕜 := 𝕜) (E := E) (F := F) (Module.finrank 𝕜 F) using 1
  ext L
  rw [mem_ofPred_eq, mem_ofPred_eq, ← coe_coe, ← LinearMap.range_eq_top, LinearMap.rank]
  refine ⟨fun h ↦ by rw [h, rank_top, Module.finrank_eq_rank], fun h ↦ ?_⟩
  refine Submodule.eq_top_of_finrank_eq (Module.finrank_eq_of_rank_eq ?_)
  exact le_antisymm ((Submodule.rank_le _).trans (Module.finrank_eq_rank 𝕜 F).ge) h

end ContinuousLinearMap

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
  have hf₁ : ContMDiffAt I J 1 f x := hf.of_le hn
  set g := extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm
  have hz : extChartAt I x x ∈ range I := mem_range_self _
  -- The coordinate expression `g` is `C¹` on `range I ∩ u` for an open neighbourhood `u` of the
  -- chart image of `x`, so its derivative within `range I` is continuous there.
  obtain ⟨u, hu, hzu, hg⟩ := (contMDiffAt_iff.1 hf₁).2.contDiffOn' le_rfl (by simp)
  rw [insert_eq_of_mem hz] at hg
  have hcont := hg.continuousOn_fderivWithin (I.uniqueDiffOn.inter hu) le_rfl _ ⟨hz, hzu⟩
  have hD : ∀ w ∈ range I ∩ u, fderivWithin 𝕜 g (range I ∩ u) w = fderivWithin 𝕜 g (range I) w :=
    fun w hw ↦ fderivWithin_inter (hu.mem_nhds hw.2)
  have hsurj : Surjective (fderivWithin 𝕜 g (range I ∩ u) (extChartAt I x x)) := by
    rw [hD _ ⟨hz, hzu⟩]
    exact (isRegularPoint_iff_surjective_fderivWithin (hf₁.mdifferentiableAt one_ne_zero)
      (mem_chart_source H x) (mem_chart_source H' (f x))).1 h
  -- Near the chart image of `x`, the derivative stays surjective.
  have hev : ∀ᶠ w in 𝓝[range I] extChartAt I x x,
      w ∈ u ∧ Surjective (fderivWithin 𝕜 g (range I) w) := by
    rw [← nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds (hu.mem_nhds hzu))]
    filter_upwards [hcont (ContinuousLinearMap.isOpen_setOf_surjective.mem_nhds hsurj),
      self_mem_nhdsWithin] with w hw hwu
    exact ⟨hwu.2, hD w hwu ▸ hw⟩
  rw [← map_extChartAt_nhds, eventually_map] at hev
  filter_upwards [hev, (contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hf₁,
    (chartAt H x).open_source.mem_nhds (mem_chart_source H x),
    hf₁.continuousAt.preimage_mem_nhds
      ((chartAt H' (f x)).open_source.mem_nhds (mem_chart_source H' (f x)))] with y hy hfy hyx hfyx
  exact (isRegularPoint_iff_surjective_fderivWithin (hfy.mdifferentiableAt one_ne_zero) hyx
    hfyx).2 hy.2

/-- **The regular points of a `C¹` map form an open set.** -/
theorem isOpen_setOf_isRegularPoint (hf : ContMDiff I J n f) (hn : 1 ≤ n) :
    IsOpen {x | IsRegularPoint I J f x} :=
  isOpen_iff_mem_nhds.2 fun _ hx ↦ hx.eventually_isRegularPoint (hf _) hn

end TauCeti
