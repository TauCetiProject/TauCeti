/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Gluing local smooth representatives

Let `μ` be a measure on a manifold `M` that charges every nonempty open set. If near every point a
function `f : M → M'` into a Hausdorff manifold agrees `μ`-almost everywhere with a `C^n`
function, then `f` agrees `μ`-almost everywhere with a single `C^n` function on `M`
(`TauCeti.exists_contMDiff_ae_eq_of_forall_exists_contMDiffOn`).

Two continuous functions that agree almost everywhere on an open set agree everywhere on it,
because the measure charges the open set where they differ. So the local representatives agree
on the overlaps of their domains, and taking at each point the value of its own representative
defines a function that coincides near every point with a `C^n` function. Countably many of the
domains cover `M` when `M` is Lindelöf, so the glued function is still a representative of `f`.

This is how regularity proved in charts, such as interior elliptic regularity read in
coordinates, becomes a statement about a function on the whole manifold.
-/

public section

open MeasureTheory Set
open scoped Manifold Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M]
  [OpensMeasurableSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 F H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [T2Space M']

/-- **Local smooth representatives glue.** Let `μ` charge every nonempty open set of a Lindelöf
manifold `M`. If every point has an open neighbourhood on which `f : M → M'`, with `M'` a
Hausdorff manifold, agrees `μ`-almost everywhere with a function that is `C^n` there, then `f`
agrees `μ`-almost everywhere with a `C^n` function on `M`. -/
theorem exists_contMDiff_ae_eq_of_forall_exists_contMDiffOn [LindelofSpace M]
    {μ : Measure M} [μ.IsOpenPosMeasure] {n : WithTop ℕ∞} {f : M → M'}
    (h : ∀ x, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ g : M → M', ContMDiffOn I I' n g U ∧
      f =ᵐ[μ.restrict U] g) :
    ∃ g : M → M', ContMDiff I I' n g ∧ f =ᵐ[μ] g := by
  choose U hU hxU g hg hfg using h
  -- Two local representatives agree on the overlap of their domains.
  have hagree (x y : M) : EqOn (g x) (g y) (U x ∩ U y) := by
    have hx : f =ᵐ[μ.restrict (U x ∩ U y)] g x :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hfg x)
    have hy : f =ᵐ[μ.restrict (U x ∩ U y)] g y :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hfg y)
    exact Measure.eqOn_open_of_ae_eq (hx.symm.trans hy) ((hU x).inter (hU y))
      ((hg x).continuousOn.mono inter_subset_left) ((hg y).continuousOn.mono inter_subset_right)
  set G : M → M' := fun x ↦ g x x
  have hG (x : M) : EqOn G (g x) (U x) := fun y hy ↦ hagree y x ⟨hxU y, hy⟩
  refine ⟨G, fun x ↦ ?_, ?_⟩
  · exact ((hg x).congr (hG x)).contMDiffAt ((hU x).mem_nhds (hxU x))
  · obtain ⟨t, ht, hcover⟩ := LindelofSpace.elim_nhds_subcover U fun x ↦
      (hU x).mem_nhds (hxU x)
    have hloc : ∀ x ∈ t, f =ᵐ[μ.restrict (U x)] G := fun x _ ↦
      (hfg x).trans ((ae_restrict_iff' (hU x).measurableSet).2
        (Filter.Eventually.of_forall fun y hy ↦ (hG x hy).symm))
    rw [← Measure.restrict_univ (μ := μ), ← hcover]
    exact (ae_restrict_biUnion_iff U ht _).2 hloc

end TauCeti
