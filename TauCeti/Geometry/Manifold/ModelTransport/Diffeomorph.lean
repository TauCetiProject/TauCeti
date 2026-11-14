/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Changing the model space along a diffeomorphism

Let `Φ : H ≃ₘ^n⟮I, I'⟯ H'` be a `C^n` diffeomorphism between two model spaces. Conjugating a
`C^n` chart change of `H` by `Φ` gives a `C^n` chart change of `H'`
(`Diffeomorph.symm_trans_trans_mem_contDiffGroupoid`). Consequently, a `C^n` manifold modelled on
`I` is a `C^n` manifold modelled on `I'` for the composite charts `ChartedSpace.comp H' H M`, where
`H` carries the single chart `Φ` (`Diffeomorph.isManifold_chartedSpaceComp`). The identity on the
original carrier is a diffeomorphism to this composite atlas (`Diffeomorph.chartedSpaceComp`).

For instance, a model with corners described as a subset of `ℂ` can be compared with Mathlib's
native half-spaces in this way.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 1, Proposition 1.17, pp.13–14 (compatible smooth structures).
-/

public section

open Set ChartedSpace IsManifold
open scoped Topology
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {n : ℕ∞ω}

namespace Diffeomorph

/-- Conjugating a member of the `C^n` groupoid of `I` by a `C^n` diffeomorphism of models gives a
member of the `C^n` groupoid of `I'`. -/
theorem symm_trans_trans_mem_contDiffGroupoid (Φ : H ≃ₘ^n⟮I, I'⟯ H')
    {e : OpenPartialHomeomorph H H} (he : e ∈ contDiffGroupoid n I) :
    Φ.toHomeomorph.toOpenPartialHomeomorph.symm ≫ₕ
        (e ≫ₕ Φ.toHomeomorph.toOpenPartialHomeomorph) ∈ contDiffGroupoid n I' := by
  -- Each groupoid member `f` read through `Φ` is `C^n` where `Φ.symm` lands in its source.
  have key : ∀ f ∈ contDiffGroupoid n I,
      ContMDiffOn I' I' n (Φ ∘ f ∘ Φ.symm) (Φ.symm ⁻¹' f.source) := fun f hf ↦
    Φ.contMDiff.comp_contMDiffOn
      ((contMDiffOn_of_mem_contDiffGroupoid hf).comp Φ.symm.contMDiff.contMDiffOn fun _ hv ↦ hv)
  have hrefl : OpenPartialHomeomorph.refl H' ∈ IsManifold.maximalAtlas I' n H' :=
    StructureGroupoid.subset_maximalAtlas _ (chartedSpaceSelf_atlas.mpr rfl)
  have h := symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn hrefl hrefl
    (f := Φ.toHomeomorph.toOpenPartialHomeomorph.symm ≫ₕ
      (e ≫ₕ Φ.toHomeomorph.toOpenPartialHomeomorph)) ?_ ?_
  · simpa only [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_trans,
      OpenPartialHomeomorph.trans_refl] using h
  · refine (key e he).congr_mono (fun v _ ↦ ?_) fun v hv ↦ ?_
    · simp [OpenPartialHomeomorph.coe_trans]
    · simpa [OpenPartialHomeomorph.trans_source] using hv
  · refine (key e.symm ((contDiffGroupoid n I).symm he)).congr_mono (fun v _ ↦ ?_)
      fun v hv ↦ ?_
    · simp [OpenPartialHomeomorph.coe_trans_symm]
    · simpa [OpenPartialHomeomorph.trans_target] using hv

/-- A `C^n` manifold modelled on `I` is a `C^n` manifold modelled on `I'` for the composite
charts `ChartedSpace.comp H' H M`, when `H` carries the single chart given by a `C^n`
diffeomorphism of models `Φ`. -/
theorem isManifold_chartedSpaceComp (Φ : H ≃ₘ^n⟮I, I'⟯ H') (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I n M] :
    letI := Φ.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
    letI := ChartedSpace.comp H' H M
    IsManifold I' n M := by
  let := Φ.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  let := ChartedSpace.comp H' H M
  refine { compatible := ?_ }
  rintro _ _ ⟨c, hc, φ, hφ, rfl⟩ ⟨c', hc', φ', hφ', rfl⟩
  obtain rfl := OpenPartialHomeomorph.singletonChartedSpace_mem_atlas_eq _ _ φ hφ
  obtain rfl := OpenPartialHomeomorph.singletonChartedSpace_mem_atlas_eq _ _ φ' hφ'
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
    ← OpenPartialHomeomorph.trans_assoc c.symm]
  exact Φ.symm_trans_trans_mem_contDiffGroupoid (HasGroupoid.compatible hc hc')

private theorem contMDiff_id_of_chartAt_eq (Φ : H ≃ₘ^n⟮I, I'⟯ H') (N : Type*)
    [TopologicalSpace N] [ChartedSpace H N] [ChartedSpace H' N]
    [IsManifold I n N] [IsManifold I' n N]
    (hc : ∀ x : N, chartAt H' x =
      (chartAt H x).trans Φ.toHomeomorph.toOpenPartialHomeomorph) :
    ContMDiff I I' n (id : N → N) := by
  have hchart (x y : N) : (chartAt H' x) y = Φ ((chartAt H x) y) := by
    rw [hc]
    rfl
  intro x
  have ht : Φ ((chartAt H x) x) ∈ (chartAt H' x).target :=
    hchart x x ▸ mem_chart_target H' x
  have hf := (contMDiffAt_symm_of_mem_maximalAtlas
    (chart_mem_maximalAtlas (I := I') x) ht).comp x
      (Φ.contMDiffAt.comp x (contMDiffAt_of_mem_maximalAtlas
        (chart_mem_maximalAtlas (I := I) x) (mem_chart_source H x)))
  apply hf.congr_of_eventuallyEq
  filter_upwards [(chartAt H' x).open_source.mem_nhds (mem_chart_source H' x)] with y hy
  simp only [id_eq, Function.comp_apply, ← hchart, (chartAt H' x).left_inv hy]

/-- The identity diffeomorphism to the atlas obtained by composing charts with the
model diffeomorphism `Φ`. The underlying carrier and topology are unchanged. -/
noncomputable def chartedSpaceComp (Φ : H ≃ₘ^n⟮I, I'⟯ H') (N : Type*) [TopologicalSpace N]
    [ChartedSpace H N] [IsManifold I n N] :
    letI := Φ.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
    letI := ChartedSpace.comp H' H N
    Diffeomorph I I' N N n := by
  letI := Φ.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  letI := ChartedSpace.comp H' H N
  letI := Φ.isManifold_chartedSpaceComp N
  have hc (x : N) : chartAt H' x =
      (chartAt H x).trans Φ.toHomeomorph.toOpenPartialHomeomorph := by
    rw [chartAt_comp, OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq]
  refine
    { toEquiv := Equiv.refl N
      contMDiff_toFun := contMDiff_id_of_chartAt_eq Φ N hc
      contMDiff_invFun := contMDiff_id_of_chartAt_eq Φ.symm N ?_ }
  intro x
  rw [hc, OpenPartialHomeomorph.trans_assoc, Diffeomorph.symm_toHomeomorph,
    Homeomorph.symm_toOpenPartialHomeomorph, Homeomorph.toOpenPartialHomeomorph_trans_symm_self,
    OpenPartialHomeomorph.trans_refl]

variable (Φ : H ≃ₘ^n⟮I, I'⟯ H') (N : Type*) [TopologicalSpace N]
  [ChartedSpace H N] [IsManifold I n N]

/-- The chart-model comparison fixes every point. -/
@[simp]
theorem chartedSpaceComp_apply (x : N) :
    letI := Φ.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
    letI := ChartedSpace.comp H' H N
    Φ.chartedSpaceComp N x = x := by
  simp only [chartedSpaceComp]
  rfl

/-- The inverse chart-model comparison fixes every point. -/
@[simp]
theorem chartedSpaceComp_symm_apply (x : N) :
    letI := Φ.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
    letI := ChartedSpace.comp H' H N
    (Φ.chartedSpaceComp N).symm x = x := by
  simp only [chartedSpaceComp, Diffeomorph.symm]
  rfl

end Diffeomorph
