/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Rademacher
public import TauCeti.Geometry.Manifold.Riemannian.Distance
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Null

/-!
# Rademacher's theorem on Riemannian manifolds

Let `M` be a manifold, possibly with boundary or corners, modelled on a finite-dimensional real
normed space, whose extended distance is the Riemannian distance of a continuous Riemannian
metric. A map from `M` to a finite-dimensional real normed space that is locally Lipschitz on an
open set `U` is differentiable at almost every point of `U`: the points of `U` where it is not
differentiable form a chartwise null set, and so a set of Riemannian volume zero when `M` is
Lindelöf.

Inverses of extended charts are locally Lipschitz into `M` on the interior of their targets
(`TauCeti.IsRiemannianManifold.exists_lipschitzOnWith_of_contMDiffAt`), so in such a chart the map
reads as a locally Lipschitz map between normed spaces, to which the Euclidean Rademacher theorem
`LocallyLipschitzOn.ae_differentiableAt_of_mem` applies. The boundary points of `M` form a null
set (`TauCeti.isNullSet_boundary`).

## Main results

* `LocallyLipschitzOn.comp_extChartAt_symm`: a map locally Lipschitz on an open set `U`, read
  through the inverse of an extended chart, is locally Lipschitz on the interior of the chart
  target, within the preimage of `U`.
* `LocallyLipschitzOn.isNullSet_setOf_not_mdifferentiableAt`: the points of an open set `U` at
  which a map locally Lipschitz on `U` is not differentiable form a null set.
* `LocallyLipschitzOn.ae_mdifferentiableAt_of_mem`: such a map is differentiable at almost every
  point of `U` for the Riemannian volume.
* `LocallyLipschitz.ae_mdifferentiableAt` and `LipschitzWith.ae_mdifferentiableAt`: a locally
  Lipschitz map is differentiable almost everywhere.

## References

* H. Federer, *Geometric Measure Theory*, Springer, 1969, Theorem 3.1.6.
-/

public section

open Bundle MeasureTheory Metric Set
open scoped Manifold NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] {U : Set M}

namespace LocallyLipschitzOn

/-- A map locally Lipschitz on an open set `U` of a Riemannian manifold, read through the inverse
of an extended chart, is locally Lipschitz on the interior of the chart target, intersected with
the preimage of `U`. -/
theorem comp_extChartAt_symm {X : Type*} [PseudoEMetricSpace X] {g : M → X}
    (hg : LocallyLipschitzOn U g) (hU : IsOpen U) (p : M) :
    LocallyLipschitzOn (interior (extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' U)
      (g ∘ (extChartAt I p).symm) := by
  intro y hy
  obtain ⟨K, t, ht, hK⟩ := hg hy.2
  rw [nhdsWithin_eq_nhds.2 (hU.mem_nhds hy.2)] at ht
  have he : ContMDiffAt 𝓘(ℝ, E) I 1 (extChartAt I p).symm y :=
    (contMDiffOn_extChartAt_symm p y (interior_subset hy.1)).contMDiffAt
      (mem_interior_iff_mem_nhds.1 hy.1)
  obtain ⟨r, hr, C, hC⟩ :=
    TauCeti.IsRiemannianManifold.exists_lipschitzOnWith_of_contMDiffAt (I := I) he
  obtain ⟨r', hr', hr't⟩ := Metric.mem_nhds_iff.1 (he.continuousAt.preimage_mem_nhds ht)
  refine ⟨K * C, ball y (min r r'), mem_nhdsWithin_of_mem_nhds
    (ball_mem_nhds y (lt_min hr hr')), hK.comp (hC.mono (ball_subset_ball (min_le_left _ _)))
      fun z hz ↦ hr't (ball_subset_ball (min_le_right _ _) hz)⟩

end LocallyLipschitzOn

variable [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {f : M → F}

namespace LocallyLipschitzOn

/-- **Rademacher's theorem on a Riemannian manifold**, chartwise form. The points of an open set
`U` at which a map locally Lipschitz on `U` is not differentiable form a null set. -/
theorem isNullSet_setOf_not_mdifferentiableAt [MeasurableSpace E] [BorelSpace E]
    (hf : LocallyLipschitzOn U f) (hU : IsOpen U) :
    TauCeti.IsNullSet I {x | x ∈ U ∧ ¬MDifferentiableAt I 𝓘(ℝ, F) f x} := by
  have hint : TauCeti.IsNullSet I
      {x | x ∈ U ∧ I.IsInteriorPoint x ∧ ¬MDifferentiableAt I 𝓘(ℝ, F) f x} := by
    rw [TauCeti.isNullSet_iff]
    intro p μ _
    let e := extChartAt I p
    let V := interior e.target ∩ e.symm ⁻¹' U
    have hV : IsOpen V := ((continuousOn_extChartAt_symm p).mono interior_subset)
      |>.isOpen_inter_preimage isOpen_interior hU
    have hz : μ {y | y ∈ V ∧ ¬DifferentiableAt ℝ (f ∘ e.symm) y} = 0 := by
      simpa only [ae_iff, not_imp] using
        (hf.comp_extChartAt_symm hU p).ae_differentiableAt_of_mem (μ := μ) hV
    refine measure_mono_null ?_ hz
    rintro _ ⟨x, ⟨⟨hxU, hxint, hxbad⟩, hxsrc⟩, rfl⟩
    have hxchart : x ∈ (chartAt H p).source := by simpa only [extChartAt_source] using hxsrc
    refine ⟨⟨(I.isInteriorPoint_iff_of_mem_atlas one_ne_zero (chart_mem_atlas H p)
      hxchart).1 hxint, by rw [mem_preimage, e.left_inv hxsrc]; exact hxU⟩, fun hd ↦ ?_⟩
    refine hxbad ((mdifferentiableAt_iff_of_mem_source hxchart (mem_chart_source F (f x))).2
      ⟨hf.continuousOn.continuousAt (hU.mem_nhds hxU), ?_⟩)
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp] using
      hd.differentiableWithinAt
  refine (TauCeti.isNullSet_boundary (I := I)).union hint |>.mono fun x hx ↦ ?_
  by_cases hxi : I.IsInteriorPoint x
  · exact Or.inr ⟨hx.1, hxi, hx.2⟩
  · exact Or.inl ((I.isBoundaryPoint_iff_not_isInteriorPoint x).2 hxi)

/-- **Rademacher's theorem on a Riemannian manifold.** On a Lindelöf manifold, a map locally
Lipschitz on an open set `U` is differentiable at almost every point of `U` for the Riemannian
volume. -/
theorem ae_mdifferentiableAt_of_mem [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    (hf : LocallyLipschitzOn U f) (hU : IsOpen U) :
    ∀ᵐ x ∂TauCeti.riemannianVolume I M, x ∈ U → MDifferentiableAt I 𝓘(ℝ, F) f x := by
  borelize E
  simpa only [ae_iff, not_imp] using
    (hf.isNullSet_setOf_not_mdifferentiableAt hU).riemannianVolume_eq_zero

end LocallyLipschitzOn

/-- **Rademacher's theorem on a Riemannian manifold.** On a Lindelöf manifold, a locally
Lipschitz map is differentiable almost everywhere for the Riemannian volume. -/
theorem LocallyLipschitz.ae_mdifferentiableAt [MeasurableSpace M] [BorelSpace M]
    [LindelofSpace M] (hf : LocallyLipschitz f) :
    ∀ᵐ x ∂TauCeti.riemannianVolume I M, MDifferentiableAt I 𝓘(ℝ, F) f x := by
  simpa only [mem_univ, forall_const] using
    (locallyLipschitzOn_univ.2 hf).ae_mdifferentiableAt_of_mem (I := I) isOpen_univ

/-- **Rademacher's theorem on a Riemannian manifold.** On a Lindelöf manifold, a Lipschitz map is
differentiable almost everywhere for the Riemannian volume. -/
theorem LipschitzWith.ae_mdifferentiableAt [MeasurableSpace M] [BorelSpace M]
    [LindelofSpace M] {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∀ᵐ x ∂TauCeti.riemannianVolume I M, MDifferentiableAt I 𝓘(ℝ, F) f x :=
  hf.locallyLipschitz.ae_mdifferentiableAt
