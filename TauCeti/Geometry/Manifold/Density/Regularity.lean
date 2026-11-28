/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Density.Integral
public import TauCeti.Geometry.Manifold.VectorBundle.Density
public import Mathlib.Topology.PartitionOfUnity
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Topology.Algebra.Support
import TauCeti.Topology.PartitionOfUnity.Basic

/-!
# Regularity and partitions of unity for density integration

Provides bundle-continuity lemmas for `RoughDensity.inChartAt`, integrability under continuous
scalar multiplication (`IntegrableDensity.fun_smul`) and for continuous or `C^n` sections of
`TauCeti.DensityBundle` (`RoughDensity.integrableDensity_of_continuous_section`,
`RoughDensity.integrableDensity_of_contMDiff_section`), and partition-of-unity decompositions
(`integralDensity_eq_finsum_partitionOfUnity`).
-/

public section

noncomputable section

open Bundle MeasureTheory Set Module
open scoped Manifold ContDiff Topology

namespace TauCeti

section BundleContinuity

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {m : ℕ}

namespace RoughDensity

/-- On a chart target, `μ.inChartAt (finBasis ℝ E) α z` is the fiber coordinate of `μ` in the
preferred trivialization of `TauCeti.DensityBundle`. -/
theorem inChartAt_finBasis_eq_trivializationAt [FiniteDimensional ℝ E] [IsManifold I 1 M]
    (μ : (x : M) → DensityBundle I M x) (α : M) {z : E} (hz : z ∈ (extChartAt I α).target) :
    RoughDensity.inChartAt (I := I) μ (finBasis ℝ E) α z =
      (trivializationAt ℝ (DensityBundle I M) α
        ⟨(extChartAt I α).symm z, μ ((extChartAt I α).symm z)⟩).2 := by
  have hx : (extChartAt I α).symm z ∈ (chartAt H α).source := by
    simpa only [extChartAt_source] using (extChartAt I α).map_target hz
  have htriv : ∀ v : E,
      mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) z v =
        (trivializationAt E (TangentSpace I) α).symm ((extChartAt I α).symm z) v := by
    intro v
    have hL := (TangentBundle.symmL_trivializationAt (I := I) (𝕜 := ℝ) (x₀ := α) hx).symm
    rw [(extChartAt I α).right_inv hz] at hL
    have hL_apply : mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) z v =
        (trivializationAt E (TangentSpace I) α).symmL ℝ ((extChartAt I α).symm z) v :=
      congrArg (fun f : E →L[ℝ] TangentSpace I ((extChartAt I α).symm z) ↦ f v) hL
    rw [hL_apply, (trivializationAt E (TangentSpace I) α).symmL_apply (R := ℝ)
      (by rwa [TangentBundle.trivializationAt_baseSet])]
  rw [RoughDensity.inChartAt_of_mem_target μ (finBasis ℝ E) α hz, Density.trivializationAt_eq,
    Trivialization.density_apply]
  exact congrArg (μ ((extChartAt I α).symm z)) (funext fun i ↦ htriv (finBasis ℝ E i))

/-- A section of `TauCeti.DensityBundle` continuous on a chart source has continuous chart
coefficients in every model basis on that chart's target, including at boundary and corner
points. -/
theorem continuousOn_inChartAt_of_continuousOn_section [FiniteDimensional ℝ E] [IsManifold I 1 M]
    {μ : (x : M) → DensityBundle I M x} (b : Basis (Fin (finrank ℝ E)) ℝ E) {α : M}
    (hμ : ContinuousOn (fun x ↦ TotalSpace.mk' ℝ x (μ x)) (extChartAt I α).source) :
    ContinuousOn (RoughDensity.inChartAt (I := I) μ b α) (extChartAt I α).target := by
  let e := trivializationAt ℝ (DensityBundle I M) α
  have hmap : MapsTo (fun x ↦ TotalSpace.mk' ℝ x (μ x)) (extChartAt I α).source e.source := by
    intro x hx
    rw [e.mem_source]
    dsimp only [TotalSpace.mk', e]
    rw [Density.trivializationAt_eq, Trivialization.density_baseSet,
      TangentBundle.trivializationAt_baseSet]
    simpa only [extChartAt_source] using hx
  have hfin : ContinuousOn (RoughDensity.inChartAt (I := I) μ (finBasis ℝ E) α)
      (extChartAt I α).target :=
    (((e.continuousOn.comp hμ hmap).snd).comp (continuousOn_extChartAt_symm α)
      (extChartAt I α).mapsTo_symm).congr fun _ hz ↦ by
        simpa only [Function.comp_apply, e] using
          inChartAt_finBasis_eq_trivializationAt μ α hz
  have hmul : ContinuousOn (fun y ↦ |(finBasis ℝ E).det b| *
      RoughDensity.inChartAt (I := I) μ (finBasis ℝ E) α y) (extChartAt I α).target :=
    continuousOn_const.mul hfin
  exact hmul.congr fun y _ ↦ RoughDensity.inChartAt_basis_change μ (finBasis ℝ E) b α y

end RoughDensity

end BundleContinuity

section Regularity

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {m : ℕ}

/-- Pointwise multiplication by a continuous scalar function preserves `IntegrableDensity`, with no
Hausdorff assumption on the manifold. -/
theorem IntegrableDensity.fun_smul {μ : RoughDensity I M m} (hμ : IntegrableDensity μ)
    {f : M → ℝ} (hf : Continuous f) : IntegrableDensity (fun x ↦ f x • μ x) := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  -- `TangentSpace I x` is definitionally `E`, so `μ` has fixed codomain `Density E m`.
  let μ' : M → Density E m := μ
  obtain ⟨C, _, g, hgc, hgb, hfg⟩ :=
    TauCeti.exists_continuous_abs_le_fun_smul_eq (f := μ') hμ.isCompact hf
  have hgf : (fun x ↦ g x • μ x : RoughDensity I M m) = fun x ↦ f x • μ x := funext fun x ↦
    congrFun hfg x
  rw [← hgf, integrableDensity_iff]
  refine ⟨hμ.isCompact.of_isClosed_subset (_root_.isClosed_tsupport _)
    (_root_.tsupport_smul_subset_right g μ'), hμ.nonempty_basis, fun b α ↦ ?_⟩
  have hm := measurableSet_extChartAt_target (I := I) α
  refine (integrableOn_iff_integrable_of_support_subset
    (RoughDensity.support_inChartAt_subset_target _ b α)).mp ?_
  refine IntegrableOn.congr_fun ?_ (fun y _ ↦ (RoughDensity.inChartAt_fun_smul g μ b α y).symm) hm
  exact (hμ.integrable_inChartAt b α).integrableOn.bdd_mul
    ((hgc.comp_continuousOn (continuousOn_extChartAt_symm α)).aestronglyMeasurable hm
      (μ := b.addHaar))
    (Filter.Eventually.of_forall fun y ↦
      (Real.norm_eq_abs _).trans_le (hgb ((extChartAt I α).symm y)))

/-- A compactly supported rough density whose chart coefficient in one model basis is continuous on
every preferred chart target is integrable. -/
theorem RoughDensity.integrableDensity_of_continuousOn_inChartAt [IsManifold I 1 M]
    {μ : RoughDensity I M m} (b : Basis (Fin m) ℝ E)
    (hμ : ∀ α, ContinuousOn (μ.inChartAt b α) (extChartAt I α).target)
    (hc : IsCompact (_root_.tsupport (α := Density E m) μ)) :
    IntegrableDensity μ := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let : LocallyCompactSpace H := I.locallyCompactSpace
  obtain ⟨n, β, u, B, hu, hcover⟩ := exists_finite_precompact_chart_cover (I := I) hc
  refine μ.integrableDensity_of_open_cover hc b β u (fun i ↦ (hu i).1)
    (fun i ↦ by simpa only [extChartAt_source] using (hu i).2.1) hcover fun i ↦ ?_
  exact (((hμ (β i)).mono (hu i).2.2.2.1).integrableOn_compact
    (hu i).2.2.1 (μ := b.addHaar)).mono_set (hu i).2.2.2.2

/-- Every compactly supported continuous section of `TauCeti.DensityBundle` is integrable. -/
theorem RoughDensity.integrableDensity_of_continuous_section
    [FiniteDimensional ℝ E] [IsManifold I 1 M] {μ : (x : M) → DensityBundle I M x}
    (hμ : Continuous fun x ↦ TotalSpace.mk' ℝ x (μ x))
    (hc : IsCompact (_root_.tsupport (α := Density E (finrank ℝ E)) μ)) : IntegrableDensity μ :=
  RoughDensity.integrableDensity_of_continuousOn_inChartAt (finBasis ℝ E)
    (fun _ ↦ RoughDensity.continuousOn_inChartAt_of_continuousOn_section
      (finBasis ℝ E) hμ.continuousOn) hc

/-- On a compact manifold, every continuous section of `TauCeti.DensityBundle` is integrable. -/
theorem RoughDensity.integrableDensity_of_continuous_section_of_compactSpace
    [FiniteDimensional ℝ E] [IsManifold I 1 M] [CompactSpace M]
    {μ : (x : M) → DensityBundle I M x}
    (hμ : Continuous fun x ↦ TotalSpace.mk' ℝ x (μ x)) : IntegrableDensity μ :=
  RoughDensity.integrableDensity_of_continuous_section hμ (_root_.isClosed_tsupport _).isCompact

/-- Every compactly supported `C^n` section of `TauCeti.DensityBundle` is integrable. -/
theorem RoughDensity.integrableDensity_of_contMDiff_section
    [FiniteDimensional ℝ E] [IsManifold I 1 M] {n : ℕ∞ω} {μ : (x : M) → DensityBundle I M x}
    (hμ : ContMDiff I (I.prod 𝓘(ℝ)) n fun x ↦ TotalSpace.mk' ℝ x (μ x))
    (hc : IsCompact (_root_.tsupport (α := Density E (finrank ℝ E)) μ)) : IntegrableDensity μ :=
  RoughDensity.integrableDensity_of_continuous_section hμ.continuous hc

/-- A partition of unity covering `tsupport μ` decomposes `integralDensity μ` into a finite sum of
localized integrals, with all remaining terms vanishing. -/
theorem exists_finset_integralDensity_eq_sum_partitionOfUnity [IsManifold I 1 M] {ι : Type*}
    {μ : RoughDensity I M m} (hi : IntegrableDensity μ) {t : Set M} (ρ : PartitionOfUnity ι M t)
    (ht : _root_.tsupport (α := Density E m) μ ⊆ t) :
    ∃ s : Finset ι, integralDensity μ = ∑ i ∈ s, integralDensity (fun x ↦ ρ i x • μ x) ∧
      ∀ i ∉ s, integralDensity (fun x ↦ ρ i x • μ x) = 0 := by
  let μ' : M → Density E m := μ
  obtain ⟨s, hsum, hzero⟩ := ρ.exists_finset_eq_sum_smul μ' hi.isCompact ht
  -- `TangentSpace I x` is definitionally `E`, transferring the fixed-codomain sum.
  have hsum' : μ = ∑ i ∈ s, (fun x ↦ ρ i x • μ x : RoughDensity I M m) := by
    funext x
    rw [Finset.sum_apply]
    exact congrFun hsum x
  have hzero' : ∀ i ∉ s, (fun x ↦ ρ i x • μ x : RoughDensity I M m) = 0 := fun i his ↦ by
    funext x
    exact congrFun (hzero i his) x
  exact ⟨s, (congrArg integralDensity hsum').trans
    (integralDensity_sum _ s fun i _ ↦ hi.fun_smul (ρ i).continuous),
    fun i his ↦ by rw [hzero' i his, integralDensity_zero]⟩

/-- For any partition of unity `ρ` covering `tsupport μ`, `integralDensity μ` equals
`∑ᶠ i, integralDensity (fun x ↦ ρ i x • μ x)`. -/
theorem integralDensity_eq_finsum_partitionOfUnity [IsManifold I 1 M] {ι : Type*}
    {μ : RoughDensity I M m} (hi : IntegrableDensity μ) {t : Set M} (ρ : PartitionOfUnity ι M t)
    (ht : _root_.tsupport (α := Density E m) μ ⊆ t) :
    integralDensity μ = ∑ᶠ i, integralDensity (fun x ↦ ρ i x • μ x) := by
  classical
  obtain ⟨s, hsum, hzero⟩ := exists_finset_integralDensity_eq_sum_partitionOfUnity hi ρ ht
  rw [hsum, finsum_eq_sum_of_support_subset]
  exact fun i hi' ↦ by_contra fun his ↦ Function.mem_support.mp hi' (hzero i his)

end Regularity

end TauCeti
