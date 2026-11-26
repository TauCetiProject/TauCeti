/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Density.Integral
public import TauCeti.Geometry.Manifold.ExtChartAt.Integral
public import TauCeti.Geometry.Manifold.VectorBundle.Density
public import Mathlib.Topology.PartitionOfUnity
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.Measure
import TauCeti.MeasureTheory.Measure.Haar.OfBasis
import TauCeti.Topology.PartitionOfUnity.Basic

/-!
# Regularity, partitions of unity, and coordinate formulas for density integration

Provides chart-support and bundle-continuity lemmas for `RoughDensity.inChartAt`, integrability
under continuous scalar multiplication (`IntegrableDensity.fun_smul`) and for continuous or `C^n`
sections of `TauCeti.DensityBundle` (`RoughDensity.integrableDensity_of_continuous_section`,
`RoughDensity.integrableDensity_of_contMDiff_section`), partition-of-unity decompositions
(`integralDensity_eq_finsum_partitionOfUnity`), chosen-cover and almost-everywhere
single-chart integration (`integralDensity_eq_sum_chooseChartCover`,
`integralDensity_eq_integral_inChartAt_of_ae_support`), real-line specialization, and
zero-dimensional integration (`integralDensity_zeroDim`).
-/

public section

noncomputable section

open Bundle MeasureTheory Set Module
open scoped Manifold ContDiff Topology

namespace TauCeti

section ChartSupportAndContinuity

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {m : ℕ}

namespace RoughDensity

/-- If `μ ((extChartAt I α).symm y) = 0`, then `μ.inChartAt b α y = 0`. -/
theorem inChartAt_eq_zero_of_apply_eq_zero {μ : RoughDensity I M m} (b : Basis (Fin m) ℝ E)
    (α : M) {y : E} (h : μ ((extChartAt I α).symm y) = 0) : μ.inChartAt b α y = 0 := by
  by_cases hy : y ∈ (extChartAt I α).target
  · rw [μ.inChartAt_of_mem_target b α hy, h, Density.zero_apply]
  · exact μ.inChartAt_of_notMem_target b α hy

/-- If `x ∈ (extChartAt I α).source` lies outside `tsupport μ`, then
`μ.inChartAt b α (extChartAt I α x) = 0`. -/
theorem inChartAt_eq_zero_of_notMem_tsupport (μ : RoughDensity I M m)
    (b : Basis (Fin m) ℝ E) (α : M) {x : M} (hx : x ∈ (extChartAt I α).source)
    (hn : x ∉ _root_.tsupport (α := Density E m) μ) :
    μ.inChartAt b α (extChartAt I α x) = 0 :=
  inChartAt_eq_zero_of_apply_eq_zero b α <| by
    rw [(extChartAt I α).left_inv hx]
    exact _root_.image_eq_zero_of_notMem_tsupport (α := Density E m) hn

/-- Chart coefficients vanish outside the coordinate target. -/
theorem support_inChartAt_subset_target (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E)
    (α : M) : Function.support (μ.inChartAt b α) ⊆ (extChartAt I α).target := by
  intro y hy
  by_contra hyt
  exact hy (μ.inChartAt_of_notMem_target b α hyt)

/-- `Function.support (μ.inChartAt b α)` lies in the coordinate image of
`(extChartAt I α).source ∩ tsupport μ`. -/
theorem support_inChartAt_subset (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M) :
    Function.support (μ.inChartAt b α) ⊆
      (extChartAt I α) '' ((extChartAt I α).source ∩ _root_.tsupport (α := Density E m) μ) := by
  intro y hy
  have hyt := μ.support_inChartAt_subset_target b α hy
  refine ⟨(extChartAt I α).symm y, ⟨(extChartAt I α).map_target hyt, ?_⟩,
    (extChartAt I α).right_inv hyt⟩
  exact _root_.subset_tsupport (α := Density E m) μ fun h0 ↦
    Function.mem_support.mp hy (inChartAt_eq_zero_of_apply_eq_zero b α h0)

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

end ChartSupportAndContinuity

section RegularityAndFormulas

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {m : ℕ}

/-- Pointwise multiplication by a continuous scalar function preserves `IntegrableDensity`, with no
Hausdorff assumption on the manifold. -/
theorem IntegrableDensity.fun_smul {μ : RoughDensity I M m} (hμ : IntegrableDensity μ)
    {f : M → ℝ} (hf : Continuous f) : IntegrableDensity (fun x ↦ f x • μ x) := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  -- Clamp `f` to its compact-support bound to obtain a globally bounded continuous multiplier.
  obtain ⟨B, hB⟩ := hμ.isCompact.exists_bound_of_continuousOn hf.continuousOn
  let C := max B 0
  let g : M → ℝ := fun x ↦ max (-C) (min C (f x))
  have hgf : (fun x ↦ g x • μ x : RoughDensity I M m) = fun x ↦ f x • μ x := by
    funext x
    by_cases hx : x ∈ _root_.tsupport (α := Density E m) μ
    · obtain ⟨hl, hh⟩ := abs_le.mp
        (by simpa only [Real.norm_eq_abs] using (hB x hx).trans (le_max_left B 0))
      simp only [g, C, min_eq_right hh, max_eq_right hl]
    · have hz : μ x = 0 := _root_.image_eq_zero_of_notMem_tsupport (α := Density E m) hx
      simp [hz]
  rw [← hgf, integrableDensity_iff]
  refine ⟨hμ.isCompact.of_isClosed_subset (_root_.isClosed_tsupport _)
    (_root_.tsupport_smul_subset_right g (show M → Density E m from μ)),
    hμ.nonempty_basis, fun b α ↦ ?_⟩
  have hm := measurableSet_extChartAt_target (I := I) α
  refine (integrableOn_iff_integrable_of_support_subset
    (RoughDensity.support_inChartAt_subset_target _ b α)).mp ?_
  refine IntegrableOn.congr_fun ?_ (fun y _ ↦ (RoughDensity.inChartAt_fun_smul g μ b α y).symm) hm
  exact (hμ.integrable_inChartAt b α).integrableOn.bdd_mul
    (((continuous_const.max (continuous_const.min hf)).comp_continuousOn
      (continuousOn_extChartAt_symm α)).aestronglyMeasurable hm (μ := b.addHaar))
    (Filter.Eventually.of_forall fun _ ↦ (Real.norm_eq_abs _).trans_le <| abs_le.mpr
      ⟨le_max_left _ _, max_le (neg_le_self (le_max_right B 0)) (min_le_left _ _)⟩)

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

/-- The integral of an integrable density is the sum of its chart integrals over the disjointed
pieces of `chooseChartCover` for its support. -/
theorem integralDensity_eq_sum_chooseChartCover [IsManifold I 1 M]
    [MeasurableSpace E] [BorelSpace E] {μ : RoughDensity I M m} (hi : IntegrableDensity μ)
    (b : Basis (Fin m) ℝ E) :
    let c := chooseChartCover (I := I) (_root_.tsupport (α := Density E m) μ) hi.isCompact
    integralDensity μ =
      ∑ i, ∫ y in (extChartAt I (c.center i)) '' disjointed c.domain i,
        μ.inChartAt b (c.center i) y ∂b.addHaar := by
  let c := chooseChartCover (I := I) (_root_.tsupport (α := Density E m) μ) hi.isCompact
  exact integralDensity_eq_sum_disjointed_chart_integrals hi b c.center c.domain
    (fun i ↦ (c.isOpen_domain i).isChartMeasurable) c.domain_subset
    fun x hx ↦ c.covers (subset_closure hx)

/-- A single preferred chart computes `integralDensity` whenever `μ` vanishes outside that chart up
to a chartwise null set. -/
theorem integralDensity_eq_integral_inChartAt_of_ae_support [IsManifold I 1 M]
    [MeasurableSpace E] [BorelSpace E] {μ : RoughDensity I M m} (hi : IntegrableDensity μ)
    (b : Basis (Fin m) ℝ E) (α : M) (hs : IsNullSet I ({x | μ x ≠ 0} \ (extChartAt I α).source)) :
    integralDensity μ = ∫ y, μ.inChartAt b α y ∂b.addHaar := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let c := chooseChartCover (I := I) (_root_.tsupport (α := Density E m) μ) hi.isCompact
  have hsum := integralDensity_eq_sum_chooseChartCover hi b
  have hα_full : (∫ y, μ.inChartAt b α y ∂b.addHaar) =
      ∫ y in (extChartAt I α) '' (extChartAt I α).source, μ.inChartAt b α y ∂b.addHaar := by
    rw [(extChartAt I α).image_source_eq_target]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hy ↦
      μ.inChartAt_of_notMem_target b α hy).symm
  have hα_split := setIntegral_image_extChartAt_eq_sum_disjointed α
    (hi.integrable_inChartAt b α).integrableOn
    (isOpen_extChartAt_source (I := I) α).isChartMeasurable
    Subset.rfl (fun i ↦ (c.isOpen_domain i).isChartMeasurable)
    fun x hx hn ↦ μ.inChartAt_eq_zero_of_notMem_tsupport b α hx fun hts ↦ hn (c.covers hts)
  rw [hsum, hα_full, hα_split]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hpiece_meas := c.isChartMeasurable_piece i
  have hα_meas : IsChartMeasurable I (extChartAt I α).source :=
    (isOpen_extChartAt_source α).isChartMeasurable
  have hinter_sub : c.piece i ∩ (extChartAt I α).source ⊆
      (extChartAt I (c.center i)).source ∩ (extChartAt I α).source :=
    fun _ hx ↦ ⟨c.piece_subset i hx.1, hx.2⟩
  have hch := (μ.setIntegral_inChartAt_changeChart b (c.center i) α hinter_sub
    ((hpiece_meas.inter hα_meas).image_extChartAt (c.center i)
      (inter_subset_left.trans (c.piece_subset i))) b.addHaar).1
  rw [inter_comm ((extChartAt I α).source) (disjointed c.domain i)]
  simp_rw [← ChartCover.piece_def]
  rw [← hch]
  refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (μ := b.addHaar)
    (f := μ.inChartAt b (c.center i)) (c.measurableSet_image_piece i).nullMeasurableSet
    (image_mono (inter_subset_left : c.piece i ∩ (extChartAt I α).source ⊆ c.piece i)) ?_
  filter_upwards [hs.ae_extChartAt_symm_notMem_of_sdiff_source (c.center i) b.addHaar] with y hy
  rintro ⟨⟨x, hx, rfl⟩, hnot⟩
  have hxo : extChartAt I (c.center i) x ∉ (extChartAt I (c.center i)) ''
      ((extChartAt I (c.center i)).source ∩ (extChartAt I α).source) := by
    rintro ⟨x', hx', heq⟩
    have hx_eq : x' = x := (extChartAt I (c.center i)).injOn hx'.1 (c.piece_subset i hx) heq
    exact hnot ⟨x, ⟨hx, hx_eq ▸ hx'.2⟩, rfl⟩
  exact μ.inChartAt_eq_zero_of_apply_eq_zero b (c.center i)
    (not_not.mp (hy hxo ((extChartAt I (c.center i)).map_source (c.piece_subset i hx))))

/-- On a model normed space `E`, `μ` is integrable iff `tsupport μ` is compact and `x ↦ μ x b` is
Haar-integrable against `b.addHaar` in any model basis `b`. -/
theorem integrableDensity_modelSpace_iff [MeasurableSpace E] [BorelSpace E]
    {μ : RoughDensity 𝓘(ℝ, E) E m} (b : Basis (Fin m) ℝ E) :
    IntegrableDensity μ ↔
      IsCompact (_root_.tsupport (α := Density E m) μ) ∧ Integrable (fun x ↦ μ x b) b.addHaar := by
  refine ⟨fun hi ↦ ⟨hi.isCompact, ?_⟩, fun ⟨hc, hint⟩ ↦ ?_⟩
  · rw [← μ.inChartAt_modelSpace b 0]
    exact hi.integrable_inChartAt b 0
  · refine (μ.integrableDensity_iff_of_tsupport_subset_chart b 0 hc (by simp)).mpr ?_
    rwa [μ.inChartAt_modelSpace b 0]

/-- Evaluating a `1`-density on `ℝ` at `Basis.singleton (Fin 1) ℝ` agrees with evaluating it on the
constant tuple `fun _ ↦ 1`. -/
private theorem apply_basis_singleton (μ : RoughDensity 𝓘(ℝ, ℝ) ℝ 1) (t : ℝ) :
    μ t (Basis.singleton (Fin 1) ℝ) = μ t (fun _ ↦ (1 : ℝ)) :=
  congrArg (μ t) (by rw [Basis.coe_singleton, Pi.one_def])

/-- On `ℝ`, a `1`-density `μ` is integrable iff `tsupport μ` is compact and
`t ↦ μ t (fun _ ↦ 1)` is Lebesgue-integrable. -/
theorem integrableDensity_real_iff {μ : RoughDensity 𝓘(ℝ, ℝ) ℝ 1} :
    IntegrableDensity μ ↔
      IsCompact (_root_.tsupport (α := Density ℝ 1) μ) ∧
        Integrable (fun t ↦ μ t (fun _ ↦ (1 : ℝ))) := by
  simp only [integrableDensity_modelSpace_iff (Basis.singleton (Fin 1) ℝ),
    Basis.addHaar_singleton, apply_basis_singleton]

/-- On `ℝ`, the integral of an integrable `1`-density is `∫ t, μ t (fun _ ↦ 1)`. -/
theorem integralDensity_real_eq_integral {μ : RoughDensity 𝓘(ℝ, ℝ) ℝ 1}
    (hi : IntegrableDensity μ) : integralDensity μ = ∫ t, μ t (fun _ ↦ (1 : ℝ)) := by
  simp only [integralDensity_modelSpace hi (Basis.singleton (Fin 1) ℝ),
    Basis.addHaar_singleton, apply_basis_singleton]

section ZeroDim

variable [Subsingleton E]

/-- On a zero-dimensional model space, the Haar integral of a function over any nonempty set is
its value at any point `x`. -/
private theorem integral_addHaar_subsingleton [MeasurableSpace E] [BorelSpace E]
    (b : Basis (Fin 0) ℝ E) (f : E → ℝ) {s : Set E} (hs : s.Nonempty) (x : E) :
    (∫ y in s, f y ∂b.addHaar) = f x := by
  rw [hs.eq_univ, Measure.restrict_univ, Basis.addHaar_eq_dirac, integral_dirac,
    Subsingleton.elim 0 x]

/-- On a zero-dimensional manifold, a rough density is integrable iff its support is finite. -/
theorem integrableDensity_zeroDim_iff (μ : RoughDensity I M 0) :
    IntegrableDensity μ ↔ {x | μ x ≠ 0}.Finite := by
  have : DiscreteTopology M := I.discreteTopology M
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  rw [integrableDensity_iff]
  unfold _root_.tsupport
  rw [closure_discrete, isCompact_iff_finite]
  exact ⟨fun h ↦ h.1, fun hfin ↦ ⟨hfin, ⟨Basis.empty E⟩, fun _ _ ↦ by
    rw [Basis.addHaar_eq_dirac]
    exact integrable_dirac (by simp)⟩⟩

/-- On a zero-dimensional charted manifold, `integralDensity μ = ∑ᶠ x : M, μ x 0` unconditionally,
with no orientation signs or smoothness hypothesis. -/
theorem integralDensity_zeroDim (μ : RoughDensity I M 0) :
    integralDensity μ = ∑ᶠ x : M, μ x 0 := by
  classical
  have hsupp_eq : Function.support (fun x : M ↦ μ x 0) = {x | μ x ≠ 0} := Set.ext fun x ↦
    not_congr ⟨fun h ↦ by
      dsimp only at h
      ext v
      rw [Subsingleton.elim v 0, h, Density.zero_apply],
      fun h ↦ by dsimp only; rw [h, Density.zero_apply]⟩
  by_cases hfin : {x | μ x ≠ 0}.Finite
  swap
  · rw [integralDensity_eq_zero_of_not_integrable (mt (integrableDensity_zeroDim_iff μ).mp hfin),
      finsum_of_infinite_support (by rwa [hsupp_eq])]
  have : DiscreteTopology M := I.discreteTopology M
  have : IsManifold I 1 M := isManifold_of_contDiffOn I 1 M fun _ _ _ _ ↦
    contDiffOn_const (c := (0 : E)).congr fun _ _ ↦ Subsingleton.elim _ _
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let b : Basis (Fin 0) ℝ E := Basis.empty E
  let s := hfin.toFinset
  let e := s.equivFin
  let α (i : Fin s.card) : M := e.symm i
  have hdisj : Pairwise fun i j ↦ Disjoint ({α i} : Set M) {α j} := fun _ _ hij ↦
    disjoint_singleton.mpr fun h ↦ hij (e.symm.injective (Subtype.ext h))
  rw [integralDensity_eq_sum_disjointed_chart_integrals
      ((integrableDensity_zeroDim_iff μ).mpr hfin) b α (fun i ↦ {α i})
      (fun i ↦ (extChartAt_source_zeroDim (I := I) (α i) ▸
        isOpen_extChartAt_source (α i)).isChartMeasurable)
      (fun i ↦ (extChartAt_source_zeroDim (I := I) (α i)).ge)
      (fun x hx ↦ mem_iUnion.mpr ⟨e ⟨x, hfin.mem_toFinset.mpr hx⟩, by simp [α]⟩)]
  have hterm (i : Fin s.card) : (∫ y in (extChartAt I (α i)) '' disjointed (fun j ↦ {α j}) i,
      μ.inChartAt b (α i) y ∂b.addHaar) = μ (α i) 0 := by
    rw [disjointed_eq_self fun j hj ↦ hdisj hj.ne, image_singleton,
      integral_addHaar_subsingleton b _ (singleton_nonempty _) (extChartAt I (α i) (α i)),
      μ.inChartAt_self]
    exact congrArg (μ (α i)) (Subsingleton.elim _ 0)
  simp_rw [hterm]
  rw [finsum_eq_sum_of_support_subset (f := fun x : M ↦ μ x 0) (s := s)
    (hsupp_eq ▸ hfin.coe_toFinset.ge)]
  exact (Fintype.sum_equiv e.symm (fun i ↦ μ (α i) 0) (fun x : s ↦ μ x.val 0) fun _ ↦ rfl).trans
    (Finset.sum_attach s fun x ↦ μ x 0)

/-- On a zero-dimensional charted manifold, any rough density supported in `{x}` is integrable. -/
theorem integrableDensity_zeroDim_singleton (μ : RoughDensity I M 0) (x : M)
    (hs : _root_.tsupport (α := Density E 0) μ ⊆ {x}) : IntegrableDensity μ :=
  (integrableDensity_zeroDim_iff μ).mpr
    ((finite_singleton x).subset fun _ hy ↦ hs (_root_.subset_tsupport (α := Density E 0) μ hy))

/-- On a zero-dimensional manifold, a rough density supported in `{x}` integrates to `μ x 0`. -/
theorem integralDensity_zeroDim_singleton (μ : RoughDensity I M 0) (x : M)
    (hs : _root_.tsupport (α := Density E 0) μ ⊆ {x}) : integralDensity μ = μ x 0 := by
  rw [integralDensity_zeroDim, finsum_eq_single _ x]
  intro y hy
  have h0 : μ y = 0 := _root_.image_eq_zero_of_notMem_tsupport (α := Density E 0) fun h ↦ hy (hs h)
  rw [h0, Density.zero_apply]

/-- On a finite zero-dimensional charted manifold, `integralDensity μ = ∑ x : M, μ x 0`. -/
theorem integralDensity_finite_zeroDim [Fintype M] (μ : RoughDensity I M 0) :
    integralDensity μ = ∑ x : M, μ x 0 := by
  rw [integralDensity_zeroDim, finsum_eq_sum_of_fintype]

end ZeroDim

end RegularityAndFormulas

end TauCeti
