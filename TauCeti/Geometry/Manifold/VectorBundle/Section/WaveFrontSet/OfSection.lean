/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution.OfSection
public import TauCeti.Geometry.Manifold.VectorBundle.Section.WaveFrontSet
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.Basic
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact

/-!
# Smooth sections and the singular support of distributional sections

Let `W → M` be a smooth real vector bundle with finite-dimensional model fibre `G` over a manifold
without boundary modelled on a finite-dimensional real inner product space `E`. The singular
support of a distributional section `T` of `W` (`TauCeti.BundleTest.singularSupport`) is defined
by reading `T` in a chart and a frame: `x` lies outside it when the components of the local
representative of `T` are smooth functions near the chart image of `x`. This file shows that this
is the intrinsic notion: `x` lies outside the singular support of `T` exactly when, near `x`, `T`
is the distributional section of a smooth section of `W`
(`TauCeti.BundleDistribution.notMem_singularSupport_iff_exists_notMem_dsupport_sub_ofSection`),
that is, when `T - ofSection u` vanishes near `x` for a smooth section `u`.

In particular a smooth section `u` has empty singular support and empty wave front set
(`TauCeti.BundleDistribution.singularSupport_ofSection_eq_empty`,
`TauCeti.BundleDistribution.waveFrontSet_ofSection_eq_empty`). More precisely, a locally
integrable section that is smooth on a neighbourhood of `x` is smooth near `x` as a distributional
section (`TauCeti.BundleDistribution.notMem_singularSupport_ofSection`).

## The argument

Work in the preferred chart at `x`, restricted to the base set of the preferred frame of the
dual-density bundle (`TauCeti.baseSetChart`), and in that frame. There the local representative of
the distributional section of a locally integrable section `u` pairs a test function `φ` and a
covector `v` as `∫ φ (v ∘ s)` for the reading `s` of `u`
(`TauCeti.chartDistributionCLM_ofSection_apply_apply`), so its components are smooth wherever `u`
is.

Conversely, suppose that the components of the local representative of `T` along a basis `(bᵢ)` of
the model fibre `G →L[ℝ] ℝ` of the dual-density bundle are smooth functions `fᵢ` near the chart
image of `x`. These components are complex distributions with real values on real tests, so they
are also given by the real parts of the `fᵢ`, and near the chart image of `x` the local
representative of `T` is integration against the smooth function `g = ∑ᵢ (re fᵢ) bᵢ*` with values
in the double dual of `G`. Identified with a `G`-valued function through the finite-dimensional
double-dual equivalence (`TauCeti.inclusionInDoubleDualEquiv`), and up to the constant relating
the two Haar measures of `E` involved, `g` is the reading of a smooth section `u` of `W`, cut off
away from `x` by a smooth function equal to `1` near `x`. The local representatives of `T` and of
the distributional section of `u` then agree on the test functions supported near the chart image
of `x`, so `T - ofSection u` vanishes near `x`.
This last step uses that a functional on bundle tests vanishes over the part of a chart where its
local representative vanishes
(`Bundle.Trivialization.isVanishingOn_of_isVanishingOn_chartDistributionCLM`), the converse of
`Bundle.Trivialization.isVanishingOn_chartComponent`: a bundle test supported there is the chart
extension of its chart localization along a cutoff equal to `1` on its support.

## Main results

* `TauCeti.BundleDistribution.notMem_singularSupport_ofSection`: a locally integrable section that
  is smooth near `x` has `x` outside its singular support.
* `TauCeti.BundleDistribution.singularSupport_ofSection_eq_empty`,
  `TauCeti.BundleDistribution.waveFrontSet_ofSection_eq_empty`: a smooth section has empty
  singular support and empty wave front set.
* `TauCeti.BundleDistribution.notMem_singularSupport_iff_exists_notMem_dsupport_sub_ofSection`:
  `x` lies outside the singular support of `T` exactly when `T` agrees near `x` with the
  distributional section of a smooth section.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §2.2 (the singular support) and §6.3 (distributions on manifolds).
-/

public section

noncomputable section

open Set Filter Function TopologicalSpace Bundle MeasureTheory ContinuousLinearMap
open scoped Manifold ContDiff Distributions Topology CompactConvergenceCLM

/-! ### Smooth sections -/

namespace TauCeti.BundleDistribution

open BundleTest

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {W : M → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [∀ x, TopologicalSpace (W x)] [TopologicalSpace (TotalSpace G W)]
  [FiberBundle G W] [VectorBundle ℝ G W] [ContMDiffVectorBundle ∞ G W I]

/-- The two Haar measures on `E` met here, the one of the fixed basis used to read sections and
the volume used for the singular support of distributions on `E`, differ by a positive factor. -/
private theorem exists_pos_integral_finBasis_addHaar_eq :
    ∃ r : ℝ, 0 < r ∧
      ∀ f : E → ℝ, ∫ z, f z ∂(Module.finBasis ℝ E).addHaar = r * ∫ z, f z := by
  refine ⟨Measure.addHaarScalarFactor (Module.finBasis ℝ E).addHaar volume,
    NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _), fun f ↦ ?_⟩
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul (Module.finBasis ℝ E).addHaar volume]
  rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]

omit [MeasurableSpace E] [BorelSpace E] [T2Space M] [SigmaCompactSpace M] [FiniteDimensional ℝ G]
  [ContMDiffVectorBundle ∞ G W I] in
/-- A point of the preferred chart at `x`, restricted to the base set of the preferred frame of
the dual-density bundle, lies in the first-jet chart domain of `W` at `x`. -/
private theorem mem_firstJetBundle_baseSet {x y : M}
    (hy : y ∈ (baseSetChart (G →L[ℝ] ℝ) I (fun x ↦ W x →L[ℝ] DensityBundle I M x) x).source) :
    y ∈ FirstJetBundle.baseSet (H := H) G W x := by
  have h := source_subset_of_subset_baseSet _ (baseSetChart_source_subset _ x) hy
  exact (FirstJetBundle.mem_baseSet_iff G W).2 ⟨h.2, h.1⟩

/-- **A section smooth near a point is smooth there as a distributional section.** If a locally
integrable section `u` of `W` is smooth on a neighbourhood `U` of `x`, then `x` lies outside the
singular support of its distributional section. -/
theorem notMem_singularSupport_ofSection {u : (x : M) → W x} (hu : LocallyIntegrableSection I G u)
    {U : Set M} (hU : IsOpen U) {x : M} (hxU : x ∈ U)
    (hus : ContMDiffOn I (I.prod 𝓘(ℝ, G)) ∞ (fun y ↦ TotalSpace.mk' G y (u y)) U) :
    x ∉ singularSupport I (ofSection I G u) := by
  set V := fun x ↦ W x →L[ℝ] DensityBundle I M x
  set c := baseSetChart (G →L[ℝ] ℝ) I V x
  have hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source := contMDiffOn_baseSetChart V x
  have hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target := contMDiffOn_baseSetChart_symm V x
  have hxc : x ∈ c.source := mem_baseSetChart_source V x
  have hcα : EqOn c (extChartAt I x) c.source := eqOn_baseSetChart_extChartAt V x
  obtain ⟨r, -, hr⟩ := exists_pos_integral_finBasis_addHaar_eq (E := E)
  rw [notMem_singularSupport_iff _ hc hcs (baseSetChart_source_subset V x) hxc]
  refine fun v ↦ (Distribution.notMem_singularSupport_iff (c.map_source hxc)).2
    ⟨c.target ∩ c.symm ⁻¹' U, c.isOpen_inter_preimage_symm hU,
      ⟨c.map_source hxc, by rwa [mem_preimage, c.left_inv hxc]⟩,
      fun z ↦ ((r * v (FirstJetBundle.localRep I G u x z) : ℝ) : ℂ), fun z hz ↦ ?_, fun φ _ ↦ ?_⟩
  · -- The reading of `u` is smooth at the chart images of the points of `U`.
    have hy := c.map_target hz.1
    have h := FirstJetBundle.contDiffAt_localRep I G (hus.contMDiffAt (hU.mem_nhds hz.2))
      (mem_firstJetBundle_baseSet hy)
    rw [extChartAt_baseSetChart_symm V x hz.1] at h
    exact (Complex.ofRealCLM.contDiff.comp_contDiffAt _
      (contDiffAt_const.mul (v.contDiff.contDiffAt.comp _ h))).contDiffWithinAt
  · rw [Trivialization.chartComponent_apply, ← Trivialization.chartDistributionCLM_apply_apply,
      chartDistributionCLM_ofSection_apply_apply c hc _ hcα hu, hr, ← integral_const_mul,
      ← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    simp only [Complex.real_smul, Complex.ofReal_mul]
    ring

/-- A smooth section of `W` has empty singular support as a distributional section. -/
@[simp]
theorem singularSupport_ofSection_eq_empty {u : (x : M) → W x}
    (hu : ContMDiff I (I.prod 𝓘(ℝ, G)) ∞ fun y ↦ TotalSpace.mk' G y (u y)) :
    singularSupport I (ofSection I G u) = ∅ :=
  eq_empty_iff_forall_notMem.2 fun x ↦ notMem_singularSupport_ofSection
    (hu.continuous.locallyIntegrableSection I) isOpen_univ (mem_univ x) hu.contMDiffOn

/-- **A smooth section has empty wave front set** as a distributional section. -/
@[simp]
theorem waveFrontSet_ofSection_eq_empty {u : (x : M) → W x}
    (hu : ContMDiff I (I.prod 𝓘(ℝ, G)) ∞ fun y ↦ TotalSpace.mk' G y (u y)) :
    waveFrontSet I (ofSection I G u) = ∅ :=
  singularSupport_eq_empty_iff_waveFrontSet_eq_empty.1 (singularSupport_ofSection_eq_empty hu)

/-! ### The singular support is where a distributional section is not a smooth section -/

omit [I.Boundaryless] [SigmaCompactSpace M] in
/-- **Smooth components give a smooth reading.** If the components of the local representative of
a distributional section `T` in a chart and a frame are smooth near `z₀`, then near `z₀` the local
representative is integration against a smooth function `g` with values in the covectors of the
model fibre `G →L[ℝ] ℝ` of the dual-density bundle. -/
private theorem exists_contDiffOn_chartDistributionCLM_eq_integral
    {t : Trivialization (G →L[ℝ] ℝ) (π (G →L[ℝ] ℝ) (fun x ↦ W x →L[ℝ] DensityBundle I M x))}
    [MemTrivializationAtlas t] {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hct : c.source ⊆ t.baseSet)
    {T : BundleDistribution I M G W} {z₀ : E} (hz₀ : z₀ ∈ c.target)
    (hT : ∀ v, z₀ ∉ Distribution.singularSupport (t.chartComponent c hc hct T v)) :
    ∃ B : Set E, IsOpen B ∧ z₀ ∈ B ∧ ∃ g : E → (G →L[ℝ] ℝ) →L[ℝ] ℝ, ContDiffOn ℝ ∞ g B ∧
      ∀ φ : 𝓓(⟨c.target, c.open_target⟩, ℝ), tsupport φ ⊆ B → ∀ v,
        t.chartDistributionCLM c hc hct T φ v = ∫ z, φ z * g z v := by
  set b := Module.finBasis ℝ (G →L[ℝ] ℝ)
  choose U hU hzU f hf hTf using fun i ↦ (Distribution.notMem_singularSupport_iff
    (Opens.mem_mk.2 hz₀)).1 (hT (b i))
  refine ⟨⋂ i, U i, isOpen_iInter_of_finite hU, mem_iInter.2 hzU,
    fun z ↦ ∑ i, (f i z).re • (b.coord i).toContinuousLinearMap, ContDiffOn.sum fun i _ ↦
      ((toSpanSingleton ℝ (b.coord i).toContinuousLinearMap).contDiff.comp_contDiffOn
        (Complex.reCLM.contDiff.comp_contDiffOn ((hf i).mono (iInter_subset _ i)))).congr
          fun z _ ↦ by simp, fun φ hφ v ↦ ?_⟩
  have hint (i) := φ.integrable_smul_of_continuousOn (μ := volume) (hf i).continuousOn
    (hφ.trans (iInter_subset _ i))
  -- The component along `bᵢ` is a real distribution, given by the real part of `fᵢ`.
  have hi (i) : t.chartDistributionCLM c hc hct T φ (b i) = ∫ z, φ z * (f i z).re := by
    have h := congrArg Complex.re (hTf i φ (hφ.trans (iInter_subset _ i)))
    rw [Trivialization.chartComponent_apply, ← Trivialization.chartDistributionCLM_apply_apply,
      Complex.ofReal_re, ← Complex.reCLM_apply,
      ← ContinuousLinearMap.integral_comp_comm _ (hint i)] at h
    simpa using h
  conv_lhs => rw [← b.sum_repr v]
  simp_rw [map_sum, map_smul, hi, smul_eq_mul, ← integral_const_mul]
  rw [← integral_finsetSum _ fun i _ ↦
    ((hint i).re.congr (ae_of_all _ fun z ↦ by simp)).const_mul _]
  refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
  simp only [_root_.sum_apply, _root_.smul_apply, LinearMap.coe_toContinuousLinearMap',
    Module.Basis.coord_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

omit [MeasurableSpace E] [BorelSpace E] [T2Space M] [SigmaCompactSpace M] [FiniteDimensional ℝ G]
  [ContMDiffVectorBundle ∞ G W I] in
/-- Read in the preferred chart `c` at `x`, restricted to the base set of the preferred frame of
the dual-density bundle, the section `y ↦ ρ y • τ⁻¹ (k (c y))` is `k` wherever `ρ` is `1`, for the
preferred trivialization `τ` of `W` at `x`. -/
private theorem localRep_smul_symm_eq {x : M} {ρ : M → ℝ} {k : E → G} {z : E}
    (hz : z ∈ (baseSetChart (G →L[ℝ] ℝ) I (fun x ↦ W x →L[ℝ] DensityBundle I M x) x).target)
    (hρ : ρ ((baseSetChart (G →L[ℝ] ℝ) I (fun x ↦ W x →L[ℝ] DensityBundle I M x) x).symm z) = 1) :
    FirstJetBundle.localRep I G (fun y ↦ ρ y • (trivializationAt G W x).symm y
      (k (baseSetChart (G →L[ℝ] ℝ) I (fun x ↦ W x →L[ℝ] DensityBundle I M x) x y))) x z =
      k z := by
  set c := baseSetChart (G →L[ℝ] ℝ) I (fun x ↦ W x →L[ℝ] DensityBundle I M x) x
  have hy := c.map_target hz
  have hy' := (FirstJetBundle.mem_baseSet_iff G W).1 (mem_firstJetBundle_baseSet hy)
  rw [FirstJetBundle.localRep_apply, ← symm_eq_extChartAt_symm c (baseSetChart_source_subset _ x)
    (eqOn_baseSetChart_extChartAt _ x) hz, hρ, one_smul,
    (trivializationAt G W x).apply_mk_symm hy'.1, c.right_inv hz]

/-- The reading of a distributional section near a point outside its singular support, divided by
the factor between the two Haar measures, is the reading of a smooth section cut off away from the
point. So `T` agrees near such a point with the distributional section of a smooth section. -/
private theorem exists_contMDiff_notMem_dsupport_sub_ofSection {T : BundleDistribution I M G W}
    {x : M} (hx : x ∉ singularSupport I T) :
    ∃ u : (y : M) → W y, ContMDiff I (I.prod 𝓘(ℝ, G)) ∞ (fun y ↦ TotalSpace.mk' G y (u y)) ∧
      x ∉ dsupport ⇑(T - ofSection I G u) := by
  set V := fun x ↦ W x →L[ℝ] DensityBundle I M x
  set c := baseSetChart (G →L[ℝ] ℝ) I V x
  have hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source := contMDiffOn_baseSetChart V x
  have hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target := contMDiffOn_baseSetChart_symm V x
  have hct := baseSetChart_source_subset (I := I) (F := G →L[ℝ] ℝ) V x
  have hxc : x ∈ c.source := mem_baseSetChart_source V x
  have hcα : EqOn c (extChartAt I x) c.source := eqOn_baseSetChart_extChartAt V x
  obtain ⟨B, hB, hxB, g, hg, hTg⟩ := exists_contDiffOn_chartDistributionCLM_eq_integral hc hct
    (c.map_source hxc) ((notMem_singularSupport_iff T hc hcs hct hxc).1 hx)
  obtain ⟨r, hr0, hr⟩ := exists_pos_integral_finBasis_addHaar_eq (E := E)
  -- The section is read in the chart as `k`, with `v (k z) = r⁻¹ g z v`.
  set k : E → G := fun z ↦ r⁻¹ • (inclusionInDoubleDualEquiv ℝ G).symm (g z)
  have hL : ContDiff ℝ ∞ (inclusionInDoubleDualEquiv ℝ G).symm :=
    ContinuousLinearEquiv.contDiff _
  have hk : ContDiffOn ℝ ∞ k B := contDiffOn_const.smul (hL.comp_contDiffOn hg)
  -- A cutoff `ρ` equal to `1` on a neighbourhood `N` of `x`, supported in `c.source ∩ c ⁻¹' B`.
  have hU₀ : IsOpen (c.source ∩ c ⁻¹' B) := c.isOpen_inter_preimage hB
  obtain ⟨ρ, hρ, hρ1, -, hρU, -⟩ := isCompact_singleton.exists_contMDiff_one_nhds_tsupport_subset
    I hU₀ (singleton_subset_iff.2 ⟨hxc, hxB⟩)
  obtain ⟨N, hN1, hN, hxN⟩ := eventually_nhds_iff.1 (by simpa [nhdsSet_singleton] using hρ1)
  set τ := trivializationAt G W x
  have hτ {y : M} (hy : y ∈ c.source) : y ∈ τ.baseSet :=
    ((FirstJetBundle.mem_baseSet_iff G W).1 (mem_firstJetBundle_baseSet hy)).1
  have hu : ContMDiff I (I.prod 𝓘(ℝ, G)) ∞
      fun y ↦ TotalSpace.mk' G y (ρ y • τ.symm y (k (c y))) := by
    refine ContMDiffOn.smul_section_of_tsupport hρ.contMDiffOn hU₀ hρU
      ((τ.contMDiffOn_section_iff hU₀ fun _ hy ↦ hτ hy.1).2 ?_)
    exact ((contMDiffOn_iff_contDiffOn.2 hk).comp (hc.mono inter_subset_left)
      fun _ hy ↦ hy.2).congr fun y hy ↦ by simp [τ.apply_mk_symm (hτ hy.1)]
  have hB' : IsOpen (c.target ∩ c.symm ⁻¹' N ∩ B) := (c.isOpen_inter_preimage_symm hN).inter hB
  refine ⟨_, hu, notMem_dsupport_iff.2 ⟨_, c.isOpen_inter_preimage hB', ⟨hxc, ⟨c.map_source hxc,
      by rwa [mem_preimage, c.left_inv hxc]⟩, hxB⟩,
    Trivialization.isVanishingOn_of_isVanishingOn_chartDistributionCLM _ hc hct hcs hB'
      fun φ hφ ↦ ?_⟩⟩
  -- Over `B ∩ c(N)` the readings of `T` and of the section agree.
  ext v
  rw [map_sub, _root_.sub_apply, _root_.sub_apply, hTg φ (hφ.trans inter_subset_right) v,
    chartDistributionCLM_ofSection_apply_apply c hc hct hcα
      (hu.continuous.locallyIntegrableSection I), hr, ← integral_const_mul, _root_.zero_apply,
    sub_eq_zero]
  refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
  by_cases hz : φ z = 0
  · simp [hz]
  obtain ⟨⟨hzc, hzN⟩, -⟩ := hφ (subset_tsupport _ hz)
  dsimp only
  rw [localRep_smul_symm_eq hzc (hN1 _ hzN), map_smul, apply_inclusionInDoubleDualEquiv_symm,
    smul_eq_mul]
  field_simp

/-- **The singular support of a distributional section.** On a manifold without boundary, a point
`x` lies outside the singular support of a distributional section `T` of `W` exactly when, near
`x`, `T` is the distributional section of a smooth section `u` of `W`: `T - ofSection u` vanishes
on a neighbourhood of `x`. -/
theorem notMem_singularSupport_iff_exists_notMem_dsupport_sub_ofSection
    {T : BundleDistribution I M G W} {x : M} :
    x ∉ singularSupport I T ↔ ∃ u : (y : M) → W y,
      ContMDiff I (I.prod 𝓘(ℝ, G)) ∞ (fun y ↦ TotalSpace.mk' G y (u y)) ∧
        x ∉ dsupport ⇑(T - ofSection I G u) := by
  refine ⟨fun hx ↦ exists_contMDiff_notMem_dsupport_sub_ofSection hx, fun ⟨u, hu, hx⟩ h ↦ ?_⟩
  obtain h | h := singularSupport_add_subset (T - ofSection I G u) (ofSection I G u)
    (by rwa [sub_add_cancel])
  · exact hx (singularSupport_subset_dsupport _ h)
  · rwa [singularSupport_ofSection_eq_empty hu] at h

end TauCeti.BundleDistribution
