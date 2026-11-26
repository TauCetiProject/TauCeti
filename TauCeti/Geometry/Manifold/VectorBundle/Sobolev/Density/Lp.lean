/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Lp
import TauCeti.Analysis.Normed.Operator.Banach
import TauCeti.Analysis.Sobolev.BesselPotential.Local
import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz

/-!
# Reconstruction and density in the Bessel-potential spaces of a square chart partition

Let `A` be a square chart partition of a smooth real vector bundle `V → M`
(`TauCeti.SquareChartPartition`): finitely many charts `cᵢ` with frames `tᵢ` over their sources and
cutoffs `χᵢ` with `∑ᵢ χᵢ² = 1`. For `1 ≤ p ≤ ∞` and real `s`, the Bessel-potential space `H^{s,p}`
of `A` (`TauCeti.SquareChartPartition.besselPotentialSpace`) is the closed subspace of the product
`∏ᵢⱼ H^{s,p}(E, ℂ)`, with the maximum norm, made of the tuples of localizations `χᵢ Tᵢⱼ` of the real
functionals `T` on the bundle tests of `V` that are `H^{s,p}` with respect to `A`.

Let `1 < p < ∞`. This file shows that the **reconstruction**
`(uᵢⱼ) ↦ (s ↦ ∑ᵢⱼ Re uᵢⱼ (sᵢⱼ))` (`TauCeti.SquareChartPartition.reconstruction`) of an arbitrary
tuple in `∏ᵢⱼ H^{s,p}(E, ℂ)` is `H^{s,p}` with respect to `A`
(`TauCeti.SquareChartPartition.memBesselPotential_reconstruction`), although its localizations need
not be the `uᵢⱼ`. So localizing the reconstruction is a bounded projection of
`∏ᵢⱼ H^{s,p}(E, ℂ)` onto `H^{s,p}` (`TauCeti.SquareChartPartition.besselPotentialReconstruction`,
which fixes the elements of `H^{s,p}`,
`TauCeti.SquareChartPartition.besselPotentialReconstruction_coe`): the localization, that is the
inclusion of `H^{s,p}` into the product, and the reconstruction make `H^{s,p}` a retract of a
finite product of Euclidean Bessel-potential spaces.

Since Schwartz functions are dense in `H^{s,p}(E, ℂ)` for `p < ∞`, the functionals
`s ↦ ∑ᵢⱼ Re ∫ fᵢⱼ sᵢⱼ` reconstructed from tuples of Schwartz functions `fᵢⱼ` are dense in
`H^{s,p}`
(`TauCeti.SquareChartPartition.denseRange_besselPotentialReconstruction_toBesselPotentialSpaceCLM`).
They are `H^{t,p}` with respect to `A` for every `t`
(`TauCeti.SquareChartPartition.memBesselPotential_reconstruction_schwartzMap`). Consequently, for
`r ≤ s`, the inclusion `H^{s,p} ⊆ H^{r,p}` has dense range
(`TauCeti.SquareChartPartition.denseRange_besselPotentialInclusion`). For `p = 2` these statements
give the corresponding ones for the Sobolev spaces `H^s` of `A`, through the isomorphism
`H^{s,2} ≃ H^s` (`TauCeti.SquareChartPartition.besselPotentialSpaceTwoEquivSobolevSpace`): see
`TauCeti.SquareChartPartition.memSobolev_reconstruction`,
`TauCeti.SquareChartPartition.sobolevReconstruction` and
`TauCeti.SquareChartPartition.denseRange_inclusion`.

## The argument

Write the reconstruction as the sum over `(i, j)` of the reconstructions of single entries. The
functional `R w : s ↦ Re w (sᵢⱼ)` reconstructed from `w ∈ H^{s,p}(E, ℂ)` in the slot `(i, j)` is
`H^{s,p}` near every point `x` of `M`, which makes it `H^{s,p}` with respect to `A`
(`TauCeti.SquareChartPartition.memBesselPotential_iff_forall_isLocallyMemSobolevAt`).

* If `x` lies in the support of `χᵢ`, read `R w` in the `i`-th chart and frame. The test `φ • v`
  extended through them has localization `bⱼ*(v) χᵢ φ` in the slot `(i, j)`
  (`TauCeti.SquareChartPartition.testLocalization_chartTestCLM`), so the component of `R w` along
  `v` is the real part of `bⱼ*(v) χᵢ w`
  (`TauCeti.SquareChartPartition.chartComponent_reconstruction_single`). The tempered
  distribution `χᵢ w` is in `H^{s,p}`, and so is its complex conjugate
  (`TemperedDistribution.MemSobolev.conjPostcompCLM`), hence the real part is `H^{s,p}` near every
  point (`TemperedDistribution.MemSobolev.isLocallyMemSobolevAt_re_toDistribution`).
* Otherwise `χᵢ` vanishes near `x`, and so does `R w`: its components in a chart at `x` vanish near
  the image of `x` (`TauCeti.SquareChartPartition.isLocallyAt_reconstruction_single_of_notMem`,
  with `Distribution.IsInvariantLocalRegularity.of_notMem_dsupport`).

The reconstruction then defines a linear map from `∏ᵢⱼ H^{s,p}(E, ℂ)` to the Banach space
`H^{s,p}`, which is continuous by the closed graph theorem: the functional represented by an
element of either space depends continuously on it, test by test. No estimate for changes of chart
is needed.

## Main declarations

* `TauCeti.SquareChartPartition.isLocallyMemSobolevAt_reconstruction_single` and
  `TauCeti.SquareChartPartition.memBesselPotential_reconstruction`: the reconstruction of a tuple of
  `H^{s,p}` tempered distributions is `H^{s,p}` with respect to `A`.
* `TauCeti.SquareChartPartition.besselPotentialReconstruction`: the reconstruction as a bounded
  operator from `∏ᵢⱼ H^{s,p}(E, ℂ)` onto `H^{s,p}`, and
  `TauCeti.SquareChartPartition.besselPotentialReconstruction_coe`: it fixes the elements of
  `H^{s,p}`.
* `TauCeti.SquareChartPartition.memBesselPotential_reconstruction_schwartzMap`: reconstructions of
  tuples of Schwartz functions are `H^{t,p}` for every `t`.
* `TauCeti.SquareChartPartition.denseRange_besselPotentialReconstruction_toBesselPotentialSpaceCLM`:
  they are dense in `H^{s,p}`.
* `TauCeti.SquareChartPartition.denseRange_besselPotentialInclusion`: the inclusion
  `H^{s,p} ⊆ H^{r,p}` has dense range.

## References

* H. Triebel, *Theory of Function Spaces II*, Birkhäuser, 1992, Chapter 7 (function spaces on
  manifolds, defined through localization in charts).
* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §3
  (Sobolev spaces on compact manifolds, defined through a partition of unity and charts).
-/

public section

noncomputable section

open Bundle Set TopologicalSpace Complex ContMDiffSection Distribution
open scoped Manifold ContDiff Distributions SchwartzMap CompactConvergenceCLM ENNReal
  BesselPotentialSpace

namespace TauCeti

namespace SquareChartPartition

attribute [local instance] ContMDiffSection.ChartTestData.memTrivializationAtlas

variable {ι : Type*} [Fintype ι]
  {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

variable (A : SquareChartPartition ι I F V)

/-! ### Reconstructing a single localization -/

variable [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Near a point of the support of `χᵢ`, the functional `s ↦ Re w (sᵢⱼ)` reconstructed from
`w ∈ H^{s,p}(E, ℂ)` is `H^{s,p}`: in the `i`-th chart its components are real parts of the
`H^{s,p}` tempered distributions `bⱼ*(v) χᵢ w`. -/
private theorem isLocallyMemSobolevAt_reconstruction_single_of_mem [DecidableEq ι] (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) {s : ℝ} (i : ι) (j : Fin (Module.finrank ℝ F)) {w : 𝓢'(E, ℂ)}
    (hw : TemperedDistribution.MemSobolev s p w) {x : M} (hx : x ∈ tsupport (A.cutoff i)) :
    BundleTest.IsLocallyMemSobolevAt s p (A.reconstruction (Pi.single (i, j) w)) x := by
  have hxs := A.tsupport_cutoff_subset i hx
  refine (BundleTest.isLocallyMemSobolevAt_iff hp hp_top _ (A.chartData i).contMDiffOn_chart
    (A.contMDiffOn_chart_symm i) (A.chartData i).source_subset hxs).2 fun v ↦ ?_
  rw [chartComponent_reconstruction_single]
  exact TemperedDistribution.MemSobolev.isLocallyMemSobolevAt_re_toDistribution hp hp_top
    ((hw.smulLeftCLM_testFunction hp hp_top (A.chartCutoff i)).smul _)
    ((A.chartData i).chart.map_source hxs)

/-- Let `1 < p < ∞`. The functional `s ↦ Re w (sᵢⱼ)` reconstructed from `w ∈ H^{s,p}(E, ℂ)` in the
slot `(i, j)` is `H^{s,p}` near every point of `M`. -/
theorem isLocallyMemSobolevAt_reconstruction_single [DecidableEq ι] (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) {s : ℝ} (k : ι × Fin (Module.finrank ℝ F)) {w : 𝓢'(E, ℂ)}
    (hw : TemperedDistribution.MemSobolev s p w) (x : M) :
    BundleTest.IsLocallyMemSobolevAt s p (A.reconstruction (Pi.single k w)) x := by
  by_cases hx : x ∈ tsupport (A.cutoff k.1)
  · exact A.isLocallyMemSobolevAt_reconstruction_single_of_mem hp hp_top k.1 k.2 hw hx
  · exact BundleTest.isLocallyMemSobolevAt_def.2 <| A.isLocallyAt_reconstruction_single_of_notMem
      (fun hy hyT ↦
        (isInvariantLocalRegularity_isLocallyMemSobolevAt s hp hp_top).of_notMem_dsupport hy hyT)
      k.1 k.2 w hx

/-! ### The reconstruction as a bounded projection -/

/-- **Reconstructions of `H^{s,p}` tuples are `H^{s,p}`.** Let `1 < p < ∞`. For tempered
distributions `vᵢⱼ` in `H^{s,p}(E, ℂ)`, one for each chart and each basis vector of the model fibre,
the reconstructed functional `s ↦ ∑ᵢⱼ Re vᵢⱼ (sᵢⱼ)` is `H^{s,p}` with respect to `A`, although its
localizations need not be the `vᵢⱼ`. -/
theorem memBesselPotential_reconstruction (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) {s : ℝ}
    {v : ι × Fin (Module.finrank ℝ F) → 𝓢'(E, ℂ)}
    (hv : ∀ k, TemperedDistribution.MemSobolev s p (v k)) :
    A.MemBesselPotential s p (A.reconstruction v) := by
  classical
  rw [← Finset.univ_sum_single v, map_sum]
  exact (A.mem_memBesselPotentialSubmodule s p).1 <| Submodule.sum_mem _ fun k _ ↦
    (A.mem_memBesselPotentialSubmodule s p).2 <|
      (A.memBesselPotential_iff_forall_isLocallyMemSobolevAt hp hp_top).2
        (A.isLocallyMemSobolevAt_reconstruction_single hp hp_top k (hv k))

variable (s : ℝ) (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))

/-- The reconstruction of a tuple in `∏ᵢⱼ H^{s,p}(E, ℂ)`, as an element of the Bessel-potential
space. -/
private def besselPotentialReconstructionLinearMap :
    (ι × Fin (Module.finrank ℝ F) → H^{s, p}(E, ℂ)) →ₗ[ℝ] A.besselPotentialSpace s p where
  toFun u := A.ofMemBesselPotential
    (A.memBesselPotential_reconstruction hp hp_top fun k ↦ (u k).memSobolev_toDistr)
  map_add' u u' := A.besselPotentialToDistribution_injective <| by
    ext φ
    simp [reconstruction_apply, Finset.sum_add_distrib]
  map_smul' a u := A.besselPotentialToDistribution_injective <| by
    ext φ
    simp [reconstruction_apply, Finset.mul_sum, BesselPotentialSpace.toDistr_real_smul]

/-- The **reconstruction** of a tuple `u` in the product `∏ᵢⱼ H^{s,p}(E, ℂ)`, for `1 < p < ∞`, as a
bounded operator into the Bessel-potential space `H^{s,p}` of `A`: the element of `H^{s,p}`
representing the functional `s ↦ ∑ᵢⱼ Re uᵢⱼ (sᵢⱼ)`
(`TauCeti.SquareChartPartition.besselPotentialToDistribution_besselPotentialReconstruction`). It
fixes the elements of `H^{s,p}`
(`TauCeti.SquareChartPartition.besselPotentialReconstruction_coe`), so it is a bounded projection
of the product onto `H^{s,p}`. -/
def besselPotentialReconstruction :
    (ι × Fin (Module.finrank ℝ F) → H^{s, p}(E, ℂ)) →L[ℝ] A.besselPotentialSpace s p :=
  ⟨A.besselPotentialReconstructionLinearMap s hp hp_top,
    (A.besselPotentialReconstructionLinearMap s hp hp_top).continuous_of_injective_comp_eq
      (f := fun u φ ↦ A.reconstruction (fun l ↦ (u l).toDistr) φ)
      (continuous_pi fun φ ↦ by
        simp only [reconstruction_apply]
        exact continuous_finsetSum _ fun k _ ↦ continuous_re.comp
          ((ContinuousEvalConst.continuous_eval_const _).comp
            (BesselPotentialSpace.continuous_toDistr.comp (continuous_apply k))))
      (continuous_pi (A.continuous_besselPotentialToDistribution_apply s p))
      (DFunLike.coe_injective.comp A.besselPotentialToDistribution_injective)
      fun u ↦ congrArg DFunLike.coe (A.besselPotentialToDistribution_ofMemBesselPotential _)⟩

/-- The reconstruction represents the functional `s ↦ ∑ᵢⱼ Re uᵢⱼ (sᵢⱼ)`. -/
@[simp]
theorem besselPotentialToDistribution_besselPotentialReconstruction
    (u : ι × Fin (Module.finrank ℝ F) → H^{s, p}(E, ℂ)) :
    A.besselPotentialToDistribution s p (A.besselPotentialReconstruction s hp hp_top u) =
      A.reconstruction fun k ↦ (u k).toDistr :=
  A.besselPotentialToDistribution_ofMemBesselPotential _

/-- The reconstruction fixes the elements of the Bessel-potential space: an element of `H^{s,p}`
is the tuple of localizations of the functional it represents. -/
@[simp]
theorem besselPotentialReconstruction_coe (u : A.besselPotentialSpace s p) :
    A.besselPotentialReconstruction s hp hp_top u = u :=
  A.besselPotentialToDistribution_injective (by
    rw [besselPotentialToDistribution_besselPotentialReconstruction,
      besselPotentialToDistribution_apply])

/-- The reconstruction maps the product `∏ᵢⱼ H^{s,p}(E, ℂ)` onto the Bessel-potential space
`H^{s,p}`. -/
theorem besselPotentialReconstruction_surjective :
    Function.Surjective (A.besselPotentialReconstruction s hp hp_top) :=
  fun u ↦ ⟨u, A.besselPotentialReconstruction_coe s hp hp_top u⟩

/-! ### Density -/

include hp hp_top in
/-- **Reconstructions of Schwartz tuples lie in every `H^{t,p}`.** Let `1 < p < ∞`. The functional
`s ↦ ∑ᵢⱼ Re ∫ fᵢⱼ sᵢⱼ` reconstructed from Schwartz functions `fᵢⱼ` is `H^{t,p}` with respect to
`A` for every `t`. -/
theorem memBesselPotential_reconstruction_schwartzMap (t : ℝ)
    (f : ι × Fin (Module.finrank ℝ F) → 𝓢(E, ℂ)) :
    A.MemBesselPotential t p (A.reconstruction fun k ↦ (f k : 𝓢'(E, ℂ))) :=
  A.memBesselPotential_reconstruction hp hp_top fun k ↦ by
    simpa using
      (SchwartzMap.toBesselPotentialSpaceCLM (E := E) (F := ℂ) t p (f k)).memSobolev_toDistr

/-- The element of `H^{s,p}` representing the reconstruction of a tuple of Schwartz functions. -/
theorem besselPotentialReconstruction_toBesselPotentialSpaceCLM
    (f : ι × Fin (Module.finrank ℝ F) → 𝓢(E, ℂ)) :
    A.besselPotentialReconstruction s hp hp_top
        (fun k ↦ SchwartzMap.toBesselPotentialSpaceCLM s p (f k)) =
      A.ofMemBesselPotential (A.memBesselPotential_reconstruction_schwartzMap hp hp_top s f) :=
  A.besselPotentialToDistribution_injective (by simp)

/-- **Density of reconstructions of Schwartz tuples.** Let `1 < p < ∞`. The functionals
reconstructed from tuples of Schwartz functions are dense in the Bessel-potential space `H^{s,p}`
of `A`. -/
theorem denseRange_besselPotentialReconstruction_toBesselPotentialSpaceCLM :
    DenseRange fun f : ι × Fin (Module.finrank ℝ F) → 𝓢(E, ℂ) ↦
      A.besselPotentialReconstruction s hp hp_top
        (fun k ↦ SchwartzMap.toBesselPotentialSpaceCLM s p (f k)) :=
  (A.besselPotentialReconstruction_surjective s hp hp_top).denseRange.comp
    (DenseRange.piMap fun _ ↦ SchwartzMap.denseRange_toBesselPotentialSpaceCLM s hp_top)
    (A.besselPotentialReconstruction s hp hp_top).continuous

include hp hp_top in
/-- **Density of the smaller Bessel-potential spaces.** Let `1 < p < ∞`. For `r ≤ s`, the
inclusion `H^{s,p} ⊆ H^{r,p}` of the Bessel-potential spaces of `A` has dense range: the
reconstructions of Schwartz tuples lie in its range. -/
theorem denseRange_besselPotentialInclusion {r : ℝ} (h : r ≤ s) :
    DenseRange (A.besselPotentialInclusion (p := p) h) :=
  (A.denseRange_besselPotentialReconstruction_toBesselPotentialSpaceCLM r hp hp_top).mono <| by
    rintro _ ⟨f, rfl⟩
    refine ⟨A.besselPotentialReconstruction s hp hp_top
      (fun k ↦ SchwartzMap.toBesselPotentialSpaceCLM s p (f k)), ?_⟩
    simp only [besselPotentialReconstruction_toBesselPotentialSpaceCLM,
      besselPotentialInclusion_ofMemBesselPotential]

end SquareChartPartition

end TauCeti
