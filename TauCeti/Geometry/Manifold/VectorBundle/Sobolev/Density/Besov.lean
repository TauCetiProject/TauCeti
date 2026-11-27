/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Besov
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Schwartz
import TauCeti.Analysis.Normed.Operator.Banach

/-!
# Reconstruction and density in the Besov spaces of a square chart partition

Let `A` be a square chart partition of a smooth real vector bundle `V → M`
(`TauCeti.SquareChartPartition`): finitely many charts `cᵢ` with frames `tᵢ` over their sources and
cutoffs `χᵢ` with `∑ᵢ χᵢ² = 1`. The Besov space `B^s_{p,q}` of `A`
(`TauCeti.SquareChartPartition.besovSpace`) is the closed subspace of the product
`∏ᵢⱼ B^s_{p,q}(E, ℂ)` made of the tuples of localizations `χᵢ Tᵢⱼ` of the real functionals `T` on
the bundle tests of `V` that are `B^s_{p,q}` with respect to `A`.

This file shows that the **reconstruction** `(uᵢⱼ) ↦ (s ↦ ∑ᵢⱼ Re uᵢⱼ (sᵢⱼ))`
(`TauCeti.SquareChartPartition.reconstruction`) of an arbitrary tuple in `∏ᵢⱼ B^s_{p,q}(E, ℂ)` is
`B^s_{p,q}` with respect to `A` (`TauCeti.SquareChartPartition.memBesov_reconstruction`), although
its localizations need not be the `uᵢⱼ`. So localizing it is a bounded projection of the product
onto the Besov space (`TauCeti.SquareChartPartition.besovReconstruction`, which fixes the elements
of `B^s_{p,q}`, `TauCeti.SquareChartPartition.besovReconstruction_coe`): the Besov space of `A` is
a retract of a finite product of Euclidean Besov spaces, the inclusion being a right inverse of the
reconstruction. This holds for every real `s` and all `1 ≤ p, q ≤ ∞`, including the Hölder–Zygmund
spaces `𝒞^s = B^s_{∞,∞}`.

The functionals reconstructed from tuples of Schwartz functions lie in every Besov space of `A`
(`TauCeti.SquareChartPartition.memBesov_reconstruction_schwartzMap`): they are the functionals
`s ↦ ∑ᵢⱼ Re ∫ fᵢⱼ sᵢⱼ`, integrals of the chart readings of `s` against smooth rapidly decreasing
functions. For `p, q < ∞` the Schwartz functions are dense in `B^s_{p,q}(E, ℂ)`, so these
functionals are dense in the Besov space of `A`
(`TauCeti.SquareChartPartition.denseRange_besovReconstruction_toBesovSpaceCLM`), and every
inclusion `B^s_{p,q} ⊆ B^{s'}_{p,q'}` with `p, q' < ∞` has dense range
(`TauCeti.SquareChartPartition.denseRange_besovInclusion`). These statements need not hold for
`q = ∞` or `p = ∞`, where the closure of the Schwartz functions is a little Besov space.

## The argument

Write the reconstruction as the sum over `(i, j)` of the reconstructions of single entries. The
functional `R w : s ↦ Re w (sᵢⱼ)` reconstructed from `w ∈ B^s_{p,q}(E, ℂ)` in the slot `(i, j)` is
`B^s_{p,q}` near every point `x` of `M`, which makes it `B^s_{p,q}` with respect to `A`
(`TauCeti.SquareChartPartition.memBesov_iff_forall_isLocallyMemBesovAt`).

* If `x` lies in the support of `χᵢ`, the component of `R w` along `v` in the `i`-th chart and
  frame is the real part of the tempered distribution `bⱼ*(v) χᵢ w`
  (`TauCeti.SquareChartPartition.chartComponent_reconstruction_single`). This lies in
  `B^s_{p,q}`, and the real part of a distribution which is `B^s_{p,q}` near a point is again
  `B^s_{p,q}` there (`Distribution.IsLocallyMemBesovAt.re`), since the Littlewood–Paley blocks
  commute with complex conjugation.
* Otherwise `χᵢ` vanishes near `x`, and so does `R w`: its components in a chart at `x` vanish near
  the image of `x` (`TauCeti.SquareChartPartition.isLocallyAt_reconstruction_single_of_notMem`,
  with `Distribution.isLocallyMemBesovAt_of_notMem_dsupport`).

The reconstruction then defines a linear map from `∏ᵢⱼ B^s_{p,q}(E, ℂ)` to the Banach space
`B^s_{p,q}` of `A`, which is continuous by the closed graph theorem: the functional represented by
an element of either space depends continuously on it, test by test. No Besov estimate for changes
of chart is needed.

## Main declarations

* `TauCeti.SquareChartPartition.memBesov_reconstruction`: the reconstruction of a tuple of
  `B^s_{p,q}` tempered distributions is `B^s_{p,q}` with respect to `A`.
* `TauCeti.SquareChartPartition.besovReconstruction`: the reconstruction as a bounded operator from
  `∏ᵢⱼ B^s_{p,q}(E, ℂ)` onto the Besov space of `A`, and
  `TauCeti.SquareChartPartition.besovReconstruction_coe`: it fixes the elements of the Besov space.
* `TauCeti.SquareChartPartition.memBesov_reconstruction_schwartzMap`: reconstructions of tuples of
  Schwartz functions lie in every Besov space of `A`.
* `TauCeti.SquareChartPartition.denseRange_besovReconstruction_toBesovSpaceCLM`: for `p, q < ∞`
  they are dense.
* `TauCeti.SquareChartPartition.denseRange_besovInclusion`: for `p, q' < ∞` the inclusion
  `B^s_{p,q} ⊆ B^{s'}_{p,q'}` has dense range.

## References

* H. Triebel, *Theory of Function Spaces II*, Birkhäuser, 1992, §7.2 (function spaces on manifolds
  as retracts of finite products of Euclidean spaces, through localization and reconstruction).
* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Springer, 1976, §6.2 (the
  Euclidean Besov spaces) and Theorem 6.4.5 (the interpolation identities transported along
  retractions).
-/

public section

noncomputable section

open Bundle Set TopologicalSpace Complex ContMDiffSection Distribution
open scoped Manifold ContDiff Distributions SchwartzMap CompactConvergenceCLM ENNReal

namespace TauCeti

namespace SquareChartPartition

attribute [local instance] ContMDiffSection.ChartTestData.memTrivializationAtlas

variable {ι : Type*} [Fintype ι]
  {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

variable (A : SquareChartPartition ι I F V) (φ : ContDiffBump (0 : E))

/-! ### Reconstructing a single localization -/

section Single

variable {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Near a point of the support of `χᵢ`, the functional `s ↦ Re w (sᵢⱼ)` reconstructed from
`w ∈ B^s_{p,q}(E, ℂ)` is `B^s_{p,q}`: in the `i`-th chart its components are real parts of the
`B^s_{p,q}` tempered distributions `bⱼ*(v) χᵢ w`. -/
private theorem isLocallyMemBesovAt_reconstruction_single_of_mem [DecidableEq ι] (i : ι)
    (j : Fin (Module.finrank ℝ F)) {w : 𝓢'(E, ℂ)} (hw : w.MemBesov φ s p q) {x : M}
    (hx : x ∈ tsupport (A.cutoff i)) :
    BundleTest.IsLocallyMemBesovAt φ s p q (A.reconstruction (Pi.single (i, j) w)) x := by
  have hxs := A.tsupport_cutoff_subset i hx
  refine (BundleTest.isLocallyMemBesovAt_iff _ (A.chartData i).contMDiffOn_chart
    (A.contMDiffOn_chart_symm i) (A.chartData i).source_subset hxs).2 fun v ↦ ?_
  rw [chartComponent_reconstruction_single]
  exact (((hw.smulLeftCLM_testFunction (A.chartCutoff i)).smul _).isLocallyMemBesovAt_toDistribution
    ((A.chartData i).chart.map_source hxs)).re

/-- The functional `s ↦ Re w (sᵢⱼ)` reconstructed from `w ∈ B^s_{p,q}(E, ℂ)` in the slot `(i, j)`
is `B^s_{p,q}` near every point of `M`. -/
private theorem isLocallyMemBesovAt_reconstruction_single [DecidableEq ι]
    (k : ι × Fin (Module.finrank ℝ F)) {w : 𝓢'(E, ℂ)} (hw : w.MemBesov φ s p q) (x : M) :
    BundleTest.IsLocallyMemBesovAt φ s p q (A.reconstruction (Pi.single k w)) x := by
  by_cases hx : x ∈ tsupport (A.cutoff k.1)
  · exact A.isLocallyMemBesovAt_reconstruction_single_of_mem φ k.1 k.2 hw hx
  · exact BundleTest.isLocallyMemBesovAt_def.2 <| A.isLocallyAt_reconstruction_single_of_notMem
      isLocallyMemBesovAt_of_notMem_dsupport k.1 k.2 w hx

/-- **Reconstructions of `B^s_{p,q}` tuples are `B^s_{p,q}`.** For tempered distributions `vᵢⱼ`
in `B^s_{p,q}(E, ℂ)`, one for each chart and each basis vector of the model fibre, the
reconstructed functional `s ↦ ∑ᵢⱼ Re vᵢⱼ (sᵢⱼ)` is `B^s_{p,q}` with respect to `A`, although its
localizations need not be the `vᵢⱼ`. -/
theorem memBesov_reconstruction {v : ι × Fin (Module.finrank ℝ F) → 𝓢'(E, ℂ)}
    (hv : ∀ k, (v k).MemBesov φ s p q) : A.MemBesov φ s p q (A.reconstruction v) := by
  classical
  rw [← Finset.univ_sum_single v, map_sum]
  exact (A.mem_memBesovSubmodule φ s p q).1 <| Submodule.sum_mem _ fun k _ ↦
    (A.mem_memBesovSubmodule φ s p q).2 <| (A.memBesov_iff_forall_isLocallyMemBesovAt φ).2
      (A.isLocallyMemBesovAt_reconstruction_single φ k (hv k))

end Single

/-! ### The reconstruction as a bounded projection -/

variable (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The reconstruction of a tuple in `∏ᵢⱼ B^s_{p,q}(E, ℂ)`, as an element of the Besov space. -/
private def besovReconstructionLinearMap :
    (ι × Fin (Module.finrank ℝ F) → BesovSpace ℂ φ s p q) →ₗ[ℝ] A.besovSpace φ s p q where
  toFun u := A.ofMemBesov φ (A.memBesov_reconstruction φ fun k ↦ (u k).memBesov_toDistr)
  map_add' u u' := A.besovToDistribution_injective φ <| by
    ext ψ
    simp [reconstruction_apply, Finset.sum_add_distrib]
  map_smul' a u := A.besovToDistribution_injective φ <| by
    ext ψ
    simp [reconstruction_apply, Finset.mul_sum, BesovSpace.toDistr_real_smul]

/-- The **reconstruction** of a tuple `u` in the product `∏ᵢⱼ B^s_{p,q}(E, ℂ)`, as a bounded
operator into the Besov space `B^s_{p,q}` of `A`: the element representing the functional
`s ↦ ∑ᵢⱼ Re uᵢⱼ (sᵢⱼ)` (`TauCeti.SquareChartPartition.besovToDistribution_besovReconstruction`).
It fixes the elements of the Besov space (`TauCeti.SquareChartPartition.besovReconstruction_coe`),
so it is a bounded projection of the product onto the Besov space of `A`. -/
def besovReconstruction :
    (ι × Fin (Module.finrank ℝ F) → BesovSpace ℂ φ s p q) →L[ℝ] A.besovSpace φ s p q :=
  ⟨A.besovReconstructionLinearMap φ s p q,
    (A.besovReconstructionLinearMap φ s p q).continuous_of_injective_comp_eq
      (f := fun u ψ ↦ A.reconstruction (fun l ↦ (u l).toDistr) ψ)
      (continuous_pi fun ψ ↦ by
        simp only [reconstruction_apply]
        exact continuous_finsetSum _ fun k _ ↦ continuous_re.comp
          ((ContinuousEvalConst.continuous_eval_const _).comp
            (BesovSpace.continuous_toDistr.comp (continuous_apply k))))
      (continuous_pi (A.continuous_besovToDistribution_apply φ s p q))
      (DFunLike.coe_injective.comp (A.besovToDistribution_injective φ))
      fun u ↦ congrArg DFunLike.coe (A.besovToDistribution_ofMemBesov φ _)⟩

/-- The reconstruction represents the functional `s ↦ ∑ᵢⱼ Re uᵢⱼ (sᵢⱼ)`. -/
@[simp]
theorem besovToDistribution_besovReconstruction
    (u : ι × Fin (Module.finrank ℝ F) → BesovSpace ℂ φ s p q) :
    A.besovToDistribution φ s p q (A.besovReconstruction φ s p q u) =
      A.reconstruction fun k ↦ (u k).toDistr :=
  A.besovToDistribution_ofMemBesov φ _

/-- The reconstruction fixes the elements of the Besov space: an element of `B^s_{p,q}` is the
tuple of localizations of the functional it represents. -/
@[simp]
theorem besovReconstruction_coe (u : A.besovSpace φ s p q) :
    A.besovReconstruction φ s p q u = u :=
  A.besovToDistribution_injective φ <| by
    rw [besovToDistribution_besovReconstruction, besovToDistribution_apply]

/-- The reconstruction maps the product `∏ᵢⱼ B^s_{p,q}(E, ℂ)` onto the Besov space of `A`. -/
theorem besovReconstruction_surjective : Function.Surjective (A.besovReconstruction φ s p q) :=
  fun u ↦ ⟨u, A.besovReconstruction_coe φ s p q u⟩

/-! ### Density -/

/-- **Reconstructions of Schwartz tuples lie in every Besov space.** The functional
`s ↦ ∑ᵢⱼ Re ∫ fᵢⱼ sᵢⱼ` reconstructed from Schwartz functions `fᵢⱼ` is `B^s_{p,q}` with respect to
`A` for every `s`, `p` and `q`. -/
theorem memBesov_reconstruction_schwartzMap (f : ι × Fin (Module.finrank ℝ F) → 𝓢(E, ℂ)) :
    A.MemBesov φ s p q (A.reconstruction fun k ↦ (f k : 𝓢'(E, ℂ))) :=
  A.memBesov_reconstruction φ fun k ↦ (f k).memBesov φ s p
    (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne'

/-- The element of the Besov space representing the reconstruction of a tuple of Schwartz
functions. -/
theorem besovReconstruction_toBesovSpaceCLM (f : ι × Fin (Module.finrank ℝ F) → 𝓢(E, ℂ)) :
    A.besovReconstruction φ s p q (fun k ↦ SchwartzMap.toBesovSpaceCLM ℂ φ s p q (f k)) =
      A.ofMemBesov φ (A.memBesov_reconstruction_schwartzMap φ s p q f) :=
  A.besovToDistribution_injective φ (by simp)

/-- **Density of reconstructions of Schwartz tuples.** For `p, q < ∞`, the functionals
reconstructed from tuples of Schwartz functions are dense in the Besov space `B^s_{p,q}` of `A`. -/
theorem denseRange_besovReconstruction_toBesovSpaceCLM (hp : p ≠ ⊤) (hq : q ≠ ⊤) :
    DenseRange fun f : ι × Fin (Module.finrank ℝ F) → 𝓢(E, ℂ) ↦
      A.besovReconstruction φ s p q (fun k ↦ SchwartzMap.toBesovSpaceCLM ℂ φ s p q (f k)) :=
  (A.besovReconstruction_surjective φ s p q).denseRange.comp
    (DenseRange.piMap fun _ ↦ SchwartzMap.denseRange_toBesovSpaceCLM φ s hp hq)
    (A.besovReconstruction φ s p q).continuous

variable {s q} in
/-- **Density of the smaller Besov spaces.** For `s' ≤ s`, `q ≤ q'` and `p, q' < ∞`, the inclusion
`B^s_{p,q} ⊆ B^{s'}_{p,q'}` of the Besov spaces of `A` has dense range: the reconstructions of
Schwartz tuples lie in its range. -/
theorem denseRange_besovInclusion {s' : ℝ} {q' : ℝ≥0∞} [Fact (1 ≤ q')] (hs : s' ≤ s)
    (hq : q ≤ q') (hp : p ≠ ⊤) (hq' : q' ≠ ⊤) : DenseRange (A.besovInclusion φ p hs hq) :=
  (A.denseRange_besovReconstruction_toBesovSpaceCLM φ s' p q' hp hq').mono <| by
    rintro _ ⟨f, rfl⟩
    refine ⟨A.besovReconstruction φ s p q (fun k ↦ SchwartzMap.toBesovSpaceCLM ℂ φ s p q (f k)), ?_⟩
    simp only [besovReconstruction_toBesovSpaceCLM, besovInclusion_ofMemBesov]

end SquareChartPartition

end TauCeti
