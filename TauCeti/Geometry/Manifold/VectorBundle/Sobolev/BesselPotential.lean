/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import Mathlib.Analysis.Normed.Lp.PiLp
public import TauCeti.Analysis.Distribution.TemperedDistribution.Cutoff
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.SquareChartPartition
public import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization
public import TauCeti.Geometry.Manifold.VectorBundle.Section.LocalSobolev
public import TauCeti.Geometry.Manifold.VectorBundle.Section.WaveFrontSet
import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Distribution.TestFunction.Schwartz
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered
import TauCeti.Analysis.Normed.Lp.PiLp.Basic
import TauCeti.Analysis.Normed.Operator.Banach

/-!
# Sobolev spaces of distributions on bundle tests

Let `V → M` be a smooth real vector bundle with model fibre `F`. A real functional `T` on the
bundle tests `TauCeti.BundleTest I F V` is read through a fixed finite family of charts and frames.
This file builds the Sobolev spaces `H^s`, `s ∈ ℝ`, of such functionals from the Euclidean
Bessel-potential spaces `H^s(E, ℂ)` of Mathlib. The distributional sections
`TauCeti.BundleDistribution I M G W` of a bundle `W` with model fibre `G` are the case where `V` is
the `W`-dual density bundle `fun x ↦ W x →L[ℝ] TauCeti.DensityBundle I M x`, whose model fibre `F`
is `G →L[ℝ] ℝ`. For them the partition is a
`TauCeti.SquareChartPartition ι I (G →L[ℝ] ℝ) (fun x ↦ W x →L[ℝ] TauCeti.DensityBundle I M x)`.

The functionals are read through a square chart partition (`TauCeti.SquareChartPartition`):
finitely many charts `cᵢ` with smooth inverses, frames `tᵢ` over their sources, and smooth cutoffs
`χᵢ` with compact supports inside the chart sources such that `∑ᵢ χᵢ² = 1`, which exists on every
compact boundaryless manifold (`TauCeti.exists_squareChartPartition`). Write `(bⱼ)` for the fixed
basis `Module.finBasis ℝ F` of the model fibre (chosen non-constructively).

* The **localization** `χᵢ Tᵢⱼ` of `T` (`TauCeti.SquareChartPartition.localization`) is the
  tempered distribution on the model space `E` obtained from the component `φ ↦ T (φ • bⱼ)` of `T`
  in the `i`-th chart and frame (`Bundle.Trivialization.chartComponent`) by cutting it off with
  `χᵢ` read in the chart (`Distribution.cutoffTempered`).
* Dually, a bundle test `s` has localizations `sᵢⱼ`, the complex Schwartz functions
  `y ↦ χᵢ (cᵢ⁻¹ y) bⱼ* (tᵢ (s (cᵢ⁻¹ y)))` (`TauCeti.SquareChartPartition.testLocalization`).
* The **reconstruction** of tempered distributions `vᵢⱼ` is the functional `s ↦ ∑ᵢⱼ Re vᵢⱼ (sᵢⱼ)`
  (`TauCeti.SquareChartPartition.reconstruction`). It inverts the localization
  (`TauCeti.SquareChartPartition.reconstruction_localization`): the pairing of the localizations
  of `T` and `s` in the `i`-th chart is `T (χᵢ² s)`, and `∑ᵢ χᵢ² = 1`. In particular a functional
  is determined by its localizations (`TauCeti.SquareChartPartition.ext_localization`).
  Reconstructing a single entry `w` in the slot `(i, j)` gives components `Re (bⱼ*(v) χᵢ w)` in
  the `i`-th chart (`TauCeti.SquareChartPartition.chartComponent_reconstruction_single`) and
  vanishes away from the support of `χᵢ`
  (`TauCeti.SquareChartPartition.isLocallyAt_reconstruction_single_of_notMem`).

`T` is **`H^s` with respect to the partition** (`TauCeti.SquareChartPartition.MemSobolev`) when all
its localizations lie in `H^s(E, ℂ)`. The **Sobolev space**
`TauCeti.SquareChartPartition.sobolevSpace` is the image of the localization map: the real subspace
of the tuples `(uᵢⱼ)` in the Hilbert sum `⨁ᵢⱼ H^s(E, ℂ)` (`PiLp 2`) that are reproduced by
localizing their reconstruction. It is closed
(`TauCeti.SquareChartPartition.isClosed_sobolevSpace`), so it is a real Hilbert space, with the real
part of the inner product of the Hilbert sum (`TauCeti.SquareChartPartition.inner_sobolevSpace`),
and its norm is the pinned atlas norm `‖T‖² = ∑ᵢⱼ ‖χᵢ Tᵢⱼ‖²_{H^s}`
(`TauCeti.SquareChartPartition.norm_ofMemSobolev_sq`). It is linearly equivalent to the functionals
that are `H^s` with respect to the partition (`TauCeti.SquareChartPartition.sobolevSpaceEquiv`),
through the reconstruction `TauCeti.SquareChartPartition.toDistribution`.

It is a real, not a complex, subspace: the localizations of a real functional are the
complexifications of real distributions, and multiplying them by `i` leaves this class.

Completeness needs no Sobolev estimate for chart changes. A limit of localizations is again a
localization because the localization of a reconstruction, tested on a Schwartz function, only
involves finitely many values of the tempered distributions being reconstructed, so the defining
equations of the subspace are closed.

**Independence of the partition.** `T` is `H^s` with respect to `A` exactly when it is `H^s` near
every point of `M` (`TauCeti.SquareChartPartition.memSobolev_iff_forall_isLocallySobolevAt`), in
the sense of `TauCeti.BundleTest.IsLocallySobolevAt`, which does not depend on charts and frames.
Indeed, `χᵢ Tᵢⱼ ∈ H^s` makes `Tᵢⱼ` locally `H^s` wherever `χᵢ ≠ 0`, and every point has such an
`i` since `∑ᵢ χᵢ² = 1`; conversely, if all `Tᵢⱼ` are locally `H^s` on the support of `χᵢ`, then
`χᵢ Tᵢⱼ ∈ H^s`. This argument only uses these two cutoff properties of `H^s` and the invariance of
local `H^s` regularity, and is stated once for all such notions
(`TauCeti.SquareChartPartition.forall_localization_iff_forall_isLocallyAt`). So two square chart
partitions of `V` have the same `H^s` functionals
(`TauCeti.SquareChartPartition.memSobolev_iff_memSobolev`). Their Sobolev spaces are then
isomorphic as Banach spaces (`TauCeti.SquareChartPartition.sobolevSpaceCongr`), so that the pinned
norms are equivalent (`TauCeti.SquareChartPartition.exists_norm_ofMemSobolev_le`): the
identification is a linear bijection between Banach spaces whose graph is closed, because the
represented functional depends continuously on an element of either space, test by test, and the
closed graph theorem applies. No quantitative Sobolev estimate for chart changes or cutoffs is
needed for this comparison; such estimates would make the equivalence constants explicit.

## Main declarations

* `TauCeti.SquareChartPartition.localization`, `TauCeti.SquareChartPartition.reconstruction` and
  `TauCeti.SquareChartPartition.reconstruction_localization`.
* `TauCeti.SquareChartPartition.MemSobolev`: `H^s` regularity with respect to the partition.
* `TauCeti.SquareChartPartition.sobolevSpace`: the Sobolev space, with
  `TauCeti.SquareChartPartition.isClosed_sobolevSpace`, its `CompleteSpace` and real
  `InnerProductSpace` instances, and `TauCeti.SquareChartPartition.inner_sobolevSpace`.
* `TauCeti.SquareChartPartition.toDistribution`, `TauCeti.SquareChartPartition.ofMemSobolev`,
  `TauCeti.SquareChartPartition.range_toDistribution` and
  `TauCeti.SquareChartPartition.sobolevSpaceEquiv`: the Sobolev space represents exactly the
  functionals that are `H^s` with respect to the partition.
* `TauCeti.SquareChartPartition.norm_ofMemSobolev_sq`: the pinned norm.
* `TauCeti.SquareChartPartition.inclusion`: the norm-nonincreasing inclusion `H^s ⊆ H^r` for
  `r ≤ s`, representing the same functionals; it is compact for `r < s`
  (`TauCeti.SquareChartPartition.isCompactOperator_inclusion`).
* `TauCeti.SquareChartPartition.memSobolev_iff_forall_isLocallySobolevAt` and
  `TauCeti.SquareChartPartition.memSobolev_iff_memSobolev`: being `H^s` with respect to a partition
  is local `H^s` regularity, and does not depend on the partition.
* `TauCeti.SquareChartPartition.sobolevSpaceCongr` and
  `TauCeti.SquareChartPartition.exists_norm_ofMemSobolev_le`: the Sobolev spaces of two partitions
  are isomorphic Banach spaces, and their pinned norms are equivalent.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §3
  (Sobolev spaces on compact manifolds, defined through a partition of unity and charts).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  Appendix B.1 (Sobolev spaces on manifolds).
-/

public section

noncomputable section

open Bundle Set TopologicalSpace Complex ContMDiffSection
open scoped Manifold ContDiff Distributions SchwartzMap CompactConvergenceCLM

namespace TauCeti

namespace SquareChartPartition

attribute [local instance] ContMDiffSection.ChartTestData.memTrivializationAtlas

section Reconstruction

variable {ι : Type*} [Fintype ι]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F]
  {V : M → Type*} [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V]

variable (A : SquareChartPartition ι I F V)

private theorem tsupport_cutoff_mul_subset (i : ι) :
    tsupport ⇑(A.cutoff i * A.cutoff i) ⊆ tsupport (A.cutoff i) := by
  rw [ContMDiffMap.coe_mul]
  exact tsupport_mul_subset_left

/-! ### Localization and reconstruction -/

variable [FiniteDimensional ℝ E] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]

/-- The chart localization of bundle tests by a cutoff `ψ` supported in the support of the `i`-th
cutoff, as a continuous linear map into the test functions supported in `A.chartSupport i`. -/
private def localizationCLM (i : ι) (ψ : C^∞⟮I, M; ℝ⟯) (hψ : tsupport ψ ⊆ tsupport (A.cutoff i)) :
    BundleTest I F V →L[ℝ] 𝓓_{A.chartSupport i}(E, F) :=
  (A.chartData i).trivialization.chartLocalizationCLM (A.chartData i).chart
    (A.contMDiffOn_chart_symm i) (A.chartData i).source_subset ψ (A.chartSupport i)
    (A.chartSupport_subset_target i) ((A.mapsTo_chartSupport i).mono_left hψ)

omit [FiniteDimensional ℝ F] in
private theorem localizationCLM_apply_of_mem (i : ι) (ψ : C^∞⟮I, M; ℝ⟯)
    (hψ : tsupport ψ ⊆ tsupport (A.cutoff i)) (s : BundleTest I F V) {y : E}
    (hy : y ∈ (A.chartData i).chart.target) :
    A.localizationCLM i ψ hψ s y = ψ ((A.chartData i).chart.symm y) •
      ((A.chartData i).trivialization
        ⟨(A.chartData i).chart.symm y, s ((A.chartData i).chart.symm y)⟩).2 :=
by
  rw [localizationCLM, Bundle.Trivialization.chartLocalizationCLM_apply]
  exact (A.chartData i).trivialization.chartLocalization_apply_of_mem _ _ _ _ _ _ _ _ hy

omit [FiniteDimensional ℝ F] in
private theorem localizationCLM_apply_of_notMem (i : ι) (ψ : C^∞⟮I, M; ℝ⟯)
    (hψ : tsupport ψ ⊆ tsupport (A.cutoff i)) (s : BundleTest I F V) {y : E}
    (hy : y ∉ (A.chartData i).chart.target) :
    A.localizationCLM i ψ hψ s y = 0 := by
  rw [localizationCLM, Bundle.Trivialization.chartLocalizationCLM_apply]
  exact (A.chartData i).trivialization.chartLocalization_apply_of_notMem _ _ _ _ _ _ _ _ hy

/-- The `j`-th coordinate functional of the fixed basis `Module.finBasis ℝ F` of the model fibre
(chosen non-constructively), with complex values. -/
private def coordCLM (j : Fin (Module.finrank ℝ F)) : F →L[ℝ] ℂ :=
  ofRealCLM ∘L LinearMap.toContinuousLinearMap ((Module.finBasis ℝ F).coord j)

@[simp]
private theorem coordCLM_apply (j : Fin (Module.finrank ℝ F)) (v : F) :
    coordCLM j v = ((Module.finBasis ℝ F).repr v j : ℂ) :=
  rfl

/-- The **localization of bundle tests**: a bundle test `s` goes to the complex Schwartz function
`y ↦ χᵢ (cᵢ⁻¹ y) bⱼ* (tᵢ (s (cᵢ⁻¹ y)))` on the model space, the `j`-th frame coordinate of `s` in
the `i`-th chart cut off by `χᵢ`, extended by zero. Here `(bⱼ*)` is the dual basis of the fixed
basis `Module.finBasis ℝ F` of the model fibre (chosen non-constructively). -/
def testLocalization (i : ι) (j : Fin (Module.finrank ℝ F)) :
    BundleTest I F V →L[ℝ] 𝓢(E, ℂ) :=
  ContDiffMapSupportedIn.toSchwartzMapCLM ℝ ∘L ContDiffMapSupportedIn.postcompCLM (coordCLM j) ∘L
    A.localizationCLM i (A.cutoff i) subset_rfl

theorem testLocalization_apply_of_mem (i : ι) (j : Fin (Module.finrank ℝ F))
    (s : BundleTest I F V) {y : E} (hy : y ∈ (A.chartData i).chart.target) :
    A.testLocalization i j s y = (A.cutoff i ((A.chartData i).chart.symm y) *
      (Module.finBasis ℝ F).repr ((A.chartData i).trivialization
        ⟨(A.chartData i).chart.symm y, s ((A.chartData i).chart.symm y)⟩).2 j : ℝ) := by
  simp [testLocalization, A.localizationCLM_apply_of_mem _ _ _ _ hy]

theorem testLocalization_apply_of_notMem (i : ι) (j : Fin (Module.finrank ℝ F))
    (s : BundleTest I F V) {y : E} (hy : y ∉ (A.chartData i).chart.target) :
    A.testLocalization i j s y = 0 := by
  simp [testLocalization, A.localizationCLM_apply_of_notMem _ _ _ _ hy]

/-- The functional `s ↦ ∑ᵢⱼ Re vᵢⱼ (sᵢⱼ)` on bundle tests. -/
private def reconstructionCLM (v : ι × Fin (Module.finrank ℝ F) → 𝓢'(E, ℂ)) :
    BundleTest I F V →L_c[ℝ] ℝ where
  toFun s := ∑ k, (v k (A.testLocalization k.1 k.2 s)).re
  map_add' s s' := by simp [Finset.sum_add_distrib]
  map_smul' a s := by
    simp only [map_smul, ← Complex.coe_smul, smul_eq_mul, Complex.re_ofReal_mul, Finset.mul_sum,
      RingHom.id_apply]
  cont := continuous_finsetSum _ fun k _ ↦
    continuous_re.comp ((v k).continuous.comp (A.testLocalization k.1 k.2).continuous)

private theorem reconstructionCLM_apply (v : ι × Fin (Module.finrank ℝ F) → 𝓢'(E, ℂ))
    (s : BundleTest I F V) :
    A.reconstructionCLM v s = ∑ k, (v k (A.testLocalization k.1 k.2 s)).re :=
  (rfl)

/-- The **reconstruction** of a functional on bundle tests from tempered distributions `vᵢⱼ`, one
for each chart and each basis vector of the model fibre: `s ↦ ∑ᵢⱼ Re vᵢⱼ (sᵢⱼ)`, where `sᵢⱼ` is
the localization of `s` (`TauCeti.SquareChartPartition.testLocalization`). It inverts the
localization of distributions (`TauCeti.SquareChartPartition.reconstruction_localization`). -/
def reconstruction :
    (ι × Fin (Module.finrank ℝ F) → 𝓢'(E, ℂ)) →ₗ[ℝ] (BundleTest I F V →L_c[ℝ] ℝ) where
  toFun := A.reconstructionCLM
  map_add' v v' := by
    ext s
    simp [reconstructionCLM_apply, Finset.sum_add_distrib]
  map_smul' a v := by
    ext s
    simp [reconstructionCLM_apply, Finset.mul_sum]

theorem reconstruction_apply (v : ι × Fin (Module.finrank ℝ F) → 𝓢'(E, ℂ))
    (s : BundleTest I F V) :
    A.reconstruction v s = ∑ k, (v k (A.testLocalization k.1 k.2 s)).re :=
  (rfl)

/-- The reconstruction of a tuple with a single nonzero entry `w`, in the slot `(i, j)`, is the
functional `s ↦ Re w (sᵢⱼ)`. -/
theorem reconstruction_single_apply [DecidableEq ι] (k : ι × Fin (Module.finrank ℝ F))
    (w : 𝓢'(E, ℂ)) (s : BundleTest I F V) :
    A.reconstruction (Pi.single k w) s = (w (A.testLocalization k.1 k.2 s)).re := by
  rw [reconstruction_apply, Finset.sum_eq_single k (fun l _ hl ↦ by simp [hl]) (by simp)]
  simp

/-- A bundle test vanishing wherever `χᵢ` does not has zero localization in the `i`-th chart. -/
theorem testLocalization_eq_zero (i : ι) (j : Fin (Module.finrank ℝ F)) {s : BundleTest I F V}
    (hs : ∀ z, A.cutoff i z ≠ 0 → s z = 0) : A.testLocalization i j s = 0 := by
  ext y
  by_cases hy : y ∈ (A.chartData i).chart.target
  · rw [A.testLocalization_apply_of_mem _ _ _ hy, zero_apply]
    by_cases hz : A.cutoff i ((A.chartData i).chart.symm y) = 0
    · simp [hz]
    have hzb := (A.chartData i).source_subset ((A.chartData i).chart.map_target hy)
    have h0 := (A.chartData i).trivialization.apply_mk_symm hzb 0
    rw [← Bundle.Trivialization.symmL_apply (R := ℝ) _ hzb, map_zero] at h0
    rw [hs _ hz, h0]
    simp
  · simp [A.testLocalization_apply_of_notMem _ _ _ hy]

end Reconstruction

/-! ### Localization of distributions -/

section Localization

variable {ι : Type*} [Fintype ι]
  {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

variable (A : SquareChartPartition ι I F V)

omit [FiniteDimensional ℝ F] in
/-- Extending the localization by `ψ` back through the chart and the frame gives `ψ • s`. -/
private theorem chartTestCLM_localizationCLM (i : ι) (ψ : C^∞⟮I, M; ℝ⟯)
    (hψ : tsupport ψ ⊆ tsupport (A.cutoff i)) (s : BundleTest I F V) (x : M) :
    (A.chartData i).trivialization.chartTestCLM (A.chartData i).chart
      (A.chartData i).contMDiffOn_chart (A.chartData i).source_subset
      (TestFunction.ofSupportedIn (A.chartSupport_subset_target i) (A.localizationCLM i ψ hψ s)) x =
      ψ x • s x := by
  rw [Bundle.Trivialization.coe_chartTestCLM, localizationCLM,
    Bundle.Trivialization.chartLocalizationCLM_apply]
  refine (congr($((A.chartData i).trivialization.chartTestSection_chartLocalization
    (A.chartData i).chart (A.contMDiffOn_chart_symm i) (A.chartData i).source_subset ψ
    (A.chartSupport i) (A.chartSupport_subset_target i) ((A.mapsTo_chartSupport i).mono_left hψ)
    (A.chartData i).contMDiffOn_chart (hψ.trans (A.tsupport_cutoff_subset i))
    ((BundleTest.ofCompactlySupported I F V).symm s).val) x)).trans ?_
  simp

/-- The **localization of distributions**: a real functional `T` on bundle tests goes to the
tempered distribution `χᵢ Tᵢⱼ` on the model space, where `Tᵢⱼ` is the component of `T` along the
`j`-th basis vector `bⱼ` of the model fibre in the `i`-th chart and frame, `φ ↦ T (φ • bⱼ)`
(`Bundle.Trivialization.chartComponent`), cut off by `χᵢ` read in the chart. -/
def localization (i : ι) (j : Fin (Module.finrank ℝ F)) :
    (BundleTest I F V →L_c[ℝ] ℝ) →ₗ[ℝ] 𝓢'(E, ℂ) where
  toFun T := ((A.chartData i).trivialization.chartComponent (A.chartData i).chart
    (A.chartData i).contMDiffOn_chart (A.chartData i).source_subset T
      (Module.finBasis ℝ F j)).cutoffTempered (A.chartCutoff i)
  map_add' T S := by
    ext ψ
    simp only [Distribution.cutoffTempered_def, Distribution.complexPairing_apply,
      Bundle.Trivialization.chartComponent_apply, _root_.add_apply, ofReal_add]
    ring
  map_smul' a T := by
    ext ψ
    simp only [Distribution.cutoffTempered_def, Distribution.complexPairing_apply,
      Bundle.Trivialization.chartComponent_apply, _root_.smul_apply, RingHom.id_apply]
    simp only [smul_eq_mul, ofReal_mul, smul_add, real_smul]
    ring

theorem localization_apply (i : ι) (j : Fin (Module.finrank ℝ F)) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    A.localization i j T = ((A.chartData i).trivialization.chartComponent (A.chartData i).chart
      (A.chartData i).contMDiffOn_chart (A.chartData i).source_subset T
        (Module.finBasis ℝ F j)).cutoffTempered (A.chartCutoff i) :=
  (rfl)

/-- The localization, in the slot `(i, j)`, of the test `φ • v` extended through the `i`-th chart
and frame is `bⱼ*(v) χᵢ φ`, where `χᵢ` is read in the chart and `(bⱼ*)` is the dual basis of the
fixed basis of the model fibre. -/
theorem testLocalization_chartTestCLM (i : ι) (j : Fin (Module.finrank ℝ F))
    (φ : 𝓓(⟨(A.chartData i).chart.target, (A.chartData i).chart.open_target⟩, ℝ)) (v : F) :
    A.testLocalization i j ((A.chartData i).trivialization.chartTestCLM (A.chartData i).chart
        (A.chartData i).contMDiffOn_chart (A.chartData i).source_subset
        (TestFunction.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ v) φ)) =
      ((Module.finBasis ℝ F).repr v j : ℂ) •
        SchwartzMap.smulLeftCLM ℂ (A.chartCutoff i : E → ℂ)
          (TestFunction.toSchwartzMapCLM ℝ (TestFunction.postcompCLM ofRealCLM φ)) := by
  have hχ := (A.chartCutoff i).hasCompactSupport.hasTemperateGrowth (A.chartCutoff i).contDiff
  ext y
  rw [_root_.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hχ]
  by_cases hy : y ∈ (A.chartData i).chart.target
  · have hs := (A.chartData i).source_subset ((A.chartData i).chart.map_target hy)
    simp [A.testLocalization_apply_of_mem _ _ _ hy, A.chartCutoff_apply_of_mem hy,
      Bundle.Trivialization.chartTestCLM_apply_of_mem _ _ _ _ _
        ((A.chartData i).chart.map_target hy), (A.chartData i).chart.right_inv hy,
      Bundle.Trivialization.symmL_apply _ hs, Bundle.Trivialization.apply_mk_symm _ hs, mul_comm,
      mul_left_comm, mul_assoc]
  · simp [A.testLocalization_apply_of_notMem _ _ _ hy, A.chartCutoff_apply_of_notMem hy]

/-- The component along `v`, in the `i`-th chart and frame, of the functional `s ↦ Re w (sᵢⱼ)`
reconstructed from `w` in the slot `(i, j)`: the real part of the tempered distribution
`bⱼ*(v) χᵢ w`, restricted to the chart target. -/
theorem chartComponent_reconstruction_single [DecidableEq ι] (i : ι)
    (j : Fin (Module.finrank ℝ F)) (w : 𝓢'(E, ℂ)) (v : F) :
    (A.chartData i).trivialization.chartComponent (A.chartData i).chart
        (A.chartData i).contMDiffOn_chart (A.chartData i).source_subset
        (A.reconstruction (Pi.single (i, j) w)) v =
      Distribution.mapCLM (ofRealCLM ∘L reCLM) (TemperedDistribution.toDistribution _
        (((Module.finBasis ℝ F).repr v j : ℂ) •
          TemperedDistribution.smulLeftCLM ℂ (A.chartCutoff i : E → ℂ) w)) := by
  ext φ
  rw [Bundle.Trivialization.chartComponent_apply, reconstruction_single_apply,
    testLocalization_chartTestCLM, map_smul]
  simp

/-- **Reconstructions vanish away from the cutoff.** Away from the support of `χᵢ`, the functional
`s ↦ Re w (sᵢⱼ)` reconstructed from `w` in the slot `(i, j)` vanishes, and so do its components
near the image of `x` in a chart of the partition at `x`. So it satisfies near `x` every predicate
`P` which holds near the points outside the support of a distribution. -/
theorem isLocallyAt_reconstruction_single_of_notMem [DecidableEq ι]
    {P : (Ω : Opens E) → 𝓓'(Ω, ℂ) → E → Prop}
    (hP : ∀ {Ω : Opens E} {T : 𝓓'(Ω, ℂ)} {y : E}, y ∈ Ω → y ∉ Distribution.dsupport T →
      P Ω T y)
    (i : ι) (j : Fin (Module.finrank ℝ F)) (w : 𝓢'(E, ℂ)) {x : M}
    (hx : x ∉ tsupport (A.cutoff i)) :
    BundleTest.IsLocallyAt P (A.reconstruction (Pi.single (i, j) w)) x := by
  obtain ⟨i', hi'⟩ : ∃ i', A.cutoff i' x ≠ 0 := by
    by_contra! h
    simpa [h] using A.sum_sq_cutoff x
  set c := (A.chartData i').chart
  have hxs : x ∈ c.source := A.tsupport_cutoff_subset i' (subset_tsupport _ hi')
  refine BundleTest.IsLocallyAt.intro _ (A.chartData i').contMDiffOn_chart
    (A.contMDiffOn_chart_symm i') (A.chartData i').source_subset hxs fun v ↦ ?_
  refine hP (c.map_source hxs) ?_
  rw [Distribution.notMem_dsupport_iff]
  refine ⟨c.target ∩ c.symm ⁻¹' (tsupport (A.cutoff i))ᶜ, fun φ hφ ↦ ?_,
    c.isOpen_inter_preimage_symm (_root_.isClosed_tsupport _).isOpen_compl, c.map_source hxs,
    by rwa [mem_preimage, c.left_inv hxs]⟩
  rw [Bundle.Trivialization.chartComponent_apply, reconstruction_single_apply,
    A.testLocalization_eq_zero i j fun z hz ↦ ?_]
  · simp
  -- The extended test vanishes where `χᵢ` does not, since `φ` vanishes there in the chart.
  by_cases hz' : z ∈ c.source
  · rw [Bundle.Trivialization.chartTestCLM_apply_of_mem _ _ _ _ _ hz']
    have hφz : φ (c z) = 0 := image_eq_zero_of_notMem_tsupport fun h ↦
      (hφ h).2 (by rw [c.left_inv hz']; exact subset_tsupport _ hz)
    simp [TestFunction.postcompCLM_apply, hφz]
  · exact Bundle.Trivialization.chartTestCLM_apply_of_notMem _ _ _ _ _ hz'

/-- The localization of `T`, paired with the localization of `s`, is `T` evaluated on the `j`-th
frame component of `χᵢ² s`. -/
private theorem localization_apply_testLocalization (T : BundleTest I F V →L_c[ℝ] ℝ) (i : ι)
    (j : Fin (Module.finrank ℝ F)) (s : BundleTest I F V) :
    A.localization i j T (A.testLocalization i j s) =
      (T ((A.chartData i).trivialization.chartTestCLM (A.chartData i).chart
        (A.chartData i).contMDiffOn_chart (A.chartData i).source_subset
        (TestFunction.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (Module.finBasis ℝ F j))
          (TestFunction.postcompCLM
            (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ F).coord j))
            (TestFunction.ofSupportedIn (A.chartSupport_subset_target i)
              (A.localizationCLM i _ (A.tsupport_cutoff_mul_subset i) s))))) : ℂ) := by
  rw [localization_apply, Distribution.cutoffTempered_apply _ _ (χ := TestFunction.postcompCLM
    (𝕜 := ℝ) ofRealCLM (TestFunction.postcompCLM
      (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ F).coord j))
      (TestFunction.ofSupportedIn (A.chartSupport_subset_target i)
        (A.localizationCLM i _ (A.tsupport_cutoff_mul_subset i) s)))),
    Distribution.complexPairing_postcompCLM_ofRealCLM,
    Bundle.Trivialization.chartComponent_apply]
  intro y
  by_cases hy : y ∈ (A.chartData i).chart.target
  · simp [A.testLocalization_apply_of_mem _ _ _ hy, A.chartCutoff_apply_of_mem hy,
      A.localizationCLM_apply_of_mem _ _ _ _ hy, ContMDiffMap.coe_mul]
    ring
  · simp [A.testLocalization_apply_of_notMem _ _ _ hy,
      A.localizationCLM_apply_of_notMem _ _ _ _ hy]

/-- **Reconstruction inverts localization.** A real functional `T` on bundle tests is recovered
from its localizations: `T s = ∑ᵢⱼ Re (χᵢ Tᵢⱼ) (sᵢⱼ)`. This is `∑ᵢ χᵢ² = 1`: the pairing of the
localizations of `T` and `s` in the `i`-th chart is `T (χᵢ² s)`. -/
@[simp]
theorem reconstruction_localization (T : BundleTest I F V →L_c[ℝ] ℝ) :
    A.reconstruction (fun k ↦ A.localization k.1 k.2 T) = T := by
  ext s
  have hi : ∑ i, (A.chartData i).trivialization.chartTestCLM (A.chartData i).chart
      (A.chartData i).contMDiffOn_chart (A.chartData i).source_subset
      (TestFunction.ofSupportedIn (A.chartSupport_subset_target i)
        (A.localizationCLM i _ (A.tsupport_cutoff_mul_subset i) s)) = s := by
    ext x
    have h : ∑ i, (A.cutoff i * A.cutoff i) x = 1 := by
      simpa only [sq, ContMDiffMap.coe_mul, Pi.mul_apply] using A.sum_sq_cutoff x
    simp only [BundleTest.sum_apply, chartTestCLM_localizationCLM, ← Finset.sum_smul, h, one_smul]
  rw [reconstruction_apply, Fintype.sum_prod_type]
  simp only [localization_apply_testLocalization, ofReal_re, ← map_sum,
    TestFunction.sum_postcompCLM_toSpanSingleton_coord, hi]

/-- **Functionals on bundle tests are determined by their localizations.** -/
theorem ext_localization {T T' : BundleTest I F V →L_c[ℝ] ℝ}
    (h : ∀ i j, A.localization i j T = A.localization i j T') : T = T' := by
  rw [← A.reconstruction_localization T, ← A.reconstruction_localization T']
  exact congrArg A.reconstruction (funext fun k ↦ h k.1 k.2)

/-- The value of a localization on a Schwartz function `ψ` only involves the values of `T` on two
bundle tests, which do not depend on `T`: the chart extensions of the real and imaginary parts of
`(χᵢ ψ) bⱼ`, where `χᵢ` is read in the chart. -/
private theorem exists_localization_apply (i : ι) (j : Fin (Module.finrank ℝ F)) (ψ : 𝓢(E, ℂ)) :
    ∃ g g' : BundleTest I F V, ∀ T : BundleTest I F V →L_c[ℝ] ℝ,
      A.localization i j T ψ = (T g : ℂ) + Complex.I * (T g' : ℂ) :=
  let χψ := TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (ψ.smooth ⊤) (A.chartCutoff i)
  let g (φ : 𝓓(⟨(A.chartData i).chart.target, (A.chartData i).chart.open_target⟩, ℝ)) :
      BundleTest I F V :=
    (A.chartData i).trivialization.chartTestCLM (A.chartData i).chart
      (A.chartData i).contMDiffOn_chart (A.chartData i).source_subset
      (TestFunction.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (Module.finBasis ℝ F j)) φ)
  ⟨g (TestFunction.postcompCLM reCLM χψ), g (TestFunction.postcompCLM imCLM χψ), fun T ↦ by
    rw [localization_apply, Distribution.cutoffTempered_def, Distribution.complexPairing_apply,
      Bundle.Trivialization.chartComponent_apply, Bundle.Trivialization.chartComponent_apply]⟩

/-- **Being a tuple of localizations is a closed condition.** Let `v x` be a tuple of tempered
distributions depending on a parameter `x` in a topological space, such that each value
`v x k ψ` on a Schwartz function depends continuously on `x`. Then the parameters for which
`v x` is reproduced by localizing its reconstruction, that is, for which `v x` is the tuple of
localizations of a functional on bundle tests
(`TauCeti.SquareChartPartition.mem_sobolevSpace_iff_exists_localization`), form a closed set: a
value of the localization of a reconstruction only involves finitely many values of the `v x l`. -/
theorem isClosed_setOf_forall_localization_reconstruction_eq {X : Type*} [TopologicalSpace X]
    (v : X → ι × Fin (Module.finrank ℝ F) → 𝓢'(E, ℂ))
    (hv : ∀ k (ψ : 𝓢(E, ℂ)), Continuous fun x ↦ v x k ψ) :
    IsClosed {x | ∀ k, A.localization k.1 k.2 (A.reconstruction (v x)) = v x k} := by
  have h : {x | ∀ k, A.localization k.1 k.2 (A.reconstruction (v x)) = v x k} =
      ⋂ k, ⋂ ψ : 𝓢(E, ℂ), {x | A.localization k.1 k.2 (A.reconstruction (v x)) ψ = v x k ψ} := by
    ext x
    simp only [mem_iInter, Set.mem_ofPred_eq]
    exact forall_congr' fun k ↦ ⟨fun h ψ ↦ by rw [h], fun h ↦ ContinuousLinearMap.ext h⟩
  rw [h]
  refine isClosed_iInter fun k ↦ isClosed_iInter fun ψ ↦ isClosed_eq ?_ (hv k ψ)
  obtain ⟨g, g', hg⟩ := A.exists_localization_apply k.1 k.2 ψ
  simp only [hg, reconstruction_apply]
  refine ((continuous_ofReal.comp ?_).add (continuous_const.mul (continuous_ofReal.comp ?_))) <;>
    exact continuous_finsetSum _ fun l _ ↦ continuous_re.comp (hv l _)

/-! ### Sobolev regularity and the Sobolev spaces -/

section Sobolev

open scoped BesselPotentialSpace

variable [MeasurableSpace E] [BorelSpace E]

/-- A real functional `T` on bundle tests of `V`, for instance a distributional section of a bundle
whose dual density bundle is `V`, is **`H^s` with respect to the square chart partition `A`** when
each of its localizations `χᵢ Tᵢⱼ` (`TauCeti.SquareChartPartition.localization`) lies in the
Bessel-potential space `H^s(E, ℂ)`. -/
def MemSobolev (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) : Prop :=
  ∀ i j, (A.localization i j T).MemSobolev s 2

theorem memSobolev_iff {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} :
    A.MemSobolev s T ↔ ∀ i j, (A.localization i j T).MemSobolev s 2 :=
  Iff.rfl

variable {A} in
theorem MemSobolev.localization {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} (hT : A.MemSobolev s T)
    (i : ι) (j : Fin (Module.finrank ℝ F)) : (A.localization i j T).MemSobolev s 2 :=
  hT i j

variable {A} in
theorem MemSobolev.mono {s r : ℝ} (h : r ≤ s) {T : BundleTest I F V →L_c[ℝ] ℝ}
    (hT : A.MemSobolev s T) : A.MemSobolev r T :=
  fun i j ↦ (hT i j).mono h

/-- **Finite order.** Every real functional on bundle tests of `V`, for instance every
distributional section of a bundle whose dual density bundle is `V`, is `H^s` with respect to `A`
for some `s`: its finitely many localizations are compactly supported distributions, each of which
lies in some `H^s(E, ℂ)`. -/
theorem exists_memSobolev (T : BundleTest I F V →L_c[ℝ] ℝ) : ∃ s, A.MemSobolev s T := by
  choose r hr using fun k : ι × Fin (Module.finrank ℝ F) ↦
    Distribution.exists_memSobolev_cutoffTempered ((A.chartData k.1).trivialization.chartComponent
      (A.chartData k.1).chart (A.chartData k.1).contMDiffOn_chart (A.chartData k.1).source_subset T
      (Module.finBasis ℝ F k.2)) (A.chartCutoff k.1)
  refine ⟨-∑ k, |r k|, fun i j ↦ ?_⟩
  rw [localization_apply]
  refine (hr (i, j)).mono ?_
  -- `-∑ₖ |rₖ| ≤ -|rᵢⱼ| ≤ rᵢⱼ`.
  have := Finset.single_le_sum (fun k _ ↦ abs_nonneg (r k)) (Finset.mem_univ (i, j))
  linarith [neg_abs_le (r (i, j))]

variable (s : ℝ)

/-- The functionals on bundle tests that are `H^s` with respect to `A`, as a real subspace. -/
def memSobolevSubmodule : Submodule ℝ (BundleTest I F V →L_c[ℝ] ℝ) where
  carrier := {T | A.MemSobolev s T}
  add_mem' {T T'} hT hT' i j := by
    rw [map_add]
    exact (hT i j).add (hT' i j)
  zero_mem' i j := by
    rw [map_zero]
    exact TemperedDistribution.memSobolev_fun_zero E ℂ s 2
  smul_mem' a T hT i j := by
    rw [map_smul]
    exact TemperedDistribution.MemSobolev.smul_of_tower a (hT i j)

@[simp]
theorem mem_memSobolevSubmodule {T : BundleTest I F V →L_c[ℝ] ℝ} :
    T ∈ A.memSobolevSubmodule s ↔ A.MemSobolev s T :=
  Iff.rfl

/-- The **Sobolev space `H^s` of functionals on bundle tests of `V`** with respect to the square
chart partition `A`, for instance of distributional sections of a bundle whose dual density bundle
is `V`, realized as the tuples `(uᵢⱼ)` in the Hilbert sum `⨁ᵢⱼ H^s(E, ℂ)` that are localizations
of a functional on bundle tests: those reproduced by localizing their reconstruction. It is a closed
subspace (`TauCeti.SquareChartPartition.isClosed_sobolevSpace`), hence complete, and its norm is
the pinned norm `‖u‖² = ∑ᵢⱼ ‖uᵢⱼ‖²_{H^s}` of the Hilbert sum. The functional represented by `u`
is `TauCeti.SquareChartPartition.toDistribution`. -/
def sobolevSpace :
    Submodule ℝ (PiLp 2 fun _ : ι × Fin (Module.finrank ℝ F) ↦ H^{s}(E, ℂ)) where
  carrier := {u | ∀ k, A.localization k.1 k.2 (A.reconstruction fun l ↦ (u l).toDistr) =
    (u k).toDistr}
  add_mem' {u u'} hu hu' k := by
    simp only [PiLp.add_apply, BesselPotentialSpace.toDistr_add]
    rw [← Pi.add_def, map_add, map_add, hu k, hu' k]
  zero_mem' k := by
    simp only [PiLp.zero_apply, BesselPotentialSpace.toDistr_zero]
    rw [← Pi.zero_def, map_zero, map_zero]
  smul_mem' a u hu k := by
    simp only [PiLp.smul_apply, BesselPotentialSpace.toDistr_real_smul]
    rw [← Pi.smul_def, map_smul, map_smul, hu k]

theorem mem_sobolevSpace {u : PiLp 2 fun _ : ι × Fin (Module.finrank ℝ F) ↦ H^{s}(E, ℂ)} :
    u ∈ A.sobolevSpace s ↔
      ∀ k, A.localization k.1 k.2 (A.reconstruction fun l ↦ (u l).toDistr) = (u k).toDistr :=
  Iff.rfl

/-- The Sobolev space is the image of the localization map: `u` lies in it exactly when its
components are the localizations of some functional on bundle tests. -/
theorem mem_sobolevSpace_iff_exists_localization
    {u : PiLp 2 fun _ : ι × Fin (Module.finrank ℝ F) ↦ H^{s}(E, ℂ)} :
    u ∈ A.sobolevSpace s ↔
      ∃ T : BundleTest I F V →L_c[ℝ] ℝ, ∀ k, A.localization k.1 k.2 T = (u k).toDistr := by
  refine ⟨fun hu ↦ ⟨_, hu⟩, ?_⟩
  rintro ⟨T, hT⟩ k
  have h : (fun l : ι × Fin (Module.finrank ℝ F) ↦ (u l).toDistr) =
      fun l ↦ A.localization l.1 l.2 T := funext fun l ↦ (hT l).symm
  rw [h, reconstruction_localization, hT k]

/-- The `H^s` spaces of `A` are closed in the Hilbert sum `⨁ᵢⱼ H^s(E, ℂ)`. -/
theorem isClosed_sobolevSpace :
    IsClosed
      (A.sobolevSpace s : Set (PiLp 2 fun _ : ι × Fin (Module.finrank ℝ F) ↦ H^{s}(E, ℂ))) :=
  A.isClosed_setOf_forall_localization_reconstruction_eq
    (fun (u : PiLp 2 fun _ : ι × Fin (Module.finrank ℝ F) ↦ H^{s}(E, ℂ)) l ↦ (u l).toDistr)
    fun k ψ ↦
    (ContinuousEvalConst.continuous_eval_const ψ).comp
      (BesselPotentialSpace.continuous_toDistr.comp (PiLp.continuous_apply 2 _ k))

instance : CompleteSpace (A.sobolevSpace s) :=
  (A.isClosed_sobolevSpace s).completeSpace_coe

/-- The Sobolev space is a real Hilbert space: its inner product is the real part of the complex
inner product `∑ᵢⱼ ⟪uᵢⱼ, vᵢⱼ⟫` of the Hilbert sum `⨁ᵢⱼ H^s(E, ℂ)`
(`TauCeti.SquareChartPartition.inner_sobolevSpace`). -/
instance : InnerProductSpace ℝ (A.sobolevSpace s) :=
  letI : InnerProductSpace ℝ (PiLp 2 fun _ : ι × Fin (Module.finrank ℝ F) ↦ H^{s}(E, ℂ)) :=
    InnerProductSpace.complexToReal
  Submodule.innerProductSpace _

theorem inner_sobolevSpace (u v : A.sobolevSpace s) :
    inner ℝ u v = (∑ k, inner ℂ (u.val k) (v.val k)).re := by
  let : InnerProductSpace ℝ (PiLp 2 fun _ : ι × Fin (Module.finrank ℝ F) ↦ H^{s}(E, ℂ)) :=
    InnerProductSpace.complexToReal
  rw [Submodule.coe_inner, real_inner_eq_re_inner ℂ, PiLp.inner_apply, RCLike.re_to_complex]

/-- The functional on bundle tests represented by an element of the Sobolev space
`TauCeti.SquareChartPartition.sobolevSpace`: the reconstruction of its components. -/
def toDistribution : A.sobolevSpace s →ₗ[ℝ] (BundleTest I F V →L_c[ℝ] ℝ) where
  toFun u := A.reconstruction fun l ↦ (u.val l).toDistr
  map_add' u u' := by
    simp only [Submodule.coe_add, PiLp.add_apply, BesselPotentialSpace.toDistr_add]
    rw [← Pi.add_def, map_add]
  map_smul' a u := by
    simp only [Submodule.coe_smul, PiLp.smul_apply, BesselPotentialSpace.toDistr_real_smul,
      RingHom.id_apply]
    rw [← Pi.smul_def, map_smul]

theorem toDistribution_apply (u : A.sobolevSpace s) :
    A.toDistribution s u = A.reconstruction fun l ↦ (u.val l).toDistr :=
  (rfl)

/-- The localizations of the functional represented by `u` are the components of `u`. -/
@[simp]
theorem localization_toDistribution (u : A.sobolevSpace s) (k : ι × Fin (Module.finrank ℝ F)) :
    A.localization k.1 k.2 (A.toDistribution s u) = (u.val k).toDistr :=
  u.property k

theorem memSobolev_toDistribution (u : A.sobolevSpace s) :
    A.MemSobolev s (A.toDistribution s u) := fun i j ↦ by
  rw [A.localization_toDistribution s u (i, j)]
  exact BesselPotentialSpace.memSobolev_toDistr _

theorem toDistribution_injective : Function.Injective (A.toDistribution s) := fun u u' h ↦
  Subtype.ext <| PiLp.ext fun k ↦ BesselPotentialSpace.ext <| by
    rw [← A.localization_toDistribution s u k, ← A.localization_toDistribution s u' k, h]

/-- The element of the Sobolev space representing a functional which is `H^s` with respect to
`A`: the tuple of its localizations. -/
def ofMemSobolev {T : BundleTest I F V →L_c[ℝ] ℝ} (hT : A.MemSobolev s T) : A.sobolevSpace s :=
  ⟨WithLp.toLp 2 fun k ↦ (hT k.1 k.2).toBesselPotentialSpace, fun k ↦ by
    simp only [TemperedDistribution.MemSobolev.toBesselPotentialSpace_toDistr,
      reconstruction_localization]⟩

@[simp]
theorem ofMemSobolev_apply {T : BundleTest I F V →L_c[ℝ] ℝ} (hT : A.MemSobolev s T)
    (k : ι × Fin (Module.finrank ℝ F)) :
    (A.ofMemSobolev s hT).val k = (hT.localization k.1 k.2).toBesselPotentialSpace :=
  (rfl)

@[simp]
theorem toDistribution_ofMemSobolev {T : BundleTest I F V →L_c[ℝ] ℝ} (hT : A.MemSobolev s T) :
    A.toDistribution s (A.ofMemSobolev s hT) = T := by
  simp only [toDistribution_apply, ofMemSobolev_apply,
    TemperedDistribution.MemSobolev.toBesselPotentialSpace_toDistr, reconstruction_localization]

@[simp]
theorem ofMemSobolev_toDistribution (u : A.sobolevSpace s) :
    A.ofMemSobolev s (A.memSobolev_toDistribution s u) = u :=
  A.toDistribution_injective s (A.toDistribution_ofMemSobolev s _)

/-- The functionals represented by the Sobolev space are exactly those which are `H^s` with
respect to `A`. -/
theorem range_toDistribution : LinearMap.range (A.toDistribution s) = A.memSobolevSubmodule s :=
  Submodule.ext fun _ ↦ ⟨by rintro ⟨u, rfl⟩; exact A.memSobolev_toDistribution s u,
    fun hT ↦ ⟨_, A.toDistribution_ofMemSobolev s hT⟩⟩

/-- The Sobolev space is linearly equivalent to the space of functionals on bundle tests that are
`H^s` with respect to `A`. -/
def sobolevSpaceEquiv : A.sobolevSpace s ≃ₗ[ℝ] A.memSobolevSubmodule s :=
  (LinearEquiv.ofInjective _ (A.toDistribution_injective s)).trans
    (LinearEquiv.ofEq _ _ (A.range_toDistribution s))

@[simp]
theorem coe_sobolevSpaceEquiv_apply (u : A.sobolevSpace s) :
    (A.sobolevSpaceEquiv s u : BundleTest I F V →L_c[ℝ] ℝ) = A.toDistribution s u :=
  (rfl)

@[simp]
theorem sobolevSpaceEquiv_symm_apply (T : A.memSobolevSubmodule s) :
    (A.sobolevSpaceEquiv s).symm T =
      A.ofMemSobolev s ((A.mem_memSobolevSubmodule s).1 T.property) :=
  (A.sobolevSpaceEquiv s).symm_apply_eq.2 <| Subtype.ext (A.toDistribution_ofMemSobolev s _).symm

/-- **The pinned norm.** The squared `H^s` norm of a functional which is `H^s` with respect to `A`
is the sum of the squared `H^s(E, ℂ)` norms of its localizations `χᵢ Tᵢⱼ`. -/
theorem norm_ofMemSobolev_sq {T : BundleTest I F V →L_c[ℝ] ℝ} (hT : A.MemSobolev s T) :
    ‖A.ofMemSobolev s hT‖ ^ 2 = ∑ i, ∑ j, ‖(hT.localization i j).toBesselPotentialSpace‖ ^ 2 := by
  rw [← Submodule.norm_coe, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  simp only [ofMemSobolev_apply]

/-! ### The inclusions between the Sobolev spaces -/

variable {s} {r : ℝ}

/-- The **inclusion `H^s ⊆ H^r`** of the Sobolev spaces of `A`, for `r ≤ s`: the inclusion
`H^s(E, ℂ) ⊆ H^r(E, ℂ)` (`BesselPotentialSpace.inclusion`) in every component
(`TauCeti.SquareChartPartition.inclusion_apply`). It represents the same functional on bundle
tests (`TauCeti.SquareChartPartition.toDistribution_inclusion`). -/
def inclusion (h : r ≤ s) : A.sobolevSpace s →L[ℝ] A.sobolevSpace r :=
  (((PiLp.continuousLinearEquiv 2 ℂ _).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.pi fun k : ι × Fin (Module.finrank ℝ F) ↦
        BesselPotentialSpace.inclusion h ∘L PiLp.proj 2 (fun _ ↦ H^{s}(E, ℂ)) k).restrictScalars
      ℝ ∘L (A.sobolevSpace s).subtypeL).codRestrict (A.sobolevSpace r) fun u ↦
    (A.mem_sobolevSpace r).2 fun k ↦ by
      simpa [BesselPotentialSpace.toDistr_inclusion] using u.property k

@[simp]
theorem inclusion_apply (h : r ≤ s) (u : A.sobolevSpace s) (k : ι × Fin (Module.finrank ℝ F)) :
    (A.inclusion h u).val k = BesselPotentialSpace.inclusion h (u.val k) :=
  (rfl)

/-- The inclusion `H^s ⊆ H^r` does not change the represented functional on bundle tests. -/
@[simp]
theorem toDistribution_inclusion (h : r ≤ s) (u : A.sobolevSpace s) :
    A.toDistribution r (A.inclusion h u) = A.toDistribution s u := by
  simp [toDistribution_apply]

@[simp]
theorem inclusion_ofMemSobolev (h : r ≤ s) {T : BundleTest I F V →L_c[ℝ] ℝ}
    (hT : A.MemSobolev s T) : A.inclusion h (A.ofMemSobolev s hT) = A.ofMemSobolev r (hT.mono h) :=
  A.toDistribution_injective r (by simp)

theorem inclusion_injective (h : r ≤ s) : Function.Injective (A.inclusion h) := fun u u' huu' ↦
  A.toDistribution_injective s <| by
    rw [← A.toDistribution_inclusion h u, ← A.toDistribution_inclusion h u', huu']

@[simp]
theorem inclusion_self (u : A.sobolevSpace s) : A.inclusion le_rfl u = u :=
  A.toDistribution_injective s (A.toDistribution_inclusion le_rfl u)

@[simp]
theorem inclusion_inclusion {t : ℝ} (h₁ : r ≤ s) (h₂ : t ≤ r) (u : A.sobolevSpace s) :
    A.inclusion h₂ (A.inclusion h₁ u) = A.inclusion (h₂.trans h₁) u :=
  A.toDistribution_injective t (by simp)

/-- The inclusion `H^s ⊆ H^r` does not increase the norm. -/
theorem norm_inclusion_apply_le (h : r ≤ s) (u : A.sobolevSpace s) : ‖A.inclusion h u‖ ≤ ‖u‖ := by
  rw [← Submodule.norm_coe, ← Submodule.norm_coe u]
  refine PiLp.norm_mono fun k ↦ ?_
  rw [inclusion_apply]
  exact BesselPotentialSpace.norm_inclusion_apply_le h _

theorem norm_inclusion_le (h : r ≤ s) : ‖A.inclusion h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u ↦ by
    simpa using A.norm_inclusion_apply_le h u

end Sobolev

/-! ### Independence of the partition -/

section Independence

open scoped BesselPotentialSpace

variable {κ : Type*} [Fintype κ]

/-- **Regularity of all localizations is local regularity.** Let `P` be an invariant notion of
local regularity and `Q` a property of tempered distributions, related by cutoffs: `S` satisfies
`P` near `y` whenever `χ S` satisfies `Q` for some test function `χ` with `χ y ≠ 0`, and `χ S`
satisfies `Q` whenever `S` satisfies `P` near every point of `tsupport χ`. Then all localizations
`χᵢ Tᵢⱼ` of a real functional `T` on bundle tests satisfy `Q` exactly when `T` satisfies `P` near
every point of `M`. This is the common argument behind the independence of the partition for the
Sobolev and Besov spaces of `A`. -/
theorem forall_localization_iff_forall_isLocallyAt {P : (Ω : Opens E) → 𝓓'(Ω, ℂ) → E → Prop}
    (hP : Distribution.IsInvariantLocalRegularity P) {Q : 𝓢'(E, ℂ) → Prop}
    (hQP : ∀ (Ω : Opens E) (S : 𝓓'(Ω, ℂ)) (χ : 𝓓(Ω, ℂ)) (y : E), χ y ≠ 0 →
      Q (S.cutoffTempered χ) → P Ω S y)
    (hPQ : ∀ (Ω : Opens E) (S : 𝓓'(Ω, ℂ)) (χ : 𝓓(Ω, ℂ)), (∀ y ∈ tsupport χ, P Ω S y) →
      Q (S.cutoffTempered χ))
    {T : BundleTest I F V →L_c[ℝ] ℝ} :
    (∀ i j, Q (A.localization i j T)) ↔ ∀ x, BundleTest.IsLocallyAt P T x := by
  constructor
  · intro hT x
    -- Some cutoff does not vanish at `x`, since their squares sum to one.
    obtain ⟨i, hi⟩ : ∃ i, A.cutoff i x ≠ 0 := by
      by_contra! h
      simpa [h] using A.sum_sq_cutoff x
    have hx : x ∈ (A.chartData i).chart.source :=
      A.tsupport_cutoff_subset i (subset_tsupport _ hi)
    have hcx := (A.chartData i).chart.map_source hx
    refine (BundleTest.isLocallyAt_iff hP T (A.chartData i).contMDiffOn_chart
      (A.contMDiffOn_chart_symm i) (A.chartData i).source_subset hx).2
      (Bundle.Trivialization.chartComponent_of_basis hP.toIsLocalRegularity
        (Module.finBasis ℝ F) T hcx fun j ↦ hQP _ _ (A.chartCutoff i) _ ?_ (hT i j))
    -- The chart cutoff does not vanish at `cᵢ x`.
    rwa [A.chartCutoff_apply_of_mem hcx, (A.chartData i).chart.left_inv hx, ofReal_ne_zero]
  · intro hT i j
    refine hPQ _ _ _ fun y hy ↦ ?_
    -- A point of the support of the chart cutoff is `cᵢ x` for `x` in the support of `χᵢ`.
    obtain ⟨x, hx, rfl⟩ : y ∈ (A.chartData i).chart '' tsupport (A.cutoff i) := by
      rw [← A.coe_chartSupport]
      exact A.tsupport_chartCutoff_subset i hy
    exact (BundleTest.isLocallyAt_iff hP T (A.chartData i).contMDiffOn_chart
      (A.contMDiffOn_chart_symm i) (A.chartData i).source_subset
      (A.tsupport_cutoff_subset i hx)).1 (hT x) _

variable [MeasurableSpace E] [BorelSpace E]

/-- **`H^s` with respect to a partition is local `H^s` regularity.** A real functional `T` on
bundle tests is `H^s` with respect to the square chart partition `A` exactly when it is `H^s` near
every point of `M` (`TauCeti.BundleTest.IsLocallySobolevAt`). In particular this does not depend on
the partition (`TauCeti.SquareChartPartition.memSobolev_iff_memSobolev`). -/
theorem memSobolev_iff_forall_isLocallySobolevAt {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} :
    A.MemSobolev s T ↔ ∀ x, BundleTest.IsLocallySobolevAt s T x :=
  A.memSobolev_iff.trans <| (A.forall_localization_iff_forall_isLocallyAt
    (Distribution.isInvariantLocalRegularity_isLocallySobolevAt s)
    (fun _ _ χ _ hχ hS ↦ Distribution.isLocallySobolevAt_iff_exists_memSobolev_cutoffTempered.2
      ⟨χ, hχ, hS⟩)
    fun _ _ _ ↦ Distribution.memSobolev_cutoffTempered_of_forall_isLocallySobolevAt).trans <|
    forall_congr' fun _ ↦ BundleTest.isLocallySobolevAt_def.symm

/-- **Independence of the partition.** A real functional on bundle tests is `H^s` with respect to
one square chart partition of `V` exactly when it is `H^s` with respect to any other. -/
theorem memSobolev_iff_memSobolev (B : SquareChartPartition κ I F V) {s : ℝ}
    {T : BundleTest I F V →L_c[ℝ] ℝ} : A.MemSobolev s T ↔ B.MemSobolev s T := by
  rw [memSobolev_iff_forall_isLocallySobolevAt, memSobolev_iff_forall_isLocallySobolevAt]

/-- Two square chart partitions of `V` have the same `H^s` functionals. -/
theorem memSobolevSubmodule_eq (B : SquareChartPartition κ I F V) (s : ℝ) :
    A.memSobolevSubmodule s = B.memSobolevSubmodule s :=
  Submodule.ext fun _ ↦ A.memSobolev_iff_memSobolev B

/-- The value of the functional represented by an element of the Sobolev space at a fixed bundle
test depends continuously on the element. -/
theorem continuous_toDistribution_apply (s : ℝ) (φ : BundleTest I F V) :
    Continuous fun u : A.sobolevSpace s ↦ A.toDistribution s u φ := by
  simp only [toDistribution_apply, reconstruction_apply]
  exact continuous_finsetSum _ fun k _ ↦ continuous_re.comp
    ((ContinuousEvalConst.continuous_eval_const _).comp
      (BesselPotentialSpace.continuous_toDistr.comp
        ((PiLp.continuous_apply 2 _ k).comp continuous_subtypeVal)))

/-- The identification of the Sobolev spaces of two square chart partitions as a linear
equivalence: an element of one goes to the element of the other representing the same
functional. -/
private def sobolevSpaceLinearEquiv (B : SquareChartPartition κ I F V) (s : ℝ) :
    A.sobolevSpace s ≃ₗ[ℝ] B.sobolevSpace s :=
  (A.sobolevSpaceEquiv s).trans
    ((LinearEquiv.ofEq _ _ (A.memSobolevSubmodule_eq B s)).trans (B.sobolevSpaceEquiv s).symm)

private theorem toDistribution_sobolevSpaceLinearEquiv (B : SquareChartPartition κ I F V) (s : ℝ)
    (u : A.sobolevSpace s) :
    B.toDistribution s (A.sobolevSpaceLinearEquiv B s u) = A.toDistribution s u := by
  simp [sobolevSpaceLinearEquiv]

/-- **Equivalence of the Sobolev spaces of two partitions.** The Sobolev spaces `H^s` of two
square chart partitions `A` and `B` of `V` are isomorphic as Banach spaces, through the map sending
an element of `A.sobolevSpace s` to the element of `B.sobolevSpace s` representing the same
functional on bundle tests
(`TauCeti.SquareChartPartition.toDistribution_sobolevSpaceCongr_apply`). So the pinned norms of
the two partitions are equivalent (`TauCeti.SquareChartPartition.exists_norm_ofMemSobolev_le`).
Continuity comes from the closed graph theorem. -/
def sobolevSpaceCongr (B : SquareChartPartition κ I F V) (s : ℝ) :
    A.sobolevSpace s ≃L[ℝ] B.sobolevSpace s :=
  (A.sobolevSpaceLinearEquiv B s).toContinuousLinearEquivOfContinuous
    ((A.sobolevSpaceLinearEquiv B s).toLinearMap.continuous_of_injective_comp_eq
      (continuous_pi (A.continuous_toDistribution_apply s))
      (continuous_pi (B.continuous_toDistribution_apply s))
      (DFunLike.coe_injective.comp (B.toDistribution_injective s))
      fun u ↦ congrArg DFunLike.coe (A.toDistribution_sobolevSpaceLinearEquiv B s u))

/-- The identification of the Sobolev spaces of two partitions preserves the represented
functional. -/
@[simp]
theorem toDistribution_sobolevSpaceCongr_apply (B : SquareChartPartition κ I F V) (s : ℝ)
    (u : A.sobolevSpace s) :
    B.toDistribution s (A.sobolevSpaceCongr B s u) = A.toDistribution s u :=
  A.toDistribution_sobolevSpaceLinearEquiv B s u

/-- The identification sends the tuple of localizations of `T` with respect to `A` to its tuple of
localizations with respect to `B`. -/
@[simp]
theorem sobolevSpaceCongr_ofMemSobolev (B : SquareChartPartition κ I F V) {s : ℝ}
    {T : BundleTest I F V →L_c[ℝ] ℝ} (hT : A.MemSobolev s T) :
    A.sobolevSpaceCongr B s (A.ofMemSobolev s hT) =
      B.ofMemSobolev s ((A.memSobolev_iff_memSobolev B).1 hT) :=
  B.toDistribution_injective s (by simp)

/-- The identification of the Sobolev spaces of a partition with itself is the identity. -/
@[simp]
theorem sobolevSpaceCongr_refl (s : ℝ) :
    A.sobolevSpaceCongr A s = ContinuousLinearEquiv.refl ℝ (A.sobolevSpace s) :=
  ContinuousLinearEquiv.ext <| funext fun u ↦ A.toDistribution_injective s (by simp)

/-- The inverse of the identification from `A` to `B` is the identification from `B` to `A`. -/
@[simp]
theorem sobolevSpaceCongr_symm (B : SquareChartPartition κ I F V) (s : ℝ) :
    (A.sobolevSpaceCongr B s).symm = B.sobolevSpaceCongr A s :=
  ContinuousLinearEquiv.ext <| funext fun u ↦ (A.sobolevSpaceCongr B s).symm_apply_eq.2 <|
    B.toDistribution_injective s (by simp)

/-- The identifications compose: going from `A` to `B` and then to `C` is going from `A` to
`C`. -/
@[simp]
theorem sobolevSpaceCongr_trans {ν : Type*} [Fintype ν] (B : SquareChartPartition κ I F V)
    (C : SquareChartPartition ν I F V) (s : ℝ) :
    (A.sobolevSpaceCongr B s).trans (B.sobolevSpaceCongr C s) = A.sobolevSpaceCongr C s :=
  ContinuousLinearEquiv.ext <| funext fun u ↦ C.toDistribution_injective s (by simp)

/-- **Equivalence of the pinned norms.** For two square chart partitions `A` and `B` of `V`, the
`H^s` norm of a functional with respect to `B` is bounded by a constant multiple of its `H^s` norm
with respect to `A`. -/
theorem exists_norm_ofMemSobolev_le (B : SquareChartPartition κ I F V) (s : ℝ) :
    ∃ C, ∀ (T : BundleTest I F V →L_c[ℝ] ℝ) (hA : A.MemSobolev s T) (hB : B.MemSobolev s T),
      ‖B.ofMemSobolev s hB‖ ≤ C * ‖A.ofMemSobolev s hA‖ :=
  ⟨‖(A.sobolevSpaceCongr B s : A.sobolevSpace s →L[ℝ] B.sobolevSpace s)‖, fun T hA hB ↦ by
    simpa using (A.sobolevSpaceCongr B s : A.sobolevSpace s →L[ℝ] B.sobolevSpace s).le_opNorm
      (A.ofMemSobolev s hA)⟩

end Independence

end Localization

end SquareChartPartition

end TauCeti
