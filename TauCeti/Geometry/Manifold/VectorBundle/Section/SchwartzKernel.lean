/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.ExternalTensor
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Tensor
import TauCeti.Analysis.Distribution.SchwartzKernel.Basic
import TauCeti.Analysis.Distribution.TestFunction.TensorDensity
import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartCutoffs
import TauCeti.Geometry.Manifold.VectorBundle.Trivial
import TauCeti.Topology.FiberBundle.Trivial

/-!
# The Schwartz kernel theorem on manifolds

Let `M` and `N` be boundaryless Hausdorff `σ`-compact smooth manifolds with finite-dimensional
models. The *scalar tests* on `M` are the bundle tests of the trivial line `Bundle.Trivial M ℝ`, the
compactly supported smooth real functions on `M` with their test topology. The tensor product of a
scalar test `φ` on `M` and a scalar test `ψ` on `N` is the scalar test

`(φ ⊗ ψ)(x, y) = φ x * ψ y`

on `M × N` (`TauCeti.BundleTest.tensor`). The **Schwartz kernel theorem** says that every real
bilinear map `B` on the scalar tests on `M` and `N`, with values in a real Banach space `G`, which
is continuous in each variable is given by a unique *kernel*: a continuous linear map `K` on the
scalar tests on `M × N` with

`K (φ ⊗ ψ) = B φ ψ`

for all `φ` and `ψ` (`LinearMap.existsUnique_schwartzKernel_tensor_of_continuous`). In operator
form, every continuous linear map `A` from the scalar tests on `N` to the `G`-valued continuous
linear functionals on the scalar tests on `M` has a unique kernel `K` with `K (φ ⊗ ψ) = A ψ φ`
(`ContinuousLinearMap.existsUnique_schwartzKernel_tensor`). In particular kernels are determined
by their values on tensor products (`TauCeti.BundleTest.ext_tensor`).

The same holds with coefficients in vector bundles. Let `V → M` and `W → N` be finite-rank smooth
real vector bundles, with external tensor product `V ⊠ W` over `M × N`, whose fibre over `(x, y)` is
`V x ⊗ W y` (`TauCeti.ExternalTensor`). Every real bilinear map `B` on the bundle tests of `V` and
of `W` which is continuous in each variable has a unique kernel: a continuous linear map `K` on the
bundle tests of `V ⊠ W` with

`K (s ⊠ t) = B s t`

for all bundle tests `s` of `V` and `t` of `W`, where `(s ⊠ t)(x, y) = s x ⊗ t y`
(`TauCeti.BundleTest.externalTensor`,
`LinearMap.existsUnique_schwartzKernel_externalTensor_of_continuous`, and the operator form
`ContinuousLinearMap.existsUnique_schwartzKernel_externalTensor`). Densities enter through the
choice of bundles: an operator from the sections of `W` to the distributional sections of a bundle
`E` over `M` (`TauCeti.BundleDistribution`) is a map into the functionals on the tests of the bundle
`Hom(E, |Λ|)` of `E`-dual densities, and its kernel is a functional on the tests of
`Hom(E, |Λ|) ⊠ W`. Through `|Λ_{M×N}| ≅ |Λ_M| ⊠ |Λ_N|` (not formalized here) this corresponds to the
kernel with coefficients in `E ⊠ (W* ⊗ |Λ_N|)` of Hörmander, §6.3.

## Proof

Cover `M` and `N` by smooth charts carrying smooth partitions of unity `(ρᵢ)` and `(σⱼ)` whose
functions have compact supports in the chart sources (`TauCeti.ChartCutoffs`). The products
`ρᵢ ⊗ σⱼ` form a partition of unity on `M × N` subordinate to the product charts
(`TauCeti.ChartCutoffs.prod`), and each scalar test `Φ` on `M × N` is the finite sum of the pieces
`(ρᵢ ⊗ σⱼ) Φ` (`TauCeti.ChartCutoffs.sum_smulLeftCLM`), each the extension through a product chart
of its localization, a test function on the chart target, a product of open subsets of the two model
spaces (`TauCeti.ChartCutoffs.chartTestCLM_localize`).

* **Uniqueness.** Read through a product chart, a kernel of `B` is a distribution on a product of
  open sets of the model spaces, determined by its values on tensor products of test functions
  (`TestFunction.ext_prodSMulCLM`). Summing over the pieces of `Φ` determines its value on `Φ`.
* **Existence.** Read through the two charts, `B` becomes a separately continuous bilinear map on
  test functions on open subsets of the model spaces, which has a Euclidean kernel `κᵢⱼ`
  (`LinearMap.existsUnique_schwartzKernel_prodSMulCLM_of_continuous`). The kernel of `B` is
  `K Φ = ∑ᵢⱼ κᵢⱼ ((ρᵢ ⊗ σⱼ) Φ)`, a locally finite sum. On `φ ⊗ ψ` the term `(i, j)` is
  `B (ρᵢ φ) (σⱼ ψ)`, and summing gives `B φ ψ`.

With coefficients in bundles, the charts are chosen inside base sets of trivializations of `V` and
of `W` (`TauCeti.ChartCutoffs.exists_source_subset_baseSet`), so that a test of `V ⊠ W` localized to
a product chart is a test function with values in the tensor product `F ⊗ F'` of the model fibres.
Its coordinates in a basis `fₐ ⊗ g_b` are scalar test functions, and the term of the kernel at a
product chart is the sum over `(a, b)` of the Euclidean kernels of `(φ, ψ) ↦ B (φ • fₐ) (ψ • g_b)`,
the functions `φ • fₐ` and `ψ • g_b` being extended to bundle tests through the charts and the
trivializations. Extending `(u, u') ↦ ψ u' φ u • (fₐ ⊗ g_b)` through a product chart gives
`(φ • fₐ) ⊠ (ψ • g_b)` (`Bundle.Trivialization.chartTestCLM_externalTensor_prodSMulCLM`), which is
how both the uniqueness and the existence arguments reduce to the scalar Euclidean theorem.

## Main declarations

* `TauCeti.BundleTest.ext_tensor`: continuous linear maps on the scalar tests on `M × N` that agree
  on tensor products are equal.
* `LinearMap.existsUnique_schwartzKernel_tensor_of_continuous`: **the Schwartz kernel theorem** for
  separately continuous bilinear maps on scalar tests.
* `ContinuousLinearMap.existsUnique_schwartzKernel_tensor`: its operator form.
* `TauCeti.BundleTest.ext_externalTensor`: continuous linear maps on the bundle tests of `V ⊠ W`
  that agree on external tensor products are equal.
* `LinearMap.existsUnique_schwartzKernel_externalTensor_of_continuous`,
  `ContinuousLinearMap.existsUnique_schwartzKernel_externalTensor`: **the Schwartz kernel theorem
  with coefficients in vector bundles**.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 5.2.1 (the Schwartz kernel theorem) and §6.3 (distributions on
  manifolds through partitions of unity subordinate to charts).
-/

public noncomputable section

open Bundle Set Function TopologicalSpace ContMDiffSection
open scoped ContDiff Manifold Distributions Topology CompactConvergenceCLM

namespace TauCeti

open BundleTest (smulLeftCLM smulLeftCLM_apply)

/-! ### Scalar tests in charts -/

section Scalar

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {P : Type*} [TopologicalSpace P] [ChartedSpace H P]

private theorem subset_baseSet_trivial (s : Set P) :
    s ⊆ (Bundle.Trivial.trivialization P ℝ).baseSet :=
  fun x _ ↦ mem_univ x

variable [IsManifold I ∞ P] [T2Space P] [LocallyCompactSpace E]

/-- The extension of real test functions on a chart target to scalar tests, by zero outside the
chart source. -/
private def chartTest (c : OpenPartialHomeomorph P E) (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) :
    𝓓(⟨c.target, c.open_target⟩, ℝ) →L[ℝ] BundleTest I ℝ (Bundle.Trivial P ℝ) :=
  (Bundle.Trivial.trivialization P ℝ).chartTestCLM c hc (subset_baseSet_trivial _)

private theorem chartTest_apply_of_mem (c : OpenPartialHomeomorph P E)
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (φ : 𝓓(⟨c.target, c.open_target⟩, ℝ)) {z : P}
    (hz : z ∈ c.source) : (chartTest c hc φ z : ℝ) = φ (c z) := by
  rw [chartTest, Bundle.Trivialization.chartTestCLM_apply_of_mem _ c hc _ φ hz]
  simp

private theorem chartTest_apply_of_notMem (c : OpenPartialHomeomorph P E)
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (φ : 𝓓(⟨c.target, c.open_target⟩, ℝ)) {z : P}
    (hz : z ∉ c.source) : chartTest c hc φ z = 0 :=
  Bundle.Trivialization.chartTestCLM_apply_of_notMem _ c hc _ φ hz

private theorem chartTest_injective (c : OpenPartialHomeomorph P E)
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) : Injective (chartTest c hc) :=
  Bundle.Trivialization.chartTestCLM_injective _ c hc _

/-- The localization `Φ ↦ (ρᵢ Φ) ∘ cᵢ⁻¹` of scalar tests along chart cutoffs, read in the
trivialization of the trivial line. -/
private def scalarLocalize {ι : Type*} (A : ChartCutoffs I P ⊤ ι) (i : ι) :
    BundleTest I ℝ (Bundle.Trivial P ℝ) →L[ℝ] 𝓓(⟨(A.chart i).target, (A.chart i).open_target⟩, ℝ) :=
  A.localize (fun _ ↦ Trivial.trivialization P ℝ) (fun _ ↦ subset_baseSet_trivial _) i

/-- Extending the localization of `Φ` along chart cutoffs back through the chart gives
`ρᵢ Φ`. -/
private theorem chartTest_scalarLocalize {ι : Type*} (A : ChartCutoffs I P ⊤ ι) (i : ι)
    (Φ : BundleTest I ℝ (Bundle.Trivial P ℝ)) :
    chartTest (A.chart i) (A.contMDiffOn_chart i) (scalarLocalize A i Φ) =
      smulLeftCLM (A.cutoff i) Φ :=
  A.chartTestCLM_localize (fun _ ↦ Trivial.trivialization P ℝ)
    (fun _ ↦ subset_baseSet_trivial _) i Φ

/-- A localization to a chart whose cutoff does not meet a compact set `K` vanishes on the scalar
tests supported in `K`. -/
private theorem scalarLocalize_eq_zero {ι : Type*} (A : ChartCutoffs I P ⊤ ι) {K : Set P}
    {hK : IsCompact K} {i : ι} (hi : i ∉ A.meeting K hK)
    {Φ : BundleTest I ℝ (Bundle.Trivial P ℝ)} (hΦ : closure {x | Φ x ≠ 0} ⊆ K) :
    scalarLocalize A i Φ = 0 :=
  A.localize_eq_zero _ (fun _ ↦ subset_baseSet_trivial _) hi hΦ

end Scalar

namespace BundleTest

/-! ### Locally finite sums over chart cutoffs -/

section LocallyFinite

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {P : Type*} [TopologicalSpace P] [ChartedSpace H P]
  [IsManifold I ∞ P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : P → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {ι : Type*} (C : ChartCutoffs I P ⊤ ι) (κ : ι → BundleTest I F V →L[ℝ] G)
  (hκ : ∀ {L : Set P} {hL : IsCompact L} {i : ι}, i ∉ C.meeting L hL →
    ∀ {Φ : BundleTest I F V}, closure {x | Φ x ≠ 0} ⊆ L → κ i Φ = 0)

include hκ in
/-- Only the indices whose cutoffs meet a compact set `L` contribute to `∑ᶠ i, κ i Φ` for a bundle
test `Φ` supported in `L`. -/
private theorem finsum_eq_sum_meeting {L : Set P} (hL : IsCompact L) {Φ : BundleTest I F V}
    (hΦ : closure {x | Φ x ≠ 0} ⊆ L) : ∑ᶠ i, κ i Φ = ∑ i ∈ C.meeting L hL, κ i Φ :=
  finsum_eq_sum_of_support_subset _ fun _ hi ↦ by_contra fun h ↦ hi (hκ h hΦ)

/-- The locally finite sum `Φ ↦ ∑ᶠ i, κ i Φ` of continuous linear maps `κ i` on bundle tests, each
vanishing on the tests supported away from its cutoff, as a linear map. -/
private def finsumₗ : BundleTest I F V →ₗ[ℝ] G where
  toFun Φ := ∑ᶠ i, κ i Φ
  map_add' Φ Ψ := by
    have hL := Φ.isCompact_tsupport.union Ψ.isCompact_tsupport
    rw [finsum_eq_sum_meeting C κ hκ hL subset_union_left,
      finsum_eq_sum_meeting C κ hκ hL subset_union_right,
      finsum_eq_sum_meeting C κ hκ hL (Φ.tsupport_add_subset Ψ), ← Finset.sum_add_distrib]
    simp only [map_add]
  map_smul' a Φ := by
    rw [finsum_eq_sum_meeting C κ hκ Φ.isCompact_tsupport (Φ.tsupport_smul_subset a),
      finsum_eq_sum_meeting C κ hκ Φ.isCompact_tsupport subset_rfl, Finset.smul_sum]
    simp only [map_smul, RingHom.id_apply]

/-- The locally finite sum `Φ ↦ ∑ᶠ i, κ i Φ` of continuous linear maps `κ i` on bundle tests, each
vanishing on the tests supported away from its cutoff, as a continuous linear map. -/
private def finsumCLM : BundleTest I F V →L[ℝ] G where
  toLinearMap := finsumₗ C κ hκ
  cont := by
    let := frameTopology (I := I) (n := ∞) (fun x : P ↦ trivializationAt F V x)
      (fun x ↦ ⟨_, (trivializationAt F V x).open_baseSet⟩) fun _ ↦ subset_rfl
    refine (BundleTest.continuous_iff_continuous_comp (finsumₗ C κ hκ)).2 fun L ↦ ?_
    -- On the tests supported in `L` the sum is a finite sum of continuous maps.
    refine (continuous_finsetSum (C.meeting L L.isCompact) fun i _ ↦
      (κ i).continuous.comp (BundleTest.continuous_ofSupportedIn L)).congr fun σ ↦ ?_
    exact (finsum_eq_sum_meeting C κ hκ L.isCompact
      (BundleTest.tsupport_ofSupportedIn_subset L σ)).symm

private theorem finsumCLM_apply (Φ : BundleTest I F V) : finsumCLM C κ hκ Φ = ∑ᶠ i, κ i Φ :=
  rfl

end LocallyFinite

section BilinearCutoffs

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : N → Type*} [∀ y, AddCommGroup (W y)] [∀ y, Module ℝ (W y)] [∀ y, TopologicalSpace (W y)]
  [TopologicalSpace (TotalSpace F' W)] [FiberBundle F' W] [VectorBundle ℝ F' W]
  [ContMDiffVectorBundle ∞ F' W J]
  {G : Type*} [AddCommGroup G] [Module ℝ G]

/-- Summing a bilinear map `B` on bundle tests over the products of the cutoffs `ρᵢ` and `σⱼ` of
two families of chart cutoffs recovers it: `∑ᶠ (i, j), B (ρᵢ s) (σⱼ t) = B s t`. -/
private theorem finsum_smulLeftCLM_smulLeftCLM {ι κ : Type*} (A : ChartCutoffs I M ⊤ ι)
    (A' : ChartCutoffs J N ⊤ κ) (B : BundleTest I F V →ₗ[ℝ] BundleTest J F' W →ₗ[ℝ] G)
    (s : BundleTest I F V) (t : BundleTest J F' W) :
    ∑ᶠ p : ι × κ, B (smulLeftCLM (A.cutoff p.1) s) (smulLeftCLM (A'.cutoff p.2) t) = B s t := by
  -- Only the charts whose cutoffs meet the supports of `s` and of `t` contribute.
  refine (A.finsum_prod_eq_sum_meeting A' s.isCompact_tsupport t.isCompact_tsupport
    (f := fun i j ↦ B (smulLeftCLM (A.cutoff i) s) (smulLeftCLM (A'.cutoff j) t))
    (fun i j hi ↦ by rw [A.smulLeftCLM_eq_zero hi subset_rfl, map_zero, LinearMap.zero_apply])
    (fun i j hj ↦ by rw [A'.smulLeftCLM_eq_zero hj subset_rfl, map_zero])).trans ?_
  simp_rw [← map_sum (B _), ← LinearMap.sum_apply, ← map_sum B,
    A.sum_smulLeftCLM s.isCompact_tsupport subset_rfl,
    A'.sum_smulLeftCLM t.isCompact_tsupport subset_rfl]

end BilinearCutoffs

/-! ### Tensor products in product charts -/

section Tensor

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [LocallyCompactSpace E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

/-- Extending a tensor product of test functions through a product chart gives the tensor
product of their extensions. -/
private theorem chartTest_prod_prodSMulCLM {ι κ : Type*} (A : ChartCutoffs I M ⊤ ι)
    (B : ChartCutoffs J N ⊤ κ) (p : ι × κ)
    (φ : 𝓓(⟨(A.chart p.1).target, (A.chart p.1).open_target⟩, ℝ))
    (ψ : 𝓓(⟨(B.chart p.2).target, (B.chart p.2).open_target⟩, ℝ)) :
    chartTest ((A.prod B).chart p) ((A.prod B).contMDiffOn_chart p)
        (TestFunction.prodSMulCLM ψ (A.prod_chart_target B p).symm.subset φ) =
      (chartTest (A.chart p.1) (A.contMDiffOn_chart p.1) φ).tensor
        (chartTest (B.chart p.2) (B.contMDiffOn_chart p.2) ψ) := by
  refine BundleTest.ext fun z ↦ ?_
  by_cases hz : z ∈ ((A.prod B).chart p).source
  · have hz' := hz
    rw [ChartCutoffs.prod_chart, OpenPartialHomeomorph.prod_source] at hz'
    rw [chartTest_apply_of_mem _ _ _ hz, tensor_apply, chartTest_apply_of_mem _ _ _ hz'.1,
      chartTest_apply_of_mem _ _ _ hz'.2]
    simp [TestFunction.prodSMulCLM_apply, ChartCutoffs.prod_chart,
      OpenPartialHomeomorph.prod_apply, mul_comm]
  · rw [chartTest_apply_of_notMem _ _ _ hz]
    rw [ChartCutoffs.prod_chart, OpenPartialHomeomorph.prod_source, mem_prod, not_and_or] at hz
    rcases hz with hz | hz
    · rw [tensor_apply, chartTest_apply_of_notMem _ _ _ hz, zero_mul]
    · rw [tensor_apply, chartTest_apply_of_notMem _ _ _ hz, mul_zero]

/-- The localization of a tensor product to a product chart is the tensor product of the
localizations. -/
private theorem localize_prod_tensor {ι κ : Type*} (A : ChartCutoffs I M ⊤ ι)
    (B : ChartCutoffs J N ⊤ κ) (p : ι × κ) (φ : BundleTest I ℝ (Bundle.Trivial M ℝ))
    (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) :
    scalarLocalize (A.prod B) p (φ.tensor ψ) =
      TestFunction.prodSMulCLM (scalarLocalize B p.2 ψ) (A.prod_chart_target B p).symm.subset
        (scalarLocalize A p.1 φ) := by
  refine chartTest_injective _ ((A.prod B).contMDiffOn_chart p) ?_
  rw [chartTest_prod_prodSMulCLM, chartTest_scalarLocalize, chartTest_scalarLocalize,
    chartTest_scalarLocalize, ChartCutoffs.prod_cutoff, smulLeftCLM_mulProd_tensor]

end Tensor

/-! ### The Schwartz kernel theorem -/

section Kernel

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

/-! #### The kernel of a bilinear map -/

section Existence

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- The Euclidean kernel of a separately continuous bilinear map `B` on scalar tests, read through
the product chart `p` of chart cutoffs `A` and `A'`. -/
private def localKernel (A : ChartCutoffs I M ⊤ M) (A' : ChartCutoffs J N ⊤ N)
    (B : BundleTest I ℝ (Bundle.Trivial M ℝ) →ₗ[ℝ] BundleTest J ℝ (Bundle.Trivial N ℝ) →ₗ[ℝ] G)
    (h₁ : ∀ ψ, Continuous fun φ ↦ B φ ψ) (h₂ : ∀ φ, Continuous (B φ)) (p : M × N) :
    𝓓'(⟨((A.prod A').chart p).target, ((A.prod A').chart p).open_target⟩, G) :=
  (LinearMap.existsUnique_schwartzKernel_prodSMulCLM_of_continuous
    (B.compl₁₂ (chartTest (A.chart p.1) (A.contMDiffOn_chart p.1)).toLinearMap
      (chartTest (A'.chart p.2) (A'.contMDiffOn_chart p.2)).toLinearMap)
    (fun _ ↦ (h₁ _).comp (chartTest _ _).continuous)
    (fun _ ↦ (h₂ _).comp (chartTest _ _).continuous)
    (A.prod_chart_target A' p)).exists.choose

/-- On `φ' ⊗ ψ'` the local kernel of `B` at the product chart `c × d` takes the value of `B` on the
extensions of `φ'` and `ψ'` through `c` and `d`. -/
private theorem localKernel_prodSMulCLM (A : ChartCutoffs I M ⊤ M) (A' : ChartCutoffs J N ⊤ N)
    (B : BundleTest I ℝ (Bundle.Trivial M ℝ) →ₗ[ℝ] BundleTest J ℝ (Bundle.Trivial N ℝ) →ₗ[ℝ] G)
    (h₁ : ∀ ψ, Continuous fun φ ↦ B φ ψ) (h₂ : ∀ φ, Continuous (B φ)) (p : M × N)
    (φ : 𝓓(⟨(A.chart p.1).target, (A.chart p.1).open_target⟩, ℝ))
    (ψ : 𝓓(⟨(A'.chart p.2).target, (A'.chart p.2).open_target⟩, ℝ)) :
    localKernel A A' B h₁ h₂ p
        (TestFunction.prodSMulCLM ψ (A.prod_chart_target A' p).symm.subset φ) =
      B (chartTest (A.chart p.1) (A.contMDiffOn_chart p.1) φ)
        (chartTest (A'.chart p.2) (A'.contMDiffOn_chart p.2) ψ) :=
  (LinearMap.existsUnique_schwartzKernel_prodSMulCLM_of_continuous _
    (fun _ ↦ (h₁ _).comp (chartTest _ _).continuous)
    (fun _ ↦ (h₂ _).comp (chartTest _ _).continuous)
    (A.prod_chart_target A' p)).exists.choose_spec φ ψ

/-- The kernel `Φ ↦ ∑ₚ κ_p ((ρ ⊗ σ)_p Φ)` of `B`, a locally finite sum of the local kernels, as a
continuous linear map. -/
private def kernel (A : ChartCutoffs I M ⊤ M) (A' : ChartCutoffs J N ⊤ N)
    (B : BundleTest I ℝ (Bundle.Trivial M ℝ) →ₗ[ℝ] BundleTest J ℝ (Bundle.Trivial N ℝ) →ₗ[ℝ] G)
    (h₁ : ∀ ψ, Continuous fun φ ↦ B φ ψ) (h₂ : ∀ φ, Continuous (B φ)) :
    BundleTest (I.prod J) ℝ (Bundle.Trivial (M × N) ℝ) →L[ℝ] G :=
  finsumCLM (A.prod A')
    (fun p ↦ (ContinuousLinearMap.toUniformConvergenceCLM _ _ _).symm
      (localKernel A A' B h₁ h₂ p) ∘L scalarLocalize (A.prod A') p)
    fun hp _ hΦ ↦ by
      rw [ContinuousLinearMap.comp_apply, scalarLocalize_eq_zero (A.prod A') hp hΦ, map_zero]

private theorem kernel_apply (A : ChartCutoffs I M ⊤ M) (A' : ChartCutoffs J N ⊤ N)
    (B : BundleTest I ℝ (Bundle.Trivial M ℝ) →ₗ[ℝ] BundleTest J ℝ (Bundle.Trivial N ℝ) →ₗ[ℝ] G)
    (h₁ : ∀ ψ, Continuous fun φ ↦ B φ ψ) (h₂ : ∀ φ, Continuous (B φ))
    (Φ : BundleTest (I.prod J) ℝ (Bundle.Trivial (M × N) ℝ)) :
    kernel A A' B h₁ h₂ Φ =
      ∑ᶠ p, localKernel A A' B h₁ h₂ p (scalarLocalize (A.prod A') p Φ) :=
  rfl

/-- On `φ ⊗ ψ` the term of the product chart `p` of the kernel is `B (ρ φ) (σ ψ)`, for the cutoffs
`ρ` and `σ` of the two charts. -/
private theorem localKernel_localize_tensor (A : ChartCutoffs I M ⊤ M) (A' : ChartCutoffs J N ⊤ N)
    (B : BundleTest I ℝ (Bundle.Trivial M ℝ) →ₗ[ℝ] BundleTest J ℝ (Bundle.Trivial N ℝ) →ₗ[ℝ] G)
    (h₁ : ∀ ψ, Continuous fun φ ↦ B φ ψ) (h₂ : ∀ φ, Continuous (B φ)) (p : M × N)
    (φ : BundleTest I ℝ (Bundle.Trivial M ℝ)) (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) :
    localKernel A A' B h₁ h₂ p (scalarLocalize (A.prod A') p (φ.tensor ψ)) =
      B (smulLeftCLM (A.cutoff p.1) φ) (smulLeftCLM (A'.cutoff p.2) ψ) := by
  rw [localize_prod_tensor, localKernel_prodSMulCLM, chartTest_scalarLocalize,
    chartTest_scalarLocalize]

private theorem kernel_tensor (A : ChartCutoffs I M ⊤ M) (A' : ChartCutoffs J N ⊤ N)
    (B : BundleTest I ℝ (Bundle.Trivial M ℝ) →ₗ[ℝ] BundleTest J ℝ (Bundle.Trivial N ℝ) →ₗ[ℝ] G)
    (h₁ : ∀ ψ, Continuous fun φ ↦ B φ ψ) (h₂ : ∀ φ, Continuous (B φ))
    (φ : BundleTest I ℝ (Bundle.Trivial M ℝ)) (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) :
    kernel A A' B h₁ h₂ (φ.tensor ψ) = B φ ψ := by
  simp_rw [kernel_apply, localKernel_localize_tensor]
  exact finsum_smulLeftCLM_smulLeftCLM A A' B φ ψ

end Existence

variable [I.Boundaryless] [SigmaCompactSpace M] [J.Boundaryless] [SigmaCompactSpace N]

/-- **Kernels are determined by their values on tensor products.** Two continuous linear maps on
the scalar tests on `M × N` agree once they agree on every tensor product `φ ⊗ ψ` of scalar tests
on `M` and `N`. -/
theorem ext_tensor {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [T2Space G]
    {K₁ K₂ : BundleTest (I.prod J) ℝ (Bundle.Trivial (M × N) ℝ) →L[ℝ] G}
    (h : ∀ φ ψ, K₁ (tensor φ ψ) = K₂ (tensor φ ψ)) : K₁ = K₂ := by
  obtain ⟨A⟩ := ChartCutoffs.nonempty I M ⊤
  obtain ⟨B⟩ := ChartCutoffs.nonempty J N ⊤
  -- On the extensions through each product chart the two maps agree, by the density of tensor
  -- products of test functions.
  have hC (p : M × N) : K₁ ∘L chartTest ((A.prod B).chart p) ((A.prod B).contMDiffOn_chart p) =
      K₂ ∘L chartTest ((A.prod B).chart p) ((A.prod B).contMDiffOn_chart p) :=
    TestFunction.ext_prodSMulCLM (A.prod_chart_target B p) fun ψ φ ↦ by
      have hp := chartTest_prod_prodSMulCLM A B p φ ψ
      exact (congrArg K₁ hp).trans ((h _ _).trans (congrArg K₂ hp).symm)
  ext Φ
  rw [← (A.prod B).sum_smulLeftCLM Φ.isCompact_tsupport subset_rfl, map_sum, map_sum]
  simp_rw [← chartTest_scalarLocalize]
  exact Finset.sum_congr rfl fun p _ ↦ DFunLike.congr_fun (hC p) _

end Kernel

/-! ### Kernels with coefficients in vector bundles -/

section BundleKernel

open TestFunction (postcompCLM prodSMulCLM sum_postcompCLM_toSpanSingleton_coord
  postcompCLM_postcompCLM_toSpanSingleton)
open ContinuousLinearMap (toSpanSingleton)

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {W : N → Type*} [∀ y, AddCommGroup (W y)] [∀ y, Module ℝ (W y)] [∀ y, TopologicalSpace (W y)]
  [∀ y, IsTopologicalAddGroup (W y)] [∀ y, ContinuousSMul ℝ (W y)]
  [TopologicalSpace (TotalSpace F' W)] [FiberBundle F' W] [VectorBundle ℝ F' W]
  [ContMDiffVectorBundle ∞ F' W J]

/-! #### Frames in charts -/

/-- The extension of test functions on the target of the chart `A.chart x` to bundle tests of `V`,
through the preferred trivialization of `V` at `x`. -/
private def frameTest (A : ChartCutoffs I M ⊤ M)
    (hA : ∀ x, (A.chart x).source ⊆ (trivializationAt F V x).baseSet) (x : M) :
    𝓓(⟨(A.chart x).target, (A.chart x).open_target⟩, F) →L[ℝ] BundleTest I F V :=
  (trivializationAt F V x).chartTestCLM (A.chart x) (A.contMDiffOn_chart x) (hA x)

/-- The localization `s ↦ (ρₓ s) ∘ cₓ⁻¹` of bundle tests of `V`, read in the preferred
trivialization of `V` at `x`. -/
private def frameLocalize (A : ChartCutoffs I M ⊤ M)
    (hA : ∀ x, (A.chart x).source ⊆ (trivializationAt F V x).baseSet) (x : M) :
    BundleTest I F V →L[ℝ] 𝓓(⟨(A.chart x).target, (A.chart x).open_target⟩, F) :=
  A.localize (fun x ↦ trivializationAt F V x) hA x

omit [FiniteDimensional ℝ F] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] in
private theorem frameTest_frameLocalize (A : ChartCutoffs I M ⊤ M)
    (hA : ∀ x, (A.chart x).source ⊆ (trivializationAt F V x).baseSet) (x : M)
    (s : BundleTest I F V) :
    frameTest A hA x (frameLocalize A hA x s) = smulLeftCLM (A.cutoff x) s :=
  A.chartTestCLM_localize _ hA x s

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] in
/-- Extending the coordinates of the localization of `s` along the basis `Module.finBasis` of `F`
and summing gives back `ρₓ s`. -/
private theorem sum_frameTest_coord_frameLocalize (A : ChartCutoffs I M ⊤ M)
    (hA : ∀ x, (A.chart x).source ⊆ (trivializationAt F V x).baseSet) (x : M)
    (s : BundleTest I F V) :
    ∑ a, frameTest A hA x (postcompCLM (toSpanSingleton ℝ (Module.finBasis ℝ F a))
        (postcompCLM ((Module.finBasis ℝ F).coord a).toContinuousLinearMap
          (frameLocalize A hA x s))) =
      smulLeftCLM (A.cutoff x) s := by
  rw [← map_sum, sum_postcompCLM_toSpanSingleton_coord, frameTest_frameLocalize]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [FiniteDimensional ℝ E']
  [IsManifold J ∞ N] [T2Space N] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [ContMDiffVectorBundle ∞ F V I] [∀ y, IsTopologicalAddGroup (W y)]
  [∀ y, ContinuousSMul ℝ (W y)] [ContMDiffVectorBundle ∞ F' W J] in
/-- The product charts of chart cutoffs subordinate to trivializations of `V` and of `W` lie in
the base sets of the induced trivializations of `V ⊠ W`. -/
private theorem source_subset_baseSet_externalTensor (A : ChartCutoffs I M ⊤ M)
    (hA : ∀ x, (A.chart x).source ⊆ (trivializationAt F V x).baseSet) (A' : ChartCutoffs J N ⊤ N)
    (hA' : ∀ y, (A'.chart y).source ⊆ (trivializationAt F' W y).baseSet) (p : M × N) :
    ((A.prod A').chart p).source ⊆
      ((trivializationAt F V p.1).externalTensor ℝ (trivializationAt F' W p.2)).baseSet := by
  rw [ChartCutoffs.prod_chart, OpenPartialHomeomorph.prod_source,
    Bundle.Trivialization.baseSet_externalTensor]
  exact prod_mono (hA p.1) (hA' p.2)

/-- The extension of test functions on the target of the product chart `p` to bundle tests of
`V ⊠ W`, through the induced trivialization of `V ⊠ W`. -/
private def productTest (A : ChartCutoffs I M ⊤ M)
    (hA : ∀ x, (A.chart x).source ⊆ (trivializationAt F V x).baseSet) (A' : ChartCutoffs J N ⊤ N)
    (hA' : ∀ y, (A'.chart y).source ⊆ (trivializationAt F' W y).baseSet) (p : M × N) :
    𝓓(⟨((A.prod A').chart p).target, ((A.prod A').chart p).open_target⟩,
        ProjectiveTensor ℝ F F') →L[ℝ]
      BundleTest (I.prod J) (ProjectiveTensor ℝ F F') (ExternalTensor ℝ V W) :=
  ((trivializationAt F V p.1).externalTensor ℝ (trivializationAt F' W p.2)).chartTestCLM
    ((A.prod A').chart p) ((A.prod A').contMDiffOn_chart p)
    (source_subset_baseSet_externalTensor A hA A' hA' p)

/-- The localization of bundle tests of `V ⊠ W` to the target of the product chart `p`, read in
the induced trivialization of `V ⊠ W`. -/
private def productLocalize (A : ChartCutoffs I M ⊤ M)
    (hA : ∀ x, (A.chart x).source ⊆ (trivializationAt F V x).baseSet) (A' : ChartCutoffs J N ⊤ N)
    (hA' : ∀ y, (A'.chart y).source ⊆ (trivializationAt F' W y).baseSet) (p : M × N) :
    BundleTest (I.prod J) (ProjectiveTensor ℝ F F') (ExternalTensor ℝ V W) →L[ℝ]
      𝓓(⟨((A.prod A').chart p).target, ((A.prod A').chart p).open_target⟩,
        ProjectiveTensor ℝ F F') :=
  (A.prod A').localize
    (fun p ↦ (trivializationAt F V p.1).externalTensor ℝ (trivializationAt F' W p.2))
    (source_subset_baseSet_externalTensor A hA A' hA') p

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ y, IsTopologicalAddGroup (W y)] [∀ y, ContinuousSMul ℝ (W y)] in
private theorem productTest_productLocalize (A : ChartCutoffs I M ⊤ M)
    (hA : ∀ x, (A.chart x).source ⊆ (trivializationAt F V x).baseSet) (A' : ChartCutoffs J N ⊤ N)
    (hA' : ∀ y, (A'.chart y).source ⊆ (trivializationAt F' W y).baseSet) (p : M × N)
    (Φ : BundleTest (I.prod J) (ProjectiveTensor ℝ F F') (ExternalTensor ℝ V W)) :
    productTest A hA A' hA' p (productLocalize A hA A' hA' p Φ) =
      smulLeftCLM ((A.prod A').cutoff p) Φ :=
  (A.prod A').chartTestCLM_localize _ (source_subset_baseSet_externalTensor A hA A' hA') p Φ

/-! #### Coordinates in the tensor product of the model fibres -/

variable (F F') in
/-- The basis `(fₐ ⊗ g_b)` of the tensor product of the model fibres, for the bases
`Module.finBasis` of `F` and `F'`. -/
private def tensorBasis :
    Module.Basis (Fin (Module.finrank ℝ F) × Fin (Module.finrank ℝ F')) ℝ
      (ProjectiveTensor ℝ F F') :=
  ProjectiveTensor.basis (Module.finBasis ℝ F) (Module.finBasis ℝ F')

private theorem tensorBasis_apply (k : Fin (Module.finrank ℝ F) × Fin (Module.finrank ℝ F')) :
    tensorBasis F F' k =
      ProjectiveTensor.mk (Module.finBasis ℝ F k.1 ⊗ₜ[ℝ] Module.finBasis ℝ F' k.2) :=
  ProjectiveTensor.basis_apply _ _ k

/-- The coordinate functional of `tensorBasis` at `k`. -/
private def tensorCoord (k : Fin (Module.finrank ℝ F) × Fin (Module.finrank ℝ F')) :
    ProjectiveTensor ℝ F F' →L[ℝ] ℝ :=
  ((tensorBasis F F').coord k).toContinuousLinearMap

private theorem tensorCoord_tensorBasis
    (k k' : Fin (Module.finrank ℝ F) × Fin (Module.finrank ℝ F')) :
    tensorCoord k (tensorBasis F F' k') = if k' = k then 1 else 0 := by
  simp [tensorCoord, Finsupp.single_apply]

/-- Extending `(u, u') ↦ ψ u' φ u • (fₐ ⊗ g_b)` through the product chart `p` gives the external
tensor product of the extensions of `φ • fₐ` and `ψ • g_b`. -/
private theorem productTest_postcompCLM_prodSMulCLM (A : ChartCutoffs I M ⊤ M)
    (hA : ∀ x, (A.chart x).source ⊆ (trivializationAt F V x).baseSet) (A' : ChartCutoffs J N ⊤ N)
    (hA' : ∀ y, (A'.chart y).source ⊆ (trivializationAt F' W y).baseSet) (p : M × N)
    (k : Fin (Module.finrank ℝ F) × Fin (Module.finrank ℝ F'))
    (φ : 𝓓(⟨(A.chart p.1).target, (A.chart p.1).open_target⟩, ℝ))
    (ψ : 𝓓(⟨(A'.chart p.2).target, (A'.chart p.2).open_target⟩, ℝ)) :
    productTest A hA A' hA' p (postcompCLM (toSpanSingleton ℝ (tensorBasis F F' k))
        (prodSMulCLM ψ (A.prod_chart_target A' p).symm.subset φ)) =
      (frameTest A hA p.1
          (postcompCLM (toSpanSingleton ℝ (Module.finBasis ℝ F k.1)) φ)).externalTensor
        (frameTest A' hA' p.2
          (postcompCLM (toSpanSingleton ℝ (Module.finBasis ℝ F' k.2)) ψ)) := by
  rw [tensorBasis_apply]
  exact Bundle.Trivialization.chartTestCLM_externalTensor_prodSMulCLM _ _
    (A.contMDiffOn_chart p.1) (hA p.1) (A'.contMDiffOn_chart p.2) (hA' p.2) (A.prod_chart A' p)
    _ _ _ φ ψ _ _

/-- The localization of `s ⊠ t` to the product chart `p`, in the basis `tensorBasis`: its
coordinates are the tensor products of the coordinates of the localizations of `s` and `t`. -/
private theorem productLocalize_externalTensor (A : ChartCutoffs I M ⊤ M)
    (hA : ∀ x, (A.chart x).source ⊆ (trivializationAt F V x).baseSet) (A' : ChartCutoffs J N ⊤ N)
    (hA' : ∀ y, (A'.chart y).source ⊆ (trivializationAt F' W y).baseSet) (p : M × N)
    (s : BundleTest I F V) (t : BundleTest J F' W) :
    productLocalize A hA A' hA' p (s.externalTensor t) =
      ∑ k, postcompCLM (toSpanSingleton ℝ (tensorBasis F F' k))
        (prodSMulCLM (postcompCLM ((Module.finBasis ℝ F').coord k.2).toContinuousLinearMap
            (frameLocalize A' hA' p.2 t)) (A.prod_chart_target A' p).symm.subset
          (postcompCLM ((Module.finBasis ℝ F).coord k.1).toContinuousLinearMap
            (frameLocalize A hA p.1 s))) := by
  refine Bundle.Trivialization.chartTestCLM_injective _ ((A.prod A').chart p)
    ((A.prod A').contMDiffOn_chart p) (source_subset_baseSet_externalTensor A hA A' hA' p) ?_
  -- Both sides are chart extensions through the trivialization of `V ⊠ W` defining `productTest`.
  change productTest A hA A' hA' p _ = productTest A hA A' hA' p _
  rw [productTest_productLocalize, ChartCutoffs.prod_cutoff, smulLeftCLM_mulProd_externalTensor,
    map_sum]
  simp_rw [productTest_postcompCLM_prodSMulCLM, Fintype.sum_prod_type, ← externalTensorₗ_apply,
    ← map_sum (externalTensorₗ _), ← LinearMap.sum_apply, ← map_sum externalTensorₗ,
    sum_frameTest_coord_frameLocalize]

/-- The coordinate `k` of the localization of `s ⊠ t` to the product chart `p` is the tensor
product of the coordinates `k.1` of the localization of `s` and `k.2` of that of `t`. -/
private theorem postcompCLM_tensorCoord_productLocalize_externalTensor (A : ChartCutoffs I M ⊤ M)
    (hA : ∀ x, (A.chart x).source ⊆ (trivializationAt F V x).baseSet) (A' : ChartCutoffs J N ⊤ N)
    (hA' : ∀ y, (A'.chart y).source ⊆ (trivializationAt F' W y).baseSet) (p : M × N)
    (s : BundleTest I F V) (t : BundleTest J F' W)
    (k : Fin (Module.finrank ℝ F) × Fin (Module.finrank ℝ F')) :
    postcompCLM (tensorCoord k) (productLocalize A hA A' hA' p (s.externalTensor t)) =
      prodSMulCLM (postcompCLM ((Module.finBasis ℝ F').coord k.2).toContinuousLinearMap
          (frameLocalize A' hA' p.2 t)) (A.prod_chart_target A' p).symm.subset
        (postcompCLM ((Module.finBasis ℝ F).coord k.1).toContinuousLinearMap
          (frameLocalize A hA p.1 s)) := by
  rw [productLocalize_externalTensor, map_sum]
  simp_rw [postcompCLM_postcompCLM_toSpanSingleton, tensorCoord_tensorBasis, ite_smul, one_smul,
    zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-! #### The kernel of a bilinear map -/

section Existence

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- The Euclidean kernel of the scalar bilinear map `(φ, ψ) ↦ B (φ • fₐ) (ψ • g_b)` read through the
product chart `p`, for the basis vectors `fₐ` of `F` and `g_b` of `F'` indexed by `k = (a, b)`. -/
private def frameKernel (A : ChartCutoffs I M ⊤ M)
    (hA : ∀ x, (A.chart x).source ⊆ (trivializationAt F V x).baseSet) (A' : ChartCutoffs J N ⊤ N)
    (hA' : ∀ y, (A'.chart y).source ⊆ (trivializationAt F' W y).baseSet)
    (B : BundleTest I F V →ₗ[ℝ] BundleTest J F' W →ₗ[ℝ] G)
    (h₁ : ∀ t, Continuous fun s ↦ B s t) (h₂ : ∀ s, Continuous (B s)) (p : M × N)
    (k : Fin (Module.finrank ℝ F) × Fin (Module.finrank ℝ F')) :
    𝓓'(⟨((A.prod A').chart p).target, ((A.prod A').chart p).open_target⟩, G) :=
  (LinearMap.existsUnique_schwartzKernel_prodSMulCLM_of_continuous
    (B.compl₁₂ (frameTest A hA p.1 ∘L
        postcompCLM (toSpanSingleton ℝ (Module.finBasis ℝ F k.1))).toLinearMap
      (frameTest A' hA' p.2 ∘L
        postcompCLM (toSpanSingleton ℝ (Module.finBasis ℝ F' k.2))).toLinearMap)
    (fun _ ↦ (h₁ _).comp (ContinuousLinearMap.continuous _))
    (fun _ ↦ (h₂ _).comp (ContinuousLinearMap.continuous _))
    (A.prod_chart_target A' p)).exists.choose

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ y, IsTopologicalAddGroup (W y)] [∀ y, ContinuousSMul ℝ (W y)] in
private theorem frameKernel_prodSMulCLM (A : ChartCutoffs I M ⊤ M)
    (hA : ∀ x, (A.chart x).source ⊆ (trivializationAt F V x).baseSet) (A' : ChartCutoffs J N ⊤ N)
    (hA' : ∀ y, (A'.chart y).source ⊆ (trivializationAt F' W y).baseSet)
    (B : BundleTest I F V →ₗ[ℝ] BundleTest J F' W →ₗ[ℝ] G)
    (h₁ : ∀ t, Continuous fun s ↦ B s t) (h₂ : ∀ s, Continuous (B s)) (p : M × N)
    (k : Fin (Module.finrank ℝ F) × Fin (Module.finrank ℝ F'))
    (φ : 𝓓(⟨(A.chart p.1).target, (A.chart p.1).open_target⟩, ℝ))
    (ψ : 𝓓(⟨(A'.chart p.2).target, (A'.chart p.2).open_target⟩, ℝ)) :
    frameKernel A hA A' hA' B h₁ h₂ p k
        (prodSMulCLM ψ (A.prod_chart_target A' p).symm.subset φ) =
      B (frameTest A hA p.1 (postcompCLM (toSpanSingleton ℝ (Module.finBasis ℝ F k.1)) φ))
        (frameTest A' hA' p.2 (postcompCLM (toSpanSingleton ℝ (Module.finBasis ℝ F' k.2)) ψ)) :=
  (LinearMap.existsUnique_schwartzKernel_prodSMulCLM_of_continuous _
    (fun _ ↦ (h₁ _).comp (ContinuousLinearMap.continuous _))
    (fun _ ↦ (h₂ _).comp (ContinuousLinearMap.continuous _))
    (A.prod_chart_target A' p)).exists.choose_spec φ ψ

/-- The term of the product chart `p` in the kernel: the local kernels applied to the
coordinates of the localization of a test of `V ⊠ W`. -/
private def chartKernel (A : ChartCutoffs I M ⊤ M)
    (hA : ∀ x, (A.chart x).source ⊆ (trivializationAt F V x).baseSet) (A' : ChartCutoffs J N ⊤ N)
    (hA' : ∀ y, (A'.chart y).source ⊆ (trivializationAt F' W y).baseSet)
    (B : BundleTest I F V →ₗ[ℝ] BundleTest J F' W →ₗ[ℝ] G)
    (h₁ : ∀ t, Continuous fun s ↦ B s t) (h₂ : ∀ s, Continuous (B s)) (p : M × N) :
    BundleTest (I.prod J) (ProjectiveTensor ℝ F F') (ExternalTensor ℝ V W) →L[ℝ] G :=
  ∑ k, (ContinuousLinearMap.toUniformConvergenceCLM _ _ _).symm
      (frameKernel A hA A' hA' B h₁ h₂ p k) ∘L
    postcompCLM (tensorCoord k) ∘L productLocalize A hA A' hA' p

/-- On `s ⊠ t` the term of the product chart `p` is `B (ρ s) (σ t)`, for the cutoffs `ρ` and `σ` of
the two charts. -/
private theorem chartKernel_externalTensor (A : ChartCutoffs I M ⊤ M)
    (hA : ∀ x, (A.chart x).source ⊆ (trivializationAt F V x).baseSet) (A' : ChartCutoffs J N ⊤ N)
    (hA' : ∀ y, (A'.chart y).source ⊆ (trivializationAt F' W y).baseSet)
    (B : BundleTest I F V →ₗ[ℝ] BundleTest J F' W →ₗ[ℝ] G)
    (h₁ : ∀ t, Continuous fun s ↦ B s t) (h₂ : ∀ s, Continuous (B s)) (p : M × N)
    (s : BundleTest I F V) (t : BundleTest J F' W) :
    chartKernel A hA A' hA' B h₁ h₂ p (s.externalTensor t) =
      B (smulLeftCLM (A.cutoff p.1) s) (smulLeftCLM (A'.cutoff p.2) t) := by
  simp_rw [chartKernel, _root_.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toUniformConvergenceCLM_symm_apply,
    postcompCLM_tensorCoord_productLocalize_externalTensor, frameKernel_prodSMulCLM,
    Fintype.sum_prod_type, ← map_sum (B _), ← LinearMap.sum_apply, ← map_sum B,
    sum_frameTest_coord_frameLocalize]

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ y, IsTopologicalAddGroup (W y)] [∀ y, ContinuousSMul ℝ (W y)] in
/-- A product chart whose cutoff does not meet a compact set `L` contributes nothing to the kernel
on the tests supported in `L`. -/
private theorem chartKernel_eq_zero (A : ChartCutoffs I M ⊤ M)
    (hA : ∀ x, (A.chart x).source ⊆ (trivializationAt F V x).baseSet) (A' : ChartCutoffs J N ⊤ N)
    (hA' : ∀ y, (A'.chart y).source ⊆ (trivializationAt F' W y).baseSet)
    (B : BundleTest I F V →ₗ[ℝ] BundleTest J F' W →ₗ[ℝ] G)
    (h₁ : ∀ t, Continuous fun s ↦ B s t) (h₂ : ∀ s, Continuous (B s)) {L : Set (M × N)}
    {hL : IsCompact L} {p : M × N} (hp : p ∉ (A.prod A').meeting L hL)
    {Φ : BundleTest (I.prod J) (ProjectiveTensor ℝ F F') (ExternalTensor ℝ V W)}
    (hΦ : closure {z | Φ z ≠ 0} ⊆ L) : chartKernel A hA A' hA' B h₁ h₂ p Φ = 0 := by
  simp only [chartKernel, _root_.sum_apply, ContinuousLinearMap.comp_apply,
    productLocalize, (A.prod A').localize_eq_zero _ _ hp hΦ, map_zero, Finset.sum_const_zero]

/-- The kernel `Φ ↦ ∑ₚ κ_p Φ` of `B`, a locally finite sum over the product charts, as a
continuous linear map. -/
private def bundleKernel (A : ChartCutoffs I M ⊤ M)
    (hA : ∀ x, (A.chart x).source ⊆ (trivializationAt F V x).baseSet) (A' : ChartCutoffs J N ⊤ N)
    (hA' : ∀ y, (A'.chart y).source ⊆ (trivializationAt F' W y).baseSet)
    (B : BundleTest I F V →ₗ[ℝ] BundleTest J F' W →ₗ[ℝ] G)
    (h₁ : ∀ t, Continuous fun s ↦ B s t) (h₂ : ∀ s, Continuous (B s)) :
    BundleTest (I.prod J) (ProjectiveTensor ℝ F F') (ExternalTensor ℝ V W) →L[ℝ] G :=
  finsumCLM (A.prod A') (chartKernel A hA A' hA' B h₁ h₂) (chartKernel_eq_zero A hA A' hA' B h₁ h₂)

private theorem bundleKernel_externalTensor (A : ChartCutoffs I M ⊤ M)
    (hA : ∀ x, (A.chart x).source ⊆ (trivializationAt F V x).baseSet) (A' : ChartCutoffs J N ⊤ N)
    (hA' : ∀ y, (A'.chart y).source ⊆ (trivializationAt F' W y).baseSet)
    (B : BundleTest I F V →ₗ[ℝ] BundleTest J F' W →ₗ[ℝ] G)
    (h₁ : ∀ t, Continuous fun s ↦ B s t) (h₂ : ∀ s, Continuous (B s))
    (s : BundleTest I F V) (t : BundleTest J F' W) :
    bundleKernel A hA A' hA' B h₁ h₂ (s.externalTensor t) = B s t := by
  simp_rw [bundleKernel, finsumCLM_apply, chartKernel_externalTensor]
  exact finsum_smulLeftCLM_smulLeftCLM A A' B s t

end Existence

variable [I.Boundaryless] [SigmaCompactSpace M] [J.Boundaryless] [SigmaCompactSpace N]

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  [∀ y, AddCommGroup (W y)] [∀ y, Module ℝ (W y)] [∀ y, IsTopologicalAddGroup (W y)]
  [∀ y, ContinuousSMul ℝ (W y)] [VectorBundle ℝ F' W] [ContMDiffVectorBundle ∞ F' W J] in
/-- Chart cutoffs on `M` and on `N` whose charts lie in the base sets of the trivializations of `V`
and of `W` at their indices. -/
private theorem exists_chartCutoffs_baseSet :
    ∃ (A : ChartCutoffs I M ⊤ M) (A' : ChartCutoffs J N ⊤ N),
      (∀ x, (A.chart x).source ⊆ (trivializationAt F V x).baseSet) ∧
        ∀ y, (A'.chart y).source ⊆ (trivializationAt F' W y).baseSet := by
  obtain ⟨A, hA⟩ := ChartCutoffs.exists_source_subset_baseSet F I V (n := ⊤)
  obtain ⟨A', hA'⟩ := ChartCutoffs.exists_source_subset_baseSet F' J W (n := ⊤)
  exact ⟨A, A', hA, hA'⟩

/-- **Kernels with coefficients in vector bundles are determined by their values on external
tensor products.** Two continuous linear maps on the bundle tests of `V ⊠ W` over `M × N` agree
once they agree on every external tensor product `s ⊠ t` of a bundle test `s` of `V` and a bundle
test `t` of `W`. -/
theorem ext_externalTensor {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
    [T2Space G]
    {K₁ K₂ : BundleTest (I.prod J) (ProjectiveTensor ℝ F F') (ExternalTensor ℝ V W) →L[ℝ] G}
    (h : ∀ s t, K₁ (externalTensor s t) = K₂ (externalTensor s t)) : K₁ = K₂ := by
  obtain ⟨A, A', hA, hA'⟩ := exists_chartCutoffs_baseSet (I := I) (J := J) (F := F) (V := V)
    (F' := F') (W := W)
  -- On the extensions through each product chart of the test functions with values on a line
  -- `ℝ • (fₐ ⊗ g_b)`, the two maps agree, by the density of tensor products of test functions.
  have hC (p : M × N) (k : Fin (Module.finrank ℝ F) × Fin (Module.finrank ℝ F')) :
      K₁ ∘L productTest A hA A' hA' p ∘L postcompCLM (toSpanSingleton ℝ (tensorBasis F F' k)) =
        K₂ ∘L productTest A hA A' hA' p ∘L
          postcompCLM (toSpanSingleton ℝ (tensorBasis F F' k)) :=
    TestFunction.ext_prodSMulCLM (Ω := ⟨(A.chart p.1).target, (A.chart p.1).open_target⟩)
      (O := ⟨(A'.chart p.2).target, (A'.chart p.2).open_target⟩) (A.prod_chart_target A' p)
      fun ψ φ ↦ by
        simp only [ContinuousLinearMap.comp_apply, productTest_postcompCLM_prodSMulCLM, h]
  ext Φ
  have hΦ := (A.prod A').sum_chartTestCLM_localize
    (fun p ↦ (trivializationAt F V p.1).externalTensor ℝ (trivializationAt F' W p.2))
    (source_subset_baseSet_externalTensor A hA A' hA') Φ.isCompact_tsupport subset_rfl
  rw [← hΦ, map_sum, map_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  -- The chart extension and localization in `hΦ` are `productTest` and `productLocalize`.
  change K₁ (productTest A hA A' hA' p (productLocalize A hA A' hA' p Φ)) =
    K₂ (productTest A hA A' hA' p (productLocalize A hA A' hA' p Φ))
  rw [← sum_postcompCLM_toSpanSingleton_coord (tensorBasis F F') (productLocalize A hA A' hA' p Φ),
    map_sum, map_sum, map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ DFunLike.congr_fun (hC p k) _

/-- The kernel of a separately continuous bilinear map on bundle tests exists. -/
private theorem exists_bundleKernel {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G]
    (B : BundleTest I F V →ₗ[ℝ] BundleTest J F' W →ₗ[ℝ] G)
    (h₁ : ∀ t, Continuous fun s ↦ B s t) (h₂ : ∀ s, Continuous (B s)) :
    ∃ K : BundleTest (I.prod J) (ProjectiveTensor ℝ F F') (ExternalTensor ℝ V W) →L[ℝ] G,
      ∀ s t, K (s.externalTensor t) = B s t := by
  obtain ⟨A, A', hA, hA'⟩ := exists_chartCutoffs_baseSet (I := I) (J := J) (F := F) (V := V)
    (F' := F') (W := W)
  exact ⟨bundleKernel A hA A' hA' B h₁ h₂, bundleKernel_externalTensor A hA A' hA' B h₁ h₂⟩

end BundleKernel

end BundleTest

end TauCeti

open TauCeti TauCeti.BundleTest

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  [SigmaCompactSpace N]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- **The Schwartz kernel theorem on manifolds.** Let `B` be a real bilinear map on the scalar tests
on `M` and `N`, the compactly supported smooth real functions with their test topologies, with
values in a real Banach space `G`, which is continuous in each variable. Then there is a unique
continuous linear map `K` on the scalar tests on `M × N`, the kernel of `B`, with
`K (φ ⊗ ψ) = B φ ψ` for all scalar tests `φ` on `M` and `ψ` on `N`. -/
theorem LinearMap.existsUnique_schwartzKernel_tensor_of_continuous
    (B : BundleTest I ℝ (Bundle.Trivial M ℝ) →ₗ[ℝ] BundleTest J ℝ (Bundle.Trivial N ℝ) →ₗ[ℝ] G)
    (h₁ : ∀ ψ, Continuous fun φ ↦ B φ ψ) (h₂ : ∀ φ, Continuous (B φ)) :
    ∃! K : BundleTest (I.prod J) ℝ (Bundle.Trivial (M × N) ℝ) →L[ℝ] G,
      ∀ φ ψ, K (φ.tensor ψ) = B φ ψ := by
  obtain ⟨A⟩ := ChartCutoffs.nonempty I M ⊤
  obtain ⟨A'⟩ := ChartCutoffs.nonempty J N ⊤
  exact ⟨kernel A A' B h₁ h₂, kernel_tensor A A' B h₁ h₂, fun K hK ↦ ext_tensor fun φ ψ ↦
    (hK φ ψ).trans (kernel_tensor A A' B h₁ h₂ φ ψ).symm⟩

/-- **The Schwartz kernel theorem on manifolds, operator form.** Every continuous linear map `A`
from the scalar tests on `N` to the `G`-valued continuous linear functionals on the scalar tests on
`M`, with the topology of compact convergence, has a unique kernel: a continuous linear map `K` on
the scalar tests on `M × N` with `K (φ ⊗ ψ) = A ψ φ` for all scalar tests `φ` on `M` and `ψ` on
`N`. -/
theorem ContinuousLinearMap.existsUnique_schwartzKernel_tensor
    (A : BundleTest J ℝ (Bundle.Trivial N ℝ) →L[ℝ]
      (BundleTest I ℝ (Bundle.Trivial M ℝ) →L_c[ℝ] G)) :
    ∃! K : BundleTest (I.prod J) ℝ (Bundle.Trivial (M × N) ℝ) →L[ℝ] G,
      ∀ φ ψ, K (φ.tensor ψ) = A ψ φ :=
  LinearMap.existsUnique_schwartzKernel_tensor_of_continuous
    (LinearMap.mk₂ ℝ (fun φ ψ ↦ A ψ φ) (fun _ _ _ ↦ map_add _ _ _) (fun _ _ _ ↦ map_smul _ _ _)
      (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp))
    (fun ψ ↦ map_continuous (A ψ))
    (fun φ ↦ (ContinuousEvalConst.continuous_eval_const φ).comp A.continuous)

/-- **The Schwartz kernel theorem on manifolds, with coefficients in vector bundles.** Let `V → M`
and `W → N` be finite-rank smooth real vector bundles, and let `B` be a real bilinear map on the
bundle tests of `V` and of `W`, with values in a real Banach space `G`, which is continuous in each
variable. Then there is a unique continuous linear map `K` on the bundle tests of the external
tensor product `V ⊠ W` over `M × N`, the kernel of `B`, with `K (s ⊠ t) = B s t` for all bundle
tests `s` of `V` and `t` of `W`. -/
theorem LinearMap.existsUnique_schwartzKernel_externalTensor_of_continuous
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
    [TopologicalSpace (Bundle.TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
    [ContMDiffVectorBundle ∞ F V I]
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
    {W : N → Type*} [∀ y, AddCommGroup (W y)] [∀ y, Module ℝ (W y)] [∀ y, TopologicalSpace (W y)]
    [∀ y, IsTopologicalAddGroup (W y)] [∀ y, ContinuousSMul ℝ (W y)]
    [TopologicalSpace (Bundle.TotalSpace F' W)] [FiberBundle F' W] [VectorBundle ℝ F' W]
    [ContMDiffVectorBundle ∞ F' W J]
    (B : BundleTest I F V →ₗ[ℝ] BundleTest J F' W →ₗ[ℝ] G)
    (h₁ : ∀ t, Continuous fun s ↦ B s t) (h₂ : ∀ s, Continuous (B s)) :
    ∃! K : BundleTest (I.prod J) (ProjectiveTensor ℝ F F') (ExternalTensor ℝ V W) →L[ℝ] G,
      ∀ s t, K (s.externalTensor t) = B s t := by
  obtain ⟨K, hK⟩ := exists_bundleKernel B h₁ h₂
  exact ⟨K, hK, fun K' hK' ↦ ext_externalTensor fun s t ↦ (hK' s t).trans (hK s t).symm⟩

/-- **The Schwartz kernel theorem on manifolds with coefficients in vector bundles, operator
form.** Every continuous linear map `A` from the bundle tests of `W` over `N` to the `G`-valued
continuous linear functionals on the bundle tests of `V` over `M`, with the topology of compact
convergence, has a unique kernel: a continuous linear map `K` on the bundle tests of `V ⊠ W` over
`M × N` with `K (s ⊠ t) = A t s`. For `V` the bundle `Hom(E, |Λ|)` of `E`-dual densities on `M`
and `G = ℝ`, the functionals are the distributional sections of `E` (`TauCeti.BundleDistribution`),
so `A` is an operator from sections of `W` to distributional sections of `E`. -/
theorem ContinuousLinearMap.existsUnique_schwartzKernel_externalTensor
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
    [TopologicalSpace (Bundle.TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
    [ContMDiffVectorBundle ∞ F V I]
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
    {W : N → Type*} [∀ y, AddCommGroup (W y)] [∀ y, Module ℝ (W y)] [∀ y, TopologicalSpace (W y)]
    [∀ y, IsTopologicalAddGroup (W y)] [∀ y, ContinuousSMul ℝ (W y)]
    [TopologicalSpace (Bundle.TotalSpace F' W)] [FiberBundle F' W] [VectorBundle ℝ F' W]
    [ContMDiffVectorBundle ∞ F' W J]
    (A : BundleTest J F' W →L[ℝ] (BundleTest I F V →L_c[ℝ] G)) :
    ∃! K : BundleTest (I.prod J) (ProjectiveTensor ℝ F F') (ExternalTensor ℝ V W) →L[ℝ] G,
      ∀ s t, K (s.externalTensor t) = A t s :=
  LinearMap.existsUnique_schwartzKernel_externalTensor_of_continuous
    (LinearMap.mk₂ ℝ (fun s t ↦ A t s) (fun _ _ _ ↦ map_add _ _ _) (fun _ _ _ ↦ map_smul _ _ _)
      (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp))
    (fun t ↦ map_continuous (A t))
    (fun s ↦ (ContinuousEvalConst.continuous_eval_const s).comp A.continuous)
