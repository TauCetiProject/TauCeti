/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

These are the statements for the trivial line bundles: tests are real-valued functions, with no
density factors and no coefficient bundles.

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

## Main declarations

* `TauCeti.BundleTest.ext_tensor`: continuous linear maps on the scalar tests on `M × N` that agree
  on tensor products are equal.
* `LinearMap.existsUnique_schwartzKernel_tensor_of_continuous`: **the Schwartz kernel theorem** for
  separately continuous bilinear maps on scalar tests.
* `ContinuousLinearMap.existsUnique_schwartzKernel_tensor`: its operator form.

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

/-- Only the product charts whose cutoffs meet the support of a scalar test contribute to the
kernel. -/
private theorem finsum_localKernel (A : ChartCutoffs I M ⊤ M) (A' : ChartCutoffs J N ⊤ N)
    (B : BundleTest I ℝ (Bundle.Trivial M ℝ) →ₗ[ℝ] BundleTest J ℝ (Bundle.Trivial N ℝ) →ₗ[ℝ] G)
    (h₁ : ∀ ψ, Continuous fun φ ↦ B φ ψ) (h₂ : ∀ φ, Continuous (B φ)) {L : Set (M × N)}
    (hL : IsCompact L) {Φ : BundleTest (I.prod J) ℝ (Bundle.Trivial (M × N) ℝ)}
    (hΦ : closure {z | Φ z ≠ 0} ⊆ L) :
    ∑ᶠ p, localKernel A A' B h₁ h₂ p (scalarLocalize (A.prod A') p Φ) =
      ∑ p ∈ (A.prod A').meeting L hL,
        localKernel A A' B h₁ h₂ p (scalarLocalize (A.prod A') p Φ) := by
  refine finsum_eq_sum_of_support_subset _ fun p hp ↦ ?_
  by_contra h
  exact hp (by simp only [scalarLocalize_eq_zero (A.prod A') h hΦ, map_zero])

/-- The kernel `Φ ↦ ∑ₚ κ_p ((ρ ⊗ σ)_p Φ)` of `B`, a locally finite sum of the local kernels, as a
linear map. -/
private def kernelₗ (A : ChartCutoffs I M ⊤ M) (A' : ChartCutoffs J N ⊤ N)
    (B : BundleTest I ℝ (Bundle.Trivial M ℝ) →ₗ[ℝ] BundleTest J ℝ (Bundle.Trivial N ℝ) →ₗ[ℝ] G)
    (h₁ : ∀ ψ, Continuous fun φ ↦ B φ ψ) (h₂ : ∀ φ, Continuous (B φ)) :
    BundleTest (I.prod J) ℝ (Bundle.Trivial (M × N) ℝ) →ₗ[ℝ] G where
  toFun Φ := ∑ᶠ p, localKernel A A' B h₁ h₂ p (scalarLocalize (A.prod A') p Φ)
  map_add' Φ Ψ := by
    have hL := Φ.isCompact_tsupport.union Ψ.isCompact_tsupport
    rw [finsum_localKernel A A' B h₁ h₂ hL subset_union_left,
      finsum_localKernel A A' B h₁ h₂ hL subset_union_right,
      finsum_localKernel A A' B h₁ h₂ hL (Φ.tsupport_add_subset Ψ), ← Finset.sum_add_distrib]
    simp only [map_add]
  map_smul' a Φ := by
    rw [finsum_localKernel A A' B h₁ h₂ Φ.isCompact_tsupport (Φ.tsupport_smul_subset a),
      finsum_localKernel A A' B h₁ h₂ Φ.isCompact_tsupport subset_rfl, Finset.smul_sum]
    simp only [map_smul, RingHom.id_apply]

/-- The kernel of `B`, as a continuous linear map. -/
private def kernel (A : ChartCutoffs I M ⊤ M) (A' : ChartCutoffs J N ⊤ N)
    (B : BundleTest I ℝ (Bundle.Trivial M ℝ) →ₗ[ℝ] BundleTest J ℝ (Bundle.Trivial N ℝ) →ₗ[ℝ] G)
    (h₁ : ∀ ψ, Continuous fun φ ↦ B φ ψ) (h₂ : ∀ φ, Continuous (B φ)) :
    BundleTest (I.prod J) ℝ (Bundle.Trivial (M × N) ℝ) →L[ℝ] G where
  toLinearMap := kernelₗ A A' B h₁ h₂
  cont := by
    let := frameTopology (I := I.prod J) (n := ∞)
      (fun x : M × N ↦ trivializationAt ℝ (Bundle.Trivial (M × N) ℝ) x)
      (fun x ↦ ⟨_, (trivializationAt ℝ (Bundle.Trivial (M × N) ℝ) x).open_baseSet⟩)
      fun _ ↦ subset_rfl
    refine (BundleTest.continuous_iff_continuous_comp (kernelₗ A A' B h₁ h₂)).2 fun L ↦ ?_
    -- On the tests supported in `L` the kernel is a finite sum of continuous maps.
    refine (continuous_finsetSum ((A.prod A').meeting L L.isCompact) fun p _ ↦
      (map_continuous (localKernel A A' B h₁ h₂ p)).comp
        ((scalarLocalize (A.prod A') p).continuous.comp
        (BundleTest.continuous_ofSupportedIn L))).congr fun σ ↦ ?_
    exact (finsum_localKernel A A' B h₁ h₂ L.isCompact
      (BundleTest.tsupport_ofSupportedIn_subset L σ)).symm

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
  -- Only the charts whose cutoffs meet the supports of `φ` and of `ψ` contribute.
  refine (A.finsum_prod_eq_sum_meeting A' φ.isCompact_tsupport ψ.isCompact_tsupport
    (f := fun i j ↦ B (smulLeftCLM (A.cutoff i) φ) (smulLeftCLM (A'.cutoff j) ψ))
    (fun i j hi ↦ by rw [A.smulLeftCLM_eq_zero hi subset_rfl, map_zero, LinearMap.zero_apply])
    (fun i j hj ↦ by rw [A'.smulLeftCLM_eq_zero hj subset_rfl, map_zero])).trans ?_
  simp_rw [← map_sum (B _), ← LinearMap.sum_apply, ← map_sum B,
    A.sum_smulLeftCLM φ.isCompact_tsupport subset_rfl,
    A'.sum_smulLeftCLM ψ.isCompact_tsupport subset_rfl]

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
