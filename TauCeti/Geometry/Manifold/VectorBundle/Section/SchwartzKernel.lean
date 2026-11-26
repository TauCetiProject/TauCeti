/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution
import TauCeti.Analysis.Distribution.SchwartzKernel.Basic
import TauCeti.Analysis.Distribution.TestFunction.TensorDensity
import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization
import TauCeti.Geometry.Manifold.VectorBundle.Section.SmulLeft
import TauCeti.Geometry.Manifold.VectorBundle.Section.Trivial
import TauCeti.Geometry.Manifold.VectorBundle.Trivial
import TauCeti.Topology.Algebra.Support

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
functions have compact supports in the chart sources. The products `ρᵢ ⊗ σⱼ` form a partition of
unity on `M × N` subordinate to the product charts, and each scalar test `Φ` on `M × N` is the
finite sum of the pieces `(ρᵢ ⊗ σⱼ) Φ`, each the extension through a product chart of a test
function on its target, a product of open subsets of the two model spaces.

* **Uniqueness.** Read through a product chart, a kernel of `B` is a distribution on a product of
  open sets of the model spaces, determined by its values on tensor products of test functions
  (`TestFunction.ext_prodSMulCLM`). Summing over the pieces of `Φ` determines its value on `Φ`.
* **Existence.** Read through the two charts, `B` becomes a separately continuous bilinear map on
  test functions on open subsets of the model spaces, which has a Euclidean kernel `κᵢⱼ`
  (`LinearMap.existsUnique_schwartzKernel_prodSMulCLM_of_continuous`). The kernel of `B` is
  `K Φ = ∑ᵢⱼ κᵢⱼ ((ρᵢ ⊗ σⱼ) Φ)`, a locally finite sum. On `φ ⊗ ψ` the term `(i, j)` is
  `B (ρᵢ φ) (σⱼ ψ)`, and summing gives `B φ ψ`.

## Main declarations

* `TauCeti.BundleTest.tensor`: the tensor product `φ ⊗ ψ` of scalar tests.
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

namespace TauCeti.BundleTest

/-! ### Charts with subordinate cutoffs -/

section Cutoffs

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {P : Type*} [TopologicalSpace P] [ChartedSpace H P]

variable (I P) in
/-- Smooth charts of `P` with smooth inverses, indexed by `ι`, with smooth cutoffs supported in
compact subsets of their sources, summing to `1`, finitely many of which meet a compact set. -/
private structure ChartCutoffs (ι : Type*) where
  /-- The charts. -/
  chart : ι → OpenPartialHomeomorph P E
  contMDiffOn_chart : ∀ i, ContMDiffOn I 𝓘(ℝ, E) ∞ (chart i) (chart i).source
  contMDiffOn_chart_symm : ∀ i, ContMDiffOn 𝓘(ℝ, E) I ∞ (chart i).symm (chart i).target
  /-- The cutoffs. -/
  cutoff : ι → C^∞⟮I, P; ℝ⟯
  tsupport_subset : ∀ i, tsupport (cutoff i) ⊆ (chart i).source
  /-- Compact subsets of the chart targets containing the images of the supports of the cutoffs. -/
  box : ι → Compacts E
  box_subset : ∀ i, (box i : Set E) ⊆ (chart i).target
  mapsTo : ∀ i, MapsTo (chart i) (tsupport (cutoff i)) (box i)
  finite : ∀ K : Set P, IsCompact K → {i | (tsupport (cutoff i) ∩ K).Nonempty}.Finite
  sum_eq_one : ∀ z, ∑ᶠ i, cutoff i z = 1

namespace ChartCutoffs

variable {ι : Type*}

/-- The indices of the cutoffs meeting a compact set. -/
private def meeting (A : ChartCutoffs I P ι) (K : Set P) (hK : IsCompact K) : Finset ι :=
  (A.finite K hK).toFinset

private theorem mem_meeting (A : ChartCutoffs I P ι) {K : Set P} {hK : IsCompact K} {i : ι} :
    i ∈ A.meeting K hK ↔ (tsupport (A.cutoff i) ∩ K).Nonempty := by
  simp [meeting]

private theorem cutoff_eq_zero (A : ChartCutoffs I P ι) {K : Set P} {hK : IsCompact K} {i : ι}
    (hi : i ∉ A.meeting K hK) {z : P} (hz : z ∈ K) : A.cutoff i z = 0 := by
  by_contra h
  exact hi (A.mem_meeting.2 ⟨z, subset_tsupport _ h, hz⟩)

/-- On a compact set `K` the cutoffs meeting `K` sum to `1`. -/
private theorem sum_meeting_eq_one (A : ChartCutoffs I P ι) {K : Set P} (hK : IsCompact K) {z : P}
    (hz : z ∈ K) : ∑ i ∈ A.meeting K hK, A.cutoff i z = 1 := by
  rw [← A.sum_eq_one z, finsum_eq_sum_of_support_subset]
  intro i hi
  by_contra h
  exact hi (A.cutoff_eq_zero h hz)

end ChartCutoffs

variable [IsManifold I ∞ P] [I.Boundaryless] [FiniteDimensional ℝ E] [T2Space P]
  [SigmaCompactSpace P]

variable (I P) in
/-- A smooth partition of unity subordinate to charts gives chart cutoffs. -/
private theorem nonempty_chartCutoffs : Nonempty (ChartCutoffs I P P) := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace P := ChartedSpace.locallyCompactSpace H P
  choose c hc hcs _ hxc using fun x : P ↦
    TauCeti.exists_chart_source_subset_baseSet (I := I) (F := ℝ) (Bundle.Trivial P ℝ) (n := ∞) x
  -- Shrink each chart source to an open neighbourhood with compact closure inside it.
  choose W hWo hxW hWs hWc using fun x : P ↦ exists_open_between_and_isCompact_closure
    isCompact_singleton (c x).open_source (singleton_subset_iff.2 (hxc x))
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ W hWo
    fun y _ ↦ mem_iUnion.2 ⟨y, hxW y rfl⟩
  exact ⟨{
    chart := c
    contMDiffOn_chart := hc
    contMDiffOn_chart_symm := hcs
    cutoff := fun x ↦ ⟨ρ x, (ρ x).contMDiff.of_le (WithTop.coe_le_coe.2 le_top)⟩
    tsupport_subset := fun x ↦ (hρ x).trans (subset_closure.trans (hWs x))
    box := fun x ↦ ⟨c x '' closure (W x),
      (hWc x).image_of_continuousOn ((c x).continuousOn.mono (hWs x))⟩
    box_subset := fun x ↦ image_subset_iff.2 fun y hy ↦ (c x).map_source (hWs x hy)
    mapsTo := fun x y hy ↦ mem_image_of_mem _ (subset_closure (hρ x hy))
    finite := fun K hK ↦ ρ.locallyFinite.closure.finite_nonempty_inter_compact hK
    sum_eq_one := fun z ↦ ρ.sum_eq_one (mem_univ z) }⟩

end Cutoffs

/-! ### Products of charts and cutoffs -/

section Prod

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- The smooth function `(x, y) ↦ f x * g y` on `M × N`. -/
private def mulProd (f : C^∞⟮I, M; ℝ⟯) (g : C^∞⟮J, N; ℝ⟯) : C^∞⟮I.prod J, M × N; ℝ⟯ :=
  ⟨fun z ↦ f z.1 * g z.2, (f.contMDiff.comp contMDiff_fst).mul (g.contMDiff.comp contMDiff_snd)⟩

private theorem mulProd_apply (f : C^∞⟮I, M; ℝ⟯) (g : C^∞⟮J, N; ℝ⟯) (z : M × N) :
    mulProd f g z = f z.1 * g z.2 :=
  rfl

private theorem tsupport_mulProd_subset (f : C^∞⟮I, M; ℝ⟯) (g : C^∞⟮J, N; ℝ⟯) :
    tsupport (mulProd f g) ⊆ tsupport f ×ˢ tsupport g := by
  have h : (mulProd f g : M × N → ℝ) = fun z ↦ g z.2 • f z.1 :=
    funext fun z ↦ mul_comm (f z.1) (g z.2)
  rw [h]
  exact tsupport_snd_smul_fst_subset _ _

/-- A product of smooth charts is smooth. -/
private theorem contMDiffOn_prod (c : OpenPartialHomeomorph M E) (d : OpenPartialHomeomorph N E')
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hd : ContMDiffOn J 𝓘(ℝ, E') ∞ d d.source) :
    ContMDiffOn (I.prod J) 𝓘(ℝ, E × E') ∞ (c.prod d) (c.prod d).source :=
  (hc.comp contMDiff_fst.contMDiffOn fun _ (hz : _ ∈ c.source ×ˢ d.source) ↦ hz.1).prodMk_space
    (hd.comp contMDiff_snd.contMDiffOn fun _ (hz : _ ∈ c.source ×ˢ d.source) ↦ hz.2)

/-- The inverse of a product of charts with smooth inverses is smooth. -/
private theorem contMDiffOn_prod_symm (c : OpenPartialHomeomorph M E)
    (d : OpenPartialHomeomorph N E') (hc : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hd : ContMDiffOn 𝓘(ℝ, E') J ∞ d.symm d.target) :
    ContMDiffOn 𝓘(ℝ, E × E') (I.prod J) ∞ (c.prod d).symm (c.prod d).target :=
  (hc.comp contDiff_fst.contMDiff.contMDiffOn
      fun _ (hz : _ ∈ c.target ×ˢ d.target) ↦ hz.1).prodMk
    (hd.comp contDiff_snd.contMDiff.contMDiffOn fun _ (hz : _ ∈ c.target ×ˢ d.target) ↦ hz.2)

namespace ChartCutoffs

variable {ι κ : Type*}

/-- The product charts and product cutoffs of chart cutoffs on `M` and on `N`. -/
private def prod (A : ChartCutoffs I M ι) (B : ChartCutoffs J N κ) :
    ChartCutoffs (I.prod J) (M × N) (ι × κ) where
  chart p := (A.chart p.1).prod (B.chart p.2)
  contMDiffOn_chart p := contMDiffOn_prod _ _ (A.contMDiffOn_chart p.1) (B.contMDiffOn_chart p.2)
  contMDiffOn_chart_symm p :=
    contMDiffOn_prod_symm _ _ (A.contMDiffOn_chart_symm p.1) (B.contMDiffOn_chart_symm p.2)
  cutoff p := mulProd (A.cutoff p.1) (B.cutoff p.2)
  tsupport_subset p := (tsupport_mulProd_subset _ _).trans
    (prod_mono (A.tsupport_subset p.1) (B.tsupport_subset p.2))
  box p := A.box p.1 ×ˢ B.box p.2
  box_subset p := prod_mono (A.box_subset p.1) (B.box_subset p.2)
  mapsTo p := ((A.mapsTo p.1).prodMap (B.mapsTo p.2)).mono_left (tsupport_mulProd_subset _ _)
  finite K hK := ((A.finite _ (hK.image continuous_fst)).prod
    (B.finite _ (hK.image continuous_snd))).subset fun p ⟨z, hz, hzK⟩ ↦
      ⟨⟨z.1, (tsupport_mulProd_subset _ _ hz).1, mem_image_of_mem _ hzK⟩,
        ⟨z.2, (tsupport_mulProd_subset _ _ hz).2, mem_image_of_mem _ hzK⟩⟩
  sum_eq_one z := by
    rw [finsum_eq_sum_of_support_subset (s := A.meeting {z.1} isCompact_singleton ×ˢ
      B.meeting {z.2} isCompact_singleton), Finset.sum_product]
    · simp_rw [mulProd_apply, ← Finset.mul_sum, ← Finset.sum_mul]
      rw [A.sum_meeting_eq_one _ rfl, B.sum_meeting_eq_one _ rfl, one_mul]
    · intro p hp
      rw [Finset.coe_product, mem_prod, Finset.mem_coe, Finset.mem_coe, A.mem_meeting,
        B.mem_meeting]
      rw [mem_support, mulProd_apply] at hp
      exact ⟨⟨z.1, subset_tsupport _ (left_ne_zero_of_mul hp), rfl⟩,
        ⟨z.2, subset_tsupport _ (right_ne_zero_of_mul hp), rfl⟩⟩

/-- The target of a product chart is the product of the targets. -/
private theorem coe_prod_chart_target (A : ChartCutoffs I M ι) (B : ChartCutoffs J N κ)
    (p : ι × κ) :
    ((⟨((A.prod B).chart p).target, ((A.prod B).chart p).open_target⟩ : Opens (E × E')) :
      Set (E × E')) =
      ((⟨(A.chart p.1).target, (A.chart p.1).open_target⟩ : Opens E) : Set E) ×ˢ
        ((⟨(B.chart p.2).target, (B.chart p.2).open_target⟩ : Opens E') : Set E') :=
  OpenPartialHomeomorph.prod_target (A.chart p.1) (B.chart p.2)

end ChartCutoffs

end Prod

/-! ### Scalar tests in charts -/

section Scalar

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {P : Type*} [TopologicalSpace P] [ChartedSpace H P]

/-- The closed support of a scalar test, a compact set. -/
private def supp (Φ : BundleTest I ℝ (Bundle.Trivial P ℝ)) : Set P :=
  ((ofCompactlySupported I ℝ (Bundle.Trivial P ℝ)).symm Φ).val.tsupport

private theorem isCompact_supp (Φ : BundleTest I ℝ (Bundle.Trivial P ℝ)) : IsCompact (supp Φ) :=
  mem_compactlySupported.1 ((ofCompactlySupported I ℝ (Bundle.Trivial P ℝ)).symm Φ).property

private theorem apply_eq_zero_of_notMem_supp (Φ : BundleTest I ℝ (Bundle.Trivial P ℝ)) {z : P}
    (hz : z ∉ supp Φ) : Φ z = 0 := by
  by_contra h
  exact hz (by rw [supp, tsupport_def]; exact subset_closure h)

private theorem supp_add_subset (Φ Ψ : BundleTest I ℝ (Bundle.Trivial P ℝ)) :
    supp (Φ + Ψ) ⊆ supp Φ ∪ supp Ψ :=
  ContMDiffSection.tsupport_add_subset _ _

private theorem supp_smul_subset (a : ℝ) (Φ : BundleTest I ℝ (Bundle.Trivial P ℝ)) :
    supp (a • Φ) ⊆ supp Φ :=
  ContMDiffSection.tsupport_smul_subset _ _

private theorem supp_ofSupportedIn_subset (K : Compacts P)
    (σ : supportedIn I ℝ ∞ (Bundle.Trivial P ℝ) K) :
    supp (ofCompactlySupported I ℝ (Bundle.Trivial P ℝ) (ofSupportedIn K σ)) ⊆ K := by
  simpa [supp] using mem_supportedIn.1 σ.property

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

namespace ChartCutoffs

variable {ι : Type*}

/-- The localization `Φ ↦ (ρᵢ Φ) ∘ cᵢ⁻¹` of scalar tests to the target of the chart `cᵢ`, for the
cutoff `ρᵢ`. -/
private def localize (A : ChartCutoffs I P ι) (i : ι) :
    BundleTest I ℝ (Bundle.Trivial P ℝ) →L[ℝ] 𝓓(⟨(A.chart i).target, (A.chart i).open_target⟩, ℝ)
    where
  toLinearMap := (TestFunction.ofSupportedInCLM ℝ (A.box_subset i)).toLinearMap ∘ₗ
    (Bundle.Trivial.trivialization P ℝ).chartLocalization (A.chart i)
      (A.contMDiffOn_chart_symm i) (subset_baseSet_trivial _) (A.cutoff i) (A.box i)
      (A.box_subset i) (A.mapsTo i) ∘ₗ (compactlySupported I ℝ ∞ (Bundle.Trivial P ℝ)).subtype ∘ₗ
    (ofCompactlySupported I ℝ (Bundle.Trivial P ℝ)).symm.toLinearMap
  cont := by
    let := frameTopology (I := I) (n := ∞)
      (fun x : P ↦ trivializationAt ℝ (Bundle.Trivial P ℝ) x)
      (fun x ↦ ⟨_, (trivializationAt ℝ (Bundle.Trivial P ℝ) x).open_baseSet⟩) fun _ ↦ subset_rfl
    exact (TestFunction.ofSupportedInCLM ℝ (A.box_subset i)).continuous.comp
      ((Bundle.Trivialization.continuous_chartLocalization _ _ _ _ _ _ _ _ _ _ _
        fun x ↦ ⟨x, mem_univ x⟩).comp
      (continuous_val_compactlySupportedTopology (I := I) (n := ∞) _ _ _))

/-- Extending the localization back through the chart gives `ρᵢ Φ`. -/
private theorem chartTest_localize (A : ChartCutoffs I P ι) (i : ι)
    (Φ : BundleTest I ℝ (Bundle.Trivial P ℝ)) :
    chartTest (A.chart i) (A.contMDiffOn_chart i) (A.localize i Φ) =
      smulLeftCLM (A.cutoff i) Φ := by
  refine BundleTest.ext fun z ↦ ?_
  have h := (Bundle.Trivial.trivialization P ℝ).chartTestSection_chartLocalization (A.chart i)
    (A.contMDiffOn_chart_symm i) (subset_baseSet_trivial _) (A.cutoff i) (A.box i)
    (A.box_subset i) (A.mapsTo i) (A.contMDiffOn_chart i) (A.tsupport_subset i)
    ((ofCompactlySupported I ℝ (Bundle.Trivial P ℝ)).symm Φ).val
  simpa [chartTest, localize] using congrArg (fun s ↦ s z) h

omit [T2Space P] [LocallyCompactSpace E] in
/-- A cutoff not meeting a compact set `K` kills every scalar test supported in `K`. -/
private theorem smulLeftCLM_eq_zero (A : ChartCutoffs I P ι) {K : Set P} {hK : IsCompact K}
    {i : ι} (hi : i ∉ A.meeting K hK) {Φ : BundleTest I ℝ (Bundle.Trivial P ℝ)}
    (hΦ : supp Φ ⊆ K) : smulLeftCLM (A.cutoff i) Φ = 0 := by
  refine BundleTest.ext fun z ↦ ?_
  rw [smulLeftCLM_apply, zero_apply]
  by_cases hz : z ∈ supp Φ
  · rw [A.cutoff_eq_zero hi (hΦ hz), zero_smul]
  · rw [apply_eq_zero_of_notMem_supp Φ hz, smul_zero]

omit [T2Space P] [LocallyCompactSpace E] in
/-- The cutoffs meeting a compact set `K` decompose every scalar test supported in `K`. -/
private theorem sum_smulLeftCLM (A : ChartCutoffs I P ι) {K : Set P} (hK : IsCompact K)
    {Φ : BundleTest I ℝ (Bundle.Trivial P ℝ)} (hΦ : supp Φ ⊆ K) :
    ∑ i ∈ A.meeting K hK, smulLeftCLM (A.cutoff i) Φ = Φ := by
  refine BundleTest.ext fun z ↦ ?_
  rw [sum_apply]
  simp_rw [smulLeftCLM_apply, ← Finset.sum_smul]
  by_cases hz : z ∈ K
  · rw [A.sum_meeting_eq_one hK hz, one_smul]
  · rw [apply_eq_zero_of_notMem_supp Φ fun h ↦ hz (hΦ h), smul_zero]

/-- A localization to a chart whose cutoff does not meet a compact set `K` vanishes on the scalar
tests supported in `K`. -/
private theorem localize_eq_zero (A : ChartCutoffs I P ι) {K : Set P} {hK : IsCompact K} {i : ι}
    (hi : i ∉ A.meeting K hK) {Φ : BundleTest I ℝ (Bundle.Trivial P ℝ)} (hΦ : supp Φ ⊆ K) :
    A.localize i Φ = 0 :=
  chartTest_injective _ (A.contMDiffOn_chart i) <| by
    rw [A.chartTest_localize, A.smulLeftCLM_eq_zero hi hΦ, map_zero]

/-- A scalar test supported in a compact set `K` is the sum of the chart extensions of its
localizations to the charts whose cutoffs meet `K`. -/
private theorem sum_chartTest_localize (A : ChartCutoffs I P ι) {K : Set P} (hK : IsCompact K)
    {Φ : BundleTest I ℝ (Bundle.Trivial P ℝ)} (hΦ : supp Φ ⊆ K) :
    ∑ i ∈ A.meeting K hK, chartTest (A.chart i) (A.contMDiffOn_chart i) (A.localize i Φ) = Φ := by
  simp_rw [A.chartTest_localize]
  exact A.sum_smulLeftCLM hK hΦ

end ChartCutoffs

end Scalar

/-! ### Tensor products of scalar tests -/

section Tensor

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- The section `(x, y) ↦ φ x * ψ y` of the trivial line over `M × N`. -/
private def tensorSection (φ : BundleTest I ℝ (Bundle.Trivial M ℝ))
    (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) : Cₛ^∞⟮I.prod J; ℝ, Bundle.Trivial (M × N) ℝ⟯ :=
  trivialEquiv.symm (mulProd (trivialEquiv ((ofCompactlySupported I ℝ _).symm φ).val)
    (trivialEquiv ((ofCompactlySupported J ℝ _).symm ψ).val))

private theorem tensorSection_apply (φ : BundleTest I ℝ (Bundle.Trivial M ℝ))
    (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) (z : M × N) :
    (tensorSection φ ψ z : ℝ) = φ z.1 * ψ z.2 := by
  simp [tensorSection, mulProd_apply]

private theorem tsupport_tensorSection_subset (φ : BundleTest I ℝ (Bundle.Trivial M ℝ))
    (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) :
    (tensorSection φ ψ).tsupport ⊆ supp φ ×ˢ supp ψ := by
  rw [tensorSection, supp, supp, tsupport_def, tsupport_def, tsupport_def]
  simpa [_root_.tsupport, Function.support] using
    tsupport_mulProd_subset (trivialEquiv ((ofCompactlySupported I ℝ _).symm φ).val)
      (trivialEquiv ((ofCompactlySupported J ℝ _).symm ψ).val)

/-- The **tensor product** `(φ ⊗ ψ)(x, y) = φ x * ψ y` of a scalar test `φ` on `M` and a scalar
test `ψ` on `N`, a scalar test on `M × N`. -/
def tensor (φ : BundleTest I ℝ (Bundle.Trivial M ℝ)) (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) :
    BundleTest (I.prod J) ℝ (Bundle.Trivial (M × N) ℝ) :=
  ofCompactlySupported _ _ _ ⟨tensorSection φ ψ, mem_compactlySupported.2 <|
    ((isCompact_supp φ).prod (isCompact_supp ψ)).of_isClosed_subset
      (ContMDiffSection.isClosed_tsupport _) (tsupport_tensorSection_subset φ ψ)⟩

/-- The tensor product of scalar tests is `(φ ⊗ ψ)(x, y) = φ x * ψ y`. -/
@[simp]
theorem tensor_apply (φ : BundleTest I ℝ (Bundle.Trivial M ℝ))
    (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) (z : M × N) :
    (φ.tensor ψ z : ℝ) = φ z.1 * ψ z.2 :=
  tensorSection_apply φ ψ z

/-- The tensor product of scalar tests is additive in its first factor. -/
theorem add_tensor (φ φ' : BundleTest I ℝ (Bundle.Trivial M ℝ))
    (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) : (φ + φ').tensor ψ = φ.tensor ψ + φ'.tensor ψ :=
  BundleTest.ext fun z ↦ by simp only [add_apply, tensor_apply]; exact add_mul _ _ _

/-- The tensor product of scalar tests is additive in its second factor. -/
theorem tensor_add (φ : BundleTest I ℝ (Bundle.Trivial M ℝ))
    (ψ ψ' : BundleTest J ℝ (Bundle.Trivial N ℝ)) : φ.tensor (ψ + ψ') = φ.tensor ψ + φ.tensor ψ' :=
  BundleTest.ext fun z ↦ by simp only [add_apply, tensor_apply]; exact mul_add _ _ _

/-- The tensor product of scalar tests is homogeneous in its first factor. -/
theorem smul_tensor (a : ℝ) (φ : BundleTest I ℝ (Bundle.Trivial M ℝ))
    (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) : (a • φ).tensor ψ = a • φ.tensor ψ :=
  BundleTest.ext fun z ↦ by simp only [smul_apply, tensor_apply]; exact mul_assoc _ _ _

/-- The tensor product of scalar tests is homogeneous in its second factor. -/
theorem tensor_smul (a : ℝ) (φ : BundleTest I ℝ (Bundle.Trivial M ℝ))
    (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) : φ.tensor (a • ψ) = a • φ.tensor ψ :=
  BundleTest.ext fun z ↦ by simp only [smul_apply, tensor_apply]; exact mul_left_comm _ _ _

variable [IsManifold I ∞ M] [IsManifold J ∞ N]

private theorem smulLeftCLM_mulProd_tensor (f : C^∞⟮I, M; ℝ⟯) (g : C^∞⟮J, N; ℝ⟯)
    (φ : BundleTest I ℝ (Bundle.Trivial M ℝ)) (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) :
    smulLeftCLM (mulProd f g) (φ.tensor ψ) = (smulLeftCLM f φ).tensor (smulLeftCLM g ψ) := by
  refine BundleTest.ext fun z ↦ ?_
  simp only [smulLeftCLM_apply, tensor_apply, mulProd_apply, smul_eq_mul]
  ring

variable [T2Space M] [LocallyCompactSpace E] [T2Space N] [LocallyCompactSpace E']

/-- Extending a tensor product of test functions through a product of charts gives the tensor
product of their extensions. -/
private theorem chartTest_prod_prodSMulCLM (c : OpenPartialHomeomorph M E)
    (d : OpenPartialHomeomorph N E') (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source)
    (hd : ContMDiffOn J 𝓘(ℝ, E') ∞ d d.source) (φ : 𝓓(⟨c.target, c.open_target⟩, ℝ))
    (ψ : 𝓓(⟨d.target, d.open_target⟩, ℝ)) :
    chartTest (c.prod d) (contMDiffOn_prod c d hc hd)
        (TestFunction.prodSMulCLM ψ (OpenPartialHomeomorph.prod_target c d).symm.subset φ) =
      (chartTest c hc φ).tensor (chartTest d hd ψ) := by
  refine BundleTest.ext fun z ↦ ?_
  by_cases hz : z ∈ (c.prod d).source
  · rw [OpenPartialHomeomorph.prod_source] at hz
    rw [chartTest_apply_of_mem _ _ _ (by simpa using hz), tensor_apply,
      chartTest_apply_of_mem _ _ _ hz.1, chartTest_apply_of_mem _ _ _ hz.2,
      TestFunction.prodSMulCLM_apply, smul_eq_mul, mul_comm]
    rfl
  · rw [chartTest_apply_of_notMem _ _ _ hz]
    rw [OpenPartialHomeomorph.prod_source, mem_prod, not_and_or] at hz
    rcases hz with hz | hz
    · rw [tensor_apply, chartTest_apply_of_notMem _ _ _ hz, zero_mul]
    · rw [tensor_apply, chartTest_apply_of_notMem _ _ _ hz, mul_zero]

/-- The localization of a tensor product to a product chart is the tensor product of the
localizations. -/
private theorem ChartCutoffs.localize_prod_tensor {ι κ : Type*} (A : ChartCutoffs I M ι)
    (B : ChartCutoffs J N κ) (p : ι × κ) (φ : BundleTest I ℝ (Bundle.Trivial M ℝ))
    (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) :
    (A.prod B).localize p (φ.tensor ψ) = TestFunction.prodSMulCLM (B.localize p.2 ψ)
      (A.coe_prod_chart_target B p).symm.subset (A.localize p.1 φ) := by
  refine chartTest_injective _ ((A.prod B).contMDiffOn_chart p) ?_
  rw [ChartCutoffs.chartTest_localize]
  refine (smulLeftCLM_mulProd_tensor _ _ φ ψ).trans ?_
  rw [← A.chartTest_localize, ← B.chartTest_localize]
  exact (chartTest_prod_prodSMulCLM _ _ _ _ _ _).symm

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
private def localKernel (A : ChartCutoffs I M M) (A' : ChartCutoffs J N N)
    (B : BundleTest I ℝ (Bundle.Trivial M ℝ) →ₗ[ℝ] BundleTest J ℝ (Bundle.Trivial N ℝ) →ₗ[ℝ] G)
    (h₁ : ∀ ψ, Continuous fun φ ↦ B φ ψ) (h₂ : ∀ φ, Continuous (B φ)) (p : M × N) :
    𝓓'(⟨((A.prod A').chart p).target, ((A.prod A').chart p).open_target⟩, G) :=
  (LinearMap.existsUnique_schwartzKernel_prodSMulCLM_of_continuous
    (B.compl₁₂ (chartTest (A.chart p.1) (A.contMDiffOn_chart p.1)).toLinearMap
      (chartTest (A'.chart p.2) (A'.contMDiffOn_chart p.2)).toLinearMap)
    (fun _ ↦ (h₁ _).comp (chartTest _ _).continuous)
    (fun _ ↦ (h₂ _).comp (chartTest _ _).continuous)
    (A.coe_prod_chart_target A' p)).exists.choose

/-- On `φ' ⊗ ψ'` the local kernel of `B` at the product chart `c × d` takes the value of `B` on the
extensions of `φ'` and `ψ'` through `c` and `d`. -/
private theorem localKernel_prodSMulCLM (A : ChartCutoffs I M M) (A' : ChartCutoffs J N N)
    (B : BundleTest I ℝ (Bundle.Trivial M ℝ) →ₗ[ℝ] BundleTest J ℝ (Bundle.Trivial N ℝ) →ₗ[ℝ] G)
    (h₁ : ∀ ψ, Continuous fun φ ↦ B φ ψ) (h₂ : ∀ φ, Continuous (B φ)) (p : M × N)
    (φ : 𝓓(⟨(A.chart p.1).target, (A.chart p.1).open_target⟩, ℝ))
    (ψ : 𝓓(⟨(A'.chart p.2).target, (A'.chart p.2).open_target⟩, ℝ)) :
    localKernel A A' B h₁ h₂ p
        (TestFunction.prodSMulCLM ψ (A.coe_prod_chart_target A' p).symm.subset φ) =
      B (chartTest (A.chart p.1) (A.contMDiffOn_chart p.1) φ)
        (chartTest (A'.chart p.2) (A'.contMDiffOn_chart p.2) ψ) :=
  (LinearMap.existsUnique_schwartzKernel_prodSMulCLM_of_continuous _
    (fun _ ↦ (h₁ _).comp (chartTest _ _).continuous)
    (fun _ ↦ (h₂ _).comp (chartTest _ _).continuous)
    (A.coe_prod_chart_target A' p)).exists.choose_spec φ ψ

/-- Only the product charts whose cutoffs meet the support of a scalar test contribute to the
kernel. -/
private theorem finsum_localKernel (A : ChartCutoffs I M M) (A' : ChartCutoffs J N N)
    (B : BundleTest I ℝ (Bundle.Trivial M ℝ) →ₗ[ℝ] BundleTest J ℝ (Bundle.Trivial N ℝ) →ₗ[ℝ] G)
    (h₁ : ∀ ψ, Continuous fun φ ↦ B φ ψ) (h₂ : ∀ φ, Continuous (B φ)) {L : Set (M × N)}
    (hL : IsCompact L) {Φ : BundleTest (I.prod J) ℝ (Bundle.Trivial (M × N) ℝ)}
    (hΦ : supp Φ ⊆ L) :
    ∑ᶠ p, localKernel A A' B h₁ h₂ p ((A.prod A').localize p Φ) =
      ∑ p ∈ (A.prod A').meeting L hL, localKernel A A' B h₁ h₂ p ((A.prod A').localize p Φ) := by
  refine finsum_eq_sum_of_support_subset _ fun p hp ↦ ?_
  by_contra h
  exact hp (by simp only [(A.prod A').localize_eq_zero h hΦ, map_zero])

/-- The kernel `Φ ↦ ∑ₚ κ_p ((ρ ⊗ σ)_p Φ)` of `B`, a locally finite sum of the local kernels, as a
linear map. -/
private def kernelₗ (A : ChartCutoffs I M M) (A' : ChartCutoffs J N N)
    (B : BundleTest I ℝ (Bundle.Trivial M ℝ) →ₗ[ℝ] BundleTest J ℝ (Bundle.Trivial N ℝ) →ₗ[ℝ] G)
    (h₁ : ∀ ψ, Continuous fun φ ↦ B φ ψ) (h₂ : ∀ φ, Continuous (B φ)) :
    BundleTest (I.prod J) ℝ (Bundle.Trivial (M × N) ℝ) →ₗ[ℝ] G where
  toFun Φ := ∑ᶠ p, localKernel A A' B h₁ h₂ p ((A.prod A').localize p Φ)
  map_add' Φ Ψ := by
    have hL := (isCompact_supp Φ).union (isCompact_supp Ψ)
    rw [finsum_localKernel A A' B h₁ h₂ hL subset_union_left,
      finsum_localKernel A A' B h₁ h₂ hL subset_union_right,
      finsum_localKernel A A' B h₁ h₂ hL (supp_add_subset Φ Ψ), ← Finset.sum_add_distrib]
    simp only [map_add]
  map_smul' a Φ := by
    rw [finsum_localKernel A A' B h₁ h₂ (isCompact_supp Φ) (supp_smul_subset a Φ),
      finsum_localKernel A A' B h₁ h₂ (isCompact_supp Φ) subset_rfl, Finset.smul_sum]
    simp only [map_smul, RingHom.id_apply]

/-- The kernel of `B`, as a continuous linear map. -/
private def kernel (A : ChartCutoffs I M M) (A' : ChartCutoffs J N N)
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
      (map_continuous (localKernel A A' B h₁ h₂ p)).comp (((A.prod A').localize p).continuous.comp
        (BundleTest.continuous_ofSupportedIn L))).congr fun σ ↦ ?_
    exact (finsum_localKernel A A' B h₁ h₂ L.isCompact (supp_ofSupportedIn_subset L σ)).symm

private theorem kernel_apply (A : ChartCutoffs I M M) (A' : ChartCutoffs J N N)
    (B : BundleTest I ℝ (Bundle.Trivial M ℝ) →ₗ[ℝ] BundleTest J ℝ (Bundle.Trivial N ℝ) →ₗ[ℝ] G)
    (h₁ : ∀ ψ, Continuous fun φ ↦ B φ ψ) (h₂ : ∀ φ, Continuous (B φ))
    (Φ : BundleTest (I.prod J) ℝ (Bundle.Trivial (M × N) ℝ)) :
    kernel A A' B h₁ h₂ Φ = ∑ᶠ p, localKernel A A' B h₁ h₂ p ((A.prod A').localize p Φ) :=
  rfl

/-- On `φ ⊗ ψ` the term of the product chart `p` of the kernel is `B (ρ φ) (σ ψ)`, for the cutoffs
`ρ` and `σ` of the two charts. -/
private theorem localKernel_localize_tensor (A : ChartCutoffs I M M) (A' : ChartCutoffs J N N)
    (B : BundleTest I ℝ (Bundle.Trivial M ℝ) →ₗ[ℝ] BundleTest J ℝ (Bundle.Trivial N ℝ) →ₗ[ℝ] G)
    (h₁ : ∀ ψ, Continuous fun φ ↦ B φ ψ) (h₂ : ∀ φ, Continuous (B φ)) (p : M × N)
    (φ : BundleTest I ℝ (Bundle.Trivial M ℝ)) (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) :
    localKernel A A' B h₁ h₂ p ((A.prod A').localize p (φ.tensor ψ)) =
      B (smulLeftCLM (A.cutoff p.1) φ) (smulLeftCLM (A'.cutoff p.2) ψ) := by
  rw [ChartCutoffs.localize_prod_tensor, localKernel_prodSMulCLM, A.chartTest_localize,
    A'.chartTest_localize]

private theorem kernel_tensor (A : ChartCutoffs I M M) (A' : ChartCutoffs J N N)
    (B : BundleTest I ℝ (Bundle.Trivial M ℝ) →ₗ[ℝ] BundleTest J ℝ (Bundle.Trivial N ℝ) →ₗ[ℝ] G)
    (h₁ : ∀ ψ, Continuous fun φ ↦ B φ ψ) (h₂ : ∀ φ, Continuous (B φ))
    (φ : BundleTest I ℝ (Bundle.Trivial M ℝ)) (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) :
    kernel A A' B h₁ h₂ (φ.tensor ψ) = B φ ψ := by
  -- Only the charts whose cutoffs meet the supports of `φ` and of `ψ` contribute.
  rw [kernel_apply, finsum_eq_sum_of_support_subset (s := A.meeting (supp φ) (isCompact_supp φ) ×ˢ
    A'.meeting (supp ψ) (isCompact_supp ψ)), Finset.sum_product]
  · simp_rw [localKernel_localize_tensor, ← map_sum (B _), ← LinearMap.sum_apply, ← map_sum B,
      A.sum_smulLeftCLM (isCompact_supp φ) subset_rfl,
      A'.sum_smulLeftCLM (isCompact_supp ψ) subset_rfl]
  · intro p hp
    rw [Finset.coe_product, mem_prod, Finset.mem_coe, Finset.mem_coe]
    by_contra hn
    refine hp ?_
    change localKernel A A' B h₁ h₂ p ((A.prod A').localize p (φ.tensor ψ)) = 0
    rw [localKernel_localize_tensor]
    rcases not_and_or.1 hn with h | h
    · rw [A.smulLeftCLM_eq_zero h subset_rfl, map_zero, LinearMap.zero_apply]
    · rw [A'.smulLeftCLM_eq_zero h subset_rfl, map_zero]

end Existence

variable [I.Boundaryless] [SigmaCompactSpace M] [J.Boundaryless] [SigmaCompactSpace N]

/-- **Kernels are determined by their values on tensor products.** Two continuous linear maps on
the scalar tests on `M × N` agree once they agree on every tensor product `φ ⊗ ψ` of scalar tests
on `M` and `N`. -/
theorem ext_tensor {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [T2Space G]
    {K₁ K₂ : BundleTest (I.prod J) ℝ (Bundle.Trivial (M × N) ℝ) →L[ℝ] G}
    (h : ∀ φ ψ, K₁ (tensor φ ψ) = K₂ (tensor φ ψ)) : K₁ = K₂ := by
  obtain ⟨A⟩ := nonempty_chartCutoffs I M
  obtain ⟨B⟩ := nonempty_chartCutoffs J N
  -- On the extensions through each product chart the two maps agree, by the density of tensor
  -- products of test functions.
  have hC (p : M × N) : K₁ ∘L chartTest ((A.prod B).chart p) ((A.prod B).contMDiffOn_chart p) =
      K₂ ∘L chartTest ((A.prod B).chart p) ((A.prod B).contMDiffOn_chart p) :=
    TestFunction.ext_prodSMulCLM (A.coe_prod_chart_target B p) fun ψ φ ↦ by
      have hp := chartTest_prod_prodSMulCLM _ _ (A.contMDiffOn_chart p.1)
        (B.contMDiffOn_chart p.2) φ ψ
      exact (congrArg K₁ hp).trans ((h _ _).trans (congrArg K₂ hp).symm)
  ext Φ
  rw [← (A.prod B).sum_chartTest_localize (isCompact_supp Φ) subset_rfl, map_sum, map_sum]
  exact Finset.sum_congr rfl fun p _ ↦ DFunLike.congr_fun (hC p) _

end Kernel

end TauCeti.BundleTest

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
  obtain ⟨A⟩ := nonempty_chartCutoffs I M
  obtain ⟨A'⟩ := nonempty_chartCutoffs J N
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
