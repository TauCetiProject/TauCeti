/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Prod
public import TauCeti.Geometry.Manifold.VectorBundle.ExternalTensor
public import TauCeti.Geometry.Manifold.VectorBundle.Section.SmulLeft
public import TauCeti.Analysis.Distribution.TestFunction.Prod

/-!
# External tensor products of bundle tests

Let `V → M` and `W → N` be finite-rank smooth real vector bundles. The external tensor product of
a bundle test `s` of `V` and a bundle test `t` of `W` is the bundle test

`(s ⊠ t)(x, y) = s x ⊗ t y`

of the external tensor product bundle `V ⊠ W` over `M × N` (`TauCeti.BundleTest.externalTensor`).
It is bilinear (`TauCeti.BundleTest.externalTensorₗ`), supported in the product of the supports
(`TauCeti.BundleTest.tsupport_externalTensor_subset`), and multiplying it by `(x, y) ↦ f x * g y`
multiplies the factors by `f` and `g` (`TauCeti.BundleTest.smulLeftCLM_mulProd_externalTensor`).

In a product chart `c × d` with the frame of `V ⊠ W` induced by frames `t` of `V` and `t'` of `W`
(`Bundle.Trivialization.externalTensor`), extending the test function
`(u, u') ↦ ψ u' φ u • (v ⊗ w)` gives the external tensor product of the extensions of `φ • v`
through `c` and `t` and of `ψ • w` through `d` and `t'`
(`Bundle.Trivialization.chartTestCLM_externalTensor_prodSMulCLM`). This is how statements about
tests of `V ⊠ W` reduce to statements about scalar test functions in product charts.

External tensor products of bundle tests are the tests on which a distributional kernel with
coefficients in vector bundles is evaluated, as tensor products of scalar tests
(`TauCeti.BundleTest.tensor`) are for scalar kernels.

## Main declarations

* `TauCeti.BundleTest.externalTensor`: the external tensor product `s ⊠ t` of bundle tests.
* `TauCeti.BundleTest.externalTensor_apply`: its values `s x ⊗ t y`.
* `Bundle.Trivialization.chartTestCLM_externalTensor_prodSMulCLM`: chart extensions of tensor
  products of test functions in product charts.
-/

public noncomputable section

open Bundle Set Function ContMDiffSection ContinuousLinearMap
open scoped ContDiff Manifold TensorProduct Distributions

namespace TauCeti.BundleTest

variable {EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {J : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {W : N → Type*} [∀ y, AddCommGroup (W y)] [∀ y, Module ℝ (W y)] [∀ y, TopologicalSpace (W y)]
  [∀ y, IsTopologicalAddGroup (W y)] [∀ y, ContinuousSMul ℝ (W y)]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W] [VectorBundle ℝ G W]

/-- The **external tensor product** `(s ⊠ t)(x, y) = s x ⊗ t y` of a bundle test `s` of `V` over
`M` and a bundle test `t` of `W` over `N`, a bundle test of `V ⊠ W` over `M × N`. -/
def externalTensor (s : BundleTest I F V) (t : BundleTest J G W) :
    BundleTest (I.prod J) (ProjectiveTensor ℝ F G) (ExternalTensor ℝ V W) :=
  ofCompactlySupported _ _ _
    ⟨((ofCompactlySupported I F V).symm s).val.externalTensor
        ((ofCompactlySupported J G W).symm t).val,
      mem_compactlySupported.2 <|
        (s.isCompact_tsupport.prod t.isCompact_tsupport).of_isClosed_subset
        (ContMDiffSection.isClosed_tsupport _) (by
          simpa only [tsupport_def] using ContMDiffSection.tsupport_externalTensor_subset _ _)⟩

/-- The external tensor product of bundle tests is `(s ⊠ t)(x, y) = s x ⊗ t y`. -/
@[simp]
theorem externalTensor_apply (s : BundleTest I F V) (t : BundleTest J G W) (p : M × N) :
    s.externalTensor t p = (s p.1 ⊗ₜ[ℝ] t p.2 : ExternalTensor ℝ V W p) := by
  rw [externalTensor, coe_ofCompactlySupported]
  exact ContMDiffSection.externalTensor_apply _ _ p

/-- The closed support of `s ⊠ t` lies in the product of the closed supports of `s` and `t`. -/
theorem tsupport_externalTensor_subset (s : BundleTest I F V) (t : BundleTest J G W) :
    closure {p | s.externalTensor t p ≠ 0} ⊆ closure {x | s x ≠ 0} ×ˢ closure {y | t y ≠ 0} := by
  rw [externalTensor, LinearEquiv.symm_apply_apply]
  simpa only [tsupport_def] using ContMDiffSection.tsupport_externalTensor_subset _ _

/-- The external tensor product with the zero test on the left vanishes. -/
@[simp]
theorem zero_externalTensor (t : BundleTest J G W) :
    (0 : BundleTest I F V).externalTensor t = 0 :=
  BundleTest.ext fun p ↦ by
    simp only [externalTensor_apply, zero_apply]; exact TensorProduct.zero_tmul _ _

/-- The external tensor product with the zero test on the right vanishes. -/
@[simp]
theorem externalTensor_zero (s : BundleTest I F V) :
    s.externalTensor (0 : BundleTest J G W) = 0 :=
  BundleTest.ext fun p ↦ by
    simp only [externalTensor_apply, zero_apply]; exact TensorProduct.tmul_zero _ _

/-- The external tensor product of bundle tests is additive in its first factor. -/
theorem add_externalTensor (s s' : BundleTest I F V) (t : BundleTest J G W) :
    (s + s').externalTensor t = s.externalTensor t + s'.externalTensor t :=
  BundleTest.ext fun p ↦ by
    simp only [externalTensor_apply, add_apply]; exact TensorProduct.add_tmul _ _ _

/-- The external tensor product of bundle tests is additive in its second factor. -/
theorem externalTensor_add (s : BundleTest I F V) (t t' : BundleTest J G W) :
    s.externalTensor (t + t') = s.externalTensor t + s.externalTensor t' :=
  BundleTest.ext fun p ↦ by
    simp only [externalTensor_apply, add_apply]; exact TensorProduct.tmul_add _ _ _

/-- The external tensor product of bundle tests is homogeneous in its first factor. -/
theorem smul_externalTensor (a : ℝ) (s : BundleTest I F V) (t : BundleTest J G W) :
    (a • s).externalTensor t = a • s.externalTensor t :=
  BundleTest.ext fun p ↦ by
    simpa only [externalTensor_apply, smul_apply, one_smul, mul_one] using
      ExternalTensor.smul_tmul_smul a 1 (s p.1) (t p.2)

/-- The external tensor product of bundle tests is homogeneous in its second factor. -/
theorem externalTensor_smul (a : ℝ) (s : BundleTest I F V) (t : BundleTest J G W) :
    s.externalTensor (a • t) = a • s.externalTensor t :=
  BundleTest.ext fun p ↦ by
    simpa only [externalTensor_apply, smul_apply, one_smul, one_mul] using
      ExternalTensor.smul_tmul_smul 1 a (s p.1) (t p.2)

/-- The external tensor product of bundle tests, as a bilinear map. -/
def externalTensorₗ :
    BundleTest I F V →ₗ[ℝ] BundleTest J G W →ₗ[ℝ]
      BundleTest (I.prod J) (ProjectiveTensor ℝ F G) (ExternalTensor ℝ V W) :=
  LinearMap.mk₂ ℝ externalTensor add_externalTensor smul_externalTensor externalTensor_add
    externalTensor_smul

@[simp]
theorem externalTensorₗ_apply (s : BundleTest I F V) (t : BundleTest J G W) :
    externalTensorₗ s t = s.externalTensor t :=
  (rfl)

variable [IsManifold I ∞ M] [IsManifold J ∞ N] [ContMDiffVectorBundle ∞ F V I]
  [ContMDiffVectorBundle ∞ G W J]

/-- Multiplying `s ⊠ t` by the smooth function `(x, y) ↦ f x * g y` multiplies `s` by `f` and `t`
by `g`. -/
theorem smulLeftCLM_mulProd_externalTensor (f : C^∞⟮I, M; ℝ⟯) (g : C^∞⟮J, N; ℝ⟯)
    (s : BundleTest I F V) (t : BundleTest J G W) :
    smulLeftCLM (f.mulProd g) (s.externalTensor t) =
      (smulLeftCLM f s).externalTensor (smulLeftCLM g t) := by
  refine BundleTest.ext fun p ↦ ?_
  simp only [smulLeftCLM_apply, externalTensor_apply, ContMDiffMap.mulProd_apply]
  exact (ExternalTensor.smul_tmul_smul _ _ _ _).symm

end TauCeti.BundleTest

namespace Bundle.Trivialization

open TauCeti TestFunction

variable {EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [LocallyCompactSpace EM]
  [TopologicalSpace HM] {I : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M]
  [ChartedSpace HM M] [T2Space M] [IsManifold I ∞ M]
  {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [LocallyCompactSpace EN]
  [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N]
  [ChartedSpace HN N] [T2Space N] [IsManifold J ∞ N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {W : N → Type*} [∀ y, AddCommGroup (W y)] [∀ y, Module ℝ (W y)] [∀ y, TopologicalSpace (W y)]
  [∀ y, IsTopologicalAddGroup (W y)] [∀ y, ContinuousSMul ℝ (W y)]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W] [VectorBundle ℝ G W]
  [ContMDiffVectorBundle ∞ G W J]
  (t : Trivialization F (π F V)) [MemTrivializationAtlas t]
  (t' : Trivialization G (π G W)) [MemTrivializationAtlas t']
  {c : OpenPartialHomeomorph M EM} (hc : ContMDiffOn I 𝓘(ℝ, EM) ∞ c c.source)
  (hct : c.source ⊆ t.baseSet)
  {d : OpenPartialHomeomorph N EN} (hd : ContMDiffOn J 𝓘(ℝ, EN) ∞ d d.source)
  (hdt : d.source ⊆ t'.baseSet)
  {e : OpenPartialHomeomorph (M × N) (EM × EN)} (he : e = c.prod d)
  (hce : ContMDiffOn (I.prod J) 𝓘(ℝ, EM × EN) ∞ e e.source)
  (hcet : e.source ⊆ (t.externalTensor ℝ t').baseSet)

include he in
/-- **Chart extensions of tensor products in product charts.** Extending the test function
`(u, u') ↦ ψ u' φ u • (v ⊗ w)` through a product chart `e = c × d` and the frame of `V ⊠ W`
induced by `t` and `t'` gives the external tensor product of the extension of `φ • v` through `c`
and `t` and the extension of `ψ • w` through `d` and `t'`. -/
theorem chartTestCLM_externalTensor_prodSMulCLM
    (hV : (c.target : Set EM) ×ˢ (d.target : Set EN) ⊆ e.target)
    (φ : 𝓓(⟨c.target, c.open_target⟩, ℝ)) (ψ : 𝓓(⟨d.target, d.open_target⟩, ℝ)) (v : F)
    (w : G) :
    (t.externalTensor ℝ t').chartTestCLM e hce hcet
        (postcompCLM (toSpanSingleton ℝ (ProjectiveTensor.mk (v ⊗ₜ[ℝ] w)))
          (prodSMulCLM (V := ⟨e.target, e.open_target⟩) ψ hV φ)) =
      (t.chartTestCLM c hc hct (postcompCLM (toSpanSingleton ℝ v) φ)).externalTensor
        (t'.chartTestCLM d hd hdt (postcompCLM (toSpanSingleton ℝ w) ψ)) := by
  subst he
  refine BundleTest.ext fun z ↦ ?_
  rw [BundleTest.externalTensor_apply]
  by_cases hz : z ∈ (c.prod d).source
  · have hz' : z.1 ∈ c.source ∧ z.2 ∈ d.source := by
      rwa [OpenPartialHomeomorph.prod_source] at hz
    rw [chartTestCLM_apply_of_mem _ _ _ _ _ hz, chartTestCLM_apply_of_mem _ _ _ _ _ hz'.1,
      chartTestCLM_apply_of_mem _ _ _ _ _ hz'.2]
    simp only [postcompCLM_apply, Function.comp_apply, toSpanSingleton_apply, prodSMulCLM_apply,
      OpenPartialHomeomorph.prod_apply, map_smul]
    rw [symmL_apply _ (hcet hz), symmL_apply _ (hct hz'.1), symmL_apply _ (hdt hz'.2)]
    rw [externalTensor_symm_apply_tmul ⟨hct hz'.1, hdt hz'.2⟩, smul_smul, mul_comm]
    exact (ExternalTensor.smul_tmul_smul _ _ _ _).symm
  · rw [chartTestCLM_apply_of_notMem _ _ _ _ _ hz]
    rw [OpenPartialHomeomorph.prod_source, mem_prod, not_and_or] at hz
    rcases hz with hz | hz
    · rw [chartTestCLM_apply_of_notMem _ _ _ _ _ hz]
      exact (TensorProduct.zero_tmul _ _).symm
    · rw [chartTestCLM_apply_of_notMem _ _ _ _ _ hz]
      exact (TensorProduct.tmul_zero _ _).symm

end Bundle.Trivialization
