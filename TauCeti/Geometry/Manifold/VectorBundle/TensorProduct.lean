/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.TensorProduct.Operations

/-!
# Smooth tensor products of finite-rank vector bundles

For `C^n` vector bundles `E₁` and `E₂` over a manifold `B` with finite-dimensional model fibres
`F₁` and `F₂` over a complete nontrivially normed field `𝕜`, the topological tensor-product vector
bundle `fun x ↦ E₁ x ⊗[𝕜] E₂ x` constructed in
`TauCeti.Topology.VectorBundle.TensorProduct.Basic` is a `C^n` vector bundle
(`ContMDiffVectorBundle.tensorProduct`). Smoothness of transition functions
(`contMDiffOn_tensorProductCoordChange`) follows by composing factor coordinate changes with the
continuous bilinear operator `TauCeti.ProjectiveTensor.mapCLM`.

## Main definitions and results

* `contMDiffOn_tensorProductCoordChange`, `mdifferentiableOn_tensorProductCoordChange`: transition
  functions of tensor-product trivializations are `C^n` (respectively differentiable) on the
  intersection of their base sets.
* `chartAt_tensorProduct`, `contMDiffWithinAt_tensorProduct_bundle`,
  `contMDiffAt_tensorProduct_bundle`, `mdifferentiableWithinAt_tensorProduct_bundle`,
  `mdifferentiableAt_tensorProduct_bundle`: manifold chart formula and coordinate characterisations
  for maps into a tensor-product bundle.
* `Bundle.TensorProduct.vectorPrebundle.isContMDiff`, `ContMDiffVectorBundle.tensorProduct`: `C^n`
  vector-bundle structure on `fun x ↦ E₁ x ⊗[𝕜] E₂ x`.
* `TauCeti.contMDiff_bundleTmul`, `ContMDiffWithinAt.tmul_section`, `ContMDiffAt.tmul_section`,
  `ContMDiffOn.tmul_section`, `ContMDiff.tmul_section`, `ContMDiffSection.tmul`: `C^n` regularity
  of the canonical pure-tensor bilinear map and induced `𝕜`-bilinear map on bundled `C^n` sections.
* `TauCeti.contMDiffAt_bundleTensorLift_iff`, `TauCeti.contMDiff_bundleTensorLift_iff`: universal
  property of the tensor-product bundle for `C^n` Hom-bundle sections into an arbitrary Banach
  vector bundle `E₃` (not assumed finite-rank).
* `TauCeti.contMDiffWithinAt_bundleTensorMap`, `TauCeti.contMDiff_bundleTensorMap`,
  `TauCeti.bundleTensorCongrDiffeomorph`: `C^n` functoriality of tensor products of bundle
  morphisms and induced `C^n` diffeomorphism of total spaces.
* `TauCeti.contMDiff_bundleTensorComm`, `TauCeti.bundleTensorCommDiffeomorph`,
  `TauCeti.contMDiff_bundleTensorAssoc`, `TauCeti.bundleTensorAssocDiffeomorph`: canonical symmetry
  and associativity `C^n` diffeomorphisms of tensor-product total spaces.
* `TauCeti.contMDiff_bundleDualTensorHom`, `TauCeti.bundleDualTensorHomDiffeomorph`,
  `ContMDiffSection.dualTensorHomEquiv`: canonical `C^n` total-space diffeomorphism between
  `StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x` and `E₁ x →L[𝕜] E₂ x`, together with the induced `𝕜`-linear
  equivalence on bundled `C^n` sections.

## References

* `Mathlib.Geometry.Manifold.VectorBundle.Hom` for the parallel `ContMDiffVectorBundle` construction
  on continuous linear map bundles.
* `TauCeti.Geometry.Manifold.VectorBundle.Hom` for constant-coordinate Hom-bundle smoothness and
  `TauCeti.bundleDiffeomorph`.
* [J. M. Lee, *Introduction to Smooth Manifolds* (2nd ed.), Chapter 10 and Chapter 12][lee2013]
-/

public section

noncomputable section

open Bundle Set OpenPartialHomeomorph Pretrivialization
open scoped Manifold Bundle Topology ContDiff TensorProduct

/-! ### `C^n` vector-bundle structure and chart characterisations -/

section SmoothPrebundle

variable {𝕜 B F₁ F₂ M : Type*} {n : WithTop ℕ∞}
  {E₁ : B → Type*} {E₂ : B → Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {e₁ e₁' : Trivialization F₁ (π F₁ E₁)} {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}

/-- Transition functions between induced tensor-product trivializations of `C^n` vector bundles are
`C^n` on the intersection of their base sets (assuming `F₁` is finite-dimensional so that
`ProjectiveTensor 𝕜 F₁ F₂` is a normed space). -/
theorem contMDiffOn_tensorProductCoordChange
    [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    ContMDiffOn IB
      𝓘(𝕜, TauCeti.ProjectiveTensor 𝕜 F₁ F₂ →L[𝕜] TauCeti.ProjectiveTensor 𝕜 F₁ F₂) n
      (tensorProductCoordChange 𝕜 e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  let s := e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)
  have h₁ : ContMDiffOn IB 𝓘(𝕜, F₁ →L[𝕜] F₁) n
      (fun b ↦ (e₁.coordChangeL 𝕜 e₁' b : F₁ →L[𝕜] F₁)) s :=
    (contMDiffOn_coordChangeL (IB := IB) e₁ e₁' (n := n)).mono fun _ hb ↦ ⟨hb.1.1, hb.2.1⟩
  have h₂ : ContMDiffOn IB 𝓘(𝕜, F₂ →L[𝕜] F₂) n
      (fun b ↦ (e₂.coordChangeL 𝕜 e₂' b : F₂ →L[𝕜] F₂)) s :=
    (contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := n)).mono fun _ hb ↦ ⟨hb.1.2, hb.2.2⟩
  have h : ContMDiffOn IB
      𝓘(𝕜, TauCeti.ProjectiveTensor 𝕜 F₁ F₂ →L[𝕜] TauCeti.ProjectiveTensor 𝕜 F₁ F₂) n
      (fun b ↦ TauCeti.ProjectiveTensor.mapCLM 𝕜 F₁ F₁ F₂ F₂
        (e₁.coordChangeL 𝕜 e₁' b : F₁ →L[𝕜] F₁)
        (e₂.coordChangeL 𝕜 e₂' b : F₂ →L[𝕜] F₂)) s :=
    fun b hb ↦
      ((TauCeti.ProjectiveTensor.mapCLM 𝕜 F₁ F₁ F₂ F₂).contDiff.comp_contMDiffWithinAt
        (h₁ b hb)).clm_apply (h₂ b hb)
  exact h.congr fun b _ ↦ by simp [tensorProductCoordChange_eq]

/-- Transition functions between induced tensor-product trivializations of `C^1` vector bundles are
differentiable on the intersection of their base sets. -/
theorem mdifferentiableOn_tensorProductCoordChange
    [ContMDiffVectorBundle 1 F₁ E₁ IB] [ContMDiffVectorBundle 1 F₂ E₂ IB]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    MDifferentiableOn IB
      𝓘(𝕜, TauCeti.ProjectiveTensor 𝕜 F₁ F₂ →L[𝕜] TauCeti.ProjectiveTensor 𝕜 F₁ F₂)
      (tensorProductCoordChange 𝕜 e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) :=
  (contMDiffOn_tensorProductCoordChange (IB := IB) (n := 1)).mdifferentiableOn one_ne_zero

section FiniteRankCharts

variable [FiniteDimensional 𝕜 F₂]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]

@[simp]
theorem chartAt_tensorProduct
    (y₀ y : TotalSpace (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) :
    chartAt (ModelProd HB (TauCeti.ProjectiveTensor 𝕜 F₁ F₂)) y₀ y =
      (chartAt HB y₀.1 y.1, TensorProduct.inCoordinates F₁ E₁ F₂ E₂ y₀.1 y.1 y₀.1 y.1 y.2) := by
  rw [FiberBundle.chartedSpace_chartAt, trans_apply, OpenPartialHomeomorph.prod_apply,
    Trivialization.coe_coe, OpenPartialHomeomorph.refl_apply, Function.id_def,
    tensorProduct_trivializationAt_apply]

/-- Characterisation of `ContMDiffWithinAt` for maps into a tensor-product bundle via
`TensorProduct.inCoordinates`. -/
theorem contMDiffWithinAt_tensorProduct_bundle
    (f : M → TotalSpace (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x))
    {s : Set M} {x₀ : M} :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, TauCeti.ProjectiveTensor 𝕜 F₁ F₂)) n f s x₀ ↔
      ContMDiffWithinAt IM IB n (fun x ↦ (f x).1) s x₀ ∧
        ContMDiffWithinAt IM 𝓘(𝕜, TauCeti.ProjectiveTensor 𝕜 F₁ F₂) n
          (fun x ↦ TensorProduct.inCoordinates F₁ E₁ F₂ E₂
            (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) s x₀ := by
  simpa only [tensorProduct_trivializationAt_apply] using
    (contMDiffWithinAt_totalSpace (IB := IB) (IM := IM) (n := n)
      (F := TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (E := fun x ↦ E₁ x ⊗[𝕜] E₂ x)
      (f := f) (s := s) (x₀ := x₀))

/-- Characterisation of `ContMDiffAt` for maps into a tensor-product bundle via
`TensorProduct.inCoordinates`. -/
theorem contMDiffAt_tensorProduct_bundle
    (f : M → TotalSpace (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) {x₀ : M} :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, TauCeti.ProjectiveTensor 𝕜 F₁ F₂)) n f x₀ ↔
      ContMDiffAt IM IB n (fun x ↦ (f x).1) x₀ ∧
        ContMDiffAt IM 𝓘(𝕜, TauCeti.ProjectiveTensor 𝕜 F₁ F₂) n
          (fun x ↦ TensorProduct.inCoordinates F₁ E₁ F₂ E₂
            (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ := by
  simpa only [← contMDiffWithinAt_univ] using
    contMDiffWithinAt_tensorProduct_bundle (IB := IB) (IM := IM) (n := n) f (s := univ) (x₀ := x₀)

/-- Characterisation of `MDifferentiableWithinAt` for maps into a tensor-product bundle via
`TensorProduct.inCoordinates`. -/
theorem mdifferentiableWithinAt_tensorProduct_bundle
    (f : M → TotalSpace (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x))
    {s : Set M} {x₀ : M} :
    MDifferentiableWithinAt IM (IB.prod 𝓘(𝕜, TauCeti.ProjectiveTensor 𝕜 F₁ F₂)) f s x₀ ↔
      MDifferentiableWithinAt IM IB (fun x ↦ (f x).1) s x₀ ∧
        MDifferentiableWithinAt IM 𝓘(𝕜, TauCeti.ProjectiveTensor 𝕜 F₁ F₂)
          (fun x ↦ TensorProduct.inCoordinates F₁ E₁ F₂ E₂
            (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) s x₀ := by
  simpa only [tensorProduct_trivializationAt_apply] using
    (mdifferentiableWithinAt_totalSpace IB (IM := IM)
      (F := TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (E := fun x ↦ E₁ x ⊗[𝕜] E₂ x) f (s := s) (x₀ := x₀))

/-- Characterisation of `MDifferentiableAt` for maps into a tensor-product bundle via
`TensorProduct.inCoordinates`. -/
theorem mdifferentiableAt_tensorProduct_bundle
    (f : M → TotalSpace (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) {x₀ : M} :
    MDifferentiableAt IM (IB.prod 𝓘(𝕜, TauCeti.ProjectiveTensor 𝕜 F₁ F₂)) f x₀ ↔
      MDifferentiableAt IM IB (fun x ↦ (f x).1) x₀ ∧
        MDifferentiableAt IM 𝓘(𝕜, TauCeti.ProjectiveTensor 𝕜 F₁ F₂)
          (fun x ↦ TensorProduct.inCoordinates F₁ E₁ F₂ E₂
            (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ := by
  simpa only [← mdifferentiableWithinAt_univ] using
    mdifferentiableWithinAt_tensorProduct_bundle (IB := IB) (IM := IM) f (s := univ) (x₀ := x₀)

variable [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]

instance Bundle.TensorProduct.vectorPrebundle.isContMDiff :
    (Bundle.TensorProduct.vectorPrebundle 𝕜 F₁ E₁ F₂ E₂).IsContMDiff IB n where
  exists_contMDiffCoordChange := by
    intro _ he _ he'
    rcases (Bundle.TensorProduct.mem_pretrivializationAtlas_iff 𝕜 F₁ E₁ F₂ E₂).1 he with
      ⟨e₁, e₂, he₁, he₂, rfl⟩
    rcases (Bundle.TensorProduct.mem_pretrivializationAtlas_iff 𝕜 F₁ E₁ F₂ E₂).1 he' with
      ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨tensorProductCoordChange 𝕜 e₁ e₁' e₂ e₂',
      by simpa only [Pretrivialization.tensorProduct_baseSet] using
        (contMDiffOn_tensorProductCoordChange (IB := IB) (n := n)
          (e₁ := e₁) (e₁' := e₁') (e₂ := e₂) (e₂' := e₂')),
      by simpa only [Pretrivialization.tensorProduct_baseSet] using
        tensorProductCoordChange_apply 𝕜 e₁ e₁' e₂ e₂'⟩

/-- The tensor product of two `C^n` finite-rank vector bundles is a `C^n` vector bundle. -/
instance ContMDiffVectorBundle.tensorProduct :
    ContMDiffVectorBundle n (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) IB :=
  (Bundle.TensorProduct.vectorPrebundle 𝕜 F₁ E₁ F₂ E₂).contMDiffVectorBundle IB

end FiniteRankCharts

end SmoothPrebundle

/-! ### `C^n` pure-tensor maps and bundled sections -/

namespace TauCeti

section PureTensorSmooth

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] {n : WithTop ℕ∞}
  {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₁ E₂ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]

/-- `bundleTmul` is a `C^n` section of the Hom bundle `E₁ →L E₂ →L (E₁ ⊗ E₂)`. Neither factor
bundle need be assumed `C^n`. -/
theorem contMDiff_bundleTmul :
    ContMDiff IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] ProjectiveTensor 𝕜 F₁ F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] ProjectiveTensor 𝕜 F₁ F₂)
        (E := fun y ↦ E₁ y →L[𝕜] E₂ y →L[𝕜] (E₁ y ⊗[𝕜] E₂ y)) x (bundleTmul F₁ F₂ x)) :=
  contMDiff_hom_bundle_of_inCoordinates_eq_const
    (c := fun _ ↦ ProjectiveTensor.tmulL 𝕜 F₁ F₂)
    fun a x hx₁ hx₂ ↦ bundleTmul_inCoordinates a x hx₁
      (by rw [hom_trivializationAt_baseSet] at hx₂; exact hx₂.1)

end PureTensorSmooth

end TauCeti

section PureTensorSectionSmooth

variable {𝕜 B M F₁ F₂ : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {n : WithTop ℕ∞}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₁ E₂ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]
  {b : M → B} {v : ∀ m, E₁ (b m)} {w : ∀ m, E₂ (b m)} {s : Set M} {x : M}

/-- Pointwise pure tensor of two bundle-valued maps `C^n` within `s` at `x` is `C^n` within `s` at
`x`. -/
theorem ContMDiffWithinAt.tmul_section
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₁)) n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s x)
    (hw : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₂)) n (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) s x) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, TauCeti.ProjectiveTensor 𝕜 F₁ F₂)) n
      (fun m ↦ TotalSpace.mk' (TauCeti.ProjectiveTensor 𝕜 F₁ F₂)
        (E := fun y ↦ E₁ y ⊗[𝕜] E₂ y) (b m) (v m ⊗ₜ[𝕜] w m)) s x := by
  have hb : ContMDiffWithinAt IM IB n b s x :=
    (contMDiffAt_proj E₁).comp_contMDiffWithinAt x hv
  have htmul : ContMDiffWithinAt IM
      (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] TauCeti.ProjectiveTensor 𝕜 F₁ F₂)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] TauCeti.ProjectiveTensor 𝕜 F₁ F₂)
        (E := fun y ↦ E₁ y →L[𝕜] E₂ y →L[𝕜] (E₁ y ⊗[𝕜] E₂ y)) (b m)
        (TauCeti.bundleTmul F₁ F₂ (b m))) s x :=
    (TauCeti.contMDiff_bundleTmul (IB := IB) (n := n) (F₁ := F₁) (F₂ := F₂)
      (b x)).comp_contMDiffWithinAt x hb
  simpa only [TauCeti.bundleTmul_apply] using
    htmul.clm_bundle_apply₂
      (F₁ := F₁) (F₂ := F₂) (F₃ := TauCeti.ProjectiveTensor 𝕜 F₁ F₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := fun y ↦ E₁ y ⊗[𝕜] E₂ y) hv hw

/-- Pointwise pure tensor of two bundle-valued maps `C^n` at `x` is `C^n` at `x`. -/
theorem ContMDiffAt.tmul_section
    (hv : ContMDiffAt IM (IB.prod 𝓘(𝕜, F₁)) n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x)
    (hw : ContMDiffAt IM (IB.prod 𝓘(𝕜, F₂)) n (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) x) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, TauCeti.ProjectiveTensor 𝕜 F₁ F₂)) n
      (fun m ↦ TotalSpace.mk' (TauCeti.ProjectiveTensor 𝕜 F₁ F₂)
        (E := fun y ↦ E₁ y ⊗[𝕜] E₂ y) (b m) (v m ⊗ₜ[𝕜] w m)) x := by
  rw [← contMDiffWithinAt_univ] at hv hw ⊢
  exact hv.tmul_section hw

/-- Pointwise pure tensor of two bundle-valued maps `C^n` on `s` is `C^n` on `s`. -/
theorem ContMDiffOn.tmul_section
    (hv : ContMDiffOn IM (IB.prod 𝓘(𝕜, F₁)) n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s)
    (hw : ContMDiffOn IM (IB.prod 𝓘(𝕜, F₂)) n (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) s) :
    ContMDiffOn IM (IB.prod 𝓘(𝕜, TauCeti.ProjectiveTensor 𝕜 F₁ F₂)) n
      (fun m ↦ TotalSpace.mk' (TauCeti.ProjectiveTensor 𝕜 F₁ F₂)
        (E := fun y ↦ E₁ y ⊗[𝕜] E₂ y) (b m) (v m ⊗ₜ[𝕜] w m)) s :=
  fun m hm ↦ (hv m hm).tmul_section (hw m hm)

/-- Pointwise pure tensor of two `C^n` bundle-valued maps is `C^n`. -/
theorem ContMDiff.tmul_section
    (hv : ContMDiff IM (IB.prod 𝓘(𝕜, F₁)) n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)))
    (hw : ContMDiff IM (IB.prod 𝓘(𝕜, F₂)) n (fun m ↦ TotalSpace.mk' F₂ (b m) (w m))) :
    ContMDiff IM (IB.prod 𝓘(𝕜, TauCeti.ProjectiveTensor 𝕜 F₁ F₂)) n
      (fun m ↦ TotalSpace.mk' (TauCeti.ProjectiveTensor 𝕜 F₁ F₂)
        (E := fun y ↦ E₁ y ⊗[𝕜] E₂ y) (b m) (v m ⊗ₜ[𝕜] w m)) :=
  fun m ↦ (hv m).tmul_section (hw m)

end PureTensorSectionSmooth

namespace ContMDiffSection

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] {n : ℕ∞ω}
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]

/-- The `𝕜`-bilinear pure-tensor map on bundled `C^n` sections of finite-rank vector bundles. -/
def tmul :
    Cₛ^n⟮IB; F₁, E₁⟯ →ₗ[𝕜] Cₛ^n⟮IB; F₂, E₂⟯ →ₗ[𝕜]
      Cₛ^n⟮IB; TauCeti.ProjectiveTensor 𝕜 F₁ F₂, fun x ↦ E₁ x ⊗[𝕜] E₂ x⟯ where
  toFun s :=
    { toFun t := ⟨fun x ↦ s x ⊗ₜ[𝕜] t x, s.contMDiff.tmul_section t.contMDiff⟩
      map_add' t₁ t₂ := by ext x; simp [TensorProduct.tmul_add]
      map_smul' c t := by ext x; simp [TensorProduct.tmul_smul] }
  map_add' s₁ s₂ := by ext t x; simp [TensorProduct.add_tmul]
  map_smul' c s := by ext t x; simp [TensorProduct.smul_tmul']

@[simp]
theorem tmul_apply (s : Cₛ^n⟮IB; F₁, E₁⟯) (t : Cₛ^n⟮IB; F₂, E₂⟯) (x : B) :
    tmul s t x = s x ⊗ₜ[𝕜] t x :=
  (rfl)

end ContMDiffSection

/-! ### Smooth universal property, functoriality, and canonical diffeomorphisms -/

namespace TauCeti

section LiftSmooth

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] {n : WithTop ℕ∞}
  {F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {E₁ E₂ E₃ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜 (E₃ x)] [∀ x, TopologicalSpace (E₃ x)]
  [∀ x, IsTopologicalAddGroup (E₃ x)] [∀ x, ContinuousSMul 𝕜 (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)] [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]

/-- Pointwise `C^n` universal property of the tensor-product bundle: `bundleTensorLift Φ` is `C^n`
at `a` as a section of `(E₁ ⊗ E₂) →L E₃` if and only if `Φ` is `C^n` at `a` as a section of
`E₁ →L E₂ →L E₃`. The target model fibre `F₃` need not have finite dimension. -/
theorem contMDiffAt_bundleTensorLift_iff (Φ : ∀ x, E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x) (a : B) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, ProjectiveTensor 𝕜 F₁ F₂ →L[𝕜] F₃)) n
        (fun x ↦ TotalSpace.mk' (ProjectiveTensor 𝕜 F₁ F₂ →L[𝕜] F₃)
          (E := fun y ↦ E₁ y ⊗[𝕜] E₂ y →L[𝕜] E₃ y) x (bundleTensorLift Φ x)) a ↔
      ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃)) n
        (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
          (E := fun y ↦ E₁ y →L[𝕜] E₂ y →L[𝕜] E₃ y) x (Φ x)) a := by
  simp only [contMDiffAt_hom_bundle]
  refine and_congr_right fun _ ↦ ?_
  let L := (ProjectiveTensor.liftIsometry 𝕜 F₁ F₂ F₃).toContinuousLinearEquiv
  have hev : (fun x ↦ ContinuousLinearMap.inCoordinates (ProjectiveTensor 𝕜 F₁ F₂)
      (fun y ↦ E₁ y ⊗[𝕜] E₂ y) F₃ E₃ a x a x (bundleTensorLift Φ x)) =ᶠ[𝓝 a]
      (L ∘ fun x ↦
        ContinuousLinearMap.inCoordinates F₁ E₁ (F₂ →L[𝕜] F₃)
          (fun y ↦ E₂ y →L[𝕜] E₃ y) a x a x (Φ x)) := by
    filter_upwards [(trivializationAt F₁ E₁ a).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F₁ E₁ a),
      (trivializationAt F₂ E₂ a).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F₂ E₂ a),
      (trivializationAt F₃ E₃ a).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F₃ E₃ a)] with x hx₁ hx₂ hx₃
    exact bundleTensorLift_inCoordinates Φ a x hx₁ hx₂ hx₃
  refine ⟨fun h ↦ ?_, fun h ↦ (L.contDiff.comp_contMDiffAt h).congr_of_eventuallyEq hev⟩
  exact (L.symm.contDiff.comp_contMDiffAt (h.congr_of_eventuallyEq hev.symm)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ ↦ (L.symm_apply_apply _).symm)

/-- Global `C^n` universal property of the tensor-product bundle: `bundleTensorLift Φ` is a `C^n`
section of `(E₁ ⊗ E₂) →L E₃` if and only if `Φ` is a `C^n` section of `E₁ →L E₂ →L E₃`. The target
model fibre `F₃` need not have finite dimension. -/
theorem contMDiff_bundleTensorLift_iff (Φ : ∀ x, E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x) :
    ContMDiff IB (IB.prod 𝓘(𝕜, ProjectiveTensor 𝕜 F₁ F₂ →L[𝕜] F₃)) n
        (fun x ↦ TotalSpace.mk' (ProjectiveTensor 𝕜 F₁ F₂ →L[𝕜] F₃)
          (E := fun y ↦ E₁ y ⊗[𝕜] E₂ y →L[𝕜] E₃ y) x (bundleTensorLift Φ x)) ↔
      ContMDiff IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃)) n
        (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
          (E := fun y ↦ E₁ y →L[𝕜] E₂ y →L[𝕜] E₃ y) x (Φ x)) :=
  forall_congr' (contMDiffAt_bundleTensorLift_iff Φ)

end LiftSmooth

section MapSmooth

variable {𝕜 B M : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M] {n : WithTop ℕ∞}
  {F₁ F₁' F₂ F₂' : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  [NormedAddCommGroup F₁'] [NormedSpace 𝕜 F₁'] [FiniteDimensional 𝕜 F₁']
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  [NormedAddCommGroup F₂'] [NormedSpace 𝕜 F₂'] [FiniteDimensional 𝕜 F₂']
  {E₁ E₁' E₂ E₂' : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [∀ x, AddCommGroup (E₁' x)] [∀ x, Module 𝕜 (E₁' x)] [∀ x, TopologicalSpace (E₁' x)]
  [∀ x, IsTopologicalAddGroup (E₁' x)] [∀ x, ContinuousSMul 𝕜 (E₁' x)]
  [TopologicalSpace (TotalSpace F₁' E₁')] [FiberBundle F₁' E₁'] [VectorBundle 𝕜 F₁' E₁']
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, AddCommGroup (E₂' x)] [∀ x, Module 𝕜 (E₂' x)] [∀ x, TopologicalSpace (E₂' x)]
  [∀ x, IsTopologicalAddGroup (E₂' x)] [∀ x, ContinuousSMul 𝕜 (E₂' x)]
  [TopologicalSpace (TotalSpace F₂' E₂')] [FiberBundle F₂' E₂'] [VectorBundle 𝕜 F₂' E₂']
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]
  [∀ x, TopologicalSpace (E₁' x ⊗[𝕜] E₂' x)] [∀ x, IsModuleTopology 𝕜 (E₁' x ⊗[𝕜] E₂' x)]

/-- Functoriality of `bundleTensorMap` preserves `ContMDiffWithinAt` along a base map `b`. -/
theorem contMDiffWithinAt_bundleTensorMap {b : M → B}
    {f : ∀ x, E₁ x →L[𝕜] E₁' x} {g : ∀ x, E₂ x →L[𝕜] E₂' x} {s : Set M} {x₀ : M}
    (hf : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₁')) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₁') (E := fun y ↦ E₁ y →L[𝕜] E₁' y) (b m) (f (b m)))
      s x₀)
    (hg : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₂')) n
      (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₂') (E := fun y ↦ E₂ y →L[𝕜] E₂' y) (b m) (g (b m)))
      s x₀) :
    ContMDiffWithinAt IM
      (IB.prod 𝓘(𝕜, ProjectiveTensor 𝕜 F₁ F₂ →L[𝕜] ProjectiveTensor 𝕜 F₁' F₂')) n
      (fun m ↦ TotalSpace.mk' (ProjectiveTensor 𝕜 F₁ F₂ →L[𝕜] ProjectiveTensor 𝕜 F₁' F₂')
        (E := fun y ↦ E₁ y ⊗[𝕜] E₂ y →L[𝕜] E₁' y ⊗[𝕜] E₂' y) (b m)
        (bundleTensorMap f g (b m))) s x₀ := by
  simp only [contMDiffWithinAt_hom_bundle] at hf hg ⊢
  refine ⟨hf.1, ?_⟩
  have h₁ := mem_baseSet_trivializationAt F₁ E₁ (b x₀)
  have h₁' := mem_baseSet_trivializationAt F₁' E₁' (b x₀)
  have h₂ := mem_baseSet_trivializationAt F₂ E₂ (b x₀)
  have h₂' := mem_baseSet_trivializationAt F₂' E₂' (b x₀)
  have hcomp : ContMDiffWithinAt IM
      𝓘(𝕜, ProjectiveTensor 𝕜 F₁ F₂ →L[𝕜] ProjectiveTensor 𝕜 F₁' F₂') n
      (fun m ↦ ProjectiveTensor.mapCLM 𝕜 F₁ F₁' F₂ F₂'
        (ContinuousLinearMap.inCoordinates F₁ E₁ F₁' E₁' (b x₀) (b m) (b x₀) (b m) (f (b m)))
        (ContinuousLinearMap.inCoordinates F₂ E₂ F₂' E₂' (b x₀) (b m) (b x₀) (b m) (g (b m))))
      s x₀ :=
    ((ProjectiveTensor.mapCLM 𝕜 F₁ F₁' F₂ F₂').contDiff.comp_contMDiffWithinAt hf.2).clm_apply hg.2
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hf.1.continuousWithinAt.preimage_mem_nhdsWithin <| Filter.inter_mem
        (Filter.inter_mem ((trivializationAt F₁ E₁ (b x₀)).open_baseSet.mem_nhds h₁)
          ((trivializationAt F₁' E₁' (b x₀)).open_baseSet.mem_nhds h₁'))
        (Filter.inter_mem ((trivializationAt F₂ E₂ (b x₀)).open_baseSet.mem_nhds h₂)
          ((trivializationAt F₂' E₂' (b x₀)).open_baseSet.mem_nhds h₂'))] with m hm
    exact (bundleTensorMap_inCoordinates f g (b x₀) (b m) hm.1.1 hm.1.2 hm.2.1 hm.2.2).trans
      (ProjectiveTensor.mapCLM_apply _ _).symm
  · exact (bundleTensorMap_inCoordinates f g (b x₀) (b x₀) h₁ h₁' h₂ h₂').trans
      (ProjectiveTensor.mapCLM_apply _ _).symm

/-- Functoriality of `bundleTensorMap` on globally `C^n` Hom-bundle sections. -/
theorem contMDiff_bundleTensorMap
    {f : ∀ x, E₁ x →L[𝕜] E₁' x} {g : ∀ x, E₂ x →L[𝕜] E₂' x}
    (hf : ContMDiff IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₁')) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₁') (E := fun y ↦ E₁ y →L[𝕜] E₁' y) x (f x)))
    (hg : ContMDiff IB (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₂')) n
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₂') (E := fun y ↦ E₂ y →L[𝕜] E₂' y) x (g x))) :
    ContMDiff IB (IB.prod 𝓘(𝕜, ProjectiveTensor 𝕜 F₁ F₂ →L[𝕜] ProjectiveTensor 𝕜 F₁' F₂')) n
      (fun x ↦ TotalSpace.mk' (ProjectiveTensor 𝕜 F₁ F₂ →L[𝕜] ProjectiveTensor 𝕜 F₁' F₂')
        (E := fun y ↦ E₁ y ⊗[𝕜] E₂ y →L[𝕜] E₁' y ⊗[𝕜] E₂' y) x (bundleTensorMap f g x)) :=
  fun x ↦ by
    rw [← contMDiffWithinAt_univ]
    exact contMDiffWithinAt_bundleTensorMap (IB := IB) (IM := IB) (b := id)
      (hf x).contMDiffWithinAt (hg x).contMDiffWithinAt

/-- `C^n` diffeomorphism of tensor-product total spaces induced by two `C^n` families of fibrewise
linear equivalences. Smoothness of the inverse follows automatically from finite rank. -/
def bundleTensorCongrDiffeomorph
    (e₁ : ∀ x, E₁ x ≃L[𝕜] E₁' x) (e₂ : ∀ x, E₂ x ≃L[𝕜] E₂' x)
    (he₁ : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₁')) n
      (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₁' p.proj (e₁ p.proj p.2)))
    (he₂ : ContMDiff (IB.prod 𝓘(𝕜, F₂)) (IB.prod 𝓘(𝕜, F₂')) n
      (fun p : TotalSpace F₂ E₂ ↦ TotalSpace.mk' F₂' p.proj (e₂ p.proj p.2))) :
    TotalSpace (ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)
      ≃ₘ^n⟮IB.prod 𝓘(𝕜, ProjectiveTensor 𝕜 F₁ F₂), IB.prod 𝓘(𝕜, ProjectiveTensor 𝕜 F₁' F₂')⟯
      TotalSpace (ProjectiveTensor 𝕜 F₁' F₂') (fun x ↦ E₁' x ⊗[𝕜] E₂' x) :=
  bundleDiffeomorph
    (F₁ := ProjectiveTensor 𝕜 F₁ F₂) (F₂ := ProjectiveTensor 𝕜 F₁' F₂')
    (E₁ := fun x ↦ E₁ x ⊗[𝕜] E₂ x) (E₂ := fun x ↦ E₁' x ⊗[𝕜] E₂' x)
    (bundleTensorCongr e₁ e₂) <|
    ((contMDiff_hom_bundle_iff (IB := IB)
      (F₁ := ProjectiveTensor 𝕜 F₁ F₂) (F₂ := ProjectiveTensor 𝕜 F₁' F₂')
      (E₁ := fun x ↦ E₁ x ⊗[𝕜] E₂ x) (E₂ := fun x ↦ E₁' x ⊗[𝕜] E₂' x)
      (fun x ↦ (bundleTensorCongr e₁ e₂ x).toContinuousLinearMap)).1 <| by
        simpa only [bundleTensorCongr_toContinuousLinearMap] using
          contMDiff_bundleTensorMap
            ((contMDiff_hom_bundle_iff (IB := IB) (fun x ↦ (e₁ x).toContinuousLinearMap)).2 he₁)
            ((contMDiff_hom_bundle_iff (IB := IB) (fun x ↦ (e₂ x).toContinuousLinearMap)).2
              he₂)).congr fun _ ↦ rfl

@[simp]
theorem bundleTensorCongrDiffeomorph_apply
    (e₁ : ∀ x, E₁ x ≃L[𝕜] E₁' x) (e₂ : ∀ x, E₂ x ≃L[𝕜] E₂' x)
    (he₁ : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₁')) n
      (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₁' p.proj (e₁ p.proj p.2)))
    (he₂ : ContMDiff (IB.prod 𝓘(𝕜, F₂)) (IB.prod 𝓘(𝕜, F₂')) n
      (fun p : TotalSpace F₂ E₂ ↦ TotalSpace.mk' F₂' p.proj (e₂ p.proj p.2)))
    (p : TotalSpace (ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) :
    bundleTensorCongrDiffeomorph e₁ e₂ he₁ he₂ p =
      ⟨p.proj, bundleTensorCongr e₁ e₂ p.proj p.2⟩ := by
  rw [bundleTensorCongrDiffeomorph, bundleDiffeomorph_apply]

@[simp]
theorem bundleTensorCongrDiffeomorph_symm_apply
    (e₁ : ∀ x, E₁ x ≃L[𝕜] E₁' x) (e₂ : ∀ x, E₂ x ≃L[𝕜] E₂' x)
    (he₁ : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₁')) n
      (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₁' p.proj (e₁ p.proj p.2)))
    (he₂ : ContMDiff (IB.prod 𝓘(𝕜, F₂)) (IB.prod 𝓘(𝕜, F₂')) n
      (fun p : TotalSpace F₂ E₂ ↦ TotalSpace.mk' F₂' p.proj (e₂ p.proj p.2)))
    (p : TotalSpace (ProjectiveTensor 𝕜 F₁' F₂') (fun x ↦ E₁' x ⊗[𝕜] E₂' x)) :
    (bundleTensorCongrDiffeomorph e₁ e₂ he₁ he₂).symm p =
      ⟨p.proj, (bundleTensorCongr e₁ e₂ p.proj).symm p.2⟩ := by
  rw [bundleTensorCongrDiffeomorph, bundleDiffeomorph_symm_apply]

@[simp]
theorem toHomeomorph_bundleTensorCongrDiffeomorph
    (e₁ : ∀ x, E₁ x ≃L[𝕜] E₁' x) (e₂ : ∀ x, E₂ x ≃L[𝕜] E₂' x)
    (he₁ : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₁')) n
      (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₁' p.proj (e₁ p.proj p.2)))
    (he₂ : ContMDiff (IB.prod 𝓘(𝕜, F₂)) (IB.prod 𝓘(𝕜, F₂')) n
      (fun p : TotalSpace F₂ E₂ ↦ TotalSpace.mk' F₂' p.proj (e₂ p.proj p.2))) :
    (bundleTensorCongrDiffeomorph e₁ e₂ he₁ he₂).toHomeomorph =
      bundleTensorCongrHomeomorph e₁ e₂ he₁.continuous he₂.continuous :=
  Homeomorph.ext fun p ↦ by simp

end MapSmooth

section CommSmooth

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] {n : WithTop ℕ∞}
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]
  [∀ x, TopologicalSpace (E₂ x ⊗[𝕜] E₁ x)] [∀ x, IsModuleTopology 𝕜 (E₂ x ⊗[𝕜] E₁ x)]

/-- `bundleTensorCommEquiv` defines a `C^n` section of the Hom bundle
`(E₁ ⊗ E₂) →L (E₂ ⊗ E₁)`. -/
theorem contMDiff_bundleTensorComm :
    ContMDiff IB (IB.prod 𝓘(𝕜, ProjectiveTensor 𝕜 F₁ F₂ →L[𝕜] ProjectiveTensor 𝕜 F₂ F₁)) n
      (fun x ↦ TotalSpace.mk'
        (ProjectiveTensor 𝕜 F₁ F₂ →L[𝕜] ProjectiveTensor 𝕜 F₂ F₁)
        (E := fun y ↦ E₁ y ⊗[𝕜] E₂ y →L[𝕜] E₂ y ⊗[𝕜] E₁ y)
        x (bundleTensorCommEquiv x).toContinuousLinearMap) :=
  contMDiff_hom_bundle_of_inCoordinates_eq_const
    (c := fun _ ↦ (ProjectiveTensor.comm 𝕜 F₁ F₂).toLinearIsometry.toContinuousLinearMap)
    fun a x hx₁₂ _ ↦ by
      rw [tensorProduct_trivializationAt_baseSet] at hx₁₂
      exact bundleTensorCommEquiv_inCoordinates a x hx₁₂.1 hx₁₂.2

variable (IB n F₁ E₁ F₂ E₂) in
/-- Canonical symmetry `C^n` diffeomorphism between the total spaces of `E₁ ⊗ E₂` and `E₂ ⊗ E₁`. -/
def bundleTensorCommDiffeomorph :
    TotalSpace (ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)
      ≃ₘ^n⟮IB.prod 𝓘(𝕜, ProjectiveTensor 𝕜 F₁ F₂), IB.prod 𝓘(𝕜, ProjectiveTensor 𝕜 F₂ F₁)⟯
      TotalSpace (ProjectiveTensor 𝕜 F₂ F₁) (fun x ↦ E₂ x ⊗[𝕜] E₁ x) :=
  bundleDiffeomorph
    (F₁ := ProjectiveTensor 𝕜 F₁ F₂) (F₂ := ProjectiveTensor 𝕜 F₂ F₁)
    (E₁ := fun x ↦ E₁ x ⊗[𝕜] E₂ x) (E₂ := fun x ↦ E₂ x ⊗[𝕜] E₁ x)
    bundleTensorCommEquiv <|
    ((contMDiff_hom_bundle_iff (IB := IB)
      (F₁ := ProjectiveTensor 𝕜 F₁ F₂) (F₂ := ProjectiveTensor 𝕜 F₂ F₁)
      (E₁ := fun x ↦ E₁ x ⊗[𝕜] E₂ x) (E₂ := fun x ↦ E₂ x ⊗[𝕜] E₁ x)
      (fun x ↦ (bundleTensorCommEquiv x).toContinuousLinearMap)).1
      contMDiff_bundleTensorComm).congr fun _ ↦ rfl

@[simp]
theorem bundleTensorCommDiffeomorph_apply
    (p : TotalSpace (ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) :
    bundleTensorCommDiffeomorph IB n F₁ E₁ F₂ E₂ p =
      ⟨p.proj, bundleTensorCommEquiv p.proj p.2⟩ := by
  rw [bundleTensorCommDiffeomorph, bundleDiffeomorph_apply]

@[simp]
theorem bundleTensorCommDiffeomorph_symm_apply
    (p : TotalSpace (ProjectiveTensor 𝕜 F₂ F₁) (fun x ↦ E₂ x ⊗[𝕜] E₁ x)) :
    (bundleTensorCommDiffeomorph IB n F₁ E₁ F₂ E₂).symm p =
      ⟨p.proj, (bundleTensorCommEquiv p.proj).symm p.2⟩ := by
  rw [bundleTensorCommDiffeomorph, bundleDiffeomorph_symm_apply]

@[simp]
theorem toHomeomorph_bundleTensorCommDiffeomorph :
    (bundleTensorCommDiffeomorph IB n F₁ E₁ F₂ E₂).toHomeomorph =
      bundleTensorCommHomeomorph F₁ E₁ F₂ E₂ :=
  Homeomorph.ext fun p ↦ by simp

end CommSmooth

section AssocSmooth

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] {n : WithTop ℕ∞}
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] [FiniteDimensional 𝕜 F₃]
  {E₃ : B → Type*} [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜 (E₃ x)] [∀ x, TopologicalSpace (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)] [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]
  [∀ x, TopologicalSpace (E₂ x ⊗[𝕜] E₃ x)] [∀ x, IsModuleTopology 𝕜 (E₂ x ⊗[𝕜] E₃ x)]
  [∀ x, TopologicalSpace ((E₁ x ⊗[𝕜] E₂ x) ⊗[𝕜] E₃ x)]
  [∀ x, IsModuleTopology 𝕜 ((E₁ x ⊗[𝕜] E₂ x) ⊗[𝕜] E₃ x)]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] (E₂ x ⊗[𝕜] E₃ x))]
  [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] (E₂ x ⊗[𝕜] E₃ x))]

/-- `bundleTensorAssocEquiv` defines a `C^n` section of the Hom bundle
`((E₁ ⊗ E₂) ⊗ E₃) →L (E₁ ⊗ (E₂ ⊗ E₃))`. -/
theorem contMDiff_bundleTensorAssoc :
    ContMDiff IB
      (IB.prod 𝓘(𝕜, ProjectiveTensor 𝕜 (ProjectiveTensor 𝕜 F₁ F₂) F₃ →L[𝕜]
        ProjectiveTensor 𝕜 F₁ (ProjectiveTensor 𝕜 F₂ F₃))) n
      (fun x ↦ TotalSpace.mk'
        (ProjectiveTensor 𝕜 (ProjectiveTensor 𝕜 F₁ F₂) F₃ →L[𝕜]
          ProjectiveTensor 𝕜 F₁ (ProjectiveTensor 𝕜 F₂ F₃))
        (E := fun y ↦ ((E₁ y ⊗[𝕜] E₂ y) ⊗[𝕜] E₃ y) →L[𝕜] (E₁ y ⊗[𝕜] (E₂ y ⊗[𝕜] E₃ y)))
        x (bundleTensorAssocEquiv x).toContinuousLinearMap) :=
  contMDiff_hom_bundle_of_inCoordinates_eq_const
    (c := fun _ ↦ (ProjectiveTensor.assoc 𝕜 F₁ F₂ F₃).toLinearIsometry.toContinuousLinearMap)
    fun a x hx_left _ ↦ by
      rw [tensorProduct_trivializationAt_baseSet,
        tensorProduct_trivializationAt_baseSet] at hx_left
      exact bundleTensorAssocEquiv_inCoordinates a x hx_left.1.1 hx_left.1.2 hx_left.2

variable (IB n F₁ E₁ F₂ E₂ F₃ E₃) in
/-- Canonical associativity `C^n` diffeomorphism between the total spaces of `(E₁ ⊗ E₂) ⊗ E₃` and
`E₁ ⊗ (E₂ ⊗ E₃)`. -/
def bundleTensorAssocDiffeomorph :
    TotalSpace (ProjectiveTensor 𝕜 (ProjectiveTensor 𝕜 F₁ F₂) F₃)
        (fun x ↦ (E₁ x ⊗[𝕜] E₂ x) ⊗[𝕜] E₃ x)
      ≃ₘ^n⟮IB.prod 𝓘(𝕜, ProjectiveTensor 𝕜 (ProjectiveTensor 𝕜 F₁ F₂) F₃),
        IB.prod 𝓘(𝕜, ProjectiveTensor 𝕜 F₁ (ProjectiveTensor 𝕜 F₂ F₃))⟯
      TotalSpace (ProjectiveTensor 𝕜 F₁ (ProjectiveTensor 𝕜 F₂ F₃))
        (fun x ↦ E₁ x ⊗[𝕜] (E₂ x ⊗[𝕜] E₃ x)) :=
  bundleDiffeomorph
    (F₁ := ProjectiveTensor 𝕜 (ProjectiveTensor 𝕜 F₁ F₂) F₃)
    (F₂ := ProjectiveTensor 𝕜 F₁ (ProjectiveTensor 𝕜 F₂ F₃))
    (E₁ := fun x ↦ (E₁ x ⊗[𝕜] E₂ x) ⊗[𝕜] E₃ x)
    (E₂ := fun x ↦ E₁ x ⊗[𝕜] (E₂ x ⊗[𝕜] E₃ x))
    bundleTensorAssocEquiv <|
    ((contMDiff_hom_bundle_iff (IB := IB)
      (F₁ := ProjectiveTensor 𝕜 (ProjectiveTensor 𝕜 F₁ F₂) F₃)
      (F₂ := ProjectiveTensor 𝕜 F₁ (ProjectiveTensor 𝕜 F₂ F₃))
      (E₁ := fun x ↦ (E₁ x ⊗[𝕜] E₂ x) ⊗[𝕜] E₃ x)
      (E₂ := fun x ↦ E₁ x ⊗[𝕜] (E₂ x ⊗[𝕜] E₃ x))
      (fun x ↦ (bundleTensorAssocEquiv x).toContinuousLinearMap)).1
      contMDiff_bundleTensorAssoc).congr fun _ ↦ rfl

@[simp]
theorem bundleTensorAssocDiffeomorph_apply
    (p : TotalSpace (ProjectiveTensor 𝕜 (ProjectiveTensor 𝕜 F₁ F₂) F₃)
      (fun x ↦ (E₁ x ⊗[𝕜] E₂ x) ⊗[𝕜] E₃ x)) :
    bundleTensorAssocDiffeomorph IB n F₁ E₁ F₂ E₂ F₃ E₃ p =
      ⟨p.proj, bundleTensorAssocEquiv p.proj p.2⟩ := by
  rw [bundleTensorAssocDiffeomorph, bundleDiffeomorph_apply]

@[simp]
theorem bundleTensorAssocDiffeomorph_symm_apply
    (p : TotalSpace (ProjectiveTensor 𝕜 F₁ (ProjectiveTensor 𝕜 F₂ F₃))
      (fun x ↦ E₁ x ⊗[𝕜] (E₂ x ⊗[𝕜] E₃ x))) :
    (bundleTensorAssocDiffeomorph IB n F₁ E₁ F₂ E₂ F₃ E₃).symm p =
      ⟨p.proj, (bundleTensorAssocEquiv p.proj).symm p.2⟩ := by
  rw [bundleTensorAssocDiffeomorph, bundleDiffeomorph_symm_apply]

@[simp]
theorem toHomeomorph_bundleTensorAssocDiffeomorph :
    (bundleTensorAssocDiffeomorph IB n F₁ E₁ F₂ E₂ F₃ E₃).toHomeomorph =
      bundleTensorAssocHomeomorph F₁ E₁ F₂ E₂ F₃ E₃ :=
  Homeomorph.ext fun p ↦ by simp

end AssocSmooth

section DualTensorHomSmooth

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] {n : WithTop ℕ∞}
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, TopologicalSpace (StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x)]
  [∀ x, IsModuleTopology 𝕜 (StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x)]

/-- `bundleDualTensorHom` induces a `C^n` map on total spaces from `StrongDual 𝕜 E₁ ⊗ E₂` to
`E₁ →L E₂`. -/
theorem contMDiff_bundleDualTensorHom :
    ContMDiff (IB.prod 𝓘(𝕜, ProjectiveTensor 𝕜 (StrongDual 𝕜 F₁) F₂))
      (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun p : TotalSpace (ProjectiveTensor 𝕜 (StrongDual 𝕜 F₁) F₂)
          (fun x ↦ StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x) ↦
        TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x)
          p.proj (bundleDualTensorHom p.proj p.2)) := by
  have : ∀ x, ContinuousAdd (E₁ x →L[𝕜] E₂ x) := fun _ ↦ inferInstance
  refine (contMDiff_hom_bundle_iff (IB := IB)
    (F₁ := ProjectiveTensor 𝕜 (StrongDual 𝕜 F₁) F₂) (F₂ := F₁ →L[𝕜] F₂)
    (E₁ := fun x ↦ StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x) (E₂ := fun x ↦ E₁ x →L[𝕜] E₂ x)
    (bundleDualTensorHom (𝕜 := 𝕜) (E₁ := E₁) (E₂ := E₂))).1 ?_
  exact contMDiff_hom_bundle_of_inCoordinates_eq_const (I := IB)
    (V := fun x ↦ StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x) (W := fun x ↦ E₁ x →L[𝕜] E₂ x)
    (c := fun _ ↦ ProjectiveTensor.toOperator 𝕜 F₁ F₂)
    fun a x _ hx_hom ↦ by
      rw [hom_trivializationAt_baseSet] at hx_hom
      exact bundleDualTensorHom_inCoordinates a x hx_hom.1 hx_hom.2

variable (IB n F₁ E₁ F₂ E₂) in
/-- Canonical `C^n` diffeomorphism between the total space of `StrongDual 𝕜 E₁ ⊗ E₂` and the total
space of the Hom bundle `E₁ →L E₂`. -/
def bundleDualTensorHomDiffeomorph :
    TotalSpace (ProjectiveTensor 𝕜 (StrongDual 𝕜 F₁) F₂)
        (fun x ↦ StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x)
      ≃ₘ^n⟮IB.prod 𝓘(𝕜, ProjectiveTensor 𝕜 (StrongDual 𝕜 F₁) F₂), IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)⟯
      TotalSpace (F₁ →L[𝕜] F₂) (fun x ↦ E₁ x →L[𝕜] E₂ x) :=
  have : ∀ x, ContinuousAdd (E₁ x →L[𝕜] E₂ x) := fun _ ↦ inferInstance
  bundleDiffeomorph
    (F₁ := ProjectiveTensor 𝕜 (StrongDual 𝕜 F₁) F₂) (F₂ := F₁ →L[𝕜] F₂)
    (E₁ := fun x ↦ StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x) (E₂ := fun x ↦ E₁ x →L[𝕜] E₂ x)
    (bundleDualTensorHomEquiv 𝕜 F₁ F₂)
    (contMDiff_bundleDualTensorHom.congr fun p ↦
      congr_arg (TotalSpace.mk' _ _)
        (DFunLike.congr_fun (bundleDualTensorHomEquiv_toContinuousLinearMap p.proj) p.2))

@[simp]
theorem bundleDualTensorHomDiffeomorph_apply
    (p : TotalSpace (ProjectiveTensor 𝕜 (StrongDual 𝕜 F₁) F₂)
      (fun x ↦ StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x)) :
    bundleDualTensorHomDiffeomorph IB n F₁ E₁ F₂ E₂ p =
      ⟨p.proj, bundleDualTensorHomEquiv 𝕜 F₁ F₂ p.proj p.2⟩ := by
  have : ∀ x, ContinuousAdd (E₁ x →L[𝕜] E₂ x) := fun _ ↦ inferInstance
  rw [bundleDualTensorHomDiffeomorph, bundleDiffeomorph_apply]

@[simp]
theorem bundleDualTensorHomDiffeomorph_symm_apply
    (p : TotalSpace (F₁ →L[𝕜] F₂) (fun x ↦ E₁ x →L[𝕜] E₂ x)) :
    (bundleDualTensorHomDiffeomorph IB n F₁ E₁ F₂ E₂).symm p =
      ⟨p.proj, (bundleDualTensorHomEquiv 𝕜 F₁ F₂ p.proj).symm p.2⟩ := by
  have : ∀ x, ContinuousAdd (E₁ x →L[𝕜] E₂ x) := fun _ ↦ inferInstance
  rw [bundleDualTensorHomDiffeomorph, bundleDiffeomorph_symm_apply]

@[simp]
theorem toHomeomorph_bundleDualTensorHomDiffeomorph :
    (bundleDualTensorHomDiffeomorph IB n F₁ E₁ F₂ E₂).toHomeomorph =
      bundleDualTensorHomHomeomorph F₁ E₁ F₂ E₂ :=
  Homeomorph.ext fun p ↦ by simp

end DualTensorHomSmooth

end TauCeti

/-! ### Equivalence of bundled `C^n` sections `(E₁* ⊗ E₂) ≃ₗ[𝕜] (E₁ →L E₂)` -/

namespace ContMDiffSection

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  (IB : ModelWithCorners 𝕜 EB HB) [TopologicalSpace B] [ChartedSpace HB B] (n : ℕ∞ω)
  (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  (E₁ : B → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  (E₂ : B → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, TopologicalSpace (StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x)]
  [∀ x, IsModuleTopology 𝕜 (StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x)]

/-- Canonical `𝕜`-linear equivalence between bundled `C^n` sections of `StrongDual 𝕜 E₁ ⊗ E₂` and
bundled `C^n` sections of the Hom bundle `E₁ →L E₂` for finite-rank vector bundles. -/
def dualTensorHomEquiv :
    Cₛ^n⟮IB; TauCeti.ProjectiveTensor 𝕜 (StrongDual 𝕜 F₁) F₂,
      fun x ↦ StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x⟯ ≃ₗ[𝕜]
      Cₛ^n⟮IB; F₁ →L[𝕜] F₂, fun x ↦ E₁ x →L[𝕜] E₂ x⟯ :=
  let Φ := TauCeti.bundleDualTensorHomDiffeomorph IB n F₁ E₁ F₂ E₂
  { toFun s :=
      ⟨fun x ↦ TauCeti.bundleDualTensorHomEquiv 𝕜 F₁ F₂ x (s x),
        (Φ.contMDiff.comp s.contMDiff).congr fun x ↦ by simp [Φ]⟩
    invFun t :=
      ⟨fun x ↦ (TauCeti.bundleDualTensorHomEquiv 𝕜 F₁ F₂ x).symm (t x),
        (Φ.symm.contMDiff.comp t.contMDiff).congr fun x ↦ by simp [Φ]⟩
    left_inv s := by ext x; simp
    right_inv t := by ext x; simp
    map_add' s₁ s₂ := by ext x; simp
    map_smul' c s := by ext x; simp }

variable {IB n F₁ E₁ F₂ E₂}

@[simp]
theorem dualTensorHomEquiv_apply
    (s : Cₛ^n⟮IB; TauCeti.ProjectiveTensor 𝕜 (StrongDual 𝕜 F₁) F₂,
      fun x ↦ StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x⟯) (x : B) :
    dualTensorHomEquiv IB n F₁ E₁ F₂ E₂ s x =
      TauCeti.bundleDualTensorHomEquiv 𝕜 F₁ F₂ x (s x) :=
  (rfl)

@[simp]
theorem dualTensorHomEquiv_symm_apply
    (t : Cₛ^n⟮IB; F₁ →L[𝕜] F₂, fun x ↦ E₁ x →L[𝕜] E₂ x⟯) (x : B) :
    (dualTensorHomEquiv IB n F₁ E₁ F₂ E₂).symm t x =
      (TauCeti.bundleDualTensorHomEquiv 𝕜 F₁ F₂ x).symm (t x) :=
  (rfl)

theorem dualTensorHomEquiv_tmul_apply
    (α : Cₛ^n⟮IB; StrongDual 𝕜 F₁, fun x ↦ StrongDual 𝕜 (E₁ x)⟯)
    (s : Cₛ^n⟮IB; F₂, E₂⟯) (x : B) (v : E₁ x) :
    dualTensorHomEquiv IB n F₁ E₁ F₂ E₂ (tmul α s) x v = α x v • s x := by
  simp

end ContMDiffSection

end
