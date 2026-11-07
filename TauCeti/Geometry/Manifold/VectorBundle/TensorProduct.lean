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
bundle `fun x ↦ E₁ x ⊗[𝕜] E₂ x` is a `C^n` vector bundle (`ContMDiffVectorBundle.tensorProduct`).
This file also establishes chart and coordinate smoothness criteria, `C^n` regularity of pure
tensors (`ContMDiffWithinAt.tmul_section`, `ContMDiffSection.tmul`), the `C^n` universal property
(`TauCeti.contMDiff_bundleTensorLift_iff`), and functoriality, symmetry, associativity, and
dual-tensor-Hom diffeomorphisms (`ContMDiffSection.dualTensorHomEquiv`).

## References
* [J. M. Lee, *Introduction to Smooth Manifolds* (2nd ed.), Chapters 10 and 12][lee2013]
-/

public section
noncomputable section
open Bundle Set OpenPartialHomeomorph Pretrivialization
open scoped Manifold Bundle Topology ContDiff TensorProduct

section ManifoldBundles
variable {𝕜 B M EB : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] {n : WithTop ℕ∞}
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
local notation "PF₁F₂" => TauCeti.ProjectiveTensor 𝕜 F₁ F₂
local notation "TE₁E₂" => fun x : B ↦ E₁ x ⊗[𝕜] E₂ x

section SmoothPrebundle
variable {e₁ e₁' : Trivialization F₁ (π F₁ E₁)} {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}
theorem contMDiffOn_tensorProductCoordChange
    [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    ContMDiffOn IB 𝓘(𝕜, PF₁F₂ →L[𝕜] PF₁F₂) n (tensorProductCoordChange 𝕜 e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  let s := e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)
  have h₁ := (contMDiffOn_coordChangeL (IB := IB) e₁ e₁' (n := n)).mono
    fun (_ : B) (hb : _ ∈ s) ↦ ⟨hb.1.1, hb.2.1⟩
  have h₂ := (contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := n)).mono
    fun (_ : B) (hb : _ ∈ s) ↦ ⟨hb.1.2, hb.2.2⟩
  exact ContMDiffOn.congr (fun b hb ↦
    ((TauCeti.ProjectiveTensor.mapCLM 𝕜 F₁ F₁ F₂ F₂).contDiff.comp_contMDiffWithinAt
      (h₁ b hb)).clm_apply (h₂ b hb)) fun _ _ ↦ by simp [tensorProductCoordChange_eq]
theorem mdifferentiableOn_tensorProductCoordChange
    [ContMDiffVectorBundle 1 F₁ E₁ IB] [ContMDiffVectorBundle 1 F₂ E₂ IB]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    MDifferentiableOn IB 𝓘(𝕜, PF₁F₂ →L[𝕜] PF₁F₂) (tensorProductCoordChange 𝕜 e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) :=
  (contMDiffOn_tensorProductCoordChange (IB := IB) (n := 1)).mdifferentiableOn one_ne_zero
end SmoothPrebundle

variable [FiniteDimensional 𝕜 F₂]
section FiniteRankCharts
variable [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]
@[simp] theorem chartAt_tensorProduct (y₀ y : TotalSpace PF₁F₂ TE₁E₂) :
    chartAt (ModelProd HB PF₁F₂) y₀ y =
      (chartAt HB y₀.1 y.1, TensorProduct.inCoordinates F₁ E₁ F₂ E₂ y₀.1 y.1 y₀.1 y.1 y.2) := by
  rw [FiberBundle.chartedSpace_chartAt, trans_apply, OpenPartialHomeomorph.prod_apply,
    Trivialization.coe_coe, OpenPartialHomeomorph.refl_apply, Function.id_def,
    tensorProduct_trivializationAt_apply]
theorem contMDiffWithinAt_tensorProduct_bundle (f : M → TotalSpace PF₁F₂ TE₁E₂) {s : Set M}
    {x₀ : M} : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, PF₁F₂)) n f s x₀ ↔
      ContMDiffWithinAt IM IB n (fun x ↦ (f x).1) s x₀ ∧ ContMDiffWithinAt IM 𝓘(𝕜, PF₁F₂) n
        (fun x ↦ TensorProduct.inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2)
        s x₀ := by
  simpa only [tensorProduct_trivializationAt_apply] using contMDiffWithinAt_totalSpace (IB := IB)
    (IM := IM) (n := n) (F := PF₁F₂) (E := TE₁E₂) (f := f) (s := s) (x₀ := x₀)
theorem contMDiffAt_tensorProduct_bundle (f : M → TotalSpace PF₁F₂ TE₁E₂) {x₀ : M} :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, PF₁F₂)) n f x₀ ↔
      ContMDiffAt IM IB n (fun x ↦ (f x).1) x₀ ∧ ContMDiffAt IM 𝓘(𝕜, PF₁F₂) n
        (fun x ↦ TensorProduct.inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2)
        x₀ := by
  simpa only [← contMDiffWithinAt_univ] using
    contMDiffWithinAt_tensorProduct_bundle (IB := IB) (IM := IM) (n := n) f (s := univ) (x₀ := x₀)
theorem mdifferentiableWithinAt_tensorProduct_bundle (f : M → TotalSpace PF₁F₂ TE₁E₂) {s : Set M}
    {x₀ : M} : MDifferentiableWithinAt IM (IB.prod 𝓘(𝕜, PF₁F₂)) f s x₀ ↔
      MDifferentiableWithinAt IM IB (fun x ↦ (f x).1) s x₀ ∧ MDifferentiableWithinAt IM 𝓘(𝕜, PF₁F₂)
        (fun x ↦ TensorProduct.inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2)
        s x₀ := by
  simpa only [tensorProduct_trivializationAt_apply] using
    mdifferentiableWithinAt_totalSpace IB (IM := IM) (F := PF₁F₂) (E := TE₁E₂) f (s := s) (x₀ := x₀)
theorem mdifferentiableAt_tensorProduct_bundle (f : M → TotalSpace PF₁F₂ TE₁E₂) {x₀ : M} :
    MDifferentiableAt IM (IB.prod 𝓘(𝕜, PF₁F₂)) f x₀ ↔
      MDifferentiableAt IM IB (fun x ↦ (f x).1) x₀ ∧ MDifferentiableAt IM 𝓘(𝕜, PF₁F₂)
        (fun x ↦ TensorProduct.inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2)
        x₀ := by
  simpa only [← mdifferentiableWithinAt_univ] using
    mdifferentiableWithinAt_tensorProduct_bundle (IB := IB) (IM := IM) f (s := univ) (x₀ := x₀)

section IsContMDiff
variable [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]

instance Bundle.TensorProduct.vectorPrebundle.isContMDiff :
    (Bundle.TensorProduct.vectorPrebundle 𝕜 F₁ E₁ F₂ E₂).IsContMDiff IB n where
  exists_contMDiffCoordChange := by
    intro _ he _ he'
    rcases (Bundle.TensorProduct.mem_pretrivializationAtlas_iff 𝕜 F₁ E₁ F₂ E₂).1 he with
      ⟨e₁, e₂, _, _, rfl⟩
    rcases (Bundle.TensorProduct.mem_pretrivializationAtlas_iff 𝕜 F₁ E₁ F₂ E₂).1 he' with
      ⟨e₁', e₂', _, _, rfl⟩
    exact ⟨tensorProductCoordChange 𝕜 e₁ e₁' e₂ e₂',
      by simpa only [Pretrivialization.tensorProduct_baseSet] using
        (contMDiffOn_tensorProductCoordChange (IB := IB) (n := n)
          (e₁ := e₁) (e₁' := e₁') (e₂ := e₂) (e₂' := e₂')),
      by simpa only [Pretrivialization.tensorProduct_baseSet] using
        tensorProductCoordChange_apply 𝕜 e₁ e₁' e₂ e₂'⟩

instance ContMDiffVectorBundle.tensorProduct : ContMDiffVectorBundle n PF₁F₂ TE₁E₂ IB :=
  (Bundle.TensorProduct.vectorPrebundle 𝕜 F₁ E₁ F₂ E₂).contMDiffVectorBundle IB
end IsContMDiff
end FiniteRankCharts

section PureTensorSmooth
variable [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]

theorem TauCeti.contMDiff_bundleTmul :
    ContMDiff IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] PF₁F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] PF₁F₂)
        (E := fun y ↦ E₁ y →L[𝕜] E₂ y →L[𝕜] TE₁E₂ y) x (TauCeti.bundleTmul F₁ F₂ x)) :=
  TauCeti.contMDiff_hom_bundle_of_inCoordinates_eq_const
    (c := fun _ ↦ TauCeti.ProjectiveTensor.tmulL 𝕜 F₁ F₂)
    fun a x hx₁ hx₂ ↦ TauCeti.bundleTmul_inCoordinates a x hx₁
      (by rw [hom_trivializationAt_baseSet] at hx₂; exact hx₂.1)

variable {b : M → B} {v : ∀ m, E₁ (b m)} {w : ∀ m, E₂ (b m)} {s : Set M} {x : M}

theorem ContMDiffWithinAt.tmul_section
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₁)) n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s x)
    (hw : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₂)) n (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) s x) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, PF₁F₂)) n
      (fun m ↦ TotalSpace.mk' PF₁F₂ (E := TE₁E₂) (b m) (v m ⊗ₜ[𝕜] w m)) s x := by
  have hb : ContMDiffWithinAt IM IB n b s x :=
    (contMDiffAt_proj E₁).comp_contMDiffWithinAt x hv
  have htmul : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] PF₁F₂)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] PF₁F₂)
        (E := fun y ↦ E₁ y →L[𝕜] E₂ y →L[𝕜] TE₁E₂ y) (b m) (TauCeti.bundleTmul F₁ F₂ (b m))) s x :=
    (TauCeti.contMDiff_bundleTmul (IB := IB) (n := n) (F₁ := F₁) (F₂ := F₂)
      (b x)).comp_contMDiffWithinAt x hb
  simpa only [TauCeti.bundleTmul_apply] using htmul.clm_bundle_apply₂ (F₁ := F₁) (F₂ := F₂)
    (F₃ := PF₁F₂) (E₁ := E₁) (E₂ := E₂) (E₃ := TE₁E₂) hv hw

theorem ContMDiffAt.tmul_section
    (hv : ContMDiffAt IM (IB.prod 𝓘(𝕜, F₁)) n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x)
    (hw : ContMDiffAt IM (IB.prod 𝓘(𝕜, F₂)) n (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) x) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, PF₁F₂)) n
      (fun m ↦ TotalSpace.mk' PF₁F₂ (E := TE₁E₂) (b m) (v m ⊗ₜ[𝕜] w m)) x := by
  rw [← contMDiffWithinAt_univ] at hv hw ⊢; exact hv.tmul_section hw

theorem ContMDiffOn.tmul_section
    (hv : ContMDiffOn IM (IB.prod 𝓘(𝕜, F₁)) n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s)
    (hw : ContMDiffOn IM (IB.prod 𝓘(𝕜, F₂)) n (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) s) :
    ContMDiffOn IM (IB.prod 𝓘(𝕜, PF₁F₂)) n
      (fun m ↦ TotalSpace.mk' PF₁F₂ (E := TE₁E₂) (b m) (v m ⊗ₜ[𝕜] w m)) s :=
  fun m hm ↦ (hv m hm).tmul_section (hw m hm)

theorem ContMDiff.tmul_section
    (hv : ContMDiff IM (IB.prod 𝓘(𝕜, F₁)) n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)))
    (hw : ContMDiff IM (IB.prod 𝓘(𝕜, F₂)) n (fun m ↦ TotalSpace.mk' F₂ (b m) (w m))) :
    ContMDiff IM (IB.prod 𝓘(𝕜, PF₁F₂)) n
      (fun m ↦ TotalSpace.mk' PF₁F₂ (E := TE₁E₂) (b m) (v m ⊗ₜ[𝕜] w m)) :=
  fun m ↦ (hv m).tmul_section (hw m)
end PureTensorSmooth

namespace TauCeti

private def bundleDiffeomorphOfHom {G₁ G₂ : Type*}
    [NormedAddCommGroup G₁] [NormedSpace 𝕜 G₁] [FiniteDimensional 𝕜 G₁]
    [NormedAddCommGroup G₂] [NormedSpace 𝕜 G₂] {V₁ V₂ : B → Type*}
    [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
    [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul 𝕜 (V₁ x)]
    [TopologicalSpace (TotalSpace G₁ V₁)] [FiberBundle G₁ V₁] [VectorBundle 𝕜 G₁ V₁]
    [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
    [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul 𝕜 (V₂ x)]
    [TopologicalSpace (TotalSpace G₂ V₂)] [FiberBundle G₂ V₂] [VectorBundle 𝕜 G₂ V₂]
    (e : ∀ x, V₁ x ≃L[𝕜] V₂ x)
    (he : ContMDiff IB (IB.prod 𝓘(𝕜, G₁ →L[𝕜] G₂)) n
      (fun x ↦ TotalSpace.mk' (G₁ →L[𝕜] G₂) (E := fun y ↦ V₁ y →L[𝕜] V₂ y)
        x (e x).toContinuousLinearMap)) :
    TotalSpace G₁ V₁ ≃ₘ^n⟮IB.prod 𝓘(𝕜, G₁), IB.prod 𝓘(𝕜, G₂)⟯ TotalSpace G₂ V₂ :=
  bundleDiffeomorph e
    (((contMDiff_hom_bundle_iff (IB := IB) (fun x ↦ (e x).toContinuousLinearMap)).1 he).congr
      fun _ ↦ rfl)

section LiftSmooth

variable {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] {E₃ : B → Type*}
  [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜 (E₃ x)] [∀ x, TopologicalSpace (E₃ x)]
  [∀ x, IsTopologicalAddGroup (E₃ x)] [∀ x, ContinuousSMul 𝕜 (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)] [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]

theorem contMDiffAt_bundleTensorLift_iff (Φ : ∀ x, E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x) (a : B) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, PF₁F₂ →L[𝕜] F₃)) n (fun x ↦ TotalSpace.mk' (PF₁F₂ →L[𝕜] F₃)
        (E := fun y ↦ TE₁E₂ y →L[𝕜] E₃ y) x (bundleTensorLift Φ x)) a ↔
      ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃)) n (fun x ↦ TotalSpace.mk'
        (F₁ →L[𝕜] F₂ →L[𝕜] F₃) (E := fun y ↦ E₁ y →L[𝕜] E₂ y →L[𝕜] E₃ y) x (Φ x)) a := by
  simp only [contMDiffAt_hom_bundle]; refine and_congr_right fun _ ↦ ?_
  let L := (ProjectiveTensor.liftIsometry 𝕜 F₁ F₂ F₃).toContinuousLinearEquiv
  have hev : (fun x ↦ ContinuousLinearMap.inCoordinates PF₁F₂ TE₁E₂ F₃ E₃ a x a x
      (bundleTensorLift Φ x)) =ᶠ[𝓝 a] (L ∘ fun x ↦ ContinuousLinearMap.inCoordinates F₁ E₁
        (F₂ →L[𝕜] F₃) (fun y ↦ E₂ y →L[𝕜] E₃ y) a x a x (Φ x)) := by
    filter_upwards [(trivializationAt F₁ E₁ a).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt ..),
      (trivializationAt F₂ E₂ a).open_baseSet.mem_nhds (mem_baseSet_trivializationAt ..),
      (trivializationAt F₃ E₃ a).open_baseSet.mem_nhds (mem_baseSet_trivializationAt ..)] with x
    exact bundleTensorLift_inCoordinates Φ a x
  exact ⟨fun h ↦ (L.symm.contDiff.comp_contMDiffAt
      (h.congr_of_eventuallyEq hev.symm)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ ↦ (L.symm_apply_apply _).symm),
    fun h ↦ (L.contDiff.comp_contMDiffAt h).congr_of_eventuallyEq hev⟩

theorem contMDiff_bundleTensorLift_iff (Φ : ∀ x, E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x) :
    ContMDiff IB (IB.prod 𝓘(𝕜, PF₁F₂ →L[𝕜] F₃)) n (fun x ↦ TotalSpace.mk' (PF₁F₂ →L[𝕜] F₃)
        (E := fun y ↦ TE₁E₂ y →L[𝕜] E₃ y) x (bundleTensorLift Φ x)) ↔
      ContMDiff IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃)) n (fun x ↦ TotalSpace.mk'
        (F₁ →L[𝕜] F₂ →L[𝕜] F₃) (E := fun y ↦ E₁ y →L[𝕜] E₂ y →L[𝕜] E₃ y) x (Φ x)) :=
  forall_congr' (contMDiffAt_bundleTensorLift_iff Φ)

end LiftSmooth

section MapSmooth
variable {F₁' F₂' : Type*} [NormedAddCommGroup F₁'] [NormedSpace 𝕜 F₁'] [FiniteDimensional 𝕜 F₁']
  [NormedAddCommGroup F₂'] [NormedSpace 𝕜 F₂'] [FiniteDimensional 𝕜 F₂'] {E₁' E₂' : B → Type*}
  [∀ x, AddCommGroup (E₁' x)] [∀ x, Module 𝕜 (E₁' x)] [∀ x, TopologicalSpace (E₁' x)]
  [∀ x, IsTopologicalAddGroup (E₁' x)] [∀ x, ContinuousSMul 𝕜 (E₁' x)]
  [TopologicalSpace (TotalSpace F₁' E₁')] [FiberBundle F₁' E₁'] [VectorBundle 𝕜 F₁' E₁']
  [∀ x, AddCommGroup (E₂' x)] [∀ x, Module 𝕜 (E₂' x)] [∀ x, TopologicalSpace (E₂' x)]
  [∀ x, IsTopologicalAddGroup (E₂' x)] [∀ x, ContinuousSMul 𝕜 (E₂' x)]
  [TopologicalSpace (TotalSpace F₂' E₂')] [FiberBundle F₂' E₂'] [VectorBundle 𝕜 F₂' E₂']
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]
  [∀ x, TopologicalSpace (E₁' x ⊗[𝕜] E₂' x)] [∀ x, IsModuleTopology 𝕜 (E₁' x ⊗[𝕜] E₂' x)]
local notation "PF₁'F₂'" => ProjectiveTensor 𝕜 F₁' F₂'
local notation "TE₁'E₂'" => fun x : B ↦ E₁' x ⊗[𝕜] E₂' x
local notation "LE₁" => fun y : B ↦ E₁ y →L[𝕜] E₁' y
local notation "LE₂" => fun y : B ↦ E₂ y →L[𝕜] E₂' y

theorem contMDiffWithinAt_bundleTensorMap {b : M → B}
    {f : ∀ x, E₁ x →L[𝕜] E₁' x} {g : ∀ x, E₂ x →L[𝕜] E₂' x} {s : Set M} {x₀ : M}
    (hf : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₁')) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₁') (E := LE₁) (b m) (f (b m))) s x₀)
    (hg : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₂')) n
      (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₂') (E := LE₂) (b m) (g (b m))) s x₀) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, PF₁F₂ →L[𝕜] PF₁'F₂')) n
      (fun m ↦ TotalSpace.mk' (PF₁F₂ →L[𝕜] PF₁'F₂')
        (E := fun y ↦ TE₁E₂ y →L[𝕜] TE₁'E₂' y) (b m) (bundleTensorMap f g (b m))) s x₀ := by
  simp only [contMDiffWithinAt_hom_bundle] at hf hg ⊢
  have h₁ := mem_baseSet_trivializationAt F₁ E₁ (b x₀)
  have h₁' := mem_baseSet_trivializationAt F₁' E₁' (b x₀)
  have h₂ := mem_baseSet_trivializationAt F₂ E₂ (b x₀)
  have h₂' := mem_baseSet_trivializationAt F₂' E₂' (b x₀)
  let M' := ProjectiveTensor.mapCLM 𝕜 F₁ F₁' F₂ F₂'
  refine ⟨hf.1, ((M'.contDiff.comp_contMDiffWithinAt hf.2).clm_apply hg.2).congr_of_eventuallyEq ?_
    ((bundleTensorMap_inCoordinates f g (b x₀) (b x₀) h₁ h₁' h₂ h₂').trans
      (ProjectiveTensor.mapCLM_apply _ _).symm)⟩
  filter_upwards [hf.1.continuousWithinAt.preimage_mem_nhdsWithin <| Filter.inter_mem
    (Filter.inter_mem ((trivializationAt F₁ E₁ (b x₀)).open_baseSet.mem_nhds h₁)
      ((trivializationAt F₁' E₁' (b x₀)).open_baseSet.mem_nhds h₁'))
    (Filter.inter_mem ((trivializationAt F₂ E₂ (b x₀)).open_baseSet.mem_nhds h₂)
      ((trivializationAt F₂' E₂' (b x₀)).open_baseSet.mem_nhds h₂'))] with m hm
  exact (bundleTensorMap_inCoordinates f g (b x₀) (b m) hm.1.1 hm.1.2 hm.2.1 hm.2.2).trans
    (ProjectiveTensor.mapCLM_apply _ _).symm

theorem contMDiff_bundleTensorMap {f : ∀ x, E₁ x →L[𝕜] E₁' x} {g : ∀ x, E₂ x →L[𝕜] E₂' x}
    (hf : ContMDiff IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₁')) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₁') (E := LE₁) x (f x)))
    (hg : ContMDiff IB (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₂')) n
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₂') (E := LE₂) x (g x))) :
    ContMDiff IB (IB.prod 𝓘(𝕜, PF₁F₂ →L[𝕜] PF₁'F₂')) n
      (fun x ↦ TotalSpace.mk' (PF₁F₂ →L[𝕜] PF₁'F₂')
        (E := fun y ↦ TE₁E₂ y →L[𝕜] TE₁'E₂' y) x (bundleTensorMap f g x)) := fun x ↦ by
  rw [← contMDiffWithinAt_univ]; exact contMDiffWithinAt_bundleTensorMap (IB := IB) (IM := IB)
    (b := id) (hf x).contMDiffWithinAt (hg x).contMDiffWithinAt

variable (e₁ : ∀ x, E₁ x ≃L[𝕜] E₁' x) (e₂ : ∀ x, E₂ x ≃L[𝕜] E₂' x)
  (he₁ : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₁')) n
    (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₁' p.proj (e₁ p.proj p.2)))
  (he₂ : ContMDiff (IB.prod 𝓘(𝕜, F₂)) (IB.prod 𝓘(𝕜, F₂')) n
    (fun p : TotalSpace F₂ E₂ ↦ TotalSpace.mk' F₂' p.proj (e₂ p.proj p.2)))

/-- `C^n` diffeomorphism of tensor-product total spaces induced by two `C^n` families of fibrewise
linear equivalences. -/
def bundleTensorCongrDiffeomorph :
    TotalSpace PF₁F₂ TE₁E₂ ≃ₘ^n⟮IB.prod 𝓘(𝕜, PF₁F₂), IB.prod 𝓘(𝕜, PF₁'F₂')⟯
      TotalSpace PF₁'F₂' TE₁'E₂' :=
  bundleDiffeomorphOfHom (IB := IB) (bundleTensorCongr e₁ e₂) <| by
    simpa only [bundleTensorCongr_toContinuousLinearMap] using contMDiff_bundleTensorMap
      ((contMDiff_hom_bundle_iff (IB := IB) (fun x ↦ (e₁ x).toContinuousLinearMap)).2 he₁)
      ((contMDiff_hom_bundle_iff (IB := IB) (fun x ↦ (e₂ x).toContinuousLinearMap)).2 he₂)

@[simp] theorem bundleTensorCongrDiffeomorph_apply (p : TotalSpace PF₁F₂ TE₁E₂) :
    bundleTensorCongrDiffeomorph e₁ e₂ he₁ he₂ p =
      ⟨p.proj, bundleTensorCongr e₁ e₂ p.proj p.2⟩ := by
  rw [bundleTensorCongrDiffeomorph, bundleDiffeomorphOfHom, bundleDiffeomorph_apply]

@[simp] theorem bundleTensorCongrDiffeomorph_symm_apply (p : TotalSpace PF₁'F₂' TE₁'E₂') :
    (bundleTensorCongrDiffeomorph e₁ e₂ he₁ he₂).symm p =
      ⟨p.proj, (bundleTensorCongr e₁ e₂ p.proj).symm p.2⟩ := by
  rw [bundleTensorCongrDiffeomorph, bundleDiffeomorphOfHom, bundleDiffeomorph_symm_apply]

@[simp] theorem toHomeomorph_bundleTensorCongrDiffeomorph :
    (bundleTensorCongrDiffeomorph e₁ e₂ he₁ he₂).toHomeomorph =
      bundleTensorCongrHomeomorph e₁ e₂ he₁.continuous he₂.continuous :=
  Homeomorph.ext fun p ↦ by simp
end MapSmooth

section CommSmooth
variable [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]
  [∀ x, TopologicalSpace (E₂ x ⊗[𝕜] E₁ x)] [∀ x, IsModuleTopology 𝕜 (E₂ x ⊗[𝕜] E₁ x)]
local notation "PF₂F₁" => ProjectiveTensor 𝕜 F₂ F₁
local notation "TE₂E₁" => fun x : B ↦ E₂ x ⊗[𝕜] E₁ x

theorem contMDiff_bundleTensorComm :
    ContMDiff IB (IB.prod 𝓘(𝕜, PF₁F₂ →L[𝕜] PF₂F₁)) n
      (fun x ↦ TotalSpace.mk' (PF₁F₂ →L[𝕜] PF₂F₁) (E := fun y ↦ TE₁E₂ y →L[𝕜] TE₂E₁ y)
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
  bundleDiffeomorphOfHom (IB := IB) bundleTensorCommEquiv contMDiff_bundleTensorComm

@[simp] theorem bundleTensorCommDiffeomorph_apply (p : TotalSpace PF₁F₂ TE₁E₂) :
    bundleTensorCommDiffeomorph IB n F₁ E₁ F₂ E₂ p =
      ⟨p.proj, bundleTensorCommEquiv p.proj p.2⟩ := by
  rw [bundleTensorCommDiffeomorph, bundleDiffeomorphOfHom, bundleDiffeomorph_apply]

@[simp] theorem bundleTensorCommDiffeomorph_symm_apply (p : TotalSpace PF₂F₁ TE₂E₁) :
    (bundleTensorCommDiffeomorph IB n F₁ E₁ F₂ E₂).symm p =
      ⟨p.proj, (bundleTensorCommEquiv p.proj).symm p.2⟩ := by
  rw [bundleTensorCommDiffeomorph, bundleDiffeomorphOfHom, bundleDiffeomorph_symm_apply]

@[simp] theorem toHomeomorph_bundleTensorCommDiffeomorph :
    (bundleTensorCommDiffeomorph IB n F₁ E₁ F₂ E₂).toHomeomorph =
      bundleTensorCommHomeomorph F₁ E₁ F₂ E₂ := Homeomorph.ext fun p ↦ by simp
end CommSmooth

section AssocSmooth
variable {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] [FiniteDimensional 𝕜 F₃]
  {E₃ : B → Type*} [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜 (E₃ x)] [∀ x, TopologicalSpace (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)] [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]
  [∀ x, TopologicalSpace (E₂ x ⊗[𝕜] E₃ x)] [∀ x, IsModuleTopology 𝕜 (E₂ x ⊗[𝕜] E₃ x)]
  [∀ x, TopologicalSpace ((E₁ x ⊗[𝕜] E₂ x) ⊗[𝕜] E₃ x)]
  [∀ x, IsModuleTopology 𝕜 ((E₁ x ⊗[𝕜] E₂ x) ⊗[𝕜] E₃ x)]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] (E₂ x ⊗[𝕜] E₃ x))]
  [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] (E₂ x ⊗[𝕜] E₃ x))]
local notation "PAssocL" => ProjectiveTensor 𝕜 (ProjectiveTensor 𝕜 F₁ F₂) F₃
local notation "PAssocR" => ProjectiveTensor 𝕜 F₁ (ProjectiveTensor 𝕜 F₂ F₃)
local notation "TAssocL" => fun x : B ↦ (E₁ x ⊗[𝕜] E₂ x) ⊗[𝕜] E₃ x
local notation "TAssocR" => fun x : B ↦ E₁ x ⊗[𝕜] (E₂ x ⊗[𝕜] E₃ x)

theorem contMDiff_bundleTensorAssoc :
    ContMDiff IB (IB.prod 𝓘(𝕜, PAssocL →L[𝕜] PAssocR)) n
      (fun x ↦ TotalSpace.mk' (PAssocL →L[𝕜] PAssocR) (E := fun y ↦ TAssocL y →L[𝕜] TAssocR y)
        x (bundleTensorAssocEquiv x).toContinuousLinearMap) :=
  contMDiff_hom_bundle_of_inCoordinates_eq_const
    (c := fun _ ↦ (ProjectiveTensor.assoc 𝕜 F₁ F₂ F₃).toLinearIsometry.toContinuousLinearMap)
    fun a x hx_l _ ↦ by
      rw [tensorProduct_trivializationAt_baseSet, tensorProduct_trivializationAt_baseSet] at hx_l
      exact bundleTensorAssocEquiv_inCoordinates a x hx_l.1.1 hx_l.1.2 hx_l.2

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
  bundleDiffeomorphOfHom (IB := IB) bundleTensorAssocEquiv contMDiff_bundleTensorAssoc

@[simp] theorem bundleTensorAssocDiffeomorph_apply (p : TotalSpace PAssocL TAssocL) :
    bundleTensorAssocDiffeomorph IB n F₁ E₁ F₂ E₂ F₃ E₃ p =
      ⟨p.proj, bundleTensorAssocEquiv p.proj p.2⟩ := by
  rw [bundleTensorAssocDiffeomorph, bundleDiffeomorphOfHom, bundleDiffeomorph_apply]

@[simp] theorem bundleTensorAssocDiffeomorph_symm_apply (p : TotalSpace PAssocR TAssocR) :
    (bundleTensorAssocDiffeomorph IB n F₁ E₁ F₂ E₂ F₃ E₃).symm p =
      ⟨p.proj, (bundleTensorAssocEquiv p.proj).symm p.2⟩ := by
  rw [bundleTensorAssocDiffeomorph, bundleDiffeomorphOfHom, bundleDiffeomorph_symm_apply]

@[simp] theorem toHomeomorph_bundleTensorAssocDiffeomorph :
    (bundleTensorAssocDiffeomorph IB n F₁ E₁ F₂ E₂ F₃ E₃).toHomeomorph =
      bundleTensorAssocHomeomorph F₁ E₁ F₂ E₂ F₃ E₃ := Homeomorph.ext fun p ↦ by simp
end AssocSmooth

section DualTensorHomSmooth
variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [∀ x, TopologicalSpace (StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x)]
  [∀ x, IsModuleTopology 𝕜 (StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x)]
local notation "PDual" => ProjectiveTensor 𝕜 (StrongDual 𝕜 F₁) F₂
local notation "TDual" => fun x : B ↦ StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x
local notation "LE₁E₂" => fun x : B ↦ E₁ x →L[𝕜] E₂ x

theorem contMDiff_bundleDualTensorHom :
    ContMDiff (IB.prod 𝓘(𝕜, PDual)) (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun p : TotalSpace PDual TDual ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := LE₁E₂)
        p.proj (bundleDualTensorHom p.proj p.2)) := by
  have : ∀ x, ContinuousAdd (E₁ x →L[𝕜] E₂ x) := fun _ ↦ inferInstance
  refine (contMDiff_hom_bundle_iff (IB := IB) (F₁ := PDual) (F₂ := F₁ →L[𝕜] F₂)
    (E₁ := TDual) (E₂ := LE₁E₂) (bundleDualTensorHom (𝕜 := 𝕜))).1 ?_
  exact contMDiff_hom_bundle_of_inCoordinates_eq_const (I := IB) (V := TDual) (W := LE₁E₂)
    (c := fun _ ↦ ProjectiveTensor.toOperator 𝕜 F₁ F₂) fun a x _ hx_hom ↦ by
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
  bundleDiffeomorph (F₁ := ProjectiveTensor 𝕜 (StrongDual 𝕜 F₁) F₂) (F₂ := F₁ →L[𝕜] F₂)
    (E₁ := fun x ↦ StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x) (E₂ := fun x ↦ E₁ x →L[𝕜] E₂ x)
    (bundleDualTensorHomEquiv 𝕜 F₁ F₂) (contMDiff_bundleDualTensorHom.congr fun p ↦
      congr_arg (TotalSpace.mk' _ _)
        (DFunLike.congr_fun (bundleDualTensorHomEquiv_toContinuousLinearMap p.proj) p.2))

@[simp] theorem bundleDualTensorHomDiffeomorph_apply (p : TotalSpace PDual TDual) :
    bundleDualTensorHomDiffeomorph IB n F₁ E₁ F₂ E₂ p =
      ⟨p.proj, bundleDualTensorHomEquiv 𝕜 F₁ F₂ p.proj p.2⟩ := by
  have : ∀ x, ContinuousAdd (E₁ x →L[𝕜] E₂ x) := fun _ ↦ inferInstance
  rw [bundleDualTensorHomDiffeomorph, bundleDiffeomorph_apply]

@[simp] theorem bundleDualTensorHomDiffeomorph_symm_apply
    (p : TotalSpace (F₁ →L[𝕜] F₂) LE₁E₂) :
    (bundleDualTensorHomDiffeomorph IB n F₁ E₁ F₂ E₂).symm p =
      ⟨p.proj, (bundleDualTensorHomEquiv 𝕜 F₁ F₂ p.proj).symm p.2⟩ := by
  have : ∀ x, ContinuousAdd (E₁ x →L[𝕜] E₂ x) := fun _ ↦ inferInstance
  rw [bundleDualTensorHomDiffeomorph, bundleDiffeomorph_symm_apply]

@[simp] theorem toHomeomorph_bundleDualTensorHomDiffeomorph :
    (bundleDualTensorHomDiffeomorph IB n F₁ E₁ F₂ E₂).toHomeomorph =
      bundleDualTensorHomHomeomorph F₁ E₁ F₂ E₂ := Homeomorph.ext fun p ↦ by simp
end DualTensorHomSmooth
end TauCeti
end ManifoldBundles

namespace ContMDiffSection
variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] {n : ℕ∞ω}
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

section Tmul
variable [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]

/-- The `𝕜`-bilinear pure-tensor map on bundled `C^n` sections of finite-rank vector bundles. -/
def tmul :
    Cₛ^n⟮IB; F₁, E₁⟯ →ₗ[𝕜] Cₛ^n⟮IB; F₂, E₂⟯ →ₗ[𝕜]
      Cₛ^n⟮IB; TauCeti.ProjectiveTensor 𝕜 F₁ F₂, fun x ↦ E₁ x ⊗[𝕜] E₂ x⟯ where
  toFun s :=
    { toFun t := ⟨fun x ↦ s x ⊗ₜ[𝕜] t x, s.contMDiff.tmul_section t.contMDiff⟩
      map_add' _ _ := by ext x; simp [TensorProduct.tmul_add]
      map_smul' _ _ := by ext x; simp [TensorProduct.tmul_smul] }
  map_add' _ _ := by ext t x; simp [TensorProduct.add_tmul]
  map_smul' _ _ := by ext t x; simp [TensorProduct.smul_tmul']

@[simp] theorem tmul_apply (s : Cₛ^n⟮IB; F₁, E₁⟯) (t : Cₛ^n⟮IB; F₂, E₂⟯) (x : B) :
    tmul s t x = s x ⊗ₜ[𝕜] t x := (rfl)
end Tmul

section DualTensorHom
variable [∀ x, TopologicalSpace (StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x)]
  [∀ x, IsModuleTopology 𝕜 (StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x)]
local notation "PDual" => TauCeti.ProjectiveTensor 𝕜 (StrongDual 𝕜 F₁) F₂
local notation "TDual" => fun x : B ↦ StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x

variable (IB n F₁ E₁ F₂ E₂) in
/-- Canonical `𝕜`-linear equivalence between bundled `C^n` sections of `StrongDual 𝕜 E₁ ⊗ E₂` and
bundled `C^n` sections of the Hom bundle `E₁ →L E₂` for finite-rank vector bundles. -/
def dualTensorHomEquiv :
    Cₛ^n⟮IB; TauCeti.ProjectiveTensor 𝕜 (StrongDual 𝕜 F₁) F₂,
      fun x ↦ StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x⟯ ≃ₗ[𝕜]
      Cₛ^n⟮IB; F₁ →L[𝕜] F₂, fun x ↦ E₁ x →L[𝕜] E₂ x⟯ :=
  let Φ := TauCeti.bundleDualTensorHomDiffeomorph IB n F₁ E₁ F₂ E₂
  { toFun s := ⟨fun x ↦ TauCeti.bundleDualTensorHomEquiv 𝕜 F₁ F₂ x (s x),
      (Φ.contMDiff.comp s.contMDiff).congr fun x ↦ by simp [Φ]⟩
    invFun t := ⟨fun x ↦ (TauCeti.bundleDualTensorHomEquiv 𝕜 F₁ F₂ x).symm (t x),
      (Φ.symm.contMDiff.comp t.contMDiff).congr fun x ↦ by simp [Φ]⟩
    left_inv _ := by ext x; simp
    right_inv _ := by ext x; simp
    map_add' _ _ := by ext x; simp
    map_smul' _ _ := by ext x; simp }

@[simp] theorem dualTensorHomEquiv_apply (s : Cₛ^n⟮IB; PDual, TDual⟯) (x : B) :
    dualTensorHomEquiv IB n F₁ E₁ F₂ E₂ s x =
      TauCeti.bundleDualTensorHomEquiv 𝕜 F₁ F₂ x (s x) := (rfl)

@[simp] theorem dualTensorHomEquiv_symm_apply
    (t : Cₛ^n⟮IB; F₁ →L[𝕜] F₂, fun x ↦ E₁ x →L[𝕜] E₂ x⟯) (x : B) :
    (dualTensorHomEquiv IB n F₁ E₁ F₂ E₂).symm t x =
      (TauCeti.bundleDualTensorHomEquiv 𝕜 F₁ F₂ x).symm (t x) := (rfl)

theorem dualTensorHomEquiv_tmul_apply
    (α : Cₛ^n⟮IB; StrongDual 𝕜 F₁, fun x ↦ StrongDual 𝕜 (E₁ x)⟯)
    (s : Cₛ^n⟮IB; F₂, E₂⟯) (x : B) (v : E₁ x) :
    dualTensorHomEquiv IB n F₁ E₁ F₂ E₂ (tmul α s) x v = α x v • s x := by simp
end DualTensorHom
end ContMDiffSection
end
