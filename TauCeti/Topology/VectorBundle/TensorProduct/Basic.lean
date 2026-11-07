/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.VectorBundle.Constructions
public import TauCeti.Analysis.Normed.Module.TensorProduct.FiniteDimension
public import TauCeti.Analysis.Normed.Module.TensorProduct.Map
public import TauCeti.Topology.VectorBundle.Hom

/-!
# Tensor products of finite-rank topological vector bundles

Given finite-rank vector bundles `E₁` and `E₂` over `B` with model fibres `F₁` and `F₂` over a
complete nontrivially normed field `𝕜`, this file constructs the `VectorBundle` structure on
`fun x ↦ E₁ x ⊗[𝕜] E₂ x`, modelled on `TauCeti.ProjectiveTensor 𝕜 F₁ F₂`, together with induced
trivializations (`Bundle.Trivialization.tensorProduct`), coordinate expressions
(`TensorProduct.inCoordinates`), and continuity of `TauCeti.bundleTmul` and pure-tensor sections.

Each fibre `E₁ x ⊗[𝕜] E₂ x` is assumed to carry `IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)`; opening
`TauCeti.TensorProduct` equips every `M ⊗[𝕜] N` with `moduleTopology 𝕜 (M ⊗[𝕜] N)` by default.

## References
* A. Hatcher, *Vector Bundles and K-Theory*, §1.1; J. M. Lee, *Smooth Manifolds* (2nd ed.), Ch. 12.
-/

public section

noncomputable section

open Bundle FiberBundle Set Topology
open scoped Bundle TensorProduct Topology

namespace TauCeti

section FiberTopology

variable {𝕜 M N : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜]
  [AddCommGroup M] [Module 𝕜 M] [AddCommGroup N] [Module 𝕜 N]

namespace TensorProduct

/-- Scoped default topology on `M ⊗[𝕜] N`, given by `moduleTopology 𝕜 (M ⊗[𝕜] N)`. -/
scoped instance instTopologicalSpaceTensorProduct : TopologicalSpace (M ⊗[𝕜] N) :=
  moduleTopology 𝕜 (M ⊗[𝕜] N)

scoped instance instIsModuleTopologyTensorProduct : IsModuleTopology 𝕜 (M ⊗[𝕜] N) := ⟨rfl⟩

end TensorProduct

instance instIsTopologicalAddGroupTensorProductOfIsModuleTopology
    [TopologicalSpace (M ⊗[𝕜] N)] [IsModuleTopology 𝕜 (M ⊗[𝕜] N)] :
    IsTopologicalAddGroup (M ⊗[𝕜] N) :=
  IsModuleTopology.isTopologicalAddGroup 𝕜 (M ⊗[𝕜] N)

end FiberTopology

/-- A Hom-bundle section whose coordinate expression in the preferred frames at each point is
constant on their common base set is continuous. -/
theorem continuous_hom_bundle_of_inCoordinates_eq_const {𝕜 B F₁ F₂ : Type*}
    [NontriviallyNormedField 𝕜] [TopologicalSpace B] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {V W : B → Type*}
    [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
    [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)] [∀ x, TopologicalSpace (W x)]
    [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul 𝕜 (W x)]
    [TopologicalSpace (TotalSpace F₁ V)] [FiberBundle F₁ V] [VectorBundle 𝕜 F₁ V]
    [TopologicalSpace (TotalSpace F₂ W)] [FiberBundle F₂ W] [VectorBundle 𝕜 F₂ W]
    {ϕ : ∀ x, V x →L[𝕜] W x} {c : B → F₁ →L[𝕜] F₂}
    (hϕ : ∀ a x, x ∈ (trivializationAt F₁ V a).baseSet → x ∈ (trivializationAt F₂ W a).baseSet →
      ContinuousLinearMap.inCoordinates F₁ V F₂ W a x a x (ϕ x) = c a) :
    Continuous (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) x (ϕ x)) := by
  refine continuous_iff_continuousAt.2 fun a ↦ ?_
  rw [continuousAt_hom_bundle]; refine ⟨continuousAt_id,
    (continuous_const (y := c a)).continuousAt.congr_of_eventuallyEq ?_⟩
  filter_upwards [(trivializationAt F₁ V a).open_baseSet.mem_nhds (mem_baseSet_trivializationAt ..),
    (trivializationAt F₂ W a).open_baseSet.mem_nhds (mem_baseSet_trivializationAt ..)] with x
  exact hϕ a x

end TauCeti

namespace TensorProduct

variable {𝕜 B₁ B₂ : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B₁] [TopologicalSpace B₂]
  (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] (E₁ : B₁ → Type*)
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] (E₂ : B₂ → Type*)
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

/-- Coordinate expression of a tensor in `E₁ x ⊗[𝕜] E₂ y` with respect to the preferred
trivializations centred at `x₀` and `y₀`, valued in `TauCeti.ProjectiveTensor 𝕜 F₁ F₂`. -/
def inCoordinates (x₀ x : B₁) (y₀ y : B₂) :
    E₁ x ⊗[𝕜] E₂ y →ₗ[𝕜] TauCeti.ProjectiveTensor 𝕜 F₁ F₂ :=
  (TauCeti.ProjectiveTensor.linearEquiv 𝕜 F₁ F₂).symm.toLinearMap ∘ₗ _root_.TensorProduct.map
    ((trivializationAt F₁ E₁ x₀).linearMapAt 𝕜 x) ((trivializationAt F₂ E₂ y₀).linearMapAt 𝕜 y)

variable {F₁ E₁ F₂ E₂}

@[simp] theorem inCoordinates_tmul (x₀ x : B₁) (y₀ y : B₂) (v : E₁ x) (w : E₂ y) :
    inCoordinates F₁ E₁ F₂ E₂ x₀ x y₀ y (v ⊗ₜ[𝕜] w) =
      ⟨(trivializationAt F₁ E₁ x₀).linearMapAt 𝕜 x v ⊗ₜ[𝕜]
        (trivializationAt F₂ E₂ y₀).linearMapAt 𝕜 y w⟩ := by simp [inCoordinates]

theorem inCoordinates_eq {x₀ x : B₁} {y₀ y : B₂} (hx : x ∈ (trivializationAt F₁ E₁ x₀).baseSet)
    (hy : y ∈ (trivializationAt F₂ E₂ y₀).baseSet) (u : E₁ x ⊗[𝕜] E₂ y) :
    inCoordinates F₁ E₁ F₂ E₂ x₀ x y₀ y u =
      ⟨_root_.TensorProduct.map ((trivializationAt F₁ E₁ x₀).linearEquivAt 𝕜 x hx).toLinearMap
        ((trivializationAt F₂ E₂ y₀).linearEquivAt 𝕜 y hy).toLinearMap u⟩ := by
  simp only [inCoordinates, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TauCeti.ProjectiveTensor.linearEquiv_symm_apply,
    Trivialization.linearMapAt_def_of_mem _ hx, Trivialization.linearMapAt_def_of_mem _ hy]

theorem inCoordinates_tmul_of_mem {x₀ x : B₁} {y₀ y : B₂}
    (hx : x ∈ (trivializationAt F₁ E₁ x₀).baseSet) (hy : y ∈ (trivializationAt F₂ E₂ y₀).baseSet)
    (v : E₁ x) (w : E₂ y) : inCoordinates F₁ E₁ F₂ E₂ x₀ x y₀ y (v ⊗ₜ[𝕜] w) =
      ⟨(trivializationAt F₁ E₁ x₀ ⟨x, v⟩).2 ⊗ₜ[𝕜] (trivializationAt F₂ E₂ y₀ ⟨y, w⟩).2⟩ := by
  simp [inCoordinates_eq hx hy]

end TensorProduct

section Prebundle

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {B : Type*} [TopologicalSpace B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  (e₁ e₁' : Trivialization F₁ (π F₁ E₁)) (e₂ e₂' : Trivialization F₂ (π F₂ E₂))

local notation "PF₁F₂" => TauCeti.ProjectiveTensor 𝕜 F₁ F₂
local notation "TE₁E₂" => fun x : B ↦ E₁ x ⊗[𝕜] E₂ x

namespace Bundle.Pretrivialization

section CoordChangeDef

variable [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜]

/-- Transition operator between two tensor-product pretrivializations, given on the model fibre
`ProjectiveTensor 𝕜 F₁ F₂` by `ProjectiveTensor.mapL` of the factor coordinate changes. -/
def tensorProductCoordChange (b : B) : PF₁F₂ →L[𝕜] PF₁F₂ :=
  TauCeti.ProjectiveTensor.mapL
    (e₁.coordChangeL 𝕜 e₁' b : F₁ →L[𝕜] F₁) (e₂.coordChangeL 𝕜 e₂' b : F₂ →L[𝕜] F₂)

theorem tensorProductCoordChange_eq (b : B) : tensorProductCoordChange 𝕜 e₁ e₁' e₂ e₂' b =
    TauCeti.ProjectiveTensor.mapL (e₁.coordChangeL 𝕜 e₁' b : F₁ →L[𝕜] F₁)
      (e₂.coordChangeL 𝕜 e₂' b : F₂ →L[𝕜] F₂) := (rfl)

@[simp] theorem tensorProductCoordChange_tmul (b : B) (v : F₁) (w : F₂) :
    tensorProductCoordChange 𝕜 e₁ e₁' e₂ e₂' b ⟨v ⊗ₜ[𝕜] w⟩ =
      ⟨e₁.coordChangeL 𝕜 e₁' b v ⊗ₜ[𝕜] e₂.coordChangeL 𝕜 e₂' b w⟩ := by
  simp [tensorProductCoordChange]

end CoordChangeDef

section CoordChangeContinuity

variable {𝕜 e₁ e₁' e₂ e₂'}
  [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

theorem continuousOn_tensorProductCoordChange
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    ContinuousOn (tensorProductCoordChange 𝕜 e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  have h₁ := (continuousOn_coordChange 𝕜 e₁ e₁').mono
    fun (_ : B) (hb : _ ∈ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) ↦ ⟨hb.1.1, hb.2.1⟩
  have h₂ := (continuousOn_coordChange 𝕜 e₂ e₂').mono
    fun (_ : B) (hb : _ ∈ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) ↦ ⟨hb.1.2, hb.2.2⟩
  exact (((TauCeti.ProjectiveTensor.mapCLM 𝕜 F₁ F₁ F₂ F₂).continuous.comp_continuousOn
    h₁).clm_apply h₂).congr fun _ _ ↦ by simp [tensorProductCoordChange]

end CoordChangeContinuity

variable [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜]

/-- Induced pretrivialization of `fun x ↦ E₁ x ⊗[𝕜] E₂ x` from trivializations `e₁` and `e₂`,
acting on fibres by `TensorProduct.map` of `e₁.linearMapAt` and `e₂.linearMapAt`. -/
def tensorProduct : Pretrivialization PF₁F₂ (π PF₁F₂ TE₁E₂) where
  toFun p := ⟨p.1, ⟨_root_.TensorProduct.map (e₁.linearMapAt 𝕜 p.1) (e₂.linearMapAt 𝕜 p.1) p.2⟩⟩
  invFun p := ⟨p.1, _root_.TensorProduct.map (e₁.symmₗ 𝕜 p.1) (e₂.symmₗ 𝕜 p.1) p.2.toTensorProduct⟩
  source := TotalSpace.proj ⁻¹' (e₁.baseSet ∩ e₂.baseSet)
  target := (e₁.baseSet ∩ e₂.baseSet) ×ˢ univ
  map_source' := fun ⟨_, _⟩ h ↦ ⟨h, mem_univ _⟩
  map_target' := fun ⟨_, _⟩ h ↦ h.1
  left_inv' := fun ⟨x, _⟩ ⟨h₁, h₂⟩ ↦ by
    have h₁' : e₁.symmₗ 𝕜 x ∘ₗ e₁.linearMapAt 𝕜 x = LinearMap.id :=
      LinearMap.ext (e₁.symmₗ_linearMapAt (R := 𝕜) h₁)
    have h₂' : e₂.symmₗ 𝕜 x ∘ₗ e₂.linearMapAt 𝕜 x = LinearMap.id :=
      LinearMap.ext (e₂.symmₗ_linearMapAt (R := 𝕜) h₂)
    simp only [← LinearMap.comp_apply, ← _root_.TensorProduct.map_comp, h₁', h₂',
      _root_.TensorProduct.map_id, LinearMap.id_apply]
  right_inv' := fun ⟨x, _⟩ ⟨⟨h₁, h₂⟩, _⟩ ↦ Prod.ext rfl <|
    (TauCeti.ProjectiveTensor.linearEquiv 𝕜 F₁ F₂).injective <| by
      have h₁' : e₁.linearMapAt 𝕜 x ∘ₗ e₁.symmₗ 𝕜 x = LinearMap.id :=
        LinearMap.ext (e₁.linearMapAt_symmₗ (R := 𝕜) h₁)
      have h₂' : e₂.linearMapAt 𝕜 x ∘ₗ e₂.symmₗ 𝕜 x = LinearMap.id :=
        LinearMap.ext (e₂.linearMapAt_symmₗ (R := 𝕜) h₂)
      simp only [TauCeti.ProjectiveTensor.linearEquiv_apply, ← LinearMap.comp_apply,
        ← _root_.TensorProduct.map_comp, h₁', h₂', _root_.TensorProduct.map_id, LinearMap.id_apply]
  open_target := (e₁.open_baseSet.inter e₂.open_baseSet).prod isOpen_univ
  baseSet := e₁.baseSet ∩ e₂.baseSet
  open_baseSet := e₁.open_baseSet.inter e₂.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

@[simp] theorem tensorProduct_baseSet :
    (tensorProduct 𝕜 e₁ e₂).baseSet = e₁.baseSet ∩ e₂.baseSet := (rfl)

theorem tensorProduct_apply (p : TotalSpace PF₁F₂ TE₁E₂) :
    tensorProduct 𝕜 e₁ e₂ p =
      ⟨p.1, ⟨_root_.TensorProduct.map (e₁.linearMapAt 𝕜 p.1) (e₂.linearMapAt 𝕜 p.1) p.2⟩⟩ := (rfl)

instance tensorProduct.isLinear : (Pretrivialization.tensorProduct 𝕜 e₁ e₂).IsLinear 𝕜 where
  linear _ _ := let inj := (TauCeti.ProjectiveTensor.linearEquiv 𝕜 F₁ F₂).injective
    { map_add := fun _ _ ↦ inj (by simp [tensorProduct_apply])
      map_smul := fun _ _ ↦ inj (by simp [tensorProduct_apply]) }

theorem tensorProduct_symm_apply (p : B × PF₁F₂) :
    (tensorProduct 𝕜 e₁ e₂).toPartialEquiv.symm p =
      ⟨p.1, _root_.TensorProduct.map (e₁.symmₗ 𝕜 p.1) (e₂.symmₗ 𝕜 p.1) p.2.toTensorProduct⟩ := (rfl)

theorem tensorProduct_symm_apply' {b : B} (hb : b ∈ e₁.baseSet ∩ e₂.baseSet) (u : PF₁F₂) :
    (tensorProduct 𝕜 e₁ e₂).symm b u =
      _root_.TensorProduct.map (e₁.symmₗ 𝕜 b) (e₂.symmₗ 𝕜 b) u.toTensorProduct := by
  rw [symm_apply]; exacts [rfl, hb]

theorem tensorProduct_symm_apply_tmul {b : B} (hb : b ∈ e₁.baseSet ∩ e₂.baseSet) (v : F₁) (w : F₂) :
    (tensorProduct 𝕜 e₁ e₂).symm b ⟨v ⊗ₜ[𝕜] w⟩ = e₁.symm b v ⊗ₜ[𝕜] e₂.symm b w := by
  simp [tensorProduct_symm_apply' 𝕜 e₁ e₂ hb, hb.1, hb.2]

theorem tensorProductCoordChange_apply (b : B)
    (hb : b ∈ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) (u : PF₁F₂) :
    tensorProductCoordChange 𝕜 e₁ e₁' e₂ e₂' b u =
      (tensorProduct 𝕜 e₁' e₂' ⟨b, (tensorProduct 𝕜 e₁ e₂).symm b u⟩).2 := by
  apply (TauCeti.ProjectiveTensor.linearEquiv 𝕜 F₁ F₂).injective
  rw [tensorProductCoordChange, TauCeti.ProjectiveTensor.mapL_apply, tensorProduct_apply,
    tensorProduct_symm_apply' 𝕜 e₁ e₂ hb.1, TauCeti.ProjectiveTensor.linearEquiv_apply,
    TauCeti.ProjectiveTensor.linearEquiv_apply, ← LinearMap.comp_apply,
    ← _root_.TensorProduct.map_comp]
  have h₁ : e₁'.linearMapAt 𝕜 b ∘ₗ e₁.symmₗ 𝕜 b = (e₁.coordChangeL 𝕜 e₁' b).toLinearMap := by
    ext; simp [Trivialization.coordChangeL_apply, hb.1.1, hb.2.1]
  have h₂ : e₂'.linearMapAt 𝕜 b ∘ₗ e₂.symmₗ 𝕜 b = (e₂.coordChangeL 𝕜 e₂' b).toLinearMap := by
    ext; simp [Trivialization.coordChangeL_apply, hb.1.2, hb.2.2]
  rw [h₁, h₂]; rfl

end Bundle.Pretrivialization

open Pretrivialization

variable (F₁ E₁ F₂ E₂)
  [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]
  [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]

/-- `VectorPrebundle` collating the tensor-product pretrivializations of two finite-rank vector
bundles over a complete nontrivially normed field. -/
def Bundle.TensorProduct.vectorPrebundle : VectorPrebundle 𝕜 PF₁F₂ TE₁E₂ where
  pretrivializationAtlas := {e | ∃ (e₁ : Trivialization F₁ (π F₁ E₁))
    (e₂ : Trivialization F₂ (π F₂ E₂)) (_ : MemTrivializationAtlas e₁)
    (_ : MemTrivializationAtlas e₂), e = Pretrivialization.tensorProduct 𝕜 e₁ e₂}
  pretrivialization_linear' := by rintro _ ⟨_, _, _, _, rfl⟩; infer_instance
  pretrivializationAt x :=
    Pretrivialization.tensorProduct 𝕜 (trivializationAt F₁ E₁ x) (trivializationAt F₂ E₂ x)
  mem_base_pretrivializationAt x :=
    ⟨mem_baseSet_trivializationAt F₁ E₁ x, mem_baseSet_trivializationAt F₂ E₂ x⟩
  pretrivialization_mem_atlas x :=
    ⟨trivializationAt F₁ E₁ x, trivializationAt F₂ E₂ x, inferInstance, inferInstance, rfl⟩
  exists_coordChange := by
    rintro _ ⟨e₁, e₂, _, _, rfl⟩ _ ⟨e₁', e₂', _, _, rfl⟩
    exact ⟨tensorProductCoordChange 𝕜 e₁ e₁' e₂ e₂',
      continuousOn_tensorProductCoordChange, tensorProductCoordChange_apply 𝕜 e₁ e₁' e₂ e₂'⟩
  totalSpaceMk_isInducing b := by
    let h₁ := mem_baseSet_trivializationAt F₁ E₁ b; let h₂ := mem_baseSet_trivializationAt F₂ E₂ b
    let φ₀ := (_root_.TensorProduct.congr ((trivializationAt F₁ E₁ b).linearEquivAt 𝕜 b h₁)
      ((trivializationAt F₂ E₂ b).linearEquivAt 𝕜 b h₂)).trans
      (TauCeti.ProjectiveTensor.linearEquiv 𝕜 F₁ F₂).symm
    let φ : E₁ b ⊗[𝕜] E₂ b ≃L[𝕜] PF₁F₂ :=
      { φ₀ with continuous_toFun := IsModuleTopology.continuous_of_linearMap φ₀.toLinearMap
                continuous_invFun := φ₀.symm.toLinearMap.continuous_of_finiteDimensional }
    have heq : (Pretrivialization.tensorProduct 𝕜 (trivializationAt F₁ E₁ b)
        (trivializationAt F₂ E₂ b) : TotalSpace _ _ → _) ∘ TotalSpace.mk b = fun u ↦ (b, φ u) := by
      ext u; · rfl
      simp only [Function.comp_apply, φ, φ₀, Pretrivialization.tensorProduct_apply,
        Trivialization.linearMapAt_def_of_mem _ h₁, Trivialization.linearMapAt_def_of_mem _ h₂,
        ContinuousLinearEquiv.coe_mk, LinearEquiv.trans_apply,
        TauCeti.ProjectiveTensor.linearEquiv_symm_apply]
      induction u using _root_.TensorProduct.inductionOn with
      | tmul _ _ => simp
      | add _ _ hx hy => simp [hx, hy]
    exact heq ▸ isInducing_const_prod.mpr φ.toHomeomorph.isInducing

theorem Bundle.TensorProduct.mem_pretrivializationAtlas_iff
    {e : Pretrivialization PF₁F₂ (π PF₁F₂ TE₁E₂)} :
    e ∈ (Bundle.TensorProduct.vectorPrebundle 𝕜 F₁ E₁ F₂ E₂).pretrivializationAtlas ↔
      ∃ (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
        (_ : MemTrivializationAtlas e₁) (_ : MemTrivializationAtlas e₂),
          e = Pretrivialization.tensorProduct 𝕜 e₁ e₂ := Iff.rfl

instance Bundle.TensorProduct.topologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace PF₁F₂ TE₁E₂) :=
  (Bundle.TensorProduct.vectorPrebundle 𝕜 F₁ E₁ F₂ E₂).totalSpaceTopology

instance Bundle.TensorProduct.fiberBundle : FiberBundle PF₁F₂ TE₁E₂ :=
  (Bundle.TensorProduct.vectorPrebundle 𝕜 F₁ E₁ F₂ E₂).toFiberBundle

instance Bundle.TensorProduct.vectorBundle : VectorBundle 𝕜 PF₁F₂ TE₁E₂ :=
  (Bundle.TensorProduct.vectorPrebundle 𝕜 F₁ E₁ F₂ E₂).toVectorBundle

section TrivializationAPI

variable {F₁ E₁ F₂ E₂} [he₁ : MemTrivializationAtlas e₁] [he₂ : MemTrivializationAtlas e₂]

/-- Trivialization of `fun x ↦ E₁ x ⊗[𝕜] E₂ x` induced by atlas trivializations `e₁` and `e₂`. -/
def Bundle.Trivialization.tensorProduct : Trivialization PF₁F₂ (π PF₁F₂ TE₁E₂) :=
  VectorPrebundle.trivializationOfMemPretrivializationAtlas _ ⟨e₁, e₂, he₁, he₂, rfl⟩

instance Bundle.TensorProduct.memTrivializationAtlas :
    MemTrivializationAtlas (e₁.tensorProduct 𝕜 e₂ : Trivialization PF₁F₂ (π PF₁F₂ TE₁E₂)) where
  out := ⟨_, ⟨e₁, e₂, inferInstance, inferInstance, rfl⟩, rfl⟩

variable {𝕜 e₁ e₂}

@[simp] theorem Bundle.Trivialization.baseSet_tensorProduct :
    (e₁.tensorProduct 𝕜 e₂).baseSet = e₁.baseSet ∩ e₂.baseSet := (rfl)

theorem Bundle.Trivialization.tensorProduct_apply (p : TotalSpace PF₁F₂ TE₁E₂) :
    e₁.tensorProduct 𝕜 e₂ p =
      ⟨p.1, ⟨_root_.TensorProduct.map (e₁.linearMapAt 𝕜 p.1) (e₂.linearMapAt 𝕜 p.1) p.2⟩⟩ := (rfl)

@[simp] theorem Bundle.Trivialization.tensorProduct_apply_mk_tmul {b : B}
    (hb : b ∈ e₁.baseSet ∩ e₂.baseSet) (v : E₁ b) (w : E₂ b) :
    e₁.tensorProduct 𝕜 e₂ ⟨b, v ⊗ₜ[𝕜] w⟩ = ⟨b, ⟨(e₁ ⟨b, v⟩).2 ⊗ₜ[𝕜] (e₂ ⟨b, w⟩).2⟩⟩ := by
  simp [Bundle.Trivialization.tensorProduct_apply, hb.1, hb.2]

@[simp] theorem Bundle.Trivialization.tensorProduct_symm_apply_tmul {b : B}
    (hb : b ∈ e₁.baseSet ∩ e₂.baseSet) (v : F₁) (w : F₂) :
    (e₁.tensorProduct 𝕜 e₂).symm b ⟨v ⊗ₜ[𝕜] w⟩ = e₁.symm b v ⊗ₜ[𝕜] e₂.symm b w :=
  Pretrivialization.tensorProduct_symm_apply_tmul 𝕜 e₁ e₂ hb v w

theorem Bundle.Trivialization.coordChangeL_tensorProduct
    [MemTrivializationAtlas e₁'] [MemTrivializationAtlas e₂'] {b : B}
    (hb : b ∈ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) :
    ((e₁.tensorProduct 𝕜 e₂).coordChangeL 𝕜 (e₁'.tensorProduct 𝕜 e₂') b : PF₁F₂ →L[𝕜] PF₁F₂) =
      TauCeti.ProjectiveTensor.mapL (e₁.coordChangeL 𝕜 e₁' b : F₁ →L[𝕜] F₁)
        (e₂.coordChangeL 𝕜 e₂' b : F₂ →L[𝕜] F₂) :=
  TauCeti.ProjectiveTensor.continuousLinearMap_ext fun v w ↦ by
    rw [ContinuousLinearEquiv.coe_coe, Trivialization.coordChangeL_apply _ _ hb,
      Bundle.Trivialization.tensorProduct_symm_apply_tmul hb.1,
      Bundle.Trivialization.tensorProduct_apply_mk_tmul hb.2, TauCeti.ProjectiveTensor.mapL_tmul,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe,
      Trivialization.coordChangeL_apply e₁ e₁' ⟨hb.1.1, hb.2.1⟩,
      Trivialization.coordChangeL_apply e₂ e₂' ⟨hb.1.2, hb.2.2⟩]

end TrivializationAPI

section PreferredTrivialization

variable {𝕜 F₁ E₁ F₂ E₂}

theorem tensorProduct_trivializationAt (x₀ : B) :
    trivializationAt PF₁F₂ TE₁E₂ x₀ =
      (trivializationAt F₁ E₁ x₀).tensorProduct 𝕜 (trivializationAt F₂ E₂ x₀) := (rfl)

theorem tensorProduct_trivializationAt_apply (x₀ : B) (p : TotalSpace PF₁F₂ TE₁E₂) :
    trivializationAt PF₁F₂ TE₁E₂ x₀ p =
      ⟨p.1, TensorProduct.inCoordinates F₁ E₁ F₂ E₂ x₀ p.1 x₀ p.1 p.2⟩ := by
  simp [tensorProduct_trivializationAt, Bundle.Trivialization.tensorProduct_apply,
    TensorProduct.inCoordinates]

@[simp, mfld_simps] theorem tensorProduct_trivializationAt_source (x₀ : B) :
    (trivializationAt PF₁F₂ TE₁E₂ x₀).source = π PF₁F₂ TE₁E₂ ⁻¹'
      ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) := (rfl)

@[simp, mfld_simps] theorem tensorProduct_trivializationAt_target (x₀ : B) :
    (trivializationAt PF₁F₂ TE₁E₂ x₀).target =
      ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) ×ˢ univ := (rfl)

@[simp] theorem tensorProduct_trivializationAt_baseSet (x₀ : B) :
    (trivializationAt PF₁F₂ TE₁E₂ x₀).baseSet =
      (trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet := (rfl)

theorem tensorProduct_trivializationAt_symm_apply_tmul {x₀ x : B}
    (hx₁ : x ∈ (trivializationAt F₁ E₁ x₀).baseSet) (hx₂ : x ∈ (trivializationAt F₂ E₂ x₀).baseSet)
    (v : F₁) (w : F₂) : (trivializationAt PF₁F₂ TE₁E₂ x₀).symm x ⟨v ⊗ₜ[𝕜] w⟩ =
      (trivializationAt F₁ E₁ x₀).symm x v ⊗ₜ[𝕜] (trivializationAt F₂ E₂ x₀).symm x w :=
  Bundle.Trivialization.tensorProduct_symm_apply_tmul ⟨hx₁, hx₂⟩ v w

theorem continuousWithinAt_tensorProduct_bundle {M : Type*} [TopologicalSpace M]
    (f : M → TotalSpace PF₁F₂ TE₁E₂) {s : Set M} {x₀ : M} :
    ContinuousWithinAt f s x₀ ↔ ContinuousWithinAt (fun x ↦ (f x).1) s x₀ ∧ ContinuousWithinAt
      (fun x ↦ TensorProduct.inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2)
      s x₀ := by
  simpa only [tensorProduct_trivializationAt_apply] using
    FiberBundle.continuousWithinAt_totalSpace (F := PF₁F₂) (E := TE₁E₂) (f := f) (s := s) (x₀ := x₀)

theorem continuousAt_tensorProduct_bundle {M : Type*} [TopologicalSpace M]
    (f : M → TotalSpace PF₁F₂ TE₁E₂) {x₀ : M} :
    ContinuousAt f x₀ ↔ ContinuousAt (fun x ↦ (f x).1) x₀ ∧ ContinuousAt
      (fun x ↦ TensorProduct.inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2)
      x₀ := by
  simpa only [← continuousWithinAt_univ] using continuousWithinAt_tensorProduct_bundle f (s := univ)

end PreferredTrivialization

end Prebundle

section PureTensor

variable {𝕜 B M F₁ F₂ : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [TopologicalSpace B] [TopologicalSpace M] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [FiniteDimensional 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₁ E₂ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x, TopologicalSpace (E₁ x)] [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]

local notation "PF₁F₂" => TauCeti.ProjectiveTensor 𝕜 F₁ F₂
local notation "TE₁E₂" => fun x : B ↦ E₁ x ⊗[𝕜] E₂ x

namespace TauCeti

variable (F₁ F₂) in
/-- Canonical fibrewise continuous bilinear pure-tensor map `(v, w) ↦ v ⊗ₜ w` at `x : B` for
finite-rank vector bundles with model fibres `F₁` and `F₂`. -/
def bundleTmul (x : B) : E₁ x →L[𝕜] E₂ x →L[𝕜] (E₁ x ⊗[𝕜] E₂ x) :=
  letI := FiberBundle.t2Space F₁ E₁ x; letI := FiberBundle.t2Space F₂ E₂ x
  letI := VectorBundle.finiteDimensional 𝕜 F₁ E₁ x
  letI := VectorBundle.finiteDimensional 𝕜 F₂ E₂ x
  LinearMap.toContinuousLinearMap
    { toFun v := LinearMap.toContinuousLinearMap (_root_.TensorProduct.mk 𝕜 (E₁ x) (E₂ x) v)
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp [TensorProduct.smul_tmul'] }

@[simp] theorem bundleTmul_apply (x : B) (v : E₁ x) (w : E₂ x) :
    bundleTmul F₁ F₂ (E₁ := E₁) (E₂ := E₂) x v w = v ⊗ₜ[𝕜] w := by simp [bundleTmul]

theorem bundleTmul_inCoordinates (a x : B) (hx₁ : x ∈ (trivializationAt F₁ E₁ a).baseSet)
    (hx₂ : x ∈ (trivializationAt F₂ E₂ a).baseSet) :
    ContinuousLinearMap.inCoordinates F₁ E₁ (F₂ →L[𝕜] PF₁F₂) (fun y ↦ E₂ y →L[𝕜] TE₁E₂ y)
      a x a x (bundleTmul F₁ F₂ x) = ProjectiveTensor.tmulL 𝕜 F₁ F₂ := by
  ext v w
  have hx₁₂ : x ∈ (trivializationAt PF₁F₂ TE₁E₂ a).baseSet := ⟨hx₁, hx₂⟩
  have hx_hom : x ∈ (trivializationAt (F₂ →L[𝕜] PF₁F₂) (fun y ↦ E₂ y →L[𝕜] TE₁E₂ y) a).baseSet :=
    ⟨hx₂, hx₁₂⟩
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _ hx_hom, hom_trivializationAt_apply,
    Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _ hx₁₂,
    tensorProduct_trivializationAt_apply, Trivialization.symmL_apply _ hx₁,
    Trivialization.symmL_apply _ hx₂, bundleTmul_apply, TensorProduct.inCoordinates_tmul,
    Trivialization.linearMapAt_symm _ hx₁, Trivialization.linearMapAt_symm _ hx₂,
    ProjectiveTensor.tmulL_apply]

theorem continuous_bundleTmul :
    Continuous (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] PF₁F₂)
      (E := fun y ↦ E₁ y →L[𝕜] E₂ y →L[𝕜] TE₁E₂ y) x (bundleTmul F₁ F₂ x)) :=
  continuous_hom_bundle_of_inCoordinates_eq_const (c := fun _ ↦ ProjectiveTensor.tmulL 𝕜 F₁ F₂)
    fun a x hx₁ hx₂ ↦ bundleTmul_inCoordinates a x hx₁
      (by rw [hom_trivializationAt_baseSet] at hx₂; exact hx₂.1)

end TauCeti

variable {b : M → B} {v : ∀ m, E₁ (b m)} {w : ∀ m, E₂ (b m)} {s : Set M} {x : M}

theorem ContinuousWithinAt.tmul_section
    (hv : ContinuousWithinAt (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s x)
    (hw : ContinuousWithinAt (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) s x) :
    ContinuousWithinAt (fun m ↦ TotalSpace.mk' PF₁F₂ (E := TE₁E₂) (b m) (v m ⊗ₜ[𝕜] w m)) s x := by
  have hb := (continuous_proj F₁ E₁).continuousAt.comp_continuousWithinAt hv
  have htmul : ContinuousWithinAt (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] PF₁F₂)
      (E := fun y ↦ E₁ y →L[𝕜] E₂ y →L[𝕜] TE₁E₂ y) (b m) (TauCeti.bundleTmul F₁ F₂ (b m))) s x :=
    (TauCeti.continuous_bundleTmul (F₁ := F₁) (F₂ := F₂)).continuousAt.comp_continuousWithinAt hb
  exact htmul.clm_bundle_apply₂ hv hw

theorem ContinuousAt.tmul_section
    (hv : ContinuousAt (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x)
    (hw : ContinuousAt (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) x) :
    ContinuousAt (fun m ↦ TotalSpace.mk' PF₁F₂ (E := TE₁E₂) (b m) (v m ⊗ₜ[𝕜] w m)) x := by
  rw [← continuousWithinAt_univ] at hv hw ⊢; exact hv.tmul_section hw

theorem ContinuousOn.tmul_section
    (hv : ContinuousOn (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s)
    (hw : ContinuousOn (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) s) :
    ContinuousOn (fun m ↦ TotalSpace.mk' PF₁F₂ (E := TE₁E₂) (b m) (v m ⊗ₜ[𝕜] w m)) s :=
  fun m hm ↦ (hv m hm).tmul_section (hw m hm)

theorem Continuous.tmul_section
    (hv : Continuous (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)))
    (hw : Continuous (fun m ↦ TotalSpace.mk' F₂ (b m) (w m))) :
    Continuous (fun m ↦ TotalSpace.mk' PF₁F₂ (E := TE₁E₂) (b m) (v m ⊗ₜ[𝕜] w m)) :=
  continuous_iff_continuousAt.2 fun _ ↦ hv.continuousAt.tmul_section hw.continuousAt

end PureTensor

end
