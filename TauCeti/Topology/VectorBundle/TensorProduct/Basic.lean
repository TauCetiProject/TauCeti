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

Given two finite-rank vector bundles `E₁` and `E₂` over the same base `B`, with model fibres `F₁`
and `F₂` over a complete nontrivially normed field `𝕜`, this file constructs the topological vector
bundle structure on the fibrewise algebraic tensor product `fun x ↦ E₁ x ⊗[𝕜] E₂ x`, modelled on
the projective tensor product `TauCeti.ProjectiveTensor 𝕜 F₁ F₂`.

Each fibre `E₁ x ⊗[𝕜] E₂ x` is assumed to carry the canonical `𝕜`-module topology
`IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)`; opening the scope `TauCeti.TensorProduct` equips every
algebraic tensor product `M ⊗[𝕜] N` with `moduleTopology 𝕜 (M ⊗[𝕜] N)` automatically, while still
allowing callers to supply any Hausdorff topological vector space topology on a finite-dimensional
tensor fibre. Because `F₁` and `F₂` are finite-dimensional over the complete field `𝕜`, the model
fibre `ProjectiveTensor 𝕜 F₁ F₂` is a finite-dimensional normed space (by
`TauCeti.ProjectiveTensor.instNormedAddCommGroupOfFiniteDimensionalLeft` and
`TauCeti.ProjectiveTensor.instModuleFinite`) and therefore also carries the module topology. Thus
every fibrewise linear trivialization is automatically a linear homeomorphism without choosing
auxiliary norms on the bundle fibres.

## Main definitions and results

* `TensorProduct.inCoordinates`: coordinate expression of a tensor `u : E₁ x ⊗[𝕜] E₂ y` in the
  preferred trivializations centred at `x₀` and `y₀`.
* `Bundle.Pretrivialization.tensorProduct`, `Bundle.Trivialization.tensorProduct`: induced
  (pre)trivializations of `fun x ↦ E₁ x ⊗[𝕜] E₂ x` acting on pure tensors as
  `(e₁.tensorProduct 𝕜 e₂).symm b ⟨v ⊗ₜ w⟩ = e₁.symm b v ⊗ₜ e₂.symm b w`, with coordinate change
  `ProjectiveTensor.mapL (e₁.coordChangeL 𝕜 e₁' b) (e₂.coordChangeL 𝕜 e₂' b)`.
* `Bundle.TensorProduct.vectorBundle`: the `VectorBundle` instance on `fun x ↦ E₁ x ⊗[𝕜] E₂ x`.
* `TauCeti.bundleTmul`, `ContinuousWithinAt.tmul_section`, `Continuous.tmul_section`: continuity of
  the canonical bilinear pure-tensor map `(v, w) ↦ v ⊗ₜ w` on sections.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Chapter 12.
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

/-- Scoped default topology on an algebraic tensor product `M ⊗[𝕜] N`: the finest topology making
addition and `𝕜`-scalar multiplication continuous (`moduleTopology 𝕜 (M ⊗[𝕜] N)`). -/
scoped instance instTopologicalSpaceTensorProduct :
    TopologicalSpace (M ⊗[𝕜] N) :=
  moduleTopology 𝕜 (M ⊗[𝕜] N)

/-- With the scoped topology `TauCeti.TensorProduct`, `M ⊗[𝕜] N` carries the `𝕜`-module
topology. -/
scoped instance instIsModuleTopologyTensorProduct :
    IsModuleTopology 𝕜 (M ⊗[𝕜] N) :=
  ⟨rfl⟩

end TensorProduct

/-- Any algebraic tensor product `M ⊗[𝕜] N` carrying the `𝕜`-module topology is a topological
additive group; scalar multiplication is continuous by `IsModuleTopology.toContinuousSMul`. -/
instance instIsTopologicalAddGroupTensorProductOfIsModuleTopology
    [TopologicalSpace (M ⊗[𝕜] N)] [IsModuleTopology 𝕜 (M ⊗[𝕜] N)] :
    IsTopologicalAddGroup (M ⊗[𝕜] N) :=
  IsModuleTopology.isTopologicalAddGroup 𝕜 (M ⊗[𝕜] N)

end FiberTopology

end TauCeti

/-! ### Coordinate expressions for tensor products of bundle fibres -/

namespace TensorProduct

variable {𝕜 B₁ B₂ : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B₁] [TopologicalSpace B₂]
  (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  (E₁ : B₁ → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x, TopologicalSpace (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  (E₂ : B₂ → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [∀ x, TopologicalSpace (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

/-- Coordinate expression of a tensor in `E₁ x ⊗[𝕜] E₂ y` with respect to the preferred
trivializations centred at `x₀` and `y₀`, valued in `TauCeti.ProjectiveTensor 𝕜 F₁ F₂`. -/
def inCoordinates (x₀ x : B₁) (y₀ y : B₂) :
    E₁ x ⊗[𝕜] E₂ y →ₗ[𝕜] TauCeti.ProjectiveTensor 𝕜 F₁ F₂ :=
  (TauCeti.ProjectiveTensor.linearEquiv 𝕜 F₁ F₂).symm.toLinearMap ∘ₗ
    _root_.TensorProduct.map ((trivializationAt F₁ E₁ x₀).linearMapAt 𝕜 x)
      ((trivializationAt F₂ E₂ y₀).linearMapAt 𝕜 y)

variable {F₁ E₁ F₂ E₂}

/-- `TensorProduct.inCoordinates` acts factorwise on pure tensors. -/
@[simp]
theorem inCoordinates_tmul (x₀ x : B₁) (y₀ y : B₂) (v : E₁ x) (w : E₂ y) :
    inCoordinates F₁ E₁ F₂ E₂ x₀ x y₀ y (v ⊗ₜ[𝕜] w) =
      ⟨(trivializationAt F₁ E₁ x₀).linearMapAt 𝕜 x v ⊗ₜ[𝕜]
        (trivializationAt F₂ E₂ y₀).linearMapAt 𝕜 y w⟩ := by
  simp [inCoordinates]

/-- Inside the base sets of the preferred trivializations, `TensorProduct.inCoordinates` is given
by `TensorProduct.map` of the fibrewise linear equivalences. -/
theorem inCoordinates_eq {x₀ x : B₁} {y₀ y : B₂}
    (hx : x ∈ (trivializationAt F₁ E₁ x₀).baseSet)
    (hy : y ∈ (trivializationAt F₂ E₂ y₀).baseSet) (u : E₁ x ⊗[𝕜] E₂ y) :
    inCoordinates F₁ E₁ F₂ E₂ x₀ x y₀ y u =
      ⟨_root_.TensorProduct.map
        ((trivializationAt F₁ E₁ x₀).linearEquivAt 𝕜 x hx).toLinearMap
        ((trivializationAt F₂ E₂ y₀).linearEquivAt 𝕜 y hy).toLinearMap u⟩ := by
  simp only [inCoordinates, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TauCeti.ProjectiveTensor.linearEquiv_symm_apply,
    Trivialization.linearMapAt_def_of_mem _ hx, Trivialization.linearMapAt_def_of_mem _ hy]

/-- Inside the base sets of the preferred trivializations, `TensorProduct.inCoordinates` sends
`v ⊗ₜ w` to the pure tensor of their fibre coordinates. -/
theorem inCoordinates_tmul_of_mem {x₀ x : B₁} {y₀ y : B₂}
    (hx : x ∈ (trivializationAt F₁ E₁ x₀).baseSet)
    (hy : y ∈ (trivializationAt F₂ E₂ y₀).baseSet) (v : E₁ x) (w : E₂ y) :
    inCoordinates F₁ E₁ F₂ E₂ x₀ x y₀ y (v ⊗ₜ[𝕜] w) =
      ⟨(trivializationAt F₁ E₁ x₀ ⟨x, v⟩).2 ⊗ₜ[𝕜] (trivializationAt F₂ E₂ y₀ ⟨y, w⟩).2⟩ := by
  simp [inCoordinates_eq hx hy]

end TensorProduct

/-! ### Pretrivializations and coordinate changes -/

section Prebundle

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {B : Type*} [TopologicalSpace B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)]
  (e₁ e₁' : Trivialization F₁ (π F₁ E₁)) (e₂ e₂' : Trivialization F₂ (π F₂ E₂))

namespace Bundle.Pretrivialization

/-- Transition operator between two tensor-product pretrivializations, given on the model fibre
`ProjectiveTensor 𝕜 F₁ F₂` by `ProjectiveTensor.mapL` of the factor coordinate changes. -/
def tensorProductCoordChange [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜]
    (b : B) :
    TauCeti.ProjectiveTensor 𝕜 F₁ F₂ →L[𝕜] TauCeti.ProjectiveTensor 𝕜 F₁ F₂ :=
  TauCeti.ProjectiveTensor.mapL
    (e₁.coordChangeL 𝕜 e₁' b : F₁ →L[𝕜] F₁)
    (e₂.coordChangeL 𝕜 e₂' b : F₂ →L[𝕜] F₂)

/-- Formula for `tensorProductCoordChange` in terms of `ProjectiveTensor.mapL`. -/
theorem tensorProductCoordChange_eq [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜]
    [e₂'.IsLinear 𝕜] (b : B) :
    tensorProductCoordChange 𝕜 e₁ e₁' e₂ e₂' b =
      TauCeti.ProjectiveTensor.mapL
        (e₁.coordChangeL 𝕜 e₁' b : F₁ →L[𝕜] F₁)
        (e₂.coordChangeL 𝕜 e₂' b : F₂ →L[𝕜] F₂) :=
  (rfl)

/-- `tensorProductCoordChange` acts factorwise on pure tensors. -/
@[simp]
theorem tensorProductCoordChange_tmul [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜]
    [e₂'.IsLinear 𝕜] (b : B) (v : F₁) (w : F₂) :
    tensorProductCoordChange 𝕜 e₁ e₁' e₂ e₂' b ⟨v ⊗ₜ[𝕜] w⟩ =
      ⟨e₁.coordChangeL 𝕜 e₁' b v ⊗ₜ[𝕜] e₂.coordChangeL 𝕜 e₂' b w⟩ := by
  simp [tensorProductCoordChange]

section CoordChangeContinuity

variable {𝕜 e₁ e₁' e₂ e₂'}
  [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

/-- Continuity of the tensor-product coordinate-change map on the common base set; no
finite-dimensionality assumption on `F₁` or `F₂` is needed. -/
theorem continuousOn_tensorProductCoordChange
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    ContinuousOn (tensorProductCoordChange 𝕜 e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  let s := e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)
  have h₁ : ContinuousOn (fun b ↦ (e₁.coordChangeL 𝕜 e₁' b : F₁ →L[𝕜] F₁)) s :=
    (continuousOn_coordChange 𝕜 e₁ e₁').mono fun _ hb ↦ ⟨hb.1.1, hb.2.1⟩
  have h₂ : ContinuousOn (fun b ↦ (e₂.coordChangeL 𝕜 e₂' b : F₂ →L[𝕜] F₂)) s :=
    (continuousOn_coordChange 𝕜 e₂ e₂').mono fun _ hb ↦ ⟨hb.1.2, hb.2.2⟩
  exact (((TauCeti.ProjectiveTensor.mapCLM 𝕜 F₁ F₁ F₂ F₂).continuous.comp_continuousOn
    h₁).clm_apply h₂).congr fun b _ ↦ by simp [tensorProductCoordChange]

end CoordChangeContinuity

variable [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜]

/-- Induced pretrivialization of `fun x ↦ E₁ x ⊗[𝕜] E₂ x` from trivializations `e₁` and `e₂`,
acting on fibres by `TensorProduct.map` of `e₁.linearMapAt` and `e₂.linearMapAt`. -/
def tensorProduct :
    Pretrivialization (TauCeti.ProjectiveTensor 𝕜 F₁ F₂)
      (π (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) where
  toFun p := ⟨p.1,
    ⟨_root_.TensorProduct.map (e₁.linearMapAt 𝕜 p.1) (e₂.linearMapAt 𝕜 p.1) p.2⟩⟩
  invFun p := ⟨p.1,
    _root_.TensorProduct.map (e₁.symmₗ 𝕜 p.1) (e₂.symmₗ 𝕜 p.1) p.2.toTensorProduct⟩
  source := TotalSpace.proj ⁻¹' (e₁.baseSet ∩ e₂.baseSet)
  target := (e₁.baseSet ∩ e₂.baseSet) ×ˢ univ
  map_source' := fun ⟨_, _⟩ h ↦ ⟨h, mem_univ _⟩
  map_target' := fun ⟨_, _⟩ h ↦ h.1
  left_inv' := fun ⟨x, u⟩ ⟨h₁, h₂⟩ ↦ by
    have h₁' : e₁.symmₗ 𝕜 x ∘ₗ e₁.linearMapAt 𝕜 x = LinearMap.id :=
      LinearMap.ext (e₁.symmₗ_linearMapAt (R := 𝕜) h₁)
    have h₂' : e₂.symmₗ 𝕜 x ∘ₗ e₂.linearMapAt 𝕜 x = LinearMap.id :=
      LinearMap.ext (e₂.symmₗ_linearMapAt (R := 𝕜) h₂)
    simp only [← LinearMap.comp_apply, ← _root_.TensorProduct.map_comp,
      h₁', h₂', _root_.TensorProduct.map_id, LinearMap.id_apply]
  right_inv' := fun ⟨x, u⟩ ⟨⟨h₁, h₂⟩, _⟩ ↦ by
    have h₁' : e₁.linearMapAt 𝕜 x ∘ₗ e₁.symmₗ 𝕜 x = LinearMap.id :=
      LinearMap.ext (e₁.linearMapAt_symmₗ (R := 𝕜) h₁)
    have h₂' : e₂.linearMapAt 𝕜 x ∘ₗ e₂.symmₗ 𝕜 x = LinearMap.id :=
      LinearMap.ext (e₂.linearMapAt_symmₗ (R := 𝕜) h₂)
    simp only [Prod.mk_right_inj]
    apply (TauCeti.ProjectiveTensor.linearEquiv 𝕜 F₁ F₂).injective
    simp only [TauCeti.ProjectiveTensor.linearEquiv_apply, ← LinearMap.comp_apply,
      ← _root_.TensorProduct.map_comp, h₁', h₂', _root_.TensorProduct.map_id, LinearMap.id_apply]
  open_target := (e₁.open_baseSet.inter e₂.open_baseSet).prod isOpen_univ
  baseSet := e₁.baseSet ∩ e₂.baseSet
  open_baseSet := e₁.open_baseSet.inter e₂.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

@[simp]
theorem tensorProduct_baseSet :
    (tensorProduct 𝕜 e₁ e₂).baseSet = e₁.baseSet ∩ e₂.baseSet :=
  (rfl)

/-- Applying `Pretrivialization.tensorProduct` maps the tensor coordinatewise via `linearMapAt`. -/
theorem tensorProduct_apply
    (p : TotalSpace (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) :
    tensorProduct 𝕜 e₁ e₂ p =
      ⟨p.1, ⟨_root_.TensorProduct.map (e₁.linearMapAt 𝕜 p.1) (e₂.linearMapAt 𝕜 p.1) p.2⟩⟩ :=
  (rfl)

instance tensorProduct.isLinear : (Pretrivialization.tensorProduct 𝕜 e₁ e₂).IsLinear 𝕜 where
  linear x _ :=
    { map_add := fun u v ↦ by
        apply (TauCeti.ProjectiveTensor.linearEquiv 𝕜 F₁ F₂).injective
        simp [tensorProduct_apply]
      map_smul := fun c u ↦ by
        apply (TauCeti.ProjectiveTensor.linearEquiv 𝕜 F₁ F₂).injective
        simp [tensorProduct_apply] }

/-- Inverse partial equivalence of `Pretrivialization.tensorProduct`. -/
theorem tensorProduct_symm_apply (p : B × TauCeti.ProjectiveTensor 𝕜 F₁ F₂) :
    (tensorProduct 𝕜 e₁ e₂).toPartialEquiv.symm p =
      ⟨p.1, _root_.TensorProduct.map (e₁.symmₗ 𝕜 p.1) (e₂.symmₗ 𝕜 p.1) p.2.toTensorProduct⟩ :=
  (rfl)

/-- On `e₁.baseSet ∩ e₂.baseSet`, the inverse pretrivialization applies `TensorProduct.map` of
`e₁.symmₗ` and `e₂.symmₗ`. -/
theorem tensorProduct_symm_apply' {b : B} (hb : b ∈ e₁.baseSet ∩ e₂.baseSet)
    (u : TauCeti.ProjectiveTensor 𝕜 F₁ F₂) :
    (tensorProduct 𝕜 e₁ e₂).symm b u =
      _root_.TensorProduct.map (e₁.symmₗ 𝕜 b) (e₂.symmₗ 𝕜 b) u.toTensorProduct := by
  rw [symm_apply]
  · rfl
  · exact hb

/-- On `e₁.baseSet ∩ e₂.baseSet`, `Pretrivialization.tensorProduct` sends `⟨v ⊗ₜ w⟩` under `.symm`
to `e₁.symm b v ⊗ₜ e₂.symm b w`. -/
theorem tensorProduct_symm_apply_tmul {b : B} (hb : b ∈ e₁.baseSet ∩ e₂.baseSet)
    (v : F₁) (w : F₂) :
    (tensorProduct 𝕜 e₁ e₂).symm b ⟨v ⊗ₜ[𝕜] w⟩ = e₁.symm b v ⊗ₜ[𝕜] e₂.symm b w := by
  simp [tensorProduct_symm_apply' 𝕜 e₁ e₂ hb, hb.1, hb.2]

/-- `tensorProductCoordChange` computes the transition between two tensor-product
pretrivializations on their common domain. -/
theorem tensorProductCoordChange_apply (b : B)
    (hb : b ∈ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet))
    (u : TauCeti.ProjectiveTensor 𝕜 F₁ F₂) :
    tensorProductCoordChange 𝕜 e₁ e₁' e₂ e₂' b u =
      (tensorProduct 𝕜 e₁' e₂' ⟨b, (tensorProduct 𝕜 e₁ e₂).symm b u⟩).2 := by
  apply (TauCeti.ProjectiveTensor.linearEquiv 𝕜 F₁ F₂).injective
  rw [tensorProductCoordChange, TauCeti.ProjectiveTensor.mapL_apply, tensorProduct_apply,
    tensorProduct_symm_apply' 𝕜 e₁ e₂ hb.1, TauCeti.ProjectiveTensor.linearEquiv_apply,
    TauCeti.ProjectiveTensor.linearEquiv_apply, ← LinearMap.comp_apply,
    ← _root_.TensorProduct.map_comp]
  have h₁ : e₁'.linearMapAt 𝕜 b ∘ₗ e₁.symmₗ 𝕜 b = (e₁.coordChangeL 𝕜 e₁' b).toLinearMap := by
    ext v; simp [Trivialization.coordChangeL_apply, hb.1.1, hb.2.1]
  have h₂ : e₂'.linearMapAt 𝕜 b ∘ₗ e₂.symmₗ 𝕜 b = (e₂.coordChangeL 𝕜 e₂' b).toLinearMap := by
    ext w; simp [Trivialization.coordChangeL_apply, hb.1.2, hb.2.2]
  rw [h₁, h₂]
  rfl

end Bundle.Pretrivialization

/-! ### The `VectorBundle` structure on `fun x ↦ E₁ x ⊗[𝕜] E₂ x` -/

open Pretrivialization

variable (F₁ E₁ F₂ E₂)
  [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]
  [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]

/-- `VectorPrebundle` collating the tensor-product pretrivializations of two finite-rank vector
bundles over a complete nontrivially normed field. -/
def Bundle.TensorProduct.vectorPrebundle :
    VectorPrebundle 𝕜 (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) where
  pretrivializationAtlas :=
    {e | ∃ (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
      (_ : MemTrivializationAtlas e₁) (_ : MemTrivializationAtlas e₂),
        e = Pretrivialization.tensorProduct 𝕜 e₁ e₂}
  pretrivialization_linear' := by
    rintro _ ⟨e₁, e₂, _, _, rfl⟩
    infer_instance
  pretrivializationAt x :=
    Pretrivialization.tensorProduct 𝕜 (trivializationAt F₁ E₁ x) (trivializationAt F₂ E₂ x)
  mem_base_pretrivializationAt x :=
    ⟨mem_baseSet_trivializationAt F₁ E₁ x, mem_baseSet_trivializationAt F₂ E₂ x⟩
  pretrivialization_mem_atlas x :=
    ⟨trivializationAt F₁ E₁ x, trivializationAt F₂ E₂ x, inferInstance, inferInstance, rfl⟩
  exists_coordChange := by
    rintro _ ⟨e₁, e₂, _, _, rfl⟩ _ ⟨e₁', e₂', _, _, rfl⟩
    exact ⟨tensorProductCoordChange 𝕜 e₁ e₁' e₂ e₂',
      continuousOn_tensorProductCoordChange,
      tensorProductCoordChange_apply 𝕜 e₁ e₁' e₂ e₂'⟩
  totalSpaceMk_isInducing := by
    intro b
    let h₁ := mem_baseSet_trivializationAt F₁ E₁ b
    let h₂ := mem_baseSet_trivializationAt F₂ E₂ b
    let φ₀ : E₁ b ⊗[𝕜] E₂ b ≃ₗ[𝕜] TauCeti.ProjectiveTensor 𝕜 F₁ F₂ :=
      (_root_.TensorProduct.congr
        ((trivializationAt F₁ E₁ b).linearEquivAt 𝕜 b h₁)
        ((trivializationAt F₂ E₂ b).linearEquivAt 𝕜 b h₂)).trans
        (TauCeti.ProjectiveTensor.linearEquiv 𝕜 F₁ F₂).symm
    let φ : E₁ b ⊗[𝕜] E₂ b ≃L[𝕜] TauCeti.ProjectiveTensor 𝕜 F₁ F₂ :=
      { φ₀ with
        continuous_toFun := IsModuleTopology.continuous_of_linearMap φ₀.toLinearMap
        continuous_invFun := φ₀.symm.toLinearMap.continuous_of_finiteDimensional }
    have hind : IsInducing fun u : E₁ b ⊗[𝕜] E₂ b ↦ (b, φ u) :=
      isInducing_const_prod.mpr φ.toHomeomorph.isInducing
    have heq : (Pretrivialization.tensorProduct 𝕜 (trivializationAt F₁ E₁ b)
        (trivializationAt F₂ E₂ b) : TotalSpace _ _ → _) ∘ TotalSpace.mk b =
        fun u ↦ (b, φ u) := by
      ext u
      · rfl
      · simp only [Function.comp_apply, φ, φ₀, Pretrivialization.tensorProduct_apply,
          Trivialization.linearMapAt_def_of_mem _ h₁, Trivialization.linearMapAt_def_of_mem _ h₂,
          ContinuousLinearEquiv.coe_mk, LinearEquiv.trans_apply,
          TauCeti.ProjectiveTensor.linearEquiv_symm_apply]
        induction u using _root_.TensorProduct.inductionOn with
        | tmul v w => simp
        | add x y hx hy => simp [hx, hy]
    rwa [heq]

/-- Membership in the pretrivialization atlas of `Bundle.TensorProduct.vectorPrebundle`. -/
theorem Bundle.TensorProduct.mem_pretrivializationAtlas_iff
    {e : Pretrivialization (TauCeti.ProjectiveTensor 𝕜 F₁ F₂)
      (π (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x))} :
    e ∈ (Bundle.TensorProduct.vectorPrebundle 𝕜 F₁ E₁ F₂ E₂).pretrivializationAtlas ↔
      ∃ (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
        (_ : MemTrivializationAtlas e₁) (_ : MemTrivializationAtlas e₂),
          e = Pretrivialization.tensorProduct 𝕜 e₁ e₂ :=
  Iff.rfl

/-- Total-space topology on the tensor product of two finite-rank vector bundles. -/
instance Bundle.TensorProduct.topologicalSpaceTotalSpace :
    TopologicalSpace
      (TotalSpace (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) :=
  (Bundle.TensorProduct.vectorPrebundle 𝕜 F₁ E₁ F₂ E₂).totalSpaceTopology

/-- The tensor product of two finite-rank vector bundles is a `FiberBundle`. -/
instance Bundle.TensorProduct.fiberBundle :
    FiberBundle (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) :=
  (Bundle.TensorProduct.vectorPrebundle 𝕜 F₁ E₁ F₂ E₂).toFiberBundle

/-- The tensor product of two finite-rank vector bundles is a `VectorBundle`. -/
instance Bundle.TensorProduct.vectorBundle :
    VectorBundle 𝕜 (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) :=
  (Bundle.TensorProduct.vectorPrebundle 𝕜 F₁ E₁ F₂ E₂).toVectorBundle

section TrivializationAPI

variable {F₁ E₁ F₂ E₂}
  [he₁ : MemTrivializationAtlas e₁] [he₂ : MemTrivializationAtlas e₂]

/-- Trivialization of `fun x ↦ E₁ x ⊗[𝕜] E₂ x` induced by atlas trivializations `e₁` and `e₂`. -/
def Bundle.Trivialization.tensorProduct :
    Trivialization (TauCeti.ProjectiveTensor 𝕜 F₁ F₂)
      (π (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) :=
  VectorPrebundle.trivializationOfMemPretrivializationAtlas _ ⟨e₁, e₂, he₁, he₂, rfl⟩

instance Bundle.TensorProduct.memTrivializationAtlas :
    MemTrivializationAtlas
      (e₁.tensorProduct 𝕜 e₂ :
        Trivialization (TauCeti.ProjectiveTensor 𝕜 F₁ F₂)
          (π (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x))) where
  out := ⟨_, ⟨e₁, e₂, inferInstance, inferInstance, rfl⟩, rfl⟩

variable {𝕜 e₁ e₂}

@[simp]
theorem Bundle.Trivialization.baseSet_tensorProduct :
    (e₁.tensorProduct 𝕜 e₂).baseSet = e₁.baseSet ∩ e₂.baseSet :=
  (rfl)

theorem Bundle.Trivialization.tensorProduct_apply
    (p : TotalSpace (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) :
    e₁.tensorProduct 𝕜 e₂ p =
      ⟨p.1, ⟨_root_.TensorProduct.map (e₁.linearMapAt 𝕜 p.1) (e₂.linearMapAt 𝕜 p.1) p.2⟩⟩ :=
  (rfl)

/-- On `e₁.baseSet ∩ e₂.baseSet`, the tensor-product trivialization sends a pure tensor `v ⊗ₜ w`
to the pure tensor of fibre coordinates. -/
@[simp]
theorem Bundle.Trivialization.tensorProduct_apply_mk_tmul {b : B}
    (hb : b ∈ e₁.baseSet ∩ e₂.baseSet) (v : E₁ b) (w : E₂ b) :
    e₁.tensorProduct 𝕜 e₂ ⟨b, v ⊗ₜ[𝕜] w⟩ = ⟨b, ⟨(e₁ ⟨b, v⟩).2 ⊗ₜ[𝕜] (e₂ ⟨b, w⟩).2⟩⟩ := by
  simp [Bundle.Trivialization.tensorProduct_apply, hb.1, hb.2]

/-- On `e₁.baseSet ∩ e₂.baseSet`, the inverse tensor-product trivialization sends `⟨v ⊗ₜ w⟩` to
`e₁.symm b v ⊗ₜ e₂.symm b w`. -/
@[simp]
theorem Bundle.Trivialization.tensorProduct_symm_apply_tmul {b : B}
    (hb : b ∈ e₁.baseSet ∩ e₂.baseSet) (v : F₁) (w : F₂) :
    (e₁.tensorProduct 𝕜 e₂).symm b ⟨v ⊗ₜ[𝕜] w⟩ = e₁.symm b v ⊗ₜ[𝕜] e₂.symm b w :=
  Pretrivialization.tensorProduct_symm_apply_tmul 𝕜 e₁ e₂ hb v w

/-- Coordinate change between two induced tensor-product trivializations is `ProjectiveTensor.mapL`
of the factor coordinate changes. -/
theorem Bundle.Trivialization.coordChangeL_tensorProduct
    [MemTrivializationAtlas e₁'] [MemTrivializationAtlas e₂'] {b : B}
    (hb : b ∈ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) :
    ((e₁.tensorProduct 𝕜 e₂).coordChangeL 𝕜 (e₁'.tensorProduct 𝕜 e₂') b :
        TauCeti.ProjectiveTensor 𝕜 F₁ F₂ →L[𝕜] TauCeti.ProjectiveTensor 𝕜 F₁ F₂) =
      TauCeti.ProjectiveTensor.mapL
        (e₁.coordChangeL 𝕜 e₁' b : F₁ →L[𝕜] F₁)
        (e₂.coordChangeL 𝕜 e₂' b : F₂ →L[𝕜] F₂) := by
  refine TauCeti.ProjectiveTensor.continuousLinearMap_ext fun v w ↦ ?_
  rw [ContinuousLinearEquiv.coe_coe, Trivialization.coordChangeL_apply _ _ hb,
    Bundle.Trivialization.tensorProduct_symm_apply_tmul hb.1,
    Bundle.Trivialization.tensorProduct_apply_mk_tmul hb.2,
    TauCeti.ProjectiveTensor.mapL_tmul, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_coe,
    Trivialization.coordChangeL_apply e₁ e₁' ⟨hb.1.1, hb.2.1⟩,
    Trivialization.coordChangeL_apply e₂ e₂' ⟨hb.1.2, hb.2.2⟩]

end TrivializationAPI

section PreferredTrivialization

variable {𝕜 F₁ E₁ F₂ E₂}

theorem tensorProduct_trivializationAt (x₀ : B) :
    trivializationAt (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) x₀ =
      (trivializationAt F₁ E₁ x₀).tensorProduct 𝕜 (trivializationAt F₂ E₂ x₀) :=
  (rfl)

theorem tensorProduct_trivializationAt_apply (x₀ : B)
    (p : TotalSpace (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) :
    trivializationAt (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) x₀ p =
      ⟨p.1, TensorProduct.inCoordinates F₁ E₁ F₂ E₂ x₀ p.1 x₀ p.1 p.2⟩ := by
  simp [tensorProduct_trivializationAt, Bundle.Trivialization.tensorProduct_apply,
    TensorProduct.inCoordinates]

@[simp, mfld_simps]
theorem tensorProduct_trivializationAt_source (x₀ : B) :
    (trivializationAt (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) x₀).source =
      π (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) ⁻¹'
        ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) :=
  (rfl)

@[simp, mfld_simps]
theorem tensorProduct_trivializationAt_target (x₀ : B) :
    (trivializationAt (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) x₀).target =
      ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) ×ˢ univ :=
  (rfl)

@[simp]
theorem tensorProduct_trivializationAt_baseSet (x₀ : B) :
    (trivializationAt (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) x₀).baseSet =
      (trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet :=
  (rfl)

/-- On the intersection of the preferred base sets at `x₀`, the inverse preferred trivialization of
the tensor-product bundle acts factorwise on pure tensors. -/
theorem tensorProduct_trivializationAt_symm_apply_tmul {x₀ x : B}
    (hx₁ : x ∈ (trivializationAt F₁ E₁ x₀).baseSet)
    (hx₂ : x ∈ (trivializationAt F₂ E₂ x₀).baseSet) (v : F₁) (w : F₂) :
    (trivializationAt (TauCeti.ProjectiveTensor 𝕜 F₁ F₂)
      (fun y ↦ E₁ y ⊗[𝕜] E₂ y) x₀).symm x ⟨v ⊗ₜ[𝕜] w⟩ =
      (trivializationAt F₁ E₁ x₀).symm x v ⊗ₜ[𝕜] (trivializationAt F₂ E₂ x₀).symm x w :=
  Bundle.Trivialization.tensorProduct_symm_apply_tmul ⟨hx₁, hx₂⟩ v w

/-- Characterisation of `ContinuousWithinAt` for maps into a tensor-product bundle via
`TensorProduct.inCoordinates`. -/
theorem continuousWithinAt_tensorProduct_bundle {M : Type*} [TopologicalSpace M]
    (f : M → TotalSpace (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x))
    {s : Set M} {x₀ : M} :
    ContinuousWithinAt f s x₀ ↔
      ContinuousWithinAt (fun x ↦ (f x).1) s x₀ ∧
        ContinuousWithinAt
          (fun x ↦ TensorProduct.inCoordinates F₁ E₁ F₂ E₂
            (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) s x₀ := by
  simpa only [tensorProduct_trivializationAt_apply] using
    (FiberBundle.continuousWithinAt_totalSpace (F := TauCeti.ProjectiveTensor 𝕜 F₁ F₂)
      (E := fun x ↦ E₁ x ⊗[𝕜] E₂ x) (f := f) (s := s) (x₀ := x₀))

/-- Characterisation of `ContinuousAt` for maps into a tensor-product bundle via
`TensorProduct.inCoordinates`. -/
theorem continuousAt_tensorProduct_bundle {M : Type*} [TopologicalSpace M]
    (f : M → TotalSpace (TauCeti.ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) {x₀ : M} :
    ContinuousAt f x₀ ↔
      ContinuousAt (fun x ↦ (f x).1) x₀ ∧
        ContinuousAt
          (fun x ↦ TensorProduct.inCoordinates F₁ E₁ F₂ E₂
            (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ := by
  simpa only [← continuousWithinAt_univ] using
    continuousWithinAt_tensorProduct_bundle f (s := univ) (x₀ := x₀)

end PreferredTrivialization

end Prebundle

/-! ### Canonical pure-tensor map and continuity on sections -/

section PureTensor

namespace TauCeti

section Bundle

variable {𝕜 B F₁ F₂ : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [TopologicalSpace B]
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

variable (F₁ F₂) in
/-- Canonical fibrewise continuous bilinear pure-tensor map `(v, w) ↦ v ⊗ₜ w` at `x : B` for
finite-rank vector bundles with model fibres `F₁` and `F₂`. -/
def bundleTmul (x : B) : E₁ x →L[𝕜] E₂ x →L[𝕜] (E₁ x ⊗[𝕜] E₂ x) :=
  letI := FiberBundle.t2Space F₁ E₁ x
  letI := FiberBundle.t2Space F₂ E₂ x
  letI := VectorBundle.finiteDimensional 𝕜 F₁ E₁ x
  letI := VectorBundle.finiteDimensional 𝕜 F₂ E₂ x
  LinearMap.toContinuousLinearMap
    { toFun v := LinearMap.toContinuousLinearMap (_root_.TensorProduct.mk 𝕜 (E₁ x) (E₂ x) v)
      map_add' u v := by ext w; simp
      map_smul' c v := by ext w; simp [TensorProduct.smul_tmul'] }

@[simp]
theorem bundleTmul_apply (x : B) (v : E₁ x) (w : E₂ x) :
    bundleTmul F₁ F₂ (E₁ := E₁) (E₂ := E₂) x v w = v ⊗ₜ[𝕜] w := by
  simp [bundleTmul]

/-- In the preferred frames at `a`, `bundleTmul` is the constant bilinear map
`ProjectiveTensor.tmulL 𝕜 F₁ F₂`. -/
theorem bundleTmul_inCoordinates (a x : B)
    (hx₁ : x ∈ (trivializationAt F₁ E₁ a).baseSet)
    (hx₂ : x ∈ (trivializationAt F₂ E₂ a).baseSet) :
    ContinuousLinearMap.inCoordinates F₁ E₁
      (F₂ →L[𝕜] ProjectiveTensor 𝕜 F₁ F₂) (fun y ↦ E₂ y →L[𝕜] (E₁ y ⊗[𝕜] E₂ y))
      a x a x (bundleTmul F₁ F₂ x) = ProjectiveTensor.tmulL 𝕜 F₁ F₂ := by
  ext v w
  have hx₁₂ : x ∈ (trivializationAt (ProjectiveTensor 𝕜 F₁ F₂)
      (fun y ↦ E₁ y ⊗[𝕜] E₂ y) a).baseSet := ⟨hx₁, hx₂⟩
  have hx_hom : x ∈ (trivializationAt (F₂ →L[𝕜] ProjectiveTensor 𝕜 F₁ F₂)
      (fun y ↦ E₂ y →L[𝕜] (E₁ y ⊗[𝕜] E₂ y)) a).baseSet := ⟨hx₂, hx₁₂⟩
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _ hx_hom, hom_trivializationAt_apply,
    Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _ hx₁₂,
    tensorProduct_trivializationAt_apply, Trivialization.symmL_apply _ hx₁,
    Trivialization.symmL_apply _ hx₂, bundleTmul_apply, TensorProduct.inCoordinates_tmul,
    Trivialization.linearMapAt_symm _ hx₁, Trivialization.linearMapAt_symm _ hx₂,
    ProjectiveTensor.tmulL_apply]

/-- `bundleTmul` is a continuous section of the Hom bundle `E₁ →L E₂ →L (E₁ ⊗ E₂)`. -/
theorem continuous_bundleTmul :
    Continuous (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] ProjectiveTensor 𝕜 F₁ F₂)
      (E := fun y ↦ E₁ y →L[𝕜] E₂ y →L[𝕜] (E₁ y ⊗[𝕜] E₂ y)) x (bundleTmul F₁ F₂ x)) := by
  refine continuous_iff_continuousAt.2 fun a ↦ ?_
  rw [continuousAt_hom_bundle]
  refine ⟨continuousAt_id,
    (continuous_const (y := ProjectiveTensor.tmulL 𝕜 F₁ F₂)).continuousAt.congr_of_eventuallyEq ?_⟩
  filter_upwards [(trivializationAt F₁ E₁ a).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F₁ E₁ a),
    (trivializationAt F₂ E₂ a).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F₂ E₂ a)] with x hx₁ hx₂
  exact bundleTmul_inCoordinates a x hx₁ hx₂

end Bundle

end TauCeti

section PureTensorContinuity

variable {𝕜 B M F₁ F₂ : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [TopologicalSpace B] [TopologicalSpace M]
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

/-- Pointwise pure tensor of two bundle-valued maps continuous within a set is continuous within
that set. -/
theorem ContinuousWithinAt.tmul_section
    (hv : ContinuousWithinAt (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s x)
    (hw : ContinuousWithinAt (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) s x) :
    ContinuousWithinAt
      (fun m ↦ TotalSpace.mk' (TauCeti.ProjectiveTensor 𝕜 F₁ F₂)
        (E := fun y ↦ E₁ y ⊗[𝕜] E₂ y) (b m) (v m ⊗ₜ[𝕜] w m)) s x := by
  have hb : ContinuousWithinAt b s x :=
    (continuous_proj F₁ E₁).continuousAt.comp_continuousWithinAt hv
  have htmul : ContinuousWithinAt
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] TauCeti.ProjectiveTensor 𝕜 F₁ F₂)
        (E := fun y ↦ E₁ y →L[𝕜] E₂ y →L[𝕜] (E₁ y ⊗[𝕜] E₂ y)) (b m)
        (TauCeti.bundleTmul F₁ F₂ (b m)))
      s x :=
    (TauCeti.continuous_bundleTmul (F₁ := F₁) (F₂ := F₂)).continuousAt.comp_continuousWithinAt hb
  exact htmul.clm_bundle_apply₂ hv hw

/-- Pointwise pure tensor of two bundle-valued maps continuous at `x` is continuous at `x`. -/
theorem ContinuousAt.tmul_section
    (hv : ContinuousAt (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x)
    (hw : ContinuousAt (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) x) :
    ContinuousAt
      (fun m ↦ TotalSpace.mk' (TauCeti.ProjectiveTensor 𝕜 F₁ F₂)
        (E := fun y ↦ E₁ y ⊗[𝕜] E₂ y) (b m) (v m ⊗ₜ[𝕜] w m)) x := by
  rw [← continuousWithinAt_univ] at hv hw ⊢
  exact hv.tmul_section hw

/-- Pointwise pure tensor of two bundle-valued maps continuous on `s` is continuous on `s`. -/
theorem ContinuousOn.tmul_section
    (hv : ContinuousOn (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s)
    (hw : ContinuousOn (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) s) :
    ContinuousOn
      (fun m ↦ TotalSpace.mk' (TauCeti.ProjectiveTensor 𝕜 F₁ F₂)
        (E := fun y ↦ E₁ y ⊗[𝕜] E₂ y) (b m) (v m ⊗ₜ[𝕜] w m)) s :=
  fun m hm ↦ (hv m hm).tmul_section (hw m hm)

/-- Pointwise pure tensor of two continuous bundle-valued maps is continuous. -/
theorem Continuous.tmul_section
    (hv : Continuous (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)))
    (hw : Continuous (fun m ↦ TotalSpace.mk' F₂ (b m) (w m))) :
    Continuous
      (fun m ↦ TotalSpace.mk' (TauCeti.ProjectiveTensor 𝕜 F₁ F₂)
        (E := fun y ↦ E₁ y ⊗[𝕜] E₂ y) (b m) (v m ⊗ₜ[𝕜] w m)) :=
  continuous_iff_continuousAt.2 fun _ ↦ hv.continuousAt.tmul_section hw.continuousAt

end PureTensorContinuity

end PureTensor

end
