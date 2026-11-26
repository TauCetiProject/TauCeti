/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Topology.VectorBundle.Basic

/-!
# The vector bundle of continuous multilinear maps

Let `E₁` and `E₂` be topological vector bundles over the same base `B`, with model fibres the
normed spaces `F₁` and `F₂`, and let `ι` be a finite index type. This file constructs the
topological vector bundle whose fibre over `x` is the space
`ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ x) (E₂ x)` of continuous multilinear maps
`E₁ x × ⋯ × E₁ x → E₂ x`, with model fibre `ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂`.

For a finite-rank bundle `E₁` this is the bundle `(E₁*)^{⊗ι} ⊗ E₂`. For the tangent bundle `E₁`
of a manifold, its sections are the `E₂`-valued covariant tensor fields of rank `card ι`; the
iterated covariant derivatives `∇ʲσ` of a section `σ` of `E₂` are sections of this bundle with
`ι = Fin j`, which is how they enter the expansion of a differential operator of order `m` as
`Σ_{j ≤ m} Aⱼ (∇ʲσ)`.

The fibre `ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ x) (E₂ x)` carries the topology of uniform
convergence on bounded sets, `ContinuousMultilinearMap.instTopologicalSpace`; the bundle
structure makes each of its trivializations a homeomorphism onto the normed model fibre.

## Main definitions

* `ContinuousMultilinearMap.inCoordinates`: a fibrewise multilinear map read in the
  trivializations at two base points.
* `Bundle.Pretrivialization.continuousMultilinearMap`,
  `Bundle.Trivialization.continuousMultilinearMap`: the (pre)trivialization induced by
  trivializations of `E₁` and `E₂`.
* `Bundle.ContinuousMultilinearMap.vectorPrebundle`: the vector prebundle collecting them, and the
  instances `TopologicalSpace`, `FiberBundle` and `VectorBundle` it induces.

## Main results

* `TauCeti.continuousAt_continuousMultilinearMap_bundle`,
  `TauCeti.continuousWithinAt_continuousMultilinearMap_bundle`: a map into the total space is
  continuous exactly when its projection and its fibre component read in coordinates are.

## Implementation notes

The construction follows the topological vector bundle of continuous alternating maps of
Yury Kudryashov, Heather Macbeth and Floris van Doorn in Mathlib
(`Mathlib.Topology.VectorBundle.ContinuousAlternatingMap`), itself modelled on Heather Macbeth
and Floris van Doorn's bundle of continuous linear maps (`Mathlib.Topology.VectorBundle.Hom`). As
there, the definitions are exposed: the formulas for the trivializations, their inverses and
coordinate changes hold by definition, and the topology and smooth structure of the bundle are
read off the vector prebundle.
-/

@[expose] public section

noncomputable section

open Bundle Set Topology
open scoped Bundle

/-!
### Continuous multilinear maps between fibres written in coordinates
-/

namespace ContinuousMultilinearMap

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜]

variable {B₁ : Type*} (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace B₁] [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

variable {B₂ : Type*} (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace B₂] [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

/-- A continuous multilinear map `ϕ : E₁ x × ⋯ × E₁ x → E₂ y` between fibres of two vector
bundles, read in the trivialization of `E₁` at `x₀` and the trivialization of `E₂` at `y₀`: it is
`ϕ` precomposed in each variable with the inverse of the first and postcomposed with the second.

It uses `Bundle.Trivialization.symmL` and `Bundle.Trivialization.continuousLinearMapAt`, which
are defined everywhere, so `ContinuousMultilinearMap.inCoordinates` makes sense even when `x`
and `y` lie outside the base sets; inside them it is a conjugation by continuous linear
equivalences (`ContinuousMultilinearMap.inCoordinates_eq`). It is the fibre component of the
trivialization at `x₀` of the bundle of continuous multilinear maps when `x₀ = y₀` and `x = y`
(`FiberBundle.trivializationAt_continuousMultilinearMap_apply`). -/
def inCoordinates (x₀ x : B₁) (y₀ y : B₂)
    (ϕ : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ x) (E₂ y)) :
    ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂ :=
  (trivializationAt F₂ E₂ y₀).continuousLinearMapAt 𝕜 y |>.compContinuousMultilinearMap
    ϕ |>.compContinuousLinearMap fun _ ↦ (trivializationAt F₁ E₁ x₀).symmL 𝕜 x

theorem inCoordinates_apply (x₀ x : B₁) (y₀ y : B₂)
    (ϕ : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ x) (E₂ y)) (v : ι → F₁) :
    inCoordinates F₁ F₂ x₀ x y₀ y ϕ v =
      (trivializationAt F₂ E₂ y₀).continuousLinearMapAt 𝕜 y
        (ϕ fun i ↦ (trivializationAt F₁ E₁ x₀).symmL 𝕜 x (v i)) :=
  rfl

/-- Inside the base sets, `ContinuousMultilinearMap.inCoordinates` is the conjugation of `ϕ` by
the continuous linear equivalences of the two trivializations. -/
theorem inCoordinates_eq {x₀ x : B₁} {y₀ y : B₂}
    {ϕ : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ x) (E₂ y)}
    (hx : x ∈ (trivializationAt F₁ E₁ x₀).baseSet)
    (hy : y ∈ (trivializationAt F₂ E₂ y₀).baseSet) :
    inCoordinates F₁ F₂ x₀ x y₀ y ϕ =
      (((trivializationAt F₂ E₂ y₀).continuousLinearEquivAt 𝕜 y hy : E₂ y →L[𝕜] F₂)
        |>.compContinuousMultilinearMap ϕ |>.compContinuousLinearMap fun _ ↦
          (((trivializationAt F₁ E₁ x₀).continuousLinearEquivAt 𝕜 x hx).symm : F₁ →L[𝕜] E₁ x)) := by
  ext
  simp [inCoordinates, *]

/-- Rewrite `ContinuousMultilinearMap.inCoordinates` using a continuous linear equivalence in the
target, assuming only that the point belongs to the base set in the target. This is the form
that is useful when `ι` is empty, so that the source plays no role. -/
theorem inCoordinates_eq_of_mem_baseSet₂ {x₀ x : B₁} {y₀ y : B₂}
    {ϕ : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ x) (E₂ y)}
    (hy : y ∈ (trivializationAt F₂ E₂ y₀).baseSet) :
    inCoordinates F₁ F₂ x₀ x y₀ y ϕ =
      (((trivializationAt F₂ E₂ y₀).continuousLinearEquivAt 𝕜 y hy : E₂ y →L[𝕜] F₂)
        |>.compContinuousMultilinearMap ϕ |>.compContinuousLinearMap fun _ ↦
          ((trivializationAt F₁ E₁ x₀).symmL 𝕜 x : F₁ →L[𝕜] E₁ x)) := by
  ext
  simp [inCoordinates, *]

end ContinuousMultilinearMap

open ContinuousMultilinearMap (inCoordinates)

/-!
### Pretrivializations of the bundle of continuous multilinear maps
-/

namespace Bundle.Pretrivialization

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜]

variable {B : Type*} [TopologicalSpace B]

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]

variable (𝕜 ι) in
/-- For trivializations `e₁, e₁'` of `E₁` and `e₂, e₂'` of `E₂`, the coordinate change at `b`
between the induced pretrivializations `Pretrivialization.continuousMultilinearMap 𝕜 ι e₁ e₂` and
`Pretrivialization.continuousMultilinearMap 𝕜 ι e₁' e₂'` of the bundle of continuous multilinear
maps: it precomposes each variable with the coordinate change from `e₁'` to `e₁` and
postcomposes with the coordinate change from `e₂` to `e₂'`. -/
def continuousMultilinearMapCoordChange (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
    (e₂ e₂' : Trivialization F₂ (π F₂ E₂))
    [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜] (b : B) :
    ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂ →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂ :=
  (ContinuousMultilinearMap.compContinuousLinearMapL fun _ ↦
      (e₁'.coordChangeL 𝕜 e₁ b : F₁ →L[𝕜] F₁)).comp
    (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜 _ F₂ F₂
      (e₂.coordChangeL 𝕜 e₂' b : F₂ →L[𝕜] F₂))

theorem continuousMultilinearMapCoordChange_apply_apply (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
    (e₂ e₂' : Trivialization F₂ (π F₂ E₂))
    [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜] (b : B)
    (L : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂) (v : ι → F₁) :
    continuousMultilinearMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂' b L v =
      e₂.coordChangeL 𝕜 e₂' b (L fun i ↦ e₁'.coordChangeL 𝕜 e₁ b (v i)) :=
  rfl

variable [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁]
variable [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]
variable {e₁ e₁' : Trivialization F₁ (π F₁ E₁)} {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}

/-- The coordinate changes of the bundle of continuous multilinear maps are continuous on the
intersection of the base sets: in each slot they are given by the coordinate changes of `E₁` and
`E₂`, and `ContinuousMultilinearMap.compContinuousLinearMapL` depends multilinearly, hence
continuously, on the maps it precomposes with. -/
theorem continuousOn_continuousMultilinearMapCoordChange [Finite ι]
    [VectorBundle 𝕜 F₁ E₁] [VectorBundle 𝕜 F₂ E₂]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁'] [MemTrivializationAtlas e₂]
    [MemTrivializationAtlas e₂'] :
    ContinuousOn (continuousMultilinearMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  cases nonempty_fintype ι
  refine ContinuousOn.clm_comp ?_ ?_
  · have hc : Continuous fun L : F₁ →L[𝕜] F₁ ↦
        ContinuousMultilinearMap.compContinuousLinearMapL (F := F₂) fun _ : ι ↦ L :=
      (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜
        (fun _ : ι ↦ F₁) (fun _ : ι ↦ F₁) F₂).coe_continuous.comp
        (continuous_pi fun _ ↦ continuous_id)
    exact hc.comp_continuousOn
      ((continuousOn_coordChange 𝕜 e₁' e₁).mono (by mfld_set_tac))
  · exact (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜 (fun _ : ι ↦ F₁) F₂ F₂).continuous
      |>.comp_continuousOn ((continuousOn_coordChange 𝕜 e₂ e₂').mono (by mfld_set_tac))

variable [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜]

variable (𝕜 ι e₁ e₂) in
/-- Given trivializations `e₁`, `e₂` of the vector bundles `E₁`, `E₂`, the induced
pretrivialization of the bundle of continuous multilinear maps from `E₁` to `E₂`, over
`e₁.baseSet ∩ e₂.baseSet`. It becomes a trivialization once the total space carries the topology
of `Bundle.ContinuousMultilinearMap.vectorPrebundle`. -/
def continuousMultilinearMap :
    Pretrivialization (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
      (π (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
        (fun x ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ x) (E₂ x))) where
  toFun p := ⟨p.proj, (e₂.continuousLinearMapAt 𝕜 p.proj).compContinuousMultilinearMap <|
    p.snd.compContinuousLinearMap fun _ ↦ e₁.symmL 𝕜 p.proj⟩
  invFun p := ⟨p.1, (e₂.symmL 𝕜 p.1).compContinuousMultilinearMap <|
    p.2.compContinuousLinearMap fun _ ↦ e₁.continuousLinearMapAt 𝕜 p.1⟩
  source := Bundle.TotalSpace.proj ⁻¹' (e₁.baseSet ∩ e₂.baseSet)
  target := (e₁.baseSet ∩ e₂.baseSet) ×ˢ Set.univ
  map_source' := fun ⟨_, _⟩ h ↦ ⟨h, Set.mem_univ _⟩
  map_target' := fun ⟨_, _⟩ h ↦ h.1
  left_inv' := by
    rintro ⟨x, L⟩ ⟨h₁, h₂⟩
    simp only [TotalSpace.mk_inj]
    ext v
    simp [h₁, h₂]
  right_inv' := by
    rintro ⟨x, f⟩ ⟨⟨h₁, h₂⟩, -⟩
    simp only [Prod.mk_right_inj]
    ext v
    simp [h₁, h₂]
  open_target := (e₁.open_baseSet.inter e₂.open_baseSet).prod isOpen_univ
  baseSet := e₁.baseSet ∩ e₂.baseSet
  open_baseSet := e₁.open_baseSet.inter e₂.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

instance continuousMultilinearMap.isLinear
    [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)] :
    (Pretrivialization.continuousMultilinearMap 𝕜 ι e₁ e₂).IsLinear 𝕜 where
  linear x _ :=
    { map_add L L' := by ext; simp [continuousMultilinearMap, Pretrivialization.toFun']
      map_smul c L := by ext; simp [continuousMultilinearMap, Pretrivialization.toFun'] }

theorem continuousMultilinearMap_apply
    (p : TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
      fun x ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ x) (E₂ x)) :
    continuousMultilinearMap 𝕜 ι e₁ e₂ p =
      ⟨p.proj, (e₂.continuousLinearMapAt 𝕜 p.proj).compContinuousMultilinearMap <|
        p.snd.compContinuousLinearMap fun _ ↦ e₁.symmL 𝕜 p.proj⟩ :=
  rfl

theorem continuousMultilinearMap_symm_apply
    (p : B × ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂) :
    (continuousMultilinearMap 𝕜 ι e₁ e₂).toPartialEquiv.symm p =
      ⟨p.1, (e₂.symmL 𝕜 p.1).compContinuousMultilinearMap <|
        p.2.compContinuousLinearMap fun _ ↦ e₁.continuousLinearMapAt 𝕜 p.1⟩ :=
  rfl

theorem continuousMultilinearMap_symm_apply' {b : B} (hb : b ∈ e₁.baseSet ∩ e₂.baseSet)
    (L : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂) :
    (continuousMultilinearMap 𝕜 ι e₁ e₂).symm b L =
      ((e₂.symmL 𝕜 b).compContinuousMultilinearMap <|
        L.compContinuousLinearMap fun _ ↦ e₁.continuousLinearMapAt 𝕜 b) := by
  rw [Pretrivialization.symm_apply]
  · rfl
  · exact hb

theorem continuousMultilinearMapCoordChange_apply (b : B)
    (hb : b ∈ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet))
    (L : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂) :
    continuousMultilinearMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂' b L =
      (continuousMultilinearMap 𝕜 ι e₁' e₂'
        ⟨b, (continuousMultilinearMap 𝕜 ι e₁ e₂).symm b L⟩).2 := by
  ext v
  simp only [mem_inter_iff] at hb
  simp [continuousMultilinearMapCoordChange_apply_apply, continuousMultilinearMap_apply,
    Trivialization.coordChangeL_apply,
    continuousMultilinearMap_symm_apply' hb.left, hb]

end Bundle.Pretrivialization

/-!
### Vector bundle structure
-/

namespace Bundle.ContinuousMultilinearMap

open Pretrivialization

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]

variable {B : Type*} [TopologicalSpace B]

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

variable (𝕜 ι F₁ E₁ F₂ E₂) in
/-- The continuous multilinear maps between two topological vector bundles form a
`VectorPrebundle`: its pretrivializations are those induced by pairs of trivializations in the
atlases of `E₁` and `E₂`. This is the auxiliary construction behind the topology and the
`FiberBundle` and `VectorBundle` instances on the bundle of continuous multilinear maps. -/
def vectorPrebundle :
    VectorPrebundle 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
      (fun x ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ x) (E₂ x)) where
  pretrivializationAtlas :=
    {e | ∃ (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
      (_ : MemTrivializationAtlas e₁) (_ : MemTrivializationAtlas e₂),
        e = Pretrivialization.continuousMultilinearMap 𝕜 ι e₁ e₂}
  pretrivialization_linear' := by
    rintro _ ⟨e₁, he₁, e₂, he₂, rfl⟩
    infer_instance
  pretrivializationAt x := Pretrivialization.continuousMultilinearMap 𝕜 ι
    (trivializationAt F₁ E₁ x) (trivializationAt F₂ E₂ x)
  mem_base_pretrivializationAt x :=
    ⟨mem_baseSet_trivializationAt F₁ E₁ x, mem_baseSet_trivializationAt F₂ E₂ x⟩
  pretrivialization_mem_atlas x :=
    ⟨trivializationAt F₁ E₁ x, trivializationAt F₂ E₂ x, inferInstance, inferInstance, rfl⟩
  exists_coordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨continuousMultilinearMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂',
      continuousOn_continuousMultilinearMapCoordChange,
      continuousMultilinearMapCoordChange_apply⟩
  totalSpaceMk_isInducing b := by
    simp only [Function.comp_def, continuousMultilinearMap_apply, isInducing_const_prod]
    let L₁ : E₁ b ≃L[𝕜] F₁ :=
      (trivializationAt F₁ E₁ b).continuousLinearEquivAt 𝕜 b
        (mem_baseSet_trivializationAt _ _ _)
    let L₂ : E₂ b ≃L[𝕜] F₂ :=
      (trivializationAt F₂ E₂ b).continuousLinearEquivAt 𝕜 b
        (mem_baseSet_trivializationAt _ _ _)
    convert! ((L₂.continuousMultilinearMapCongrRight (fun _ : ι ↦ E₁ b)).trans
      (ContinuousLinearEquiv.continuousMultilinearMapCongrLeft F₂
        fun _ : ι ↦ L₁.symm)).toHomeomorph.isInducing
    ext f
    simp [Trivialization.linearMapAt_def_of_mem _ (mem_baseSet_trivializationAt _ _ _), L₁, L₂,
      mem_baseSet_trivializationAt]

/-- The topology on the total space of the bundle of continuous multilinear maps between two
vector bundles with normed model fibres over the same base. -/
instance instTopologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
      (fun x ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ x) (E₂ x))) :=
  (vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).totalSpaceTopology

/-- The continuous multilinear maps between two vector bundles form a fiber bundle. -/
instance instFiberBundle :
    FiberBundle (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
      fun x ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ x) (E₂ x) :=
  (vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).toFiberBundle

/-- The continuous multilinear maps between two vector bundles form a vector bundle. -/
instance instVectorBundle :
    VectorBundle 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
      (fun x ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ x) (E₂ x)) :=
  (vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).toVectorBundle

end Bundle.ContinuousMultilinearMap

/-!
### Trivializations of the bundle of continuous multilinear maps
-/

namespace Bundle.Trivialization

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]

variable {B : Type*} [TopologicalSpace B]

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

variable {e₁ : Trivialization F₁ (π F₁ E₁)} {e₂ : Trivialization F₂ (π F₂ E₂)}
variable [he₁ : MemTrivializationAtlas e₁] [he₂ : MemTrivializationAtlas e₂]

variable (𝕜 ι e₁ e₂) in
/-- Given trivializations `e₁`, `e₂` in the atlases of the vector bundles `E₁`, `E₂`, the induced
trivialization of the bundle of continuous multilinear maps from `E₁` to `E₂`, with base set
`e₁.baseSet ∩ e₂.baseSet`. -/
def continuousMultilinearMap :
    Trivialization (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
      (π (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
        (fun x ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ x) (E₂ x))) :=
  VectorPrebundle.trivializationOfMemPretrivializationAtlas _ ⟨e₁, e₂, he₁, he₂, rfl⟩

instance memTrivializationAtlas_continuousMultilinearMap :
    MemTrivializationAtlas
      (e₁.continuousMultilinearMap 𝕜 ι e₂ :
        Trivialization (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
          (π (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
            (fun x ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ x) (E₂ x)))) :=
  ⟨⟨_, ⟨e₁, e₂, by infer_instance, by infer_instance, rfl⟩, rfl⟩⟩

@[simp]
theorem baseSet_continuousMultilinearMap :
    (e₁.continuousMultilinearMap 𝕜 ι e₂).baseSet = e₁.baseSet ∩ e₂.baseSet :=
  rfl

theorem continuousMultilinearMap_apply
    (p : TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
      (fun x ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ x) (E₂ x))) :
    e₁.continuousMultilinearMap 𝕜 ι e₂ p =
      ⟨p.proj, (e₂.continuousLinearMapAt 𝕜 p.proj : _ →L[𝕜] _).compContinuousMultilinearMap p.snd
        |>.compContinuousLinearMap fun _ ↦ (e₁.symmL 𝕜 p.proj : F₁ →L[𝕜] E₁ p.proj)⟩ :=
  rfl

end Bundle.Trivialization

/-!
### `trivializationAt` for the bundle of continuous multilinear maps
-/

namespace FiberBundle

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]

variable {B : Type*} [TopologicalSpace B]

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

theorem trivializationAt_continuousMultilinearMap (x₀ : B) :
    trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
        (fun x ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ x) (E₂ x)) x₀ =
      (trivializationAt F₁ E₁ x₀).continuousMultilinearMap 𝕜 ι (trivializationAt F₂ E₂ x₀) :=
  rfl

theorem trivializationAt_continuousMultilinearMap_apply (x₀ : B)
    (x : TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
      (fun x ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ x) (E₂ x))) :
    trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
        (fun x ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ x) (E₂ x)) x₀ x =
      ⟨x.proj, inCoordinates F₁ F₂ x₀ x.proj x₀ x.proj x.snd⟩ :=
  rfl

@[simp, mfld_simps]
theorem trivializationAt_continuousMultilinearMap_source (x₀ : B) :
    (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
        (fun x ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ x) (E₂ x)) x₀).source =
      π (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
          (fun x ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ x) (E₂ x)) ⁻¹'
        ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) :=
  rfl

@[simp, mfld_simps]
theorem trivializationAt_continuousMultilinearMap_target (x₀ : B) :
    (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
        (fun x ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ x) (E₂ x)) x₀).target =
      ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) ×ˢ Set.univ :=
  rfl

@[simp]
theorem trivializationAt_continuousMultilinearMap_baseSet (x₀ : B) :
    (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
        (fun x ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ x) (E₂ x)) x₀).baseSet =
      (trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet :=
  rfl

end FiberBundle

/-!
### Continuity of maps into the bundle of continuous multilinear maps
-/

namespace TauCeti

section Continuity

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]

variable {B : Type*} [TopologicalSpace B]

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

variable {X : Type*} [TopologicalSpace X] {s : Set X} {x₀ : X}

/-- A map into the bundle of continuous multilinear maps is continuous within a set at a point
exactly when its projection is and its fibre component, read in the trivializations at the
image of the point, is. -/
theorem continuousWithinAt_continuousMultilinearMap_bundle
    (f : X → TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
      (fun x ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ x) (E₂ x))) :
    ContinuousWithinAt f s x₀ ↔
      ContinuousWithinAt (fun x ↦ (f x).proj) s x₀ ∧
        ContinuousWithinAt
          (fun x ↦
            inCoordinates F₁ F₂ (f x₀).proj (f x).proj (f x₀).proj (f x).proj (f x).snd) s x₀ :=
  FiberBundle.continuousWithinAt_totalSpace ..

/-- A map into the bundle of continuous multilinear maps is continuous at a point exactly when
its projection is and its fibre component, read in the trivializations at the image of the
point, is. -/
theorem continuousAt_continuousMultilinearMap_bundle
    (f : X → TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)
      (fun x ↦ ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E₁ x) (E₂ x))) :
    ContinuousAt f x₀ ↔
      ContinuousAt (fun x ↦ (f x).proj) x₀ ∧
        ContinuousAt
          (fun x ↦
            inCoordinates F₁ F₂ (f x₀).proj (f x).proj (f x₀).proj (f x).proj (f x).snd) x₀ :=
  FiberBundle.continuousAt_totalSpace ..

end Continuity

end TauCeti
