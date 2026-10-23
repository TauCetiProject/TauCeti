/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic
public import TauCeti.Topology.Algebra.Module.SymmetricBilinear

/-!
# The vector bundle of symmetric bilinear maps

Let `V` be a topological vector bundle with model fibre `F` over a normed field `𝕜`, and let `G`
be a normed space. The fibres `symmetricBilinearMaps 𝕜 (V x) G` of symmetric continuous bilinear
maps `V x → V x → G` form a topological vector bundle with model fibre
`symmetricBilinearMaps 𝕜 F G`. For `G = ℝ` and `V` the tangent bundle this is the bundle
`Sym²(T*M)` of symmetric covariant two-tensors, the ambient bundle of Riemannian metrics.

Each trivialization `e` of `V` induces the trivialization `e.symmetricBilinearMaps 𝕜 G`, which
reads a symmetric bilinear map in the coordinates of `e`, pulling both arguments back along
`e.symmL`. The coordinate changes are the pullbacks along the coordinate changes of `V`. The
topology on the total space is then constructed by Mathlib's `VectorPrebundle` machinery.

The construction follows Mathlib's bundle of continuous alternating maps,
`Mathlib.Topology.VectorBundle.ContinuousAlternatingMap`, by Yury Kudryashov,
Heather Macbeth and Floris van Doorn.

## Main definitions

* `Bundle.Pretrivialization.symmetricBilinearMaps`: the pretrivialization induced by a
  trivialization of `V`.
* `TauCeti.symmetricBilinearMapsVectorPrebundle`: the vector prebundle structure.
* `Bundle.Trivialization.symmetricBilinearMaps`: the induced trivialization, in the atlas of the
  bundle of symmetric bilinear maps.

The instances `FiberBundle` and `VectorBundle` for `fun x ↦ symmetricBilinearMaps 𝕜 (V x) G`
are registered.
-/

public section

noncomputable section

open Bundle Set Topology

open TauCeti

/-! ### Pretrivializations -/

namespace Bundle.Pretrivialization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable (𝕜) in
/-- The coordinate change between the trivializations of the bundle of symmetric bilinear maps
induced by trivializations `e` and `e'` of `V`: pullback along the coordinate change of `V`
from `e'` to `e`. -/
def symmetricBilinearMapsCoordChange (e e' : Trivialization F (π F V)) [e.IsLinear 𝕜]
    [e'.IsLinear 𝕜] (b : B) :
    TauCeti.symmetricBilinearMaps 𝕜 F G →L[𝕜] TauCeti.symmetricBilinearMaps 𝕜 F G :=
  (e'.coordChangeL 𝕜 e b : F →L[𝕜] F).symmetricBilinearMapsComp

omit [∀ x, TopologicalSpace (V x)] [FiberBundle F V] in
theorem symmetricBilinearMapsCoordChange_def (e e' : Trivialization F (π F V)) [e.IsLinear 𝕜]
    [e'.IsLinear 𝕜] :
    symmetricBilinearMapsCoordChange 𝕜 G e e' =
      fun b ↦ (e'.coordChangeL 𝕜 e b : F →L[𝕜] F).symmetricBilinearMapsComp :=
  (rfl)

theorem continuousOn_symmetricBilinearMapsCoordChange [VectorBundle 𝕜 F V]
    (e e' : Trivialization F (π F V)) [MemTrivializationAtlas e] [MemTrivializationAtlas e'] :
    ContinuousOn (symmetricBilinearMapsCoordChange 𝕜 G e e') (e.baseSet ∩ e'.baseSet) := by
  rw [symmetricBilinearMapsCoordChange_def]
  refine ContinuousOn.symmetricBilinearMapsComp ?_
  exact (continuousOn_coordChange 𝕜 e' e).mono (inter_comm _ _).subset

variable (𝕜) in
/-- A trivialization `e` of `V` induces a pretrivialization of the bundle of symmetric bilinear
maps on `V`, reading each map in the coordinates of `e`. -/
def symmetricBilinearMaps (e : Trivialization F (π F V)) [e.IsLinear 𝕜] :
    Pretrivialization (TauCeti.symmetricBilinearMaps 𝕜 F G)
      (π (TauCeti.symmetricBilinearMaps 𝕜 F G)
        fun x ↦ TauCeti.symmetricBilinearMaps 𝕜 (V x) G) where
  toFun p := ⟨p.1, (e.symmL 𝕜 p.1).symmetricBilinearMapsComp p.2⟩
  invFun p := ⟨p.1, (e.continuousLinearMapAt 𝕜 p.1).symmetricBilinearMapsComp p.2⟩
  source := TotalSpace.proj ⁻¹' e.baseSet
  target := e.baseSet ×ˢ univ
  map_source' _ h := ⟨h, mem_univ _⟩
  map_target' _ h := h.1
  left_inv' := by
    rintro ⟨x, b⟩ h
    simp only [TotalSpace.mk_inj]
    ext v w
    simp only [ContinuousLinearMap.symmetricBilinearMapsComp_apply,
      e.symmL_continuousLinearMapAt h]
  right_inv' := by
    rintro ⟨x, b⟩ ⟨h, -⟩
    simp only [Prod.mk_right_inj]
    ext v w
    simp only [ContinuousLinearMap.symmetricBilinearMapsComp_apply,
      e.continuousLinearMapAt_symmL h]
  open_target := e.open_baseSet.prod isOpen_univ
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

variable {e : Trivialization F (π F V)} [e.IsLinear 𝕜]

instance symmetricBilinearMaps.isLinear : (symmetricBilinearMaps 𝕜 G e).IsLinear 𝕜 where
  linear x _ :=
    { map_add b c := by ext; simp [symmetricBilinearMaps, Pretrivialization.toFun']
      map_smul a b := by ext; simp [symmetricBilinearMaps, Pretrivialization.toFun'] }

theorem symmetricBilinearMaps_apply
    (p : TotalSpace (TauCeti.symmetricBilinearMaps 𝕜 F G)
      fun x ↦ TauCeti.symmetricBilinearMaps 𝕜 (V x) G) :
    symmetricBilinearMaps 𝕜 G e p = (p.1, (e.symmL 𝕜 p.1).symmetricBilinearMapsComp p.2) :=
  (rfl)

@[simp]
theorem baseSet_symmetricBilinearMaps : (symmetricBilinearMaps 𝕜 G e).baseSet = e.baseSet :=
  (rfl)

theorem symmetricBilinearMaps_symm_apply {b : B} (hb : b ∈ e.baseSet)
    (β : TauCeti.symmetricBilinearMaps 𝕜 F G) :
    (symmetricBilinearMaps 𝕜 G e).symm b β =
      (e.continuousLinearMapAt 𝕜 b).symmetricBilinearMapsComp β := by
  rw [Pretrivialization.symm_apply _ hb]
  rfl

theorem symmetricBilinearMapsCoordChange_apply {e' : Trivialization F (π F V)} [e'.IsLinear 𝕜]
    {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) (β : TauCeti.symmetricBilinearMaps 𝕜 F G) :
    symmetricBilinearMapsCoordChange 𝕜 G e e' b β =
      (symmetricBilinearMaps 𝕜 G e' ⟨b, (symmetricBilinearMaps 𝕜 G e).symm b β⟩).2 := by
  ext v w
  simp [symmetricBilinearMapsCoordChange, symmetricBilinearMaps_apply,
    symmetricBilinearMaps_symm_apply G hb.1, Trivialization.coordChangeL_apply e' e ⟨hb.2, hb.1⟩,
    e'.symmL_apply hb.2, e.coe_linearMapAt_of_mem hb.1]

end Bundle.Pretrivialization

/-! ### The vector bundle structure -/

namespace TauCeti

open Pretrivialization

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {B : Type*} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] (V : B → Type*)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The symmetric bilinear maps on the fibres of a vector bundle form a vector prebundle. This
auxiliary structure collects the induced pretrivializations; it provides the topology of the
total space. -/
def symmetricBilinearMapsVectorPrebundle :
    VectorPrebundle 𝕜 (symmetricBilinearMaps 𝕜 F G)
      fun x ↦ symmetricBilinearMaps 𝕜 (V x) G where
  pretrivializationAtlas :=
    {e' | ∃ (e : Trivialization F (π F V)) (_ : MemTrivializationAtlas e),
      e' = Pretrivialization.symmetricBilinearMaps 𝕜 G e}
  pretrivialization_linear' := by
    rintro _ ⟨e, he, rfl⟩
    infer_instance
  pretrivializationAt x := Pretrivialization.symmetricBilinearMaps 𝕜 G (trivializationAt F V x)
  mem_base_pretrivializationAt x := mem_baseSet_trivializationAt F V x
  pretrivialization_mem_atlas x := ⟨trivializationAt F V x, inferInstance, rfl⟩
  exists_coordChange := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    exact ⟨symmetricBilinearMapsCoordChange 𝕜 G e e',
      continuousOn_symmetricBilinearMapsCoordChange G e e',
      fun _ hb ↦ symmetricBilinearMapsCoordChange_apply G hb⟩
  totalSpaceMk_isInducing b := by
    simp only [Function.comp_def, symmetricBilinearMaps_apply, isInducing_const_prod]
    let L : V b ≃L[𝕜] F := (trivializationAt F V b).continuousLinearEquivAt 𝕜 b
      (mem_baseSet_trivializationAt _ _ _)
    convert (L.symmetricBilinearMapsCongr (G := G)).toHomeomorph.isInducing
    ext β v
    simp [L, Trivialization.symmL_apply _ (mem_baseSet_trivializationAt F V b)]

variable {𝕜 F V G} in
/-- The pretrivializations in the atlas of the bundle of symmetric bilinear maps are those induced
by the trivializations in the atlas of `V`. -/
theorem mem_pretrivializationAtlas_symmetricBilinearMapsVectorPrebundle
    {e' : Pretrivialization (symmetricBilinearMaps 𝕜 F G)
      (π (symmetricBilinearMaps 𝕜 F G) fun x ↦ symmetricBilinearMaps 𝕜 (V x) G)} :
    e' ∈ (symmetricBilinearMapsVectorPrebundle 𝕜 F V G).pretrivializationAtlas ↔
      ∃ (e : Trivialization F (π F V)) (_ : MemTrivializationAtlas e),
        e' = Pretrivialization.symmetricBilinearMaps 𝕜 G e :=
  Iff.rfl

/-- The topology on the total space of the bundle of symmetric bilinear maps. -/
instance instTopologicalSpaceTotalSpaceSymmetricBilinearMaps :
    TopologicalSpace (TotalSpace (symmetricBilinearMaps 𝕜 F G)
      fun x ↦ symmetricBilinearMaps 𝕜 (V x) G) :=
  (symmetricBilinearMapsVectorPrebundle 𝕜 F V G).totalSpaceTopology

/-- The symmetric bilinear maps on the fibres of a vector bundle form a fibre bundle. -/
instance instFiberBundleSymmetricBilinearMaps :
    FiberBundle (symmetricBilinearMaps 𝕜 F G) fun x ↦ symmetricBilinearMaps 𝕜 (V x) G :=
  (symmetricBilinearMapsVectorPrebundle 𝕜 F V G).toFiberBundle

/-- The symmetric bilinear maps on the fibres of a vector bundle form a vector bundle. -/
instance instVectorBundleSymmetricBilinearMaps :
    VectorBundle 𝕜 (symmetricBilinearMaps 𝕜 F G) fun x ↦ symmetricBilinearMaps 𝕜 (V x) G :=
  (symmetricBilinearMapsVectorPrebundle 𝕜 F V G).toVectorBundle

end TauCeti

/-! ### Trivializations -/

namespace Bundle.Trivialization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  (e : Trivialization F (π F V)) [he : MemTrivializationAtlas e]

variable (𝕜) in
/-- The trivialization of the bundle of symmetric bilinear maps induced by a trivialization `e`
in the atlas of `V`, with base set `e.baseSet`. -/
def symmetricBilinearMaps :
    Trivialization (TauCeti.symmetricBilinearMaps 𝕜 F G)
      (π (TauCeti.symmetricBilinearMaps 𝕜 F G)
        fun x ↦ TauCeti.symmetricBilinearMaps 𝕜 (V x) G) :=
  VectorPrebundle.trivializationOfMemPretrivializationAtlas _ ⟨e, he, rfl⟩

instance memTrivializationAtlas_symmetricBilinearMaps :
    MemTrivializationAtlas (e.symmetricBilinearMaps 𝕜 G) :=
  ⟨⟨_, ⟨e, he, rfl⟩, rfl⟩⟩

@[simp]
theorem baseSet_symmetricBilinearMaps : (e.symmetricBilinearMaps 𝕜 G).baseSet = e.baseSet :=
  (rfl)

theorem symmetricBilinearMaps_apply
    (p : TotalSpace (TauCeti.symmetricBilinearMaps 𝕜 F G)
      fun x ↦ TauCeti.symmetricBilinearMaps 𝕜 (V x) G) :
    e.symmetricBilinearMaps 𝕜 G p = (p.1, (e.symmL 𝕜 p.1).symmetricBilinearMapsComp p.2) :=
  (rfl)

end Bundle.Trivialization

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The chosen trivialization of the bundle of symmetric bilinear maps at `x₀` is induced by the
chosen trivialization of `V` at `x₀`. -/
theorem trivializationAt_symmetricBilinearMaps (x₀ : B) :
    trivializationAt (symmetricBilinearMaps 𝕜 F G)
        (fun x ↦ symmetricBilinearMaps 𝕜 (V x) G) x₀ =
      (trivializationAt F V x₀).symmetricBilinearMaps 𝕜 G :=
  (rfl)

theorem trivializationAt_symmetricBilinearMaps_apply (x₀ : B)
    (p : TotalSpace (symmetricBilinearMaps 𝕜 F G) fun x ↦ symmetricBilinearMaps 𝕜 (V x) G) :
    trivializationAt (symmetricBilinearMaps 𝕜 F G)
        (fun x ↦ symmetricBilinearMaps 𝕜 (V x) G) x₀ p =
      (p.1, ((trivializationAt F V x₀).symmL 𝕜 p.1).symmetricBilinearMapsComp p.2) :=
  (rfl)

@[simp]
theorem baseSet_trivializationAt_symmetricBilinearMaps (x₀ : B) :
    (trivializationAt (symmetricBilinearMaps 𝕜 F G)
        (fun x ↦ symmetricBilinearMaps 𝕜 (V x) G) x₀).baseSet =
      (trivializationAt F V x₀).baseSet :=
  (rfl)

end TauCeti
