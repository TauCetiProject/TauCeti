/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic

/-!
# Point-indexed coordinate cores of vector bundles

A vector bundle with model fibre `F` determines a `VectorBundleCore` whose charts
are indexed by the base itself. Its preferred chart at `b` is the original
preferred trivialization at `b`. Only open subsets of the base and continuous
linear maps between copies of `F` are stored: the universe of the original
fibres does not occur in the type of the core.

`pointIndexedCoreHomeomorph` identifies the reconstructed total space with the
original total space, over the identity of the base. On each fibre it is the
continuous linear equivalence `pointIndexedCoreFiberEquiv`. Thus passing to
coordinate data loses neither the topology nor the linear bundle structure.
Applied on each locally constant rank stratum with model `Fin n → 𝕜`, this is
the reconstruction step in a small coordinate presentation of finite-rank bundles.
No compactness, separation, or finite-dimensionality assumption is needed.

The construction uses Mathlib's `Bundle.Trivialization.coordChangeL` and
`VectorBundleCore` gluing construction.
-/

public section

open Bundle Set Topology

namespace TauCeti

universe u v w

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {B : Type u} [TopologicalSpace B]
  (F : Type w) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (E : B → Type v) [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- Coordinate data indexed by base points, with the chart at each point selected
by the original bundle's `trivializationAt`. The stored data are independent of
the universe of `E`. -/
noncomputable def pointIndexedCore : VectorBundleCore 𝕜 B F B where
  baseSet b := (trivializationAt F E b).baseSet
  isOpen_baseSet b := (trivializationAt F E b).open_baseSet
  indexAt := id
  mem_baseSet_at b := mem_baseSet_trivializationAt F E b
  coordChange b c x := (trivializationAt F E b).coordChangeL 𝕜
    (trivializationAt F E c) x
  coordChange_self b x hx v := by
    simp only [ContinuousLinearEquiv.coe_coe]
    rw [Trivialization.coe_coordChangeL (R := 𝕜) _ _ ⟨hx, hx⟩]
    exact ((trivializationAt F E b).linearEquivAt 𝕜 x hx).apply_symm_apply v
  continuousOn_coordChange b c := continuousOn_coordChange 𝕜 _ _
  coordChange_comp b c d x hx v := by
    simp only [ContinuousLinearEquiv.coe_coe]
    rw [Trivialization.coe_coordChangeL _ _ ⟨hx.1.1, hx.1.2⟩,
      Trivialization.coe_coordChangeL _ _ ⟨hx.1.2, hx.2⟩,
      Trivialization.coe_coordChangeL _ _ ⟨hx.1.1, hx.2⟩]
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

@[simp] theorem pointIndexedCore_localTriv_baseSet (b : B) :
    ((pointIndexedCore 𝕜 F E).localTriv b).baseSet = (trivializationAt F E b).baseSet := (rfl)

@[simp] theorem pointIndexedCore_indexAt (b : B) :
    (pointIndexedCore 𝕜 F E).indexAt b = b := (rfl)

/-- The core's preferred local trivialization at `b` is its chart indexed by `b`. -/
@[simp] theorem pointIndexedCore_localTrivAt (b : B) :
    (pointIndexedCore 𝕜 F E).localTrivAt b = (pointIndexedCore 𝕜 F E).localTriv b := (rfl)

/-- The reconstructed bundle's preferred trivialization at `b` is the core chart at `b`. -/
@[simp] theorem pointIndexedCore_trivializationAt (b : B) :
    trivializationAt F (pointIndexedCore 𝕜 F E).Fiber b =
      (pointIndexedCore 𝕜 F E).localTriv b := (rfl)

@[simp] theorem pointIndexedCore_coordChange (b c x : B) :
    (pointIndexedCore 𝕜 F E).coordChange b c x =
      ((trivializationAt F E b).coordChangeL 𝕜 (trivializationAt F E c) x : F →L[𝕜] F) :=
  (rfl)

/-- The reconstructed fibre at `b` is identified linearly and continuously with
the original fibre by the inverse of the preferred chart at `b`. -/
noncomputable def pointIndexedCoreFiberEquiv (b : B) :
    (pointIndexedCore 𝕜 F E).Fiber b ≃L[𝕜] E b :=
  (VectorBundle.continuousLinearEquivAt 𝕜 F E b).symm

@[simp] theorem pointIndexedCoreFiberEquiv_apply (b : B) (v : F) :
    pointIndexedCoreFiberEquiv 𝕜 F E b v =
      (trivializationAt F E b).symm b v := (rfl)

@[simp] theorem pointIndexedCoreFiberEquiv_symm_apply (b : B) (v : E b) :
    (pointIndexedCoreFiberEquiv 𝕜 F E b).symm v =
      ((trivializationAt F E b) ⟨b, v⟩).2 := (rfl)

private noncomputable def pointIndexedCoreTotalEquiv :
    (pointIndexedCore 𝕜 F E).TotalSpace ≃ TotalSpace F E where
  toFun p := ⟨p.proj, pointIndexedCoreFiberEquiv 𝕜 F E p.proj p.2⟩
  invFun p := ⟨p.proj, (pointIndexedCoreFiberEquiv 𝕜 F E p.proj).symm p.2⟩
  left_inv p := by
    dsimp only
    rw [ContinuousLinearEquiv.symm_apply_apply]
  right_inv p := by
    dsimp only
    rw [ContinuousLinearEquiv.apply_symm_apply]

private theorem pointIndexedCoreTotalEquiv_symm_proj (p : TotalSpace F E) :
    ((pointIndexedCoreTotalEquiv 𝕜 F E).symm p).proj = p.proj := (rfl)

private theorem trivializationAt_pointIndexedCoreTotalEquiv (b : B)
    (p : (pointIndexedCore 𝕜 F E).TotalSpace)
    (hp : p.proj ∈ (trivializationAt F E b).baseSet) :
    (trivializationAt F E b) (pointIndexedCoreTotalEquiv 𝕜 F E p) =
      (pointIndexedCore 𝕜 F E).localTriv b p := by
  rw [VectorBundleCore.localTriv_apply, pointIndexedCore_coordChange,
    pointIndexedCore_indexAt]
  exact ((trivializationAt F E p.proj).mk_coordChangeL (trivializationAt F E b)
    ⟨mem_baseSet_trivializationAt F E p.proj, hp⟩ p.2).symm

private theorem continuous_pointIndexedCoreTotalEquiv :
    Continuous (pointIndexedCoreTotalEquiv 𝕜 F E) := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(FiberBundle.continuous_proj F (pointIndexedCore 𝕜 F E).Fiber).continuousAt, ?_⟩
  have hp : p ∈ ((pointIndexedCore 𝕜 F E).localTriv p.proj).source :=
    (pointIndexedCore 𝕜 F E).mem_source_at p.proj p.2
  have hc := (((pointIndexedCore 𝕜 F E).localTriv p.proj).continuousOn.continuousAt
    (((pointIndexedCore 𝕜 F E).localTriv p.proj).open_source.mem_nhds hp)).snd
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [((pointIndexedCore 𝕜 F E).localTriv p.proj).open_source.mem_nhds hp]
    with q hq
  exact congrArg Prod.snd (trivializationAt_pointIndexedCoreTotalEquiv 𝕜 F E p.proj q
    (((pointIndexedCore 𝕜 F E).localTriv p.proj).mem_source.1 hq))

private theorem continuous_pointIndexedCoreTotalEquiv_symm :
    Continuous (pointIndexedCoreTotalEquiv 𝕜 F E).symm := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(FiberBundle.continuous_proj F E).continuousAt, ?_⟩
  have hp := FiberBundle.mem_trivializationAt_proj_source (x := p)
  have hc := ((trivializationAt F E p.proj).continuousOn.continuousAt
    ((trivializationAt F E p.proj).open_source.mem_nhds hp)).snd
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt F E p.proj).open_source.mem_nhds hp] with q hq
  simp only [pointIndexedCore_trivializationAt, pointIndexedCoreTotalEquiv_symm_proj]
  simpa only [Equiv.apply_symm_apply] using
    congrArg Prod.snd (trivializationAt_pointIndexedCoreTotalEquiv 𝕜 F E p.proj
      ((pointIndexedCoreTotalEquiv 𝕜 F E).symm q)
      ((trivializationAt F E p.proj).mem_source.1 hq)).symm

/-- Reconstruction of a point-indexed coordinate core is homeomorphic to the
original bundle. The homeomorphism covers the identity and is continuous linear
on each fibre, via `pointIndexedCoreFiberEquiv`. -/
noncomputable def pointIndexedCoreHomeomorph :
    (pointIndexedCore 𝕜 F E).TotalSpace ≃ₜ TotalSpace F E where
  toEquiv := pointIndexedCoreTotalEquiv 𝕜 F E
  continuous_toFun := continuous_pointIndexedCoreTotalEquiv 𝕜 F E
  continuous_invFun := continuous_pointIndexedCoreTotalEquiv_symm 𝕜 F E

@[simp] theorem pointIndexedCoreHomeomorph_apply (p : (pointIndexedCore 𝕜 F E).TotalSpace) :
    pointIndexedCoreHomeomorph 𝕜 F E p =
      ⟨p.proj, pointIndexedCoreFiberEquiv 𝕜 F E p.proj p.2⟩ := (rfl)

@[simp] theorem pointIndexedCoreHomeomorph_symm_apply (p : TotalSpace F E) :
    (pointIndexedCoreHomeomorph 𝕜 F E).symm p =
      ⟨p.proj, (pointIndexedCoreFiberEquiv 𝕜 F E p.proj).symm p.2⟩ := (rfl)

/-- The reconstruction homeomorphism intertwines every core chart with its
original chart, wherever that chart is defined. -/
theorem trivializationAt_pointIndexedCoreHomeomorph (b : B)
    (p : (pointIndexedCore 𝕜 F E).TotalSpace)
    (hp : p.proj ∈ (trivializationAt F E b).baseSet) :
    (trivializationAt F E b) (pointIndexedCoreHomeomorph 𝕜 F E p) =
      (pointIndexedCore 𝕜 F E).localTriv b p :=
  trivializationAt_pointIndexedCoreTotalEquiv 𝕜 F E b p hp

end TauCeti
