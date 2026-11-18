/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Coordinate cores from families of linear trivializations

Given an indexed family `e : ι → Trivialization F (π F E)` of linear trivializations whose pairwise
coordinate changes `coordChangeL` are continuous on base-set overlaps and a point selector
`idx : B → ι` satisfying `b ∈ (e (idx b)).baseSet`, `VectorBundleCore.ofTrivializations` packages
the open cover and transition maps into a `VectorBundleCore`. Its reconstructed fibres and total
space are identified with `E` by `VectorBundleCore.ofTrivializationsFiberEquiv` and
`VectorBundleCore.ofTrivializationsTotalEquiv`, intertwining `localTriv i` with `e i`
(`VectorBundleCore.apply_ofTrivializationsTotalEquiv`).

Specializing to `e = trivializationAt F E` and `idx = id`, a vector bundle with model fibre `F`
determines a `VectorBundleCore` (`TauCeti.pointIndexedCore`) whose charts are indexed by the base
itself. Only open subsets of the base and continuous linear maps between copies of `F` are stored:
the universe of the original fibres does not occur in the type of the core.

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

namespace VectorBundleCore

variable {𝕜 B F ι : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  [TopologicalSpace (TotalSpace F E)]
  (e : ι → Trivialization F (π F E)) [∀ i, (e i).IsLinear 𝕜]
  (hcont : ∀ i j, ContinuousOn (fun b ↦ ((e i).coordChangeL 𝕜 (e j) b : F →L[𝕜] F))
    ((e i).baseSet ∩ (e j).baseSet))
  (idx : B → ι) (hidx : ∀ b, b ∈ (e (idx b)).baseSet)

/-- The `VectorBundleCore` extracted from an indexed family `e : ι → Trivialization F (π F E)` of
linear trivializations with continuous pairwise coordinate changes and preferred chart `idx b` at
each base point `b : B`. -/
noncomputable def ofTrivializations : VectorBundleCore 𝕜 B F ι where
  baseSet i := (e i).baseSet
  isOpen_baseSet i := (e i).open_baseSet
  indexAt := idx
  mem_baseSet_at := hidx
  coordChange i j x := (e i).coordChangeL 𝕜 (e j) x
  coordChange_self i _ hx v := (e i).coordChangeL_same_apply 𝕜 hx v
  continuousOn_coordChange := hcont
  coordChange_comp i j k _ hx v :=
    (e i).coordChangeL_coordChangeL_apply 𝕜 (e j) (e k) hx.1.1 hx.1.2 hx.2 v

@[simp] theorem ofTrivializations_localTriv_baseSet (i : ι) :
    ((ofTrivializations e hcont idx hidx).localTriv i).baseSet = (e i).baseSet := (rfl)

/-- The `i`-th base set of `ofTrivializations e hcont idx hidx` is `(e i).baseSet`. (Note that
`simp` reduces `(ofTrivializations ...).baseSet i` via `VectorBundleCore.baseSet_at` and
`ofTrivializations_localTriv_baseSet`.) -/
theorem ofTrivializations_baseSet (i : ι) :
    (ofTrivializations e hcont idx hidx).baseSet i = (e i).baseSet := by
  rw [baseSet_at, ofTrivializations_localTriv_baseSet]

@[simp] theorem ofTrivializations_indexAt (b : B) :
    (ofTrivializations e hcont idx hidx).indexAt b = idx b := (rfl)

@[simp] theorem ofTrivializations_coordChange (i j : ι) (b : B) :
    (ofTrivializations e hcont idx hidx).coordChange i j b =
      ((e i).coordChangeL 𝕜 (e j) b : F →L[𝕜] F) := (rfl)

variable [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-- The continuous linear equivalence identifying the reconstructed fibre of
`ofTrivializations e hcont idx hidx` at `b` with `E b` via the inverse of `e (idx b)`. -/
noncomputable def ofTrivializationsFiberEquiv (b : B) :
    (ofTrivializations e hcont idx hidx).Fiber b ≃L[𝕜] E b :=
  ((e (idx b)).continuousLinearEquivAt 𝕜 b (hidx b)).symm

@[simp] theorem ofTrivializationsFiberEquiv_apply (b : B)
    (v : (ofTrivializations e hcont idx hidx).Fiber b) :
    ofTrivializationsFiberEquiv e hcont idx hidx b v = (e (idx b)).symm b v := (rfl)

@[simp] theorem ofTrivializationsFiberEquiv_symm_apply (b : B) (v : E b) :
    (ofTrivializationsFiberEquiv e hcont idx hidx b).symm v = (e (idx b) ⟨b, v⟩).2 := (rfl)

/-- The total-space bijection covering the identity on `B` induced fibrewise by
`ofTrivializationsFiberEquiv`. -/
noncomputable def ofTrivializationsTotalEquiv :
    (ofTrivializations e hcont idx hidx).TotalSpace ≃ TotalSpace F E where
  toFun p := ⟨p.proj, ofTrivializationsFiberEquiv e hcont idx hidx p.proj p.2⟩
  invFun q := ⟨q.proj, (ofTrivializationsFiberEquiv e hcont idx hidx q.proj).symm q.2⟩
  left_inv _ := by dsimp only; rw [ContinuousLinearEquiv.symm_apply_apply]
  right_inv _ := by dsimp only; rw [ContinuousLinearEquiv.apply_symm_apply]

@[simp] theorem ofTrivializationsTotalEquiv_apply
    (p : (ofTrivializations e hcont idx hidx).TotalSpace) :
    ofTrivializationsTotalEquiv e hcont idx hidx p =
      ⟨p.proj, ofTrivializationsFiberEquiv e hcont idx hidx p.proj p.2⟩ := (rfl)

@[simp] theorem ofTrivializationsTotalEquiv_symm_apply (q : TotalSpace F E) :
    (ofTrivializationsTotalEquiv e hcont idx hidx).symm q =
      ⟨q.proj, (ofTrivializationsFiberEquiv e hcont idx hidx q.proj).symm q.2⟩ := (rfl)

/-- `ofTrivializationsTotalEquiv` intertwines every core chart `localTriv i` with `e i` over
`(e i).baseSet`. -/
theorem apply_ofTrivializationsTotalEquiv (i : ι)
    (p : (ofTrivializations e hcont idx hidx).TotalSpace) (hp : p.proj ∈ (e i).baseSet) :
    e i (ofTrivializationsTotalEquiv e hcont idx hidx p) =
      (ofTrivializations e hcont idx hidx).localTriv i p := by
  rw [localTriv_apply, ofTrivializations_indexAt, ofTrivializations_coordChange,
    ofTrivializationsTotalEquiv_apply, ofTrivializationsFiberEquiv_apply]
  exact ((e (idx p.proj)).mk_coordChangeL (e i) ⟨hidx p.proj, hp⟩ p.2).symm

end VectorBundleCore

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
noncomputable def pointIndexedCore : VectorBundleCore 𝕜 B F B :=
  VectorBundleCore.ofTrivializations (trivializationAt F E)
    (fun _ _ ↦ continuousOn_coordChange 𝕜 _ _) id (mem_baseSet_trivializationAt F E)

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
  VectorBundleCore.ofTrivializationsFiberEquiv (trivializationAt F E)
    (fun _ _ ↦ continuousOn_coordChange 𝕜 _ _) id (mem_baseSet_trivializationAt F E) b

@[simp] theorem pointIndexedCoreFiberEquiv_apply (b : B) (v : F) :
    pointIndexedCoreFiberEquiv 𝕜 F E b v =
      (trivializationAt F E b).symm b v := (rfl)

@[simp] theorem pointIndexedCoreFiberEquiv_symm_apply (b : B) (v : E b) :
    (pointIndexedCoreFiberEquiv 𝕜 F E b).symm v =
      ((trivializationAt F E b) ⟨b, v⟩).2 := (rfl)

private noncomputable def pointIndexedCoreTotalEquiv :
    (pointIndexedCore 𝕜 F E).TotalSpace ≃ TotalSpace F E :=
  VectorBundleCore.ofTrivializationsTotalEquiv (trivializationAt F E)
    (fun _ _ ↦ continuousOn_coordChange 𝕜 _ _) id (mem_baseSet_trivializationAt F E)

private theorem pointIndexedCoreTotalEquiv_symm_proj (p : TotalSpace F E) :
    ((pointIndexedCoreTotalEquiv 𝕜 F E).symm p).proj = p.proj := (rfl)

private theorem trivializationAt_pointIndexedCoreTotalEquiv (b : B)
    (p : (pointIndexedCore 𝕜 F E).TotalSpace)
    (hp : p.proj ∈ (trivializationAt F E b).baseSet) :
    (trivializationAt F E b) (pointIndexedCoreTotalEquiv 𝕜 F E p) =
      (pointIndexedCore 𝕜 F E).localTriv b p :=
  VectorBundleCore.apply_ofTrivializationsTotalEquiv (trivializationAt F E)
    (fun _ _ ↦ continuousOn_coordChange 𝕜 _ _) id (mem_baseSet_trivializationAt F E) b p hp

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
