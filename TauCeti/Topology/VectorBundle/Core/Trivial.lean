/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic

/-!
# Global trivialization of a vector bundle core with identity transitions

`VectorBundleCore.globalTrivializationOfCoordChangeEqId` identifies the total space of a core
whose transition maps are the identity on every chart overlap with the product of its base and
model fibre.

Although each fibre `Z.Fiber x` is definitionally `F`, the total space `Z.TotalSpace` carries the
topology glued from the local charts of `Z` rather than the product topology on `B × F`, so a
global trivialization has to be constructed and checked against these charts. The construction
needs no finite-rank or completeness assumption on `F`. It shows, for instance, that the vector
bundle associated with the trivial representation of a deck group is trivial
(`IsQuotientCoveringMap.exists_trivialization_baseSet_eq_univ_associatedCore_one`).
-/

public section

open Bundle Set
open scoped Topology

namespace VectorBundleCore

variable {𝕜 B F ι : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] (Z : VectorBundleCore 𝕜 B F ι)
  (hcoord : ∀ i j, ∀ x ∈ Z.baseSet i ∩ Z.baseSet j, ∀ v, Z.coordChange i j x v = v)

/-- The global product trivialization of a core whose transitions are the identity on chart
overlaps: it has base set `univ`, sends `q : Z.TotalSpace` to `(q.proj, q.2)`, and has inverse
`q ↦ ⟨q.1, q.2⟩`. -/
def globalTrivializationOfCoordChangeEqId : Trivialization F (π F Z.Fiber) where
  toFun := fun q ↦ (q.proj, q.2)
  invFun := fun q ↦ ⟨q.1, q.2⟩
  source := univ
  target := univ
  map_source' := fun _ _ ↦ mem_univ _
  map_target' := fun _ _ ↦ mem_univ _
  left_inv' := fun _ _ ↦ rfl
  right_inv' := fun _ _ ↦ rfl
  open_source := isOpen_univ
  open_target := isOpen_univ
  continuousOn_toFun := by
    -- The fibre `Z.Fiber x` is identified with `F` by unfolding `VectorBundleCore.Fiber`; the
    -- topology on the total space comes from the core, so continuity is checked in its charts.
    apply Continuous.continuousOn
    refine continuous_iff_continuousAt.2 fun q ↦ ?_
    refine ((Z.localTrivAt q.proj).continuousAt (Z.mem_source_at q.proj q.2)).congr ?_
    filter_upwards [(Z.localTrivAt q.proj).open_source.mem_nhds (Z.mem_source_at q.proj q.2)]
      with z hz
    simp only [localTrivAt, Trivialization.coe_coe, localTriv_apply]
    -- `hcoord` is stated on `F`; elaboration identifies `z.2 : Z.Fiber z.proj` with `F`.
    exact congrArg (fun v : F ↦ (z.proj, v)) (hcoord _ _ _ ⟨Z.mem_baseSet_at _, hz⟩ z.2)
  continuousOn_invFun := by
    apply Continuous.continuousOn
    refine continuous_iff_continuousAt.2 fun q ↦ ?_
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨continuousAt_fst, continuousAt_snd.congr ?_⟩
    filter_upwards [continuousAt_fst.preimage_mem_nhds
      ((Z.isOpen_baseSet (Z.indexAt q.1)).mem_nhds (Z.mem_baseSet_at q.1))] with z hz
    simp only [Z.trivializationAt, localTrivAt, localTriv_apply]
    -- As above, apply the transition identity after identifying the core fibre with `F`.
    exact (hcoord _ _ _ ⟨Z.mem_baseSet_at _, hz⟩ z.2).symm
  baseSet := univ
  open_baseSet := isOpen_univ
  source_eq := by simp
  target_eq := by simp
  proj_toFun := fun _ _ ↦ rfl

@[simp]
theorem globalTrivializationOfCoordChangeEqId_apply (q : Z.TotalSpace) :
    Z.globalTrivializationOfCoordChangeEqId hcoord q = (q.proj, q.2) := by
  rfl

@[simp]
theorem globalTrivializationOfCoordChangeEqId_baseSet :
    (Z.globalTrivializationOfCoordChangeEqId hcoord).baseSet = univ := by
  rfl

@[simp]
theorem globalTrivializationOfCoordChangeEqId_symm_apply (x : B) (v : F) :
    (Z.globalTrivializationOfCoordChangeEqId hcoord).symm x v = v := by
  rw [(Z.globalTrivializationOfCoordChangeEqId hcoord).symm_apply (by simp)]
  rfl

/-- The global product trivialization of a core with identity transitions is fibrewise linear. -/
instance globalTrivializationOfCoordChangeEqId_isLinear :
    (Z.globalTrivializationOfCoordChangeEqId hcoord).IsLinear 𝕜 where
  -- Unfold `VectorBundleCore.Fiber` to identify the fibre's module structure with that of `F`.
  linear _ _ := (LinearMap.id : F →ₗ[𝕜] F).isLinear

end VectorBundleCore
