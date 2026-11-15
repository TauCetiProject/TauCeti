/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic

/-!
# Transporting the model fibre of a vector-bundle core

Given a vector-bundle core `Z : VectorBundleCore 𝕜 B F ι` and a continuous linear equivalence
`e : F ≃L[𝕜] G` between model fibres, `VectorBundleCore.congrModel Z e` conjugates every transition
operator of `Z` by `e` while keeping the same chart domains and preferred-chart indexing. This
avoids dependent casts on model types when standardizing coordinate fibres across strata whose
dimensions agree propositionally rather than definitionally.

`VectorBundleCore.congrModelHomeomorph` identifies `Z.TotalSpace` with `(Z.congrModel e).TotalSpace`
over the identity of `B`, acting as `e` on every fibre and intertwining all core charts.
-/

public section

open Bundle Set Topology

namespace VectorBundleCore

variable {𝕜 B F G H ι : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- Transport the model fibre of a `VectorBundleCore` along a continuous linear equivalence `e`,
conjugating transition operators by `e` and retaining the same chart domains and indices. -/
def congrModel (Z : VectorBundleCore 𝕜 B F ι) (e : F ≃L[𝕜] G) : VectorBundleCore 𝕜 B G ι where
  baseSet := Z.baseSet
  isOpen_baseSet := Z.isOpen_baseSet
  indexAt := Z.indexAt
  mem_baseSet_at := Z.mem_baseSet_at
  coordChange i j x :=
    e.toContinuousLinearMap.comp ((Z.coordChange i j x).comp e.symm.toContinuousLinearMap)
  coordChange_self i x hx v := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      Z.coordChange_self i x hx (e.symm v), e.apply_symm_apply]
  continuousOn_coordChange i j :=
    continuousOn_iff_continuous_domRestrict.2
      (((Z.continuousOn_coordChange i j).domRestrict.clm_comp_const
        e.symm.toContinuousLinearMap).const_clm_comp e.toContinuousLinearMap)
  coordChange_comp i j k x hx v := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      e.symm_apply_apply, Z.coordChange_comp i j k x hx (e.symm v)]

theorem baseSet_congrModel (Z : VectorBundleCore 𝕜 B F ι) (e : F ≃L[𝕜] G) (i : ι) :
    (Z.congrModel e).baseSet i = Z.baseSet i := (rfl)

@[simp] theorem localTriv_baseSet_congrModel (Z : VectorBundleCore 𝕜 B F ι) (e : F ≃L[𝕜] G)
    (i : ι) : ((Z.congrModel e).localTriv i).baseSet = Z.baseSet i := (rfl)

@[simp] theorem indexAt_congrModel (Z : VectorBundleCore 𝕜 B F ι) (e : F ≃L[𝕜] G) (b : B) :
    (Z.congrModel e).indexAt b = Z.indexAt b := (rfl)

@[simp] theorem coordChange_congrModel (Z : VectorBundleCore 𝕜 B F ι) (e : F ≃L[𝕜] G)
    (i j : ι) (b : B) :
    (Z.congrModel e).coordChange i j b =
      e.toContinuousLinearMap.comp ((Z.coordChange i j b).comp e.symm.toContinuousLinearMap) :=
  (rfl)

theorem coordChange_congrModel_apply (Z : VectorBundleCore 𝕜 B F ι) (e : F ≃L[𝕜] G)
    (i j : ι) (b : B) (v : G) :
    (Z.congrModel e).coordChange i j b v = e (Z.coordChange i j b (e.symm v)) := (rfl)

/-- Transporting along the identity continuous linear equivalence returns the original core. -/
@[simp] theorem congrModel_refl (Z : VectorBundleCore 𝕜 B F ι) :
    Z.congrModel (ContinuousLinearEquiv.refl 𝕜 F) = Z := by
  cases Z
  rfl

/-- Successive model-fibre transports compose. -/
@[simp] theorem congrModel_trans (Z : VectorBundleCore 𝕜 B F ι) (e₁ : F ≃L[𝕜] G)
    (e₂ : G ≃L[𝕜] H) :
    (Z.congrModel e₁).congrModel e₂ = Z.congrModel (e₁.trans e₂) := by
  cases Z
  rfl

/-- Every chart of `Z.congrModel e` intertwines `Z.localTriv i` via `e` on the fibre coordinate. -/
theorem localTriv_congrModel_apply (Z : VectorBundleCore 𝕜 B F ι) (e : F ≃L[𝕜] G)
    (i : ι) (p : Z.TotalSpace) :
    (Z.congrModel e).localTriv i ⟨p.proj, e p.2⟩ = (p.proj, e ((Z.localTriv i p).2)) := by
  simp only [localTriv_apply, indexAt_congrModel, coordChange_congrModel_apply]
  rw [e.symm_apply_apply p.2]

/-- Every chart of `Z.congrModel e` is intertwined with `Z.localTriv i` by `e.symm`. -/
theorem localTriv_congrModel_symm_apply (Z : VectorBundleCore 𝕜 B F ι) (e : F ≃L[𝕜] G)
    (i : ι) (q : (Z.congrModel e).TotalSpace) :
    Z.localTriv i ⟨q.proj, e.symm q.2⟩ = (q.proj, e.symm (((Z.congrModel e).localTriv i q).2)) := by
  simp only [localTriv_apply, indexAt_congrModel]
  rw [coordChange_congrModel_apply Z e (Z.indexAt q.proj) i q.proj q.2, e.symm_apply_apply]

/-- Transporting the model fibre along `e : F ≃L[𝕜] G` induces a homeomorphism of reconstructed
total spaces covering the identity on the base and acting as `e` on each fibre. -/
def congrModelHomeomorph (Z : VectorBundleCore 𝕜 B F ι) (e : F ≃L[𝕜] G) :
    Z.TotalSpace ≃ₜ (Z.congrModel e).TotalSpace where
  toFun p := ⟨p.proj, e p.2⟩
  invFun q := ⟨q.proj, e.symm q.2⟩
  left_inv p := by
    rcases p with ⟨x, v⟩
    dsimp only
    rw [e.symm_apply_apply v]
  right_inv q := by
    rcases q with ⟨x, v⟩
    dsimp only
    rw [e.apply_symm_apply v]
  continuous_toFun := by
    refine continuous_iff_continuousAt.2 fun p => ?_
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨Z.continuous_proj.continuousAt, ?_⟩
    have hp := Z.mem_source_at p.proj p.2
    have hc := e.continuous.continuousAt.comp
      (((Z.localTrivAt p.proj).continuousOn.continuousAt
        ((Z.localTrivAt p.proj).open_source.mem_nhds hp)).snd)
    refine hc.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
    dsimp only [Function.comp_apply, VectorBundleCore.trivializationAt, localTrivAt]
    rw [indexAt_congrModel]
    exact congrArg Prod.snd (Z.localTriv_congrModel_apply e (Z.indexAt p.proj) q)
  continuous_invFun := by
    refine continuous_iff_continuousAt.2 fun p => ?_
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨(Z.congrModel e).continuous_proj.continuousAt, ?_⟩
    have hp := (Z.congrModel e).mem_source_at p.proj p.2
    have hc := e.symm.continuous.continuousAt.comp
      ((((Z.congrModel e).localTrivAt p.proj).continuousOn.continuousAt
        (((Z.congrModel e).localTrivAt p.proj).open_source.mem_nhds hp)).snd)
    refine hc.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
    dsimp only [Function.comp_apply, VectorBundleCore.trivializationAt, localTrivAt]
    rw [indexAt_congrModel]
    exact congrArg Prod.snd (Z.localTriv_congrModel_symm_apply e (Z.indexAt p.proj) q)

@[simp] theorem congrModelHomeomorph_apply (Z : VectorBundleCore 𝕜 B F ι) (e : F ≃L[𝕜] G)
    (p : Z.TotalSpace) :
    Z.congrModelHomeomorph e p = ⟨p.proj, e p.2⟩ := (rfl)

@[simp] theorem congrModelHomeomorph_symm_apply (Z : VectorBundleCore 𝕜 B F ι) (e : F ≃L[𝕜] G)
    (q : (Z.congrModel e).TotalSpace) :
    (Z.congrModelHomeomorph e).symm q = ⟨q.proj, e.symm q.2⟩ := (rfl)

theorem proj_congrModelHomeomorph (Z : VectorBundleCore 𝕜 B F ι) (e : F ≃L[𝕜] G)
    (p : Z.TotalSpace) :
    (Z.congrModelHomeomorph e p).proj = p.proj := (rfl)

theorem proj_congrModelHomeomorph_symm (Z : VectorBundleCore 𝕜 B F ι) (e : F ≃L[𝕜] G)
    (q : (Z.congrModel e).TotalSpace) :
    ((Z.congrModelHomeomorph e).symm q).proj = q.proj := (rfl)

/-- A map into `(Z.congrModel e).TotalSpace` is continuous if and only if the map obtained by
applying `e.symm` on fibre coordinates is continuous into `Z.TotalSpace`. -/
theorem continuous_mk_congrModel_iff {Y : Type*} [TopologicalSpace Y] {b : Y → B} {s : Y → G}
    (Z : VectorBundleCore 𝕜 B F ι) (e : F ≃L[𝕜] G) :
    Continuous (fun y => (⟨b y, s y⟩ : (Z.congrModel e).TotalSpace)) ↔
      Continuous (fun y => (⟨b y, e.symm (s y)⟩ : Z.TotalSpace)) :=
  (Z.congrModelHomeomorph e).symm.comp_continuous_iff.symm

end VectorBundleCore
