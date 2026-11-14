/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic

/-!
# Model transport and index reparametrization for vector-bundle cores

Given a Mathlib coordinate core `Z : VectorBundleCore R B F ι`, this file transports its model
fibre along a continuous linear equivalence `e : F ≃L[R] G` (`VectorBundleCore.congrModel`) and
reparametrizes its chart index type along an equivalence `e : ι' ≃ ι`
(`VectorBundleCore.reindex`).

`VectorBundleCore.congrModelHomeomorph` and `VectorBundleCore.reindexHomeomorph` identify the
reconstructed total spaces with `Z.TotalSpace` over the identity of `B`, acting on each fibre by
`e` and by the identity respectively, and intertwining all core trivializations. The resulting
continuity characterizations (`VectorBundleCore.continuous_mk_congrModel_iff` and
`VectorBundleCore.continuous_mk_reindex_iff`) reduce continuity into the transported or reindexed
total space directly to continuity into `Z.TotalSpace`. No completeness, separation, or
finite-dimensionality assumption is needed.
-/

public section

open Bundle Topology

namespace VectorBundleCore

variable {R B F G ι ι' : Type*} [NontriviallyNormedField R] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace R F] [NormedAddCommGroup G] [NormedSpace R G]

section CongrModel

/-- Transport the model fibre of a `VectorBundleCore` along a continuous linear equivalence
`e : F ≃L[R] G` by conjugating every transition operator by `e`. -/
def congrModel (Z : VectorBundleCore R B F ι) (e : F ≃L[R] G) : VectorBundleCore R B G ι where
  baseSet := Z.baseSet
  isOpen_baseSet := Z.isOpen_baseSet
  indexAt := Z.indexAt
  mem_baseSet_at := Z.mem_baseSet_at
  coordChange i j x := e.arrowCongr e (Z.coordChange i j x)
  coordChange_self i x hx v := by
    simp [Z.coordChange_self i x hx (e.symm v)]
  continuousOn_coordChange i j :=
    (e.arrowCongr e).continuous.comp_continuousOn (Z.continuousOn_coordChange i j)
  coordChange_comp i j k x hx v := by
    simp [Z.coordChange_comp i j k x hx (e.symm v)]

theorem baseSet_congrModel (Z : VectorBundleCore R B F ι) (e : F ≃L[R] G) (i : ι) :
    (Z.congrModel e).baseSet i = Z.baseSet i := (rfl)

@[simp]
theorem localTriv_baseSet_congrModel (Z : VectorBundleCore R B F ι) (e : F ≃L[R] G) (i : ι) :
    ((Z.congrModel e).localTriv i).baseSet = (Z.localTriv i).baseSet := (rfl)

@[simp]
theorem indexAt_congrModel (Z : VectorBundleCore R B F ι) (e : F ≃L[R] G) (x : B) :
    (Z.congrModel e).indexAt x = Z.indexAt x := (rfl)

@[simp]
theorem coordChange_congrModel (Z : VectorBundleCore R B F ι) (e : F ≃L[R] G)
    (i j : ι) (x : B) :
    (Z.congrModel e).coordChange i j x = e.arrowCongr e (Z.coordChange i j x) := (rfl)

theorem coordChange_congrModel_apply (Z : VectorBundleCore R B F ι) (e : F ≃L[R] G)
    (i j : ι) (x : B) (v : G) :
    (Z.congrModel e).coordChange i j x v = e (Z.coordChange i j x (e.symm v)) := (rfl)

@[simp]
theorem congrModel_refl (Z : VectorBundleCore R B F ι) :
    Z.congrModel (.refl R F) = Z := by
  cases Z
  rfl

theorem congrModel_trans {H : Type*} [NormedAddCommGroup H] [NormedSpace R H]
    (Z : VectorBundleCore R B F ι) (e : F ≃L[R] G) (e' : G ≃L[R] H) :
    (Z.congrModel e).congrModel e' = Z.congrModel (e.trans e') := (rfl)

private theorem continuous_mk_congrModel {Y : Type*} [TopologicalSpace Y]
    (Z : VectorBundleCore R B F ι) (e : F ≃L[R] G) {b : Y → B} {s : Y → F}
    (hs : Continuous fun y => (⟨b y, s y⟩ : Z.TotalSpace)) :
    Continuous fun y => (⟨b y, e (s y)⟩ : (Z.congrModel e).TotalSpace) := by
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  rw [FiberBundle.continuousAt_totalSpace]
  have hs₀ := (FiberBundle.continuousAt_totalSpace _ _).1 (hs.continuousAt (x := y₀))
  refine ⟨hs₀.1, ?_⟩
  convert e.continuous.continuousAt.comp hs₀.2 using 1
  funext y
  simp [VectorBundleCore.trivializationAt, ← VectorBundleCore.localTrivAt_def]

/-- Transporting the model fibre of `Z` along `e : F ≃L[R] G` induces a homeomorphism of
reconstructed total spaces covering the identity on `B` and acting by `e` on every fibre. -/
def congrModelHomeomorph (Z : VectorBundleCore R B F ι) (e : F ≃L[R] G) :
    Z.TotalSpace ≃ₜ (Z.congrModel e).TotalSpace where
  toFun p := ⟨p.proj, e p.2⟩
  invFun p := ⟨p.proj, e.symm p.2⟩
  left_inv p := congrArg (TotalSpace.mk' F p.proj) (e.symm_apply_apply p.2)
  right_inv p := congrArg (TotalSpace.mk' G p.proj) (e.apply_symm_apply p.2)
  continuous_toFun := Z.continuous_mk_congrModel e continuous_id
  continuous_invFun := by
    refine continuous_iff_continuousAt.2 fun p₀ => ?_
    rw [FiberBundle.continuousAt_totalSpace]
    have hp₀ := (FiberBundle.continuousAt_totalSpace _ _).1
      ((continuous_id (X := (Z.congrModel e).TotalSpace)).continuousAt (x := p₀))
    refine ⟨hp₀.1, ?_⟩
    convert e.symm.continuous.continuousAt.comp hp₀.2 using 1
    funext p
    simp only [Function.comp_apply, VectorBundleCore.trivializationAt,
      ← VectorBundleCore.localTrivAt_def, localTriv_apply, indexAt_congrModel,
      coordChange_congrModel]
    exact (e.symm_apply_apply _).symm

@[simp]
theorem congrModelHomeomorph_apply (Z : VectorBundleCore R B F ι) (e : F ≃L[R] G)
    (p : Z.TotalSpace) :
    Z.congrModelHomeomorph e p = ⟨p.proj, e p.2⟩ := (rfl)

@[simp]
theorem congrModelHomeomorph_symm_apply (Z : VectorBundleCore R B F ι) (e : F ≃L[R] G)
    (p : (Z.congrModel e).TotalSpace) :
    (Z.congrModelHomeomorph e).symm p = ⟨p.proj, e.symm p.2⟩ := (rfl)

/-- Every local trivialization of `Z.congrModel e` is intertwined with the corresponding local
trivialization of `Z` by `e` on the model fibre. -/
theorem localTriv_congrModel_congrModelHomeomorph (Z : VectorBundleCore R B F ι)
    (e : F ≃L[R] G) (i : ι) (p : Z.TotalSpace) :
    (Z.congrModel e).localTriv i (Z.congrModelHomeomorph e p) =
      (p.proj, e ((Z.localTriv i p).2)) := by
  simp only [congrModelHomeomorph_apply, localTriv_apply, indexAt_congrModel,
    coordChange_congrModel, ContinuousLinearEquiv.arrowCongr_apply]
  rw [e.symm_apply_apply p.2]

/-- A map into `(Z.congrModel e).TotalSpace` is continuous if and only if the map obtained by
applying `e.symm` fibrewise into `Z.TotalSpace` is continuous. -/
theorem continuous_mk_congrModel_iff {Y : Type*} [TopologicalSpace Y]
    (Z : VectorBundleCore R B F ι) (e : F ≃L[R] G) {b : Y → B} {s : Y → G} :
    Continuous (fun y => (⟨b y, s y⟩ : (Z.congrModel e).TotalSpace)) ↔
      Continuous (fun y => (⟨b y, e.symm (s y)⟩ : Z.TotalSpace)) := by
  refine ⟨fun h => (Z.congrModelHomeomorph e).symm.continuous.comp h, fun h => ?_⟩
  convert (Z.congrModelHomeomorph e).continuous.comp h using 1
  funext y
  exact congrArg (TotalSpace.mk' G (b y)) (e.apply_symm_apply (s y)).symm

end CongrModel

section Reindex

/-- Reparametrize the chart index type of a `VectorBundleCore` along `e : ι' ≃ ι`. -/
def reindex (Z : VectorBundleCore R B F ι) (e : ι' ≃ ι) : VectorBundleCore R B F ι' where
  baseSet i := Z.baseSet (e i)
  isOpen_baseSet i := Z.isOpen_baseSet (e i)
  indexAt x := e.symm (Z.indexAt x)
  mem_baseSet_at x := by
    simpa only [Equiv.apply_symm_apply] using Z.mem_baseSet_at x
  coordChange i j x := Z.coordChange (e i) (e j) x
  coordChange_self i x hx v := Z.coordChange_self (e i) x hx v
  continuousOn_coordChange i j := Z.continuousOn_coordChange (e i) (e j)
  coordChange_comp i j k x hx v := Z.coordChange_comp (e i) (e j) (e k) x hx v

theorem baseSet_reindex (Z : VectorBundleCore R B F ι) (e : ι' ≃ ι) (i : ι') :
    (Z.reindex e).baseSet i = Z.baseSet (e i) := (rfl)

@[simp]
theorem localTriv_baseSet_reindex (Z : VectorBundleCore R B F ι) (e : ι' ≃ ι) (i : ι') :
    ((Z.reindex e).localTriv i).baseSet = (Z.localTriv (e i)).baseSet := (rfl)

@[simp]
theorem indexAt_reindex (Z : VectorBundleCore R B F ι) (e : ι' ≃ ι) (x : B) :
    (Z.reindex e).indexAt x = e.symm (Z.indexAt x) := (rfl)

@[simp]
theorem coordChange_reindex (Z : VectorBundleCore R B F ι) (e : ι' ≃ ι)
    (i j : ι') (x : B) :
    (Z.reindex e).coordChange i j x = Z.coordChange (e i) (e j) x := (rfl)

@[simp]
theorem reindex_refl (Z : VectorBundleCore R B F ι) :
    Z.reindex (.refl ι) = Z := by
  cases Z
  rfl

theorem reindex_trans {ι'' : Type*} (Z : VectorBundleCore R B F ι)
    (e : ι' ≃ ι) (e' : ι'' ≃ ι') :
    (Z.reindex e).reindex e' = Z.reindex (e'.trans e) := by
  cases Z
  rfl

/-- Reparametrizing the chart index type of `Z` along `e : ι' ≃ ι` induces the identity-on-fibres
homeomorphism of reconstructed total spaces over `B`. -/
def reindexHomeomorph (Z : VectorBundleCore R B F ι) (e : ι' ≃ ι) :
    Z.TotalSpace ≃ₜ (Z.reindex e).TotalSpace where
  toFun p := ⟨p.proj, p.2⟩
  invFun p := ⟨p.proj, p.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl
  continuous_toFun := by
    refine continuous_iff_continuousAt.2 fun p₀ => ?_
    rw [FiberBundle.continuousAt_totalSpace]
    have hp₀ := (FiberBundle.continuousAt_totalSpace _ _).1
      ((continuous_id (X := Z.TotalSpace)).continuousAt (x := p₀))
    refine ⟨hp₀.1, ?_⟩
    convert hp₀.2 using 1
    funext p
    simp [VectorBundleCore.trivializationAt, ← VectorBundleCore.localTrivAt_def]
  continuous_invFun := by
    refine continuous_iff_continuousAt.2 fun p₀ => ?_
    rw [FiberBundle.continuousAt_totalSpace]
    have hp₀ := (FiberBundle.continuousAt_totalSpace _ _).1
      ((continuous_id (X := (Z.reindex e).TotalSpace)).continuousAt (x := p₀))
    refine ⟨hp₀.1, ?_⟩
    convert hp₀.2 using 1
    funext p
    simp [VectorBundleCore.trivializationAt, ← VectorBundleCore.localTrivAt_def]

@[simp]
theorem reindexHomeomorph_apply (Z : VectorBundleCore R B F ι) (e : ι' ≃ ι)
    (p : Z.TotalSpace) :
    Z.reindexHomeomorph e p = ⟨p.proj, p.2⟩ := (rfl)

@[simp]
theorem reindexHomeomorph_symm_apply (Z : VectorBundleCore R B F ι) (e : ι' ≃ ι)
    (p : (Z.reindex e).TotalSpace) :
    (Z.reindexHomeomorph e).symm p = ⟨p.proj, p.2⟩ := (rfl)

/-- Each chart `i` of `Z.reindex e` coincides under `reindexHomeomorph` with chart `e i` of `Z`. -/
theorem localTriv_reindex_reindexHomeomorph (Z : VectorBundleCore R B F ι)
    (e : ι' ≃ ι) (i : ι') (p : Z.TotalSpace) :
    (Z.reindex e).localTriv i (Z.reindexHomeomorph e p) = Z.localTriv (e i) p := by
  simp [localTriv_apply]

/-- Continuity into `(Z.reindex e).TotalSpace` is equivalent to continuity of the same section data
into `Z.TotalSpace`. -/
theorem continuous_mk_reindex_iff {Y : Type*} [TopologicalSpace Y]
    (Z : VectorBundleCore R B F ι) (e : ι' ≃ ι) {b : Y → B} {s : Y → F} :
    Continuous (fun y => (⟨b y, s y⟩ : (Z.reindex e).TotalSpace)) ↔
      Continuous (fun y => (⟨b y, s y⟩ : Z.TotalSpace)) :=
  ⟨fun h => (Z.reindexHomeomorph e).symm.continuous.comp h,
    fun h => (Z.reindexHomeomorph e).continuous.comp h⟩

end Reindex

end VectorBundleCore
