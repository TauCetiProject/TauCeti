/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic

/-!
# Descent of vector-bundle maps from coordinates

`VectorBundleCore.CoordinateHom` consists of continuous operator-valued functions on
source/target chart intersections, intertwining the two transition functions. Values
are stored only on these intersections: there is no unconstrained off-chart data.
For finite coordinate models these are continuous finite-matrix functions, independently
of any original fibre universe.

`CoordinateHom.totalSpaceMap` glues these operators to a continuous map of the actual
Mathlib total spaces, linear on each fibre. `CoordinateHom.localTriv_fiberMap` recovers
all the prescribed coordinates, and `CoordinateHom.fiberMap_injective` proves uniqueness.
Thus coordinate descent loses no morphism data. The identity is represented by the
transition functions themselves, not by constant identity matrices in different charts.

The construction uses Mathlib's `VectorBundleCore` and its local trivializations.
-/

public section

open Bundle Set Topology

namespace VectorBundleCore

variable {𝕜 B F G ι κ : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Continuous chart operators intertwining source and target transition functions.
Only values on actual chart intersections are part of the data. -/
structure CoordinateHom (Z : VectorBundleCore 𝕜 B F ι) (W : VectorBundleCore 𝕜 B G κ) where
  /-- The operator from source chart `i` to target chart `j`. -/
  operator : ∀ i j, C(↥(Z.baseSet i ∩ W.baseSet j), F →L[𝕜] G)
  /-- Changing either chart preserves the represented fibre map. -/
  compatible : ∀ i i' j j' (x : B) (hi : x ∈ Z.baseSet i) (hi' : x ∈ Z.baseSet i')
    (hj : x ∈ W.baseSet j) (hj' : x ∈ W.baseSet j') (v : F),
    W.coordChange j j' x (operator i j ⟨x, hi, hj⟩ v) =
      operator i' j' ⟨x, hi', hj'⟩ (Z.coordChange i i' x v)

namespace CoordinateHom

variable {Z : VectorBundleCore 𝕜 B F ι} {W : VectorBundleCore 𝕜 B G κ}

@[ext] theorem ext {a b : CoordinateHom Z W}
    (h : ∀ i j x, a.operator i j x = b.operator i j x) : a = b := by
  cases a
  cases b
  congr
  funext i j
  exact ContinuousMap.ext (h i j)

/-- The descended linear operator in the preferred coordinates at a base point. -/
def fiberMap (a : CoordinateHom Z W) (x : B) : F →L[𝕜] G :=
  a.operator (Z.indexAt x) (W.indexAt x) ⟨x, Z.mem_baseSet_at x, W.mem_baseSet_at x⟩

/-- The descended operator has the prescribed expression in every pair of charts. -/
theorem coordChange_fiberMap (a : CoordinateHom Z W) (i : ι) (j : κ) {x : B}
    (hi : x ∈ Z.baseSet i) (hj : x ∈ W.baseSet j) (v : F) :
    W.coordChange (W.indexAt x) j x (a.fiberMap x v) =
      a.operator i j ⟨x, hi, hj⟩ (Z.coordChange (Z.indexAt x) i x v) :=
  a.compatible _ i _ j x (Z.mem_baseSet_at x) hi (W.mem_baseSet_at x) hj v

/-- Recovery of a chart operator from the descended fibre map. -/
theorem operator_eq (a : CoordinateHom Z W) (i : ι) (j : κ)
    (x : ↥(Z.baseSet i ∩ W.baseSet j)) :
    a.operator i j x = (W.coordChange (W.indexAt x.1) j x.1).comp
      ((a.fiberMap x.1).comp (Z.coordChange i (Z.indexAt x.1) x.1)) := by
  ext v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    a.coordChange_fiberMap i j x.2.1 x.2.2,
    Z.coordChange_comp i (Z.indexAt x.1) i x.1
      ⟨⟨x.2.1, Z.mem_baseSet_at x.1⟩, x.2.1⟩,
    Z.coordChange_self i x.1 x.2.1]

/-- Preferred-coordinate descent is faithful; there is no off-chart data to forget. -/
theorem fiberMap_injective : Function.Injective (fiberMap (Z := Z) (W := W)) := by
  intro a b hab
  ext i j x
  rw [a.operator_eq, b.operator_eq, hab]

/-- The fibrewise linear map of total spaces determined by compatible chart operators. -/
def totalSpaceMap (a : CoordinateHom Z W) (p : Z.TotalSpace) : W.TotalSpace :=
  ⟨p.proj, a.fiberMap p.proj p.2⟩

@[simp] theorem totalSpaceMap_proj (a : CoordinateHom Z W) (p : Z.TotalSpace) :
    (a.totalSpaceMap p).proj = p.proj := (rfl)

@[simp] theorem totalSpaceMap_mk (a : CoordinateHom Z W) (x : B) (v : Z.Fiber x) :
    a.totalSpaceMap ⟨x, v⟩ = ⟨x, a.fiberMap x v⟩ := (rfl)

/-- In local trivializations the descended map is precisely the given chart operator. -/
theorem localTriv_fiberMap (a : CoordinateHom Z W) (i : ι) (j : κ) (p : Z.TotalSpace)
    (hi : p.proj ∈ Z.baseSet i) (hj : p.proj ∈ W.baseSet j) :
    ((W.localTriv j) (a.totalSpaceMap p)).2 =
      a.operator i j ⟨p.proj, hi, hj⟩ ((Z.localTriv i) p).2 := by
  simp only [localTriv_apply, totalSpaceMap]
  exact a.coordChange_fiberMap i j hi hj p.2

/-- Two coordinate morphisms inducing the same map of total spaces are equal. -/
theorem totalSpaceMap_injective : Function.Injective (totalSpaceMap (Z := Z) (W := W)) := by
  intro a b hab
  apply fiberMap_injective
  funext x
  ext v
  exact congrArg TotalSpace.snd (congrFun hab (⟨x, v⟩ : Z.TotalSpace))

/-- Compatible continuous coordinate operators glue to a continuous total-space map. -/
theorem continuous_totalSpaceMap (a : CoordinateHom Z W) : Continuous a.totalSpaceMap := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  -- Fix both charts near the point; the preferred chart indices need not vary continuously.
  let i := Z.indexAt p.proj
  let j := W.indexAt p.proj
  let s : Set Z.TotalSpace := {q | q.proj ∈ Z.baseSet i ∩ W.baseSet j}
  have hp : p ∈ s := ⟨Z.mem_baseSet_at _, W.mem_baseSet_at _⟩
  have hs : IsOpen s :=
    ((Z.isOpen_baseSet i).inter (W.isOpen_baseSet j)).preimage Z.continuous_proj
  have hbase : Continuous (fun q : s ↦ (⟨q.1.proj, q.2⟩ : ↥(Z.baseSet i ∩ W.baseSet j))) :=
    (Z.continuous_proj.comp continuous_subtype_val).subtype_mk _
  have hcoord : Continuous (fun q : s ↦ ((Z.localTriv i) q.1).2) :=
    ((Z.localTriv i).continuousOn.comp_continuous continuous_subtype_val
      (fun q ↦ q.2.1)).snd
  have hlocal := ((a.operator i j).continuous.comp hbase).clm_apply hcoord
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨Z.continuous_proj.continuousAt, ?_⟩
  apply ContinuousWithinAt.continuousAt (s := s) _ (hs.mem_nhds hp)
  apply (continuousWithinAt_iff_continuousAt_domRestrict _ hp).2
  apply hlocal.continuousAt.congr
  exact Filter.Eventually.of_forall fun q ↦
    (a.localTriv_fiberMap i j q.1 q.2.1 q.2.2).symm

/-- A fibre family realizing all the chart operators is necessarily the descended family.
No regularity hypothesis is needed for uniqueness. -/
theorem fiberMap_unique (a : CoordinateHom Z W) (f : B → F →L[𝕜] G)
    (hf : ∀ i j (x : ↥(Z.baseSet i ∩ W.baseSet j)) (v : F),
      W.coordChange (W.indexAt x.1) j x.1 (f x.1 v) =
        a.operator i j x (Z.coordChange (Z.indexAt x.1) i x.1 v)) :
    f = a.fiberMap := by
  funext x
  ext v
  simpa only [fiberMap, Z.coordChange_self _ _ (Z.mem_baseSet_at x),
    W.coordChange_self _ _ (W.mem_baseSet_at x)] using
    hf (Z.indexAt x) (W.indexAt x) ⟨x, Z.mem_baseSet_at x, W.mem_baseSet_at x⟩ v

/-- The identity bundle map is represented in two charts by their transition operator. -/
def id (Z : VectorBundleCore 𝕜 B F ι) : CoordinateHom Z Z where
  operator i j := ⟨_, (Z.continuousOn_coordChange i j).domRestrict⟩
  compatible i i' j j' x hi hi' hj hj' v :=
    (Z.coordChange_comp i j j' x ⟨⟨hi, hj⟩, hj'⟩ v).trans
      (Z.coordChange_comp i i' j' x ⟨⟨hi, hi'⟩, hj'⟩ v).symm

@[simp] theorem operator_id (Z : VectorBundleCore 𝕜 B F ι) (i j : ι) :
    (id Z).operator i j =
      ⟨(Z.baseSet i ∩ Z.baseSet j).domRestrict (Z.coordChange i j),
        (Z.continuousOn_coordChange i j).domRestrict⟩ := (rfl)

@[simp] theorem fiberMap_id (Z : VectorBundleCore 𝕜 B F ι) (x : B) :
    (id Z).fiberMap x = ContinuousLinearMap.id 𝕜 F := by
  ext v
  exact Z.coordChange_self _ _ (Z.mem_baseSet_at x) v

@[simp] theorem totalSpaceMap_id (Z : VectorBundleCore 𝕜 B F ι) :
    (id Z).totalSpaceMap = _root_.id := by
  funext p
  simp only [totalSpaceMap, fiberMap_id]
  rfl

end CoordinateHom
end VectorBundleCore
