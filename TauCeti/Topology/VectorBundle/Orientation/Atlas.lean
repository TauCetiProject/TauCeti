/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Basic
public import TauCeti.Topology.VectorBundle.Coordinates

/-!
# Orientations from positive bundle atlases

A covering family of trivializations with positive transition determinants induces an actual
orientation of every fibre. This constructor permits the family to be a proper subatlas.
-/

public section

noncomputable section

open Set Filter Bundle
open scoped Topology

namespace VectorBundleCore

variable {B F κ ι : Type*} [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [Fintype ι]
  (Z : VectorBundleCore ℝ B F κ) (model : Orientation ℝ F ι)
  (hι : Fintype.card ι = Module.finrank ℝ F) {S : Set κ}
  (hcover : ∀ x, ∃ i ∈ S, x ∈ Z.baseSet i)
  (hpos : ∀ i ∈ S, ∀ j ∈ S, ∀ x ∈ Z.baseSet i ∩ Z.baseSet j,
    0 < (Z.coordChange i j x).det)

private def orientationOfPositiveAtlasAt (x : B) : Orientation ℝ (Z.Fiber x) ι :=
  ((Z.localTriv (Classical.choose (hcover x))).mapOrientation ι
    (Classical.choose_spec (hcover x)).2).symm model

include hι hpos in
private theorem mapOrientation_orientationOfPositiveAtlasAt (i : κ) (hi : i ∈ S)
    (x : B) (hxi : x ∈ (Z.localTriv i).baseSet) :
    (Z.localTriv i).mapOrientation ι hxi
      (orientationOfPositiveAtlasAt Z model hcover x) = model := by
  let j := Classical.choose (hcover x)
  have hj : j ∈ S := (Classical.choose_spec (hcover x)).1
  have hxj : x ∈ (Z.localTriv j).baseSet := (Classical.choose_spec (hcover x)).2
  rw [Trivialization.mapOrientation_eq_map_coordChangeL (Z.localTriv j) _ hxj]
  simp only [orientationOfPositiveAtlasAt, j, Equiv.apply_symm_apply]
  -- The trivialization transport is Mathlib's orientation map of the coordinate equivalence.
  change Orientation.map ι ((Z.localTriv j).coordChangeL ℝ
    (Z.localTriv i) x).toLinearEquiv model = model
  rw [Orientation.map_eq_iff_det_pos _ _ hι]
  rw [Z.det_localTriv_coordChangeL ⟨hxj, hxi⟩]
  exact hpos j hj i hi x ⟨hxj, hxi⟩

/-- A positive subatlas that covers the base defines a vector bundle orientation. -/
def orientationOfPositiveAtlas : TauCeti.VectorBundleOrientation F Z.Fiber ι := by
  let idx (x : B) := Classical.choose (hcover x)
  have hidx (x : B) : idx x ∈ S := (Classical.choose_spec (hcover x)).1
  have hx (x : B) : x ∈ (Z.localTriv (idx x)).baseSet :=
    (Classical.choose_spec (hcover x)).2
  letI (x : B) : MemTrivializationAtlas (Z.localTriv (idx x)) := ⟨⟨idx x, rfl⟩⟩
  exact TauCeti.VectorBundleOrientation.ofEventually hι
    (orientationOfPositiveAtlasAt Z model hcover) (fun x ↦ Z.localTriv (idx x)) hx
    (fun b ↦ Eventually.of_forall fun x hx' ↦
      (mapOrientation_orientationOfPositiveAtlasAt Z model hι hcover hpos
        _ (hidx b) x hx').trans
      (mapOrientation_orientationOfPositiveAtlasAt Z model hι hcover hpos
        _ (hidx b) b (hx b)).symm)

/-- Every chart of the given positive subatlas reads the induced orientation as the prescribed
model orientation. -/
@[simp] theorem mapOrientation_orientationOfPositiveAtlas (i : κ) (hi : i ∈ S)
    (x : B) (hxi : x ∈ (Z.localTriv i).baseSet) :
    (Z.localTriv i).mapOrientation ι hxi
      (Z.orientationOfPositiveAtlas model hι hcover hpos x) = model := by
  simp only [orientationOfPositiveAtlas]
  -- The constructor installs point-dependent local atlas instances. The evaluation equation
  -- identifies the same family after reducing these proof-only instance arguments.
  erw [TauCeti.VectorBundleOrientation.coe_ofEventually]
  exact mapOrientation_orientationOfPositiveAtlasAt Z model hι hcover hpos i hi x hxi

end VectorBundleCore
