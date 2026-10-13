/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation

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

/-- A positive subatlas that covers the base defines a vector bundle orientation. -/
def orientationOfPositiveAtlas : TauCeti.VectorBundleOrientation F Z.Fiber ι := by
  choose idx hidx hx using hcover
  have hxb (x : B) : x ∈ (Z.localTriv (idx x)).baseSet := hx x
  letI (x : B) : MemTrivializationAtlas (Z.localTriv (idx x)) := ⟨⟨idx x, rfl⟩⟩
  let o (x : B) : Orientation ℝ (Z.Fiber x) ι :=
    ((Z.localTriv (idx x)).mapOrientation ι (hxb x)).symm model
  have hread (i : κ) (hi : i ∈ S) (x : B) (hxi : x ∈ (Z.localTriv i).baseSet) :
      (Z.localTriv i).mapOrientation ι hxi (o x) = model := by
    rw [Trivialization.mapOrientation_eq_map_coordChangeL
      (Z.localTriv (idx x)) _ (hxb x)]
    simp only [o, Equiv.apply_symm_apply]
    change Orientation.map ι ((Z.localTriv (idx x)).coordChangeL ℝ
      (Z.localTriv i) x).toLinearEquiv model = model
    rw [Orientation.map_eq_iff_det_pos _ _ hι]
    have hd : (((Z.localTriv (idx x)).coordChangeL ℝ (Z.localTriv i) x) : F →L[ℝ] F) =
        Z.coordChange (idx x) i x := by
      ext v
      exact Z.localTriv_coordChange_eq _ _ ⟨hx x, hxi⟩ v
    change (((Z.localTriv (idx x)).coordChangeL ℝ (Z.localTriv i) x) : F →L[ℝ] F).det > 0
    rw [hd]
    exact hpos _ (hidx x) i hi x ⟨hx x, hxi⟩
  exact TauCeti.VectorBundleOrientation.ofEventually hι o (fun x ↦ Z.localTriv (idx x)) hxb
    (fun b ↦ Eventually.of_forall fun x hx' ↦
      (hread _ (hidx b) x hx').trans (hread _ (hidx b) b (hxb b)).symm)

end VectorBundleCore
