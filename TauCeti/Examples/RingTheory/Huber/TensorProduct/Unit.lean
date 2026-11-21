/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Unit
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Pair.Polydisc
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Adic
public import TauCeti.RingTheory.Huber.Padic.Field

/-!
# Checks for the completed tensor unit

The unit comparison over the two-adic closed disc fixes its coordinate, preserves its
specified plus ring, and has the left coprojection as its inverse. A coefficient outside
the two-adic integral elements remains outside the completed tensor plus ring.
-/

public section

open TensorProduct TauCeti.Huber

namespace TauCeti.Examples.CompletedTensorUnit

/-- The identity coefficient map for the two-adic unit checks is adic. -/
local instance isAdicHom_self : IsAdicHom (algebraMap ℚ_[2] ℚ_[2]) := by
  simpa using (IsAdicHom.id (A := ℚ_[2]))

/-- *symmetry_and_unit_on_charts_unit*: the unit over the two-adic closed disc fixes `T`. -/
example :
    CompletedTensor.rightUnitor ℚ_[2] (restrictedMvPowerSeriesCompletion 1 ℚ_[2])
      (CompletedTensor.toCompletion ℚ_[2] (restrictedMvPowerSeriesCompletion 1 ℚ_[2]) ℚ_[2]
        (Pair.polydiscVar 1 ℚ_[2] 0 ⊗ₜ[ℚ_[2]] 1)) = Pair.polydiscVar 1 ℚ_[2] 0 := by
  simp

/-- *symmetry_and_unit_on_charts_unit*: both maps of the unit preserve the disc plus ring,
and their composites are the identity. -/
example :
    let P := Pair.powerBounded ℚ_[2]
    let D := P.polydisc 1
    ∃ f : Pair.Hom (D.completedTensor ℚ_[2] P) D,
      f.toRingHom = (CompletedTensor.rightUnitor ℚ_[2]
        (restrictedMvPowerSeriesCompletion 1 ℚ_[2])).toRingHom ∧
      f.comp (Pair.completedTensor.inl ℚ_[2] D P) = Pair.Hom.id D ∧
      (Pair.completedTensor.inl ℚ_[2] D P).comp f = Pair.Hom.id _ := by
  intro P D
  have h : ∀ a ∈ P.plus,
      algebraMap ℚ_[2] (restrictedMvPowerSeriesCompletion 1 ℚ_[2]) a ∈ D.plus := by
    intro a ha
    simpa only [Pair.Hom.toRingHom_weightedCompletionHom] using
      (P.weightedCompletionHom (k := 1) isWeightFamily_one_weight).map_mem_plus a ha
  exact ⟨Pair.completedTensor.rightUnitorHom P D h, by simp, by simp, by simp⟩

/-- A nonintegral two-adic scalar does not enter the completed tensor plus ring under the
inverse unit comparison. -/
example :
    let P := Pair.powerBounded ℚ_[2]
    (CompletedTensor.rightUnitor ℚ_[2] ℚ_[2]).symm (2 : ℚ_[2])⁻¹ ∉
      (P.completedTensor ℚ_[2] P).plus := by
  intro P hx
  have h := (Pair.completedTensor.rightUnitor_mem_plus P P
    (fun a ha => by simpa using ha) _).mp hx
  have hnorm : ‖(2 : ℚ_[2])⁻¹‖ ≤ 1 := by
    apply isPowerBounded_iff_norm_le_one.mp
    apply mem_powerBoundedSubring.mp
    simpa [P, Pair.powerBounded_plus] using h
  have hp := _root_.Padic.norm_p (p := 2)
  norm_num only [Nat.cast_ofNat] at hp
  rw [norm_inv, hp] at hnorm
  norm_num at hnorm

end TauCeti.Examples.CompletedTensorUnit
