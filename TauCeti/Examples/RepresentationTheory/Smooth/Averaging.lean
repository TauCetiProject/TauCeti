/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Averaging
import TauCeti.RepresentationTheory.Invariants

/-!
# Examples of the averaging projector

On a trivial representation of a compact group of invertible pro-order, the averaging projector is
the identity. For the finite discrete group `ℤˣ = {1, -1}` acting on `ℚ` by multiplication, it is
`v ↦ (v + (-v)) / 2 = 0`.
-/

public section

open Representation

namespace TauCeti

/-- The averaging projector of a trivial representation is the identity. -/
example {A K V : Type*} [CommRing A] [Group K] [TopologicalSpace K] [SeparatelyContinuousMul K]
    [CompactSpace K] [AddCommGroup V] [Module A V] (hK : HasUnitProOrder A K) :
    (trivial A K V).smoothAverage hK = LinearMap.id :=
  LinearMap.ext fun _ ↦ smoothAverage_apply_of_mem_invariants _ hK fun _ ↦ rfl

/-- The sign representation of `ℤˣ` on `ℚ` has averaging projector `0`. -/
example : (ofDistribMulAction ℚ ℤˣ ℚ).smoothAverage
    (hasUnitProOrder_iff_isUnit_card.2 <| by
      simp [Nat.card_eq_fintype_card, Fintype.card_units_int]) = 0 := by
  let : Invertible (Fintype.card ℤˣ : ℚ) := invertibleOfNonzero (by simp)
  rw [smoothAverage_eq_averageMap]
  refine LinearMap.ext fun v ↦ ?_
  have : (Finset.univ : Finset ℤˣ) = {1, -1} := by decide
  rw [averageMap_apply, this, Finset.sum_pair (by decide)]
  simp [Units.smul_def]

/-- Over `ZMod 2`, the group `ℤˣ` of order two does not have invertible pro-order. -/
example : ¬HasUnitProOrder (ZMod 2) ℤˣ := by
  rw [hasUnitProOrder_iff_isUnit_card, Nat.card_eq_fintype_card, Fintype.card_units_int]
  decide

end TauCeti
