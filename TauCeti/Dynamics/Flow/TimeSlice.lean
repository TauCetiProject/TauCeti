/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Global time slices of real flows

A continuous function `c` satisfying `c (φ t x) = t + c x` is a global time coordinate.
Its zero fibre meets every orbit exactly once. The flow identifies the phase space with
`ℝ × {x | c x = 0}`, and its action map `(t, x) ↦ (φ t x, x)` is proper on a Hausdorff
phase space. In particular this applies to connecting gradient trajectories after choosing
an intermediate level of the potential.
-/

public section

open Set Topology

namespace Flow

variable {X : Type*} [TopologicalSpace X] (φ : Flow ℝ X)
  (c : X → ℝ) (hc : Continuous c) (hshift : ∀ t x, c (φ t x) = t + c x)

/-- A global time coordinate trivializes a real flow over its zero slice. The inverse
flows a point of the slice for the specified time. -/
def timeSliceHomeomorph (hc : Continuous c) (hshift : ∀ t x, c (φ t x) = t + c x) :
    X ≃ₜ ℝ × {x : X | c x = 0} := by
  let forward (x : X) : ℝ × {x : X | c x = 0} :=
    (c x, ⟨φ (-c x) x, by simp only [mem_ofPred_eq, hshift, neg_add_cancel]⟩)
  let backward (tx : ℝ × {x : X | c x = 0}) : X := φ tx.1 tx.2.1
  refine
    { toFun := forward
      invFun := backward
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := hc.prodMk ((φ.continuous hc.neg continuous_id).subtype_mk _)
      continuous_invFun := φ.continuous continuous_fst
        (continuous_subtype_val.comp continuous_snd) }
  · intro x
    simp [forward, backward, ← φ.map_add]
  · rintro ⟨t, x, hx⟩
    have hx' : c x = 0 := hx
    simp [forward, backward, hshift, hx', ← φ.map_add]

@[simp]
theorem timeSliceHomeomorph_fst (x : X) :
    (φ.timeSliceHomeomorph c hc hshift x).1 = c x := (rfl)

@[simp]
theorem timeSliceHomeomorph_snd_coe (x : X) :
    ((φ.timeSliceHomeomorph c hc hshift x).2 : X) = φ (-c x) x := (rfl)

@[simp]
theorem timeSliceHomeomorph_symm_apply (tx : ℝ × {x : X | c x = 0}) :
    (φ.timeSliceHomeomorph c hc hshift).symm tx = φ tx.1 tx.2.1 := (rfl)

/-- In time-slice coordinates the flow translates only the real coordinate. -/
@[simp]
theorem timeSliceHomeomorph_flow (t : ℝ) (x : X) :
    φ.timeSliceHomeomorph c hc hshift (φ t x) =
      (t + (φ.timeSliceHomeomorph c hc hshift x).1,
        (φ.timeSliceHomeomorph c hc hshift x).2) := by
  apply Prod.ext
  · simp [hshift]
  · apply Subtype.ext
    simp only [timeSliceHomeomorph_snd_coe, hshift, ← φ.map_add]
    congr 1
    ring

include c hc hshift in
/-- A real flow with a continuous global time coordinate acts properly. No local
compactness of the phase space or compactness of the zero slice is needed. -/
theorem isProperMap_flow_pair_of_timeCoordinate [T2Space X] :
    IsProperMap (fun tx : ℝ × X ↦ (φ tx.1 tx.2, tx.2)) := by
  let r : X × X → ℝ × X := fun xy ↦ (c xy.1 - c xy.2, xy.2)
  have hr : Continuous r := ((hc.comp continuous_fst).sub
    (hc.comp continuous_snd)).prodMk continuous_snd
  have hleft : Function.LeftInverse r (fun tx : ℝ × X ↦ (φ tx.1 tx.2, tx.2)) := by
    intro tx
    simp [r, hshift]
  exact (hleft.isClosedEmbedding hr
    ((φ.continuous continuous_fst continuous_snd).prodMk continuous_snd)).isProperMap

end Flow
