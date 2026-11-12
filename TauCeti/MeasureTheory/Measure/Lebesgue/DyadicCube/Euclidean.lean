/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.MeasureTheory.Measure.Lebesgue.DyadicCube
import TauCeti.Analysis.Normed.Lp.PiLp

/-!
# Dyadic cubes in Euclidean coordinates

Dyadic cubes (`TauCeti.dyadicCube`) live in `ι → ℝ` with its sup norm. Arguments about elliptic
equations work instead in `EuclideanSpace ℝ ι`, with Euclidean balls. This file compares the two:
a dyadic cube of level `k` has Euclidean diameter at most `2ᵏ √n` and contains the Euclidean ball
of radius `2ᵏ / 2` about its centre, and the part of a cube where a function continuous on a
closed set around it is at least `t` is measurable.

## Main declarations

* `TauCeti.dist_toLp_lt_of_mem_dyadicCube`: two points of a cube of level `k` are at Euclidean
  distance less than `2ᵏ √n`.
* `TauCeti.toLp_preimage_ball_subset_dyadicCube`: a dyadic cube contains the Euclidean ball of
  half its side length around its centre.
* `TauCeti.measurableSet_setOf_le_inter_dyadicCube`: superlevel sets of a function continuous on a
  closed set containing a cube meet the cube in a measurable set.
-/

public section

namespace TauCeti

open Metric Set

variable {ι : Type*}

/-- Two points of a dyadic cube of level `k` are at Euclidean distance less than `2ᵏ √n`. -/
theorem dist_toLp_lt_of_mem_dyadicCube [Fintype ι] [Nonempty ι] {k : ℤ} {m : ι → ℤ}
    {y z : ι → ℝ} (hy : y ∈ dyadicCube k m) (hz : z ∈ dyadicCube k m) :
    dist (WithLp.toLp 2 y : EuclideanSpace ℝ ι) (WithLp.toLp 2 z) < 2 ^ k * √(Fintype.card ι) := by
  rw [mul_comm]
  exact PiLp.preimage_ofLp_ball_subset_ball (WithLp.toLp 2 z) _ (dist_lt_of_mem_dyadicCube hy hz)

/-- The Euclidean ball of radius `2ᵏ / 2` about the centre of a dyadic cube of level `k` lies in
the cube. -/
theorem toLp_preimage_ball_subset_dyadicCube [Fintype ι] (k : ℤ) (m : ι → ℤ) :
    WithLp.toLp 2 ⁻¹' ball (WithLp.toLp 2 fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k :
      EuclideanSpace ℝ ι) (2 ^ k / 2) ⊆ dyadicCube k m := fun _ hy ↦
  ball_subset_dyadicCube k m (PiLp.ball_subset_preimage_ofLp_ball _ _ hy)

/-- The part of a dyadic cube where `u ≥ t` is measurable, when `u` is continuous on a closed set
containing the cube. -/
theorem measurableSet_setOf_le_inter_dyadicCube [Countable ι] {u : EuclideanSpace ℝ ι → ℝ}
    {s : Set (EuclideanSpace ℝ ι)} (hs : IsClosed s) (hcont : ContinuousOn u s) {k : ℤ}
    {m : ι → ℤ} (hQ : dyadicCube k m ⊆ WithLp.toLp 2 ⁻¹' s) (t : ℝ) :
    MeasurableSet ({y | t ≤ u (WithLp.toLp 2 y)} ∩ dyadicCube k m) := by
  have hcl : IsClosed (WithLp.toLp 2 ⁻¹' s ∩ (u ∘ WithLp.toLp 2) ⁻¹' Ici t) :=
    ContinuousOn.preimage_isClosed_of_isClosed
      (hcont.comp (PiLp.continuous_toLp 2 _).continuousOn (mapsTo_preimage _ _))
      (hs.preimage (PiLp.continuous_toLp 2 _)) isClosed_Ici
  have heq : {y | t ≤ u (WithLp.toLp 2 y)} ∩ dyadicCube k m =
      (WithLp.toLp 2 ⁻¹' s ∩ (u ∘ WithLp.toLp 2) ⁻¹' Ici t) ∩ dyadicCube k m := by
    ext y
    exact ⟨fun h ↦ ⟨⟨hQ h.2, h.1⟩, h.2⟩, fun h ↦ ⟨h.1.2, h.2⟩⟩
  rw [heq]
  exact hcl.measurableSet.inter (measurableSet_dyadicCube k m)

end TauCeti
