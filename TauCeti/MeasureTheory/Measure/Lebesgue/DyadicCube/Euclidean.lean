/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.MeasureTheory.Measure.Lebesgue.DyadicCube
import TauCeti.Analysis.Normed.Lp.PiLp

/-!
# Dyadic cubes in Euclidean coordinates

Dyadic cubes (`TauCeti.dyadicCube`) live in `ι → ℝ` with its sup norm. Arguments about elliptic
equations work instead in `EuclideanSpace ℝ ι`, with Euclidean balls. This file compares the two:
a dyadic cube of level `k` has Euclidean diameter at most `2ᵏ √n` and contains the Euclidean ball
of radius `2ᵏ / 2` about its centre, its preimage in `EuclideanSpace ℝ ι` is measurable with volume
`(2ᵏ)ⁿ`, every positive scale `r` is bracketed by `2ᵏ √n ∈ (r / 2, r]`, and the part of a cube
where a function continuous on a closed set around it is at least `t` is measurable.

## Main declarations

* `TauCeti.dist_toLp_lt_of_mem_dyadicCube`: two points of a cube of level `k` are at Euclidean
  distance less than `2ᵏ √n`.
* `TauCeti.toLp_preimage_ball_subset_dyadicCube`: a dyadic cube contains the Euclidean ball of
  half its side length around its centre.
* `TauCeti.ball_subset_preimage_ofLp_dyadicCube`: the same inclusion in `EuclideanSpace ℝ ι`.
* `TauCeti.preimage_ofLp_dyadicCube_subset_ball`: the preimage of a level-`k` dyadic cube in
  `EuclideanSpace ℝ ι` lies in the Euclidean ball of radius `2ᵏ √n` about its centre.
* `TauCeti.measurableSet_preimage_ofLp_dyadicCube`, `TauCeti.volume_preimage_ofLp_dyadicCube`:
  measurability and volume `(2ᵏ)ⁿ` of a dyadic cube in `EuclideanSpace ℝ ι`.
* `TauCeti.exists_two_zpow_mul_sqrt_card_le_and_lt`: choosing a dyadic level `k` with
  `2ᵏ √n ≤ r < 2 · 2ᵏ √n`.
* `TauCeti.measurableSet_setOf_le_inter_dyadicCube`: superlevel sets of a function continuous on a
  closed set containing a cube meet the cube in a measurable set.
-/

public section

namespace TauCeti

open MeasureTheory Metric Set

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

/-- The Euclidean ball of radius `2ᵏ / 2` about the centre of a dyadic cube of level `k` lies in
the preimage of that cube in `EuclideanSpace ℝ ι`. -/
theorem ball_subset_preimage_ofLp_dyadicCube [Fintype ι] (k : ℤ) (m : ι → ℤ) :
    ball (WithLp.toLp 2 fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k : EuclideanSpace ℝ ι) (2 ^ k / 2) ⊆
      WithLp.ofLp ⁻¹' dyadicCube k m := fun x hx ↦
  toLp_preimage_ball_subset_dyadicCube k m (by simpa [WithLp.toLp_ofLp] using hx)

/-- The preimage of a dyadic cube of level `k` in `EuclideanSpace ℝ ι` lies in the Euclidean ball
of radius `2ᵏ √n` about its centre. -/
theorem preimage_ofLp_dyadicCube_subset_ball [Fintype ι] [Nonempty ι] (k : ℤ) (m : ι → ℤ) :
    WithLp.ofLp ⁻¹' dyadicCube k m ⊆
      ball (WithLp.toLp 2 fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k : EuclideanSpace ℝ ι)
        (2 ^ k * √(Fintype.card ι)) := fun x hx ↦ by
  have h := dist_toLp_lt_of_mem_dyadicCube hx (centre_mem_dyadicCube k m)
  rwa [WithLp.toLp_ofLp] at h

/-- The preimage of a dyadic cube in `EuclideanSpace ℝ ι` is measurable. -/
theorem measurableSet_preimage_ofLp_dyadicCube [Countable ι] (k : ℤ) (m : ι → ℤ) :
    MeasurableSet (WithLp.ofLp ⁻¹' dyadicCube k m : Set (EuclideanSpace ℝ ι)) :=
  (measurableSet_dyadicCube k m).preimage (PiLp.continuous_ofLp 2 _).measurable

/-- The volume of a dyadic cube of level `k` in `EuclideanSpace ℝ ι` is `(2ᵏ)ⁿ`. -/
theorem volume_preimage_ofLp_dyadicCube [Fintype ι] (k : ℤ) (m : ι → ℤ) :
    volume (WithLp.ofLp ⁻¹' dyadicCube k m : Set (EuclideanSpace ℝ ι)) =
      ENNReal.ofReal ((2 ^ k) ^ Fintype.card ι) := by
  rw [(PiLp.volume_preserving_ofLp ι).measure_preimage
    (measurableSet_dyadicCube k m).nullMeasurableSet, volume_dyadicCube]

/-- For any positive radius `r` in positive dimension `n`, there is a dyadic level `k : ℤ` whose
Euclidean diameter bound `2ᵏ √n` lies in `(r / 2, r]`. -/
theorem exists_two_zpow_mul_sqrt_card_le_and_lt [Fintype ι] [Nonempty ι] {r : ℝ} (hr : 0 < r) :
    ∃ k : ℤ, 2 ^ k * √(Fintype.card ι) ≤ r ∧ r < 2 * (2 ^ k * √(Fintype.card ι)) := by
  have hn : 0 < √(Fintype.card ι) := Real.sqrt_pos.2 (Nat.cast_pos.2 Fintype.card_pos)
  obtain ⟨k, hk1, hk2⟩ :=
    exists_mem_Ico_zpow (x := r / √(Fintype.card ι)) (div_pos hr hn) one_lt_two
  rw [le_div_iff₀ hn] at hk1
  rw [div_lt_iff₀ hn, zpow_add_one₀ two_ne_zero] at hk2
  exact ⟨k, hk1, by linarith⟩

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
