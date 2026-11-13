/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Quartic.Basic

/-!
# Trajectory spaces of the Euclidean quartic in time coordinates

The negative gradient flow of the Euclidean quartic `∑ i, (yᵢ² - 1)² / 4` acts coordinatewise on
the cube `[-1, 1]^ι` (`TauCeti.quarticWellSumFlow`). In one variable, every flow line in `(0, 1)`
is a translate of the unit-rate trajectory `s ↦ 1 / √(1 + e^{-2s})` (`TauCeti.intervalBaseOrbit 1`),
and the time coordinate `TauCeti.intervalBaseTimeCoordinate` inverts it. This file writes the
trajectories between two critical points in these time coordinates.

For critical points `p` and `q`, the point `TauCeti.quarticTrajectoryPoint p q u` keeps each
coordinate with `p i = q i` at `p i` and puts every other coordinate at
`q i * intervalBaseOrbit 1 (u i)`. The flow translates all time coordinates at once
(`TauCeti.quarticWellSumFlow_quarticTrajectoryPoint`), and the points of the cube on trajectories
from `p` to `q` are exactly these points, when `q` is a critical point and every coordinate with
`p i ≠ q i` has `p i = 0` (`TauCeti.tendsto_quarticWellSumFlow_atBot_atTop_iff_exists`). The time
coordinates of such a point `y` are `intervalBaseTimeCoordinate |y i|` on the moving coordinates
(`TauCeti.intervalBaseTimeCoordinate_abs_quarticTrajectoryPoint`,
`TauCeti.quarticTrajectoryPoint_intervalBaseTimeCoordinate_abs`), and they are determined there
(`TauCeti.quarticTrajectoryPoint_eq_quarticTrajectoryPoint_iff`). So the intersection of the
unstable set of `p` with the stable set of `q` in the cube is a copy of `ℝ^S` for the set `S` of
moving coordinates, with the flow acting by the diagonal translation.

## Main definitions

* `TauCeti.quarticTrajectoryPoint`: the point with given time coordinates on the trajectories
  from `p` to `q`.

## Main results

* `TauCeti.tendsto_quarticWellSumFlow_atBot_atTop_iff_exists`: the points of the cube on
  trajectories from `p` to `q` are the points `quarticTrajectoryPoint p q u`.
* `TauCeti.quarticWellSumFlow_quarticTrajectoryPoint`: the flow translates the time coordinates.
* `TauCeti.intervalBaseTimeCoordinate_abs_quarticTrajectoryPoint`,
  `TauCeti.quarticTrajectoryPoint_intervalBaseTimeCoordinate_abs`: the time coordinates are
  recovered from the point.
* `TauCeti.contDiff_quarticTrajectoryPoint`: the parametrization is smooth.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2 (spaces of unparametrized trajectories) and §3 (the
  comparison with cellular homology, which the quartic on the cube models).
-/

public section

open Filter Set Topology

namespace TauCeti

variable {ι : Type*}

/-- The point with **time coordinates** `u` on the trajectories of the Euclidean quartic from `p`
to `q`: a coordinate with `p i = q i` stays at `p i`, and every other coordinate is
`q i * intervalBaseOrbit 1 (u i)`. The values `u i` at the coordinates with `p i = q i` are not
used. -/
noncomputable def quarticTrajectoryPoint (p q u : ι → ℝ) : ι → ℝ :=
  fun i ↦ if p i = q i then p i else q i * intervalBaseOrbit 1 (u i)

@[simp]
theorem quarticTrajectoryPoint_apply (p q u : ι → ℝ) (i : ι) :
    quarticTrajectoryPoint p q u i = if p i = q i then p i else q i * intervalBaseOrbit 1 (u i) :=
  (rfl)

/-- With equal endpoints the trajectory point is the constant trajectory at `p`. -/
@[simp]
theorem quarticTrajectoryPoint_same (p u : ι → ℝ) : quarticTrajectoryPoint p p u = p := by
  funext i
  simp

/-- The flow of the quartic translates all time coordinates of a trajectory point at once. -/
theorem quarticWellSumFlow_quarticTrajectoryPoint {p q : ι → ℝ}
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (s : ℝ) (u : ι → ℝ) :
    quarticWellSumFlow s (quarticTrajectoryPoint p q u) =
      quarticTrajectoryPoint p q fun i ↦ s + u i := by
  funext i
  simp only [quarticWellSumFlow_apply, quarticTrajectoryPoint_apply]
  split_ifs with hpq
  · rw [hpq]
    rcases hq i with h | h | h <;> simp [h]
  · exact intervalBaseFlow_mul_intervalBaseOrbit 1 s (hq i) (u i)

/-- The time coordinates of a trajectory point are determined on the coordinates that move. -/
theorem quarticTrajectoryPoint_eq_quarticTrajectoryPoint_iff {p q u v : ι → ℝ} :
    quarticTrajectoryPoint p q u = quarticTrajectoryPoint p q v ↔
      ∀ i, p i ≠ q i → q i ≠ 0 → u i = v i := by
  simp only [funext_iff, quarticTrajectoryPoint_apply]
  refine forall_congr' fun i ↦ ?_
  by_cases h : p i = q i
  · simp [h]
  · rw [ite_eq_right h, ite_eq_right h, mul_eq_mul_left_iff,
      (intervalBaseOrbit_injective one_ne_zero).eq_iff]
    tauto

/-- On a coordinate moving to `±1`, the time coordinate of a trajectory point is recovered from
its absolute value. -/
theorem intervalBaseTimeCoordinate_abs_quarticTrajectoryPoint {p q : ι → ℝ} {i : ι}
    (hpq : p i ≠ q i) (hq : q i = -1 ∨ q i = 1) (u : ι → ℝ) :
    intervalBaseTimeCoordinate |quarticTrajectoryPoint p q u i| = u i := by
  have hq' : |q i| = 1 := by rcases hq with h | h <;> simp [h]
  rw [quarticTrajectoryPoint_apply, ite_eq_right hpq, abs_mul, hq', one_mul,
    abs_of_pos (intervalBaseOrbit_mem_Ioo 1 (u i)).1, intervalBaseTimeCoordinate_intervalBaseOrbit,
    one_mul]

/-- Trajectory points lie in the cube `[-1, 1]^ι` when their endpoint `q` does. -/
theorem quarticTrajectoryPoint_mem_Icc (p : ι → ℝ) {q : ι → ℝ} (hq : q ∈ Icc (-1) 1)
    (u : ι → ℝ) : quarticTrajectoryPoint p q u ∈ Icc (-1) 1 := by
  rw [← pi_univ_Icc]
  refine fun i _ ↦ abs_le.1 ?_
  have hqi : |q i| ≤ 1 := abs_le.2 ⟨hq.1 i, hq.2 i⟩
  have ho := intervalBaseOrbit_mem_Ioo 1 (u i)
  rw [quarticTrajectoryPoint_apply]
  split_ifs with h
  · rwa [h]
  · rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hqi).trans ((abs_of_pos ho.1).trans_le ho.2.le)

/-- **Time coordinates of a trajectory point.** A point `y` of the cube on a trajectory from `p`
to `q` is the trajectory point with time coordinates `intervalBaseTimeCoordinate |y i|`. -/
theorem quarticTrajectoryPoint_intervalBaseTimeCoordinate_abs {y p q : ι → ℝ}
    (hy : y ∈ Icc (-1) 1) (h : Tendsto (fun s ↦ quarticWellSumFlow s y) atBot (𝓝 p) ∧
      Tendsto (fun s ↦ quarticWellSumFlow s y) atTop (𝓝 q)) :
    quarticTrajectoryPoint p q (fun i ↦ intervalBaseTimeCoordinate |y i|) = y := by
  rw [tendsto_quarticWellSumFlow_atBot_atTop_iff hy] at h
  funext i
  rw [quarticTrajectoryPoint_apply]
  rcases h i with ⟨hyi, h0, hs⟩ | ⟨-, h1, h2⟩
  · rcases lt_trichotomy (y i) 0 with hneg | hzero | hpos
    · have hq' : q i = -1 := by simp [hs, hneg]
      rw [ite_eq_right (by rw [h0, hq']; norm_num), hq', abs_of_neg hneg,
        intervalBaseOrbit_one_intervalBaseTimeCoordinate ⟨by linarith, by linarith [hyi.1]⟩]
      ring
    · rw [ite_eq_left (by simp [h0, hs, hzero]), h0, hzero]
    · have hq' : q i = 1 := by simp [hs, hpos]
      rw [ite_eq_right (by rw [h0, hq']; norm_num), hq', abs_of_pos hpos,
        intervalBaseOrbit_one_intervalBaseTimeCoordinate ⟨hpos, hyi.2⟩, one_mul]
  · rw [ite_eq_left (h1.trans h2.symm), h1]

/-- **The trajectory space of the quartic.** The points of the cube `[-1, 1]^ι` on trajectories
from `p` to `q` are the points `quarticTrajectoryPoint p q u`, provided `q` is a critical point and
every coordinate with `p i ≠ q i` has `p i = 0`; otherwise there are none. -/
theorem tendsto_quarticWellSumFlow_atBot_atTop_iff_exists {y p q : ι → ℝ} (hy : y ∈ Icc (-1) 1) :
    Tendsto (fun s ↦ quarticWellSumFlow s y) atBot (𝓝 p) ∧
        Tendsto (fun s ↦ quarticWellSumFlow s y) atTop (𝓝 q) ↔
      (∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) ∧ (∀ i, p i ≠ q i → p i = 0) ∧
        ∃ u, y = quarticTrajectoryPoint p q u := by
  constructor
  · intro h
    refine ⟨fun i ↦ ?_, fun i hi ↦ ?_, _,
      (quarticTrajectoryPoint_intervalBaseTimeCoordinate_abs hy h).symm⟩
    · rcases (tendsto_quarticWellSumFlow_atBot_atTop_iff hy).1 h i with ⟨-, -, hs⟩ | ⟨h1, -, h2⟩
      · rcases lt_trichotomy (y i) 0 with h | h | h <;> simp [hs, h]
      · rw [h2]
        tauto
    · rcases (tendsto_quarticWellSumFlow_atBot_atTop_iff hy).1 h i with ⟨-, h0, -⟩ | ⟨-, h1, h2⟩
      · exact h0
      · exact absurd (h1.trans h2.symm) hi
  rw [tendsto_quarticWellSumFlow_atBot_atTop_iff hy]
  rintro ⟨hq, hc, u, rfl⟩ i
  have ho := intervalBaseOrbit_mem_Ioo 1 (u i)
  rw [quarticTrajectoryPoint_apply]
  by_cases hpq : p i = q i
  · rw [ite_eq_left hpq, ← hpq]
    rcases hq i with h | h | h <;> rw [← hpq] at h
    · exact Or.inr ⟨Or.inl h, rfl, rfl⟩
    · exact Or.inl ⟨by rw [h]; norm_num, h, by simp [h]⟩
    · exact Or.inr ⟨Or.inr h, rfl, rfl⟩
  · rw [ite_eq_right hpq]
    refine Or.inl ⟨?_, hc i hpq, ?_⟩ <;> rcases hq i with h | h | h
    · rw [h]; constructor <;> linarith [ho.1, ho.2]
    · exact absurd ((hc i hpq).trans h.symm) hpq
    · rw [h]; constructor <;> linarith [ho.1, ho.2]
    · simp [h, ho.1]
    · exact absurd ((hc i hpq).trans h.symm) hpq
    · simp [h, ho.1]

/-- The flow line through a trajectory point runs from `p` to `q`. -/
theorem tendsto_quarticWellSumFlow_quarticTrajectoryPoint {p q : ι → ℝ}
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (hpq : ∀ i, p i ≠ q i → p i = 0) (u : ι → ℝ) :
    Tendsto (fun s ↦ quarticWellSumFlow s (quarticTrajectoryPoint p q u)) atBot (𝓝 p) ∧
      Tendsto (fun s ↦ quarticWellSumFlow s (quarticTrajectoryPoint p q u)) atTop (𝓝 q) := by
  have hq' : q ∈ Icc (-1) 1 := ⟨fun i ↦ by rcases hq i with h | h | h <;> simp [h],
    fun i ↦ by rcases hq i with h | h | h <;> simp [h]⟩
  exact (tendsto_quarticWellSumFlow_atBot_atTop_iff_exists
    (quarticTrajectoryPoint_mem_Icc p hq' u)).2 ⟨hq, hpq, u, rfl⟩

/-- The trajectory point depends continuously on its time coordinates. -/
theorem continuous_quarticTrajectoryPoint (p q : ι → ℝ) : Continuous (quarticTrajectoryPoint p q) :=
  continuous_pi fun i ↦ by
    simp only [quarticTrajectoryPoint_apply]
    split_ifs
    · exact continuous_const
    · exact continuous_const.mul ((contDiff_intervalBaseOrbit 1 (n := 0)).continuous.comp
        (continuous_apply i))

/-- The trajectory point depends smoothly on its time coordinates. -/
theorem contDiff_quarticTrajectoryPoint [Fintype ι] {n : WithTop ℕ∞} (p q : ι → ℝ) :
    ContDiff ℝ n (quarticTrajectoryPoint p q) :=
  contDiff_pi.2 fun i ↦ by
    simp only [quarticTrajectoryPoint_apply]
    split_ifs
    · exact contDiff_const
    · exact contDiff_const.mul ((contDiff_intervalBaseOrbit 1).comp (by fun_prop))

end TauCeti
