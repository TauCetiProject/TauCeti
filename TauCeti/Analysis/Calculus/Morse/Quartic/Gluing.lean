/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Quartic.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Trajectories of the Euclidean quartic and their gluing at a break

The negative gradient flow of the Euclidean quartic `∑ i, (yᵢ² - 1)² / 4` acts coordinatewise on
the cube `[-1, 1]^ι` (`TauCeti.quarticWellSumFlow`). In one variable, every flow line in `(0, 1)`
is a translate of the unit-rate trajectory `q(s) = 1 / √(1 + e^{-2s})`
(`TauCeti.intervalBaseOrbit 1`). This file writes the trajectories between two critical points in
these time coordinates, and glues two trajectories at a break with the gluing parameter
`ρ = e^{-T}`, where `T` is the time separating the two pieces.

**Trajectory spaces.** For critical points `p` and `q`, the point
`TauCeti.quarticTrajectoryPoint p q u` keeps each coordinate with `p i = q i` at `p i` and puts
every other coordinate at `q i * q(u i)`. The flow translates all time coordinates at once
(`TauCeti.quarticWellSumFlow_quarticTrajectoryPoint`), and the points of the cube on trajectories
from `p` to `q` are exactly these points, when every coordinate with `p i ≠ q i` has `p i = 0`
(`TauCeti.tendsto_quarticWellSumFlow_atBot_atTop_iff_exists`). The time coordinates of a point are
determined on the moving coordinates (`TauCeti.quarticTrajectoryPoint_inj`), so the intersection of
the unstable set of `p` with the stable set of `q` in the cube is a copy of `ℝ^S` for the set `S`
of moving coordinates, with the flow acting by the diagonal translation.

**Gluing at a break.** Let `p → r → q` be a broken trajectory: the coordinates with `p i ≠ r i`
move first, from `0` to `r i = q i`, and those with `r i ≠ q i` move afterwards, from `0` to
`q i`. Running the first block a time `T = -log ρ` ahead of the second gives a trajectory from `p`
to `q`. It is recorded at two points: an early point, near the first piece, with the second block
delayed by `T` (`TauCeti.quarticGluingEarly`), and a late point, near the second piece, with the
first block advanced by `T` (`TauCeti.quarticGluingLate`). For `ρ > 0` these are two points of the
same trajectory, the late one the image of the early one under the flow for time `T`
(`TauCeti.quarticWellSumFlow_quarticGluingEarly`), and at `ρ = 0` they are the two pieces of the
broken trajectory (`TauCeti.quarticGluingEarly_zero`, `TauCeti.quarticGluingLate_zero`).

Both maps are smooth in the gluing parameter and the time coordinates jointly, across `ρ = 0`
(`TauCeti.contDiff_quarticGluingEarly`, `TauCeti.contDiff_quarticGluingLate`). The parameter
enters with the integer powers of the two eigenvalues of the quartic. A coordinate leaving `0`,
at rate `1`, is `x / √(1 + x²)` for `x = e^{u} ρ`
(`TauCeti.intervalBaseOrbit_one_add_log`), so the early point moves off the first piece linearly
in `ρ`, with nonzero speed in every coordinate of the second block
(`TauCeti.hasDerivAt_quarticGluingEarly_zero`). A coordinate arriving at `±1`, at rate `2`, is
`1 / √(1 + y²)` for `y = e^{-u} ρ` (`TauCeti.intervalBaseOrbit_one_sub_log`), so the late point
depends on `ρ` only through `ρ²` (`TauCeti.quarticGluingLate_neg`) and has derivative zero in `ρ`
at the break (`TauCeti.hasDerivAt_quarticGluingLate_zero`).

## Main definitions

* `TauCeti.quarticTrajectoryPoint`: the point with given time coordinates on the trajectories
  from `p` to `q`.
* `TauCeti.quarticGluingEarly`, `TauCeti.quarticGluingLate`: the early and late points of the
  trajectory glued at a break `p → r → q` with gluing parameter `ρ`.

## Main results

* `TauCeti.tendsto_quarticWellSumFlow_atBot_atTop_iff_exists`: the points of the cube on
  trajectories from `p` to `q` are the points `quarticTrajectoryPoint p q u`.
* `TauCeti.quarticWellSumFlow_quarticGluingEarly`, `TauCeti.quarticGluingEarly_zero`,
  `TauCeti.quarticGluingLate_zero`: the glued pair lies on one trajectory for `ρ > 0` and is the
  broken pair at `ρ = 0`.
* `TauCeti.contDiff_quarticGluingEarly`, `TauCeti.contDiff_quarticGluingLate`: smoothness across
  the break.
* `TauCeti.hasDerivAt_quarticGluingEarly_zero`, `TauCeti.hasDerivAt_quarticGluingLate_zero`: the
  departing coordinates move linearly in `ρ`, the arriving ones quadratically.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2 (spaces of unparametrized and broken trajectories and
  their gluing) and §3 (the comparison with cellular homology, which the quartic on the cube
  models).
* K. Wehrheim, *Smooth structures on Morse trajectory spaces, featuring finite ends and
  associative gluing*, Geom. Topol. Monogr. 18 (2012), [arXiv:1205.0713](https://arxiv.org/abs/1205.0713),
  §2 (gluing parameters `e^{-T}` near Euclidean critical points).
-/

public section

open Filter Set Topology

namespace TauCeti

/-! ### The unit-rate trajectory in the gluing parameter -/

/-- **Arrival at rate `2`.** In the gluing parameter `ρ = e^{-T}`, the unit-rate trajectory at time
`c + T` is `1 / √(1 + (e^{-c} ρ)²)`: it depends on `ρ` only through `ρ²`. -/
theorem intervalBaseOrbit_one_sub_log (c : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    intervalBaseOrbit 1 (c - Real.log ρ) = (√(1 + (Real.exp (-c) * ρ) ^ 2))⁻¹ := by
  rw [intervalBaseOrbit_apply,
    show -(2 * 1 * (c - Real.log ρ)) = (-c + Real.log ρ) + (-c + Real.log ρ) by ring,
    Real.exp_add, Real.exp_add, Real.exp_log hρ, sq]

/-- **Departure at rate `1`.** In the gluing parameter `ρ = e^{-T}`, the unit-rate trajectory at
time `c - T` is `x / √(1 + x²)` for `x = e^{c} ρ`: it is `ρ` times a function of `ρ²`. -/
theorem intervalBaseOrbit_one_add_log (c : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    intervalBaseOrbit 1 (c + Real.log ρ) =
      Real.exp c * ρ * (√(1 + (Real.exp c * ρ) ^ 2))⁻¹ := by
  have hx : 0 < Real.exp c * ρ := mul_pos (Real.exp_pos c) hρ
  have hsq : 1 + ((Real.exp c * ρ) ^ 2)⁻¹ = (1 + (Real.exp c * ρ) ^ 2) / (Real.exp c * ρ) ^ 2 := by
    field_simp
    ring
  rw [intervalBaseOrbit_apply,
    show -(2 * 1 * (c + Real.log ρ)) = -((c + Real.log ρ) + (c + Real.log ρ)) by ring,
    Real.exp_neg, Real.exp_add, Real.exp_add, Real.exp_log hρ, ← sq, hsq,
    Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hx.le, inv_div, div_eq_mul_inv]

/-! ### Trajectories between two critical points -/

variable {ι : Type*}

/-- The point with **time coordinates** `u` on the trajectories of the Euclidean quartic from `p`
to `q`: a coordinate with `p i = q i` stays at `p i`, and every other coordinate is
`q i * q(u i)` for the unit-rate trajectory `q = TauCeti.intervalBaseOrbit 1`. The values `u i`
at the coordinates with `p i = q i` are not used. -/
noncomputable def quarticTrajectoryPoint (p q u : ι → ℝ) : ι → ℝ :=
  fun i ↦ if p i = q i then p i else q i * intervalBaseOrbit 1 (u i)

@[simp]
theorem quarticTrajectoryPoint_apply (p q u : ι → ℝ) (i : ι) :
    quarticTrajectoryPoint p q u i = if p i = q i then p i else q i * intervalBaseOrbit 1 (u i) :=
  (rfl)

/-- The flow of the quartic translates all time coordinates of a trajectory point at once. -/
theorem quarticWellSumFlow_quarticTrajectoryPoint {p q : ι → ℝ}
    (hp : ∀ i, p i = -1 ∨ p i = 0 ∨ p i = 1) (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (s : ℝ)
    (u : ι → ℝ) :
    quarticWellSumFlow s (quarticTrajectoryPoint p q u) =
      quarticTrajectoryPoint p q fun i ↦ s + u i := by
  funext i
  simp only [quarticWellSumFlow_apply, quarticTrajectoryPoint_apply]
  split_ifs
  · rcases hp i with h | h | h <;> simp [h]
  · exact intervalBaseFlow_mul_intervalBaseOrbit 1 s (hq i) (u i)

/-- The time coordinates of a trajectory point are determined on the coordinates that move. -/
theorem quarticTrajectoryPoint_inj {p q u v : ι → ℝ} :
    quarticTrajectoryPoint p q u = quarticTrajectoryPoint p q v ↔
      ∀ i, p i ≠ q i → q i ≠ 0 → u i = v i := by
  simp only [funext_iff, quarticTrajectoryPoint_apply]
  refine forall_congr' fun i ↦ ?_
  by_cases h : p i = q i
  · simp [h]
  · rw [ite_eq_right h, ite_eq_right h, mul_eq_mul_left_iff,
      (intervalBaseOrbit_injective one_ne_zero).eq_iff]
    tauto

/-- Trajectory points between critical points lie in the cube `[-1, 1]^ι`. -/
theorem quarticTrajectoryPoint_mem_Icc {p q : ι → ℝ} (hp : ∀ i, p i = -1 ∨ p i = 0 ∨ p i = 1)
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (u : ι → ℝ) :
    quarticTrajectoryPoint p q u ∈ Icc (-1) 1 := by
  have ho := intervalBaseOrbit_mem_Ioo 1
  refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩ <;> simp only [Pi.neg_apply, Pi.one_apply,
    quarticTrajectoryPoint_apply] <;> split_ifs
  · rcases hp i with h | h | h <;> rw [h] <;> norm_num
  · rcases hq i with h | h | h <;> rw [h] <;> linarith [(ho (u i)).1, (ho (u i)).2]
  · rcases hp i with h | h | h <;> rw [h] <;> norm_num
  · rcases hq i with h | h | h <;> rw [h] <;> linarith [(ho (u i)).1, (ho (u i)).2]

/-- **The trajectory space of the quartic.** Between critical points `p` and `q`, the points of the
cube `[-1, 1]^ι` on trajectories from `p` to `q` are the points `quarticTrajectoryPoint p q u`,
provided every coordinate with `p i ≠ q i` has `p i = 0`; otherwise there are none. -/
theorem tendsto_quarticWellSumFlow_atBot_atTop_iff_exists {y p q : ι → ℝ} (hy : y ∈ Icc (-1) 1)
    (hp : ∀ i, p i = -1 ∨ p i = 0 ∨ p i = 1) (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) :
    Tendsto (fun s ↦ quarticWellSumFlow s y) atBot (𝓝 p) ∧
        Tendsto (fun s ↦ quarticWellSumFlow s y) atTop (𝓝 q) ↔
      (∀ i, p i ≠ q i → p i = 0) ∧ ∃ u, y = quarticTrajectoryPoint p q u := by
  rw [tendsto_quarticWellSumFlow_atBot_atTop_iff hy]
  constructor
  · intro h
    refine ⟨fun i hi ↦ ?_, fun i ↦ intervalBaseTimeCoordinate |y i|, funext fun i ↦ ?_⟩
    · rcases h i with ⟨-, h0, -⟩ | ⟨-, h1, h2⟩
      · exact h0
      · exact absurd (h1.trans h2.symm) hi
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
  · rintro ⟨hc, u, rfl⟩ i
    have ho := intervalBaseOrbit_mem_Ioo 1 (u i)
    rw [quarticTrajectoryPoint_apply]
    by_cases hpq : p i = q i
    · rw [ite_eq_left hpq, ← hpq]
      rcases hp i with h | h | h
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
    (hp : ∀ i, p i = -1 ∨ p i = 0 ∨ p i = 1) (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0) (u : ι → ℝ) :
    Tendsto (fun s ↦ quarticWellSumFlow s (quarticTrajectoryPoint p q u)) atBot (𝓝 p) ∧
      Tendsto (fun s ↦ quarticWellSumFlow s (quarticTrajectoryPoint p q u)) atTop (𝓝 q) :=
  (tendsto_quarticWellSumFlow_atBot_atTop_iff_exists (quarticTrajectoryPoint_mem_Icc hp hq u) hp
    hq).2 ⟨hpq, u, rfl⟩

/-! ### Gluing at a break -/

/-- The **early point of the glued trajectory** at a break `p → r → q`, with gluing parameter
`ρ`. For `ρ > 0` it is the trajectory point from `p` to `q` whose coordinates moving between `p`
and `r` have time coordinates `u i`, and whose coordinates moving between `r` and `q` are delayed
to `u i + log ρ` (`TauCeti.quarticGluingEarly_of_pos`). The formula `x / √(1 + x²)`,
`x = e^{u i} ρ`, extends it smoothly to every `ρ`; at `ρ = 0` it is the point of the first piece
(`TauCeti.quarticGluingEarly_zero`). -/
noncomputable def quarticGluingEarly (p r q : ι → ℝ) (ρ : ℝ) (u : ι → ℝ) : ι → ℝ :=
  fun i ↦ if p i = q i then p i
    else if p i = r i then q i * (Real.exp (u i) * ρ * (√(1 + (Real.exp (u i) * ρ) ^ 2))⁻¹)
    else q i * intervalBaseOrbit 1 (u i)

/-- The **late point of the glued trajectory** at a break `p → r → q`, with gluing parameter
`ρ`. For `ρ > 0` it is the trajectory point from `p` to `q` whose coordinates moving between `r`
and `q` have time coordinates `u i`, and whose coordinates moving between `p` and `r` are advanced
to `u i - log ρ` (`TauCeti.quarticGluingLate_of_pos`). The formula `1 / √(1 + y²)`,
`y = e^{-u i} ρ`, extends it smoothly to every `ρ`; at `ρ = 0` it is the point of the second piece
(`TauCeti.quarticGluingLate_zero`). -/
noncomputable def quarticGluingLate (p r q : ι → ℝ) (ρ : ℝ) (u : ι → ℝ) : ι → ℝ :=
  fun i ↦ if p i = q i then p i
    else if p i = r i then q i * intervalBaseOrbit 1 (u i)
    else q i * (√(1 + (Real.exp (-u i) * ρ) ^ 2))⁻¹

@[simp]
theorem quarticGluingEarly_apply (p r q : ι → ℝ) (ρ : ℝ) (u : ι → ℝ) (i : ι) :
    quarticGluingEarly p r q ρ u i = if p i = q i then p i
      else if p i = r i then q i * (Real.exp (u i) * ρ * (√(1 + (Real.exp (u i) * ρ) ^ 2))⁻¹)
      else q i * intervalBaseOrbit 1 (u i) :=
  (rfl)

@[simp]
theorem quarticGluingLate_apply (p r q : ι → ℝ) (ρ : ℝ) (u : ι → ℝ) (i : ι) :
    quarticGluingLate p r q ρ u i = if p i = q i then p i
      else if p i = r i then q i * intervalBaseOrbit 1 (u i)
      else q i * (√(1 + (Real.exp (-u i) * ρ) ^ 2))⁻¹ :=
  (rfl)

/-- For `ρ > 0` the early point is the trajectory point with the second block delayed by
`-log ρ`. -/
theorem quarticGluingEarly_of_pos (p r q : ι → ℝ) {ρ : ℝ} (hρ : 0 < ρ) (u : ι → ℝ) :
    quarticGluingEarly p r q ρ u =
      quarticTrajectoryPoint p q fun i ↦ if p i = r i then u i + Real.log ρ else u i := by
  funext i
  simp only [quarticGluingEarly_apply, quarticTrajectoryPoint_apply]
  split_ifs <;> simp [intervalBaseOrbit_one_add_log _ hρ]

/-- For `ρ > 0` the late point is the trajectory point with the first block advanced by
`-log ρ`. -/
theorem quarticGluingLate_of_pos (p r q : ι → ℝ) {ρ : ℝ} (hρ : 0 < ρ) (u : ι → ℝ) :
    quarticGluingLate p r q ρ u =
      quarticTrajectoryPoint p q fun i ↦ if p i = r i then u i else u i - Real.log ρ := by
  funext i
  simp only [quarticGluingLate_apply, quarticTrajectoryPoint_apply]
  split_ifs <;> simp [intervalBaseOrbit_one_sub_log _ hρ]

/-- **The glued pair lies on one trajectory.** For `ρ > 0` the flow for time `-log ρ` carries the
early point to the late point. -/
theorem quarticWellSumFlow_quarticGluingEarly {p r q : ι → ℝ}
    (hp : ∀ i, p i = -1 ∨ p i = 0 ∨ p i = 1) (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) {ρ : ℝ}
    (hρ : 0 < ρ) (u : ι → ℝ) :
    quarticWellSumFlow (-Real.log ρ) (quarticGluingEarly p r q ρ u) =
      quarticGluingLate p r q ρ u := by
  rw [quarticGluingEarly_of_pos p r q hρ, quarticWellSumFlow_quarticTrajectoryPoint hp hq,
    quarticGluingLate_of_pos p r q hρ, quarticTrajectoryPoint_inj]
  intro i _ _
  split_ifs <;> ring

/-- For `ρ > 0` the glued trajectory runs from `p` to `q`. -/
theorem tendsto_quarticWellSumFlow_quarticGluingEarly {p r q : ι → ℝ}
    (hp : ∀ i, p i = -1 ∨ p i = 0 ∨ p i = 1) (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpr : ∀ i, p i ≠ r i → p i = 0) (hrq : ∀ i, r i ≠ q i → r i = 0) {ρ : ℝ} (hρ : 0 < ρ)
    (u : ι → ℝ) :
    Tendsto (fun s ↦ quarticWellSumFlow s (quarticGluingEarly p r q ρ u)) atBot (𝓝 p) ∧
      Tendsto (fun s ↦ quarticWellSumFlow s (quarticGluingEarly p r q ρ u)) atTop (𝓝 q) := by
  rw [quarticGluingEarly_of_pos p r q hρ]
  refine tendsto_quarticWellSumFlow_quarticTrajectoryPoint hp hq (fun i hi ↦ ?_) _
  by_cases h : p i = r i
  · exact h.trans (hrq i (h ▸ hi))
  · exact hpr i h

/-- **The broken end, early side.** At `ρ = 0` the early point is the point with time coordinates
`u` on the first piece, from `p` to `r`. -/
theorem quarticGluingEarly_zero {p r q : ι → ℝ} (hpr : ∀ i, p i ≠ r i → p i = 0)
    (hrq : ∀ i, r i ≠ q i → r i = 0) (u : ι → ℝ) :
    quarticGluingEarly p r q 0 u = quarticTrajectoryPoint p r u := by
  funext i
  simp only [quarticGluingEarly_apply, quarticTrajectoryPoint_apply]
  by_cases hpr' : p i = r i
  · by_cases hpq : p i = q i
    · rw [ite_eq_left hpq, ite_eq_left hpr']
    · rw [ite_eq_right hpq, ite_eq_left hpr', ite_eq_left hpr', mul_zero, zero_mul, mul_zero]
      exact (hpr'.trans (hrq i fun h ↦ hpq (hpr'.trans h))).symm
  · have h0 := hpr i hpr'
    have hrq' : r i = q i := by_contra fun h ↦ hpr' (h0.trans (hrq i h).symm)
    rw [ite_eq_right fun h ↦ hpr' (h.trans hrq'.symm), ite_eq_right hpr', ite_eq_right hpr', hrq']

/-- **The broken end, late side.** At `ρ = 0` the late point is the point with time coordinates
`u` on the second piece, from `r` to `q`. -/
theorem quarticGluingLate_zero {p r q : ι → ℝ} (hpr : ∀ i, p i ≠ r i → p i = 0)
    (hrq : ∀ i, r i ≠ q i → r i = 0) (u : ι → ℝ) :
    quarticGluingLate p r q 0 u = quarticTrajectoryPoint r q u := by
  funext i
  simp only [quarticGluingLate_apply, quarticTrajectoryPoint_apply]
  by_cases hpr' : p i = r i
  · by_cases hpq : p i = q i
    · rw [ite_eq_left hpq, ite_eq_left (hpr'.symm.trans hpq), hpr']
    · rw [ite_eq_right hpq, ite_eq_left hpr', ite_eq_right fun h ↦ hpq (hpr'.trans h)]
  · have h0 := hpr i hpr'
    have hrq' : r i = q i := by_contra fun h ↦ hpr' (h0.trans (hrq i h).symm)
    rw [ite_eq_right fun h ↦ hpr' (h.trans hrq'.symm), ite_eq_right hpr', ite_eq_left hrq', hrq']
    simp

/-- The late point depends on the gluing parameter only through `ρ²`: the arriving coordinates
approach `±1` at rate `2`. -/
@[simp]
theorem quarticGluingLate_neg (p r q : ι → ℝ) (ρ : ℝ) (u : ι → ℝ) :
    quarticGluingLate p r q (-ρ) u = quarticGluingLate p r q ρ u := by
  funext i
  simp only [quarticGluingLate_apply, mul_neg, neg_sq]

/-! ### Smoothness across the break -/

private theorem contDiff_inv_sqrt_one_add_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {f : E → ℝ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n fun x ↦ (√(1 + f x ^ 2))⁻¹ :=
  ((contDiff_const.add (hf.pow 2)).sqrt fun _ ↦ by positivity).inv fun _ ↦ by positivity

/-- One coordinate of the early point is smooth in the gluing parameter and its time coordinate
jointly. -/
private theorem contDiff_quarticGluingEarly_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : WithTop ℕ∞} (p r q : ι → ℝ) (i : ι) {ρ : E → ℝ} {u : E → ι → ℝ}
    (hρ : ContDiff ℝ n ρ) (hu : ContDiff ℝ n fun x ↦ u x i) :
    ContDiff ℝ n fun x ↦ quarticGluingEarly p r q (ρ x) (u x) i := by
  have hx : ContDiff ℝ n fun x ↦ Real.exp (u x i) * ρ x := (ContDiff.exp hu).mul hρ
  simp only [quarticGluingEarly_apply]
  split_ifs
  · exact contDiff_const
  · exact contDiff_const.mul (hx.mul (contDiff_inv_sqrt_one_add_sq hx))
  · exact contDiff_const.mul ((contDiff_intervalBaseOrbit 1).comp hu)

/-- One coordinate of the late point is smooth in the gluing parameter and its time coordinate
jointly. -/
private theorem contDiff_quarticGluingLate_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : WithTop ℕ∞} (p r q : ι → ℝ) (i : ι) {ρ : E → ℝ} {u : E → ι → ℝ}
    (hρ : ContDiff ℝ n ρ) (hu : ContDiff ℝ n fun x ↦ u x i) :
    ContDiff ℝ n fun x ↦ quarticGluingLate p r q (ρ x) (u x) i := by
  simp only [quarticGluingLate_apply]
  split_ifs
  · exact contDiff_const
  · exact contDiff_const.mul ((contDiff_intervalBaseOrbit 1).comp hu)
  · exact contDiff_const.mul (contDiff_inv_sqrt_one_add_sq ((ContDiff.exp hu.neg).mul hρ))

/-- The early point is smooth in the gluing parameter and the time coordinates jointly, including
at the break `ρ = 0`. -/
theorem contDiff_quarticGluingEarly [Fintype ι] {n : WithTop ℕ∞} (p r q : ι → ℝ) :
    ContDiff ℝ n fun x : ℝ × (ι → ℝ) ↦ quarticGluingEarly p r q x.1 x.2 :=
  contDiff_pi.2 fun i ↦ contDiff_quarticGluingEarly_apply p r q i contDiff_fst (by fun_prop)

/-- The late point is smooth in the gluing parameter and the time coordinates jointly, including
at the break `ρ = 0`. -/
theorem contDiff_quarticGluingLate [Fintype ι] {n : WithTop ℕ∞} (p r q : ι → ℝ) :
    ContDiff ℝ n fun x : ℝ × (ι → ℝ) ↦ quarticGluingLate p r q x.1 x.2 :=
  contDiff_pi.2 fun i ↦ contDiff_quarticGluingLate_apply p r q i contDiff_fst (by fun_prop)

/-- **Convergence to the broken trajectory.** As the gluing parameter tends to `0`, the glued pair
tends to the pair of points with time coordinates `u` on the two pieces. -/
theorem tendsto_quarticGluing_zero {p r q : ι → ℝ} (hpr : ∀ i, p i ≠ r i → p i = 0)
    (hrq : ∀ i, r i ≠ q i → r i = 0) (u : ι → ℝ) :
    Tendsto (fun ρ ↦ (quarticGluingEarly p r q ρ u, quarticGluingLate p r q ρ u)) (𝓝 0)
      (𝓝 (quarticTrajectoryPoint p r u, quarticTrajectoryPoint r q u)) := by
  have he : Continuous fun ρ ↦ quarticGluingEarly p r q ρ u := continuous_pi fun i ↦
    (contDiff_quarticGluingEarly_apply (n := 0) p r q i contDiff_id contDiff_const).continuous
  have hl : Continuous fun ρ ↦ quarticGluingLate p r q ρ u := continuous_pi fun i ↦
    (contDiff_quarticGluingLate_apply (n := 0) p r q i contDiff_id contDiff_const).continuous
  rw [← quarticGluingEarly_zero hpr hrq u, ← quarticGluingLate_zero hpr hrq u]
  exact (he.prodMk hl).tendsto 0

/-- **Departure at rate `1`.** At the break, the early point moves off the first piece linearly in
the gluing parameter: each coordinate moving between `r` and `q` has velocity `q i * e^{u i}`,
nonzero when `q i ≠ 0`, and the other coordinates have velocity zero. -/
theorem hasDerivAt_quarticGluingEarly_zero (p r q : ι → ℝ) (u : ι → ℝ) :
    HasDerivAt (fun ρ ↦ quarticGluingEarly p r q ρ u)
      (fun i ↦ if p i ≠ q i ∧ p i = r i then q i * Real.exp (u i) else 0) 0 := by
  refine hasDerivAt_pi.2 fun i ↦ ?_
  by_cases hpq : p i = q i
  · simp only [quarticGluingEarly_apply, ite_eq_left hpq,
      ite_eq_right fun h : p i ≠ q i ∧ p i = r i ↦ h.1 hpq]
    exact hasDerivAt_const _ _
  by_cases hpr : p i = r i
  · simp only [quarticGluingEarly_apply, ite_eq_right hpq, ite_eq_left hpr,
      ite_eq_left (⟨hpq, hpr⟩ : p i ≠ q i ∧ p i = r i)]
    have hx : HasDerivAt (fun ρ : ℝ ↦ Real.exp (u i) * ρ) (Real.exp (u i)) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (Real.exp (u i))
    have hg : HasDerivAt (fun ρ : ℝ ↦ (√(1 + (Real.exp (u i) * ρ) ^ 2))⁻¹)
        (deriv (fun ρ : ℝ ↦ (√(1 + (Real.exp (u i) * ρ) ^ 2))⁻¹) 0) 0 :=
      ((contDiff_inv_sqrt_one_add_sq (n := 1) (contDiff_const.mul contDiff_id)).differentiable
        one_ne_zero 0).hasDerivAt
    simpa using (hx.mul hg).const_mul (q i)
  · simp only [quarticGluingEarly_apply, ite_eq_right hpq, ite_eq_right hpr,
      ite_eq_right fun h : p i ≠ q i ∧ p i = r i ↦ hpr h.2]
    exact hasDerivAt_const _ _

/-- **Arrival at rate `2`.** At the break, the late point has derivative zero in the gluing
parameter. -/
theorem hasDerivAt_quarticGluingLate_zero (p r q : ι → ℝ) (u : ι → ℝ) :
    HasDerivAt (fun ρ ↦ quarticGluingLate p r q ρ u) 0 0 := by
  refine hasDerivAt_pi.2 fun i ↦ ?_
  simp only [quarticGluingLate_apply, Pi.zero_apply]
  split_ifs
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · have hy : HasDerivAt (fun ρ : ℝ ↦ 1 + (Real.exp (-u i) * ρ) ^ 2) 0 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).const_mul (Real.exp (-u i))).pow 2).const_add 1
    simpa using ((hy.sqrt (by norm_num)).inv (by norm_num)).const_mul (q i)

end TauCeti
