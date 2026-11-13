/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Quartic.Trajectory
import TauCeti.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Gluing trajectories of the Euclidean quartic at a break

The negative gradient flow of the Euclidean quartic `∑ i, (yᵢ² - 1)² / 4` acts coordinatewise on
the cube `[-1, 1]^ι` (`TauCeti.quarticWellSumFlow`), and its trajectories between two critical
points are the points `TauCeti.quarticTrajectoryPoint p q u` with time coordinates `u`. This file
glues two trajectories at a break with the gluing parameter `ρ = e^{-T}`, where `T` is the time
separating the two pieces.

Let `p → r → q` be a broken trajectory: the coordinates with `p i ≠ r i` move first, from `0` to
`r i = q i`, and those with `r i ≠ q i` move afterwards, from `0` to `q i`. Running the first block
a time `T = -log ρ` ahead of the second gives a trajectory from `p` to `q`. It is recorded at two
points: an early point, near the first piece, with the second block delayed by `T`
(`TauCeti.quarticGluingEarly`), and a late point, near the second piece, with the first block
advanced by `T` (`TauCeti.quarticGluingLate`). For `ρ > 0` these are two points of the same
trajectory, the late one the image of the early one under the flow for time `T`
(`TauCeti.quarticWellSumFlow_neg_log_quarticGluingEarly`), and at `ρ = 0` they are the two pieces
of the broken trajectory (`TauCeti.quarticGluingEarly_zero`, `TauCeti.quarticGluingLate_zero`).
For every `ρ`, including `ρ = 0`, the flow translates the time coordinates of both points
(`TauCeti.quarticWellSumFlow_quarticGluingEarly`, `TauCeti.quarticWellSumFlow_quarticGluingLate`).
For `ρ ≥ 0` the glued pair determines the gluing parameter and the time coordinates of the moving
coordinates (`TauCeti.quarticGluingEarly_eq_and_quarticGluingLate_eq_iff`), and both are recovered
from it explicitly (`TauCeti.intervalBaseTimeCoordinate_abs_quarticGluingEarly`,
`TauCeti.intervalBaseTimeCoordinate_abs_quarticGluingLate`,
`TauCeti.exp_neg_mul_mul_quarticGluingEarly_div_sqrt_one_sub_sq`).

Both maps are smooth in the gluing parameter and the time coordinates jointly, across `ρ = 0`
(`TauCeti.contDiff_quarticGluingEarly`, `TauCeti.contDiff_quarticGluingLate`). The parameter
enters with integer powers of `ρ` matching the two asymptotic rates `1` and `2` of the quartic. A
coordinate leaving `0` towards `q i = ±1`, at rate `1`, is `q i * x / √(1 + x²)` for
`x = e^{u i} ρ` (`TauCeti.intervalBaseOrbit_one_add_log`), so the early point moves off the first
piece linearly in `ρ`, with nonzero speed in every coordinate of the second block
(`TauCeti.hasDerivAt_quarticGluingEarly_zero`). A coordinate arriving at `q i = ±1`, at rate `2`,
is `q i / √(1 + y²)` for `y = e^{-u i} ρ` (`TauCeti.intervalBaseOrbit_one_sub_log`), so the late
point depends on `ρ` only through `ρ²` (`TauCeti.quarticGluingLate_neg`) and has derivative zero
in `ρ` at the break (`TauCeti.hasDerivAt_quarticGluingLate_zero`).

## Main definitions

* `TauCeti.quarticGluingEarly`, `TauCeti.quarticGluingLate`: the early and late points of the
  trajectory glued at a break `p → r → q` with gluing parameter `ρ`.

## Main results

* `TauCeti.quarticWellSumFlow_neg_log_quarticGluingEarly`, `TauCeti.quarticGluingEarly_zero`,
  `TauCeti.quarticGluingLate_zero`: the glued pair lies on one trajectory for `ρ > 0` and is the
  broken pair at `ρ = 0`.
* `TauCeti.quarticWellSumFlow_quarticGluingEarly`, `TauCeti.quarticWellSumFlow_quarticGluingLate`:
  the flow translates the time coordinates of the glued pair, across `ρ = 0`.
* `TauCeti.quarticGluingEarly_eq_and_quarticGluingLate_eq_iff`: the glued pair determines its
  parameters on the moving coordinates.
* `TauCeti.contDiff_quarticGluingEarly`, `TauCeti.contDiff_quarticGluingLate`: smoothness across
  the break.
* `TauCeti.hasDerivAt_quarticGluingEarly_zero`, `TauCeti.hasDerivAt_quarticGluingLate_zero`,
  `TauCeti.quarticGluingLate_neg`: the departing coordinates move linearly in `ρ`; the late point
  is even in `ρ` and has derivative zero at `ρ = 0`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2 (spaces of broken trajectories and their gluing).
* K. Wehrheim, *Smooth structures on Morse trajectory spaces, featuring finite ends and
  associative gluing*, Geom. Topol. Monogr. 18 (2012), [arXiv:1205.0713](https://arxiv.org/abs/1205.0713),
  §2 (gluing parameters `e^{-T}` near Euclidean critical points).
-/

public section

open Filter Set Topology

namespace TauCeti

variable {ι : Type*}

/-! ### Gluing at a break -/

/-- The **early point of the glued trajectory** at a break `p → r → q`, with gluing parameter
`ρ`. For `ρ > 0` it is the trajectory point from `p` to `q` whose coordinates moving between `p`
and `r` have time coordinates `u i`, and whose coordinates moving between `r` and `q` are delayed
to `u i + log ρ` (`TauCeti.quarticGluingEarly_of_pos`). On these delayed coordinates the formula
`q i * x / √(1 + x²)`, `x = e^{u i} ρ`, extends it smoothly to every `ρ`; at `ρ = 0` it is the
point of the first piece (`TauCeti.quarticGluingEarly_zero`). -/
noncomputable def quarticGluingEarly (p r q : ι → ℝ) (ρ : ℝ) (u : ι → ℝ) : ι → ℝ :=
  fun i ↦ if p i = q i then p i
    else if p i = r i then q i * (Real.exp (u i) * ρ * (√(1 + (Real.exp (u i) * ρ) ^ 2))⁻¹)
    else q i * intervalBaseOrbit 1 (u i)

/-- The **late point of the glued trajectory** at a break `p → r → q`, with gluing parameter
`ρ`. For `ρ > 0` it is the trajectory point from `p` to `q` whose coordinates moving between `r`
and `q` have time coordinates `u i`, and whose coordinates moving between `p` and `r` are advanced
to `u i - log ρ` (`TauCeti.quarticGluingLate_of_pos`). On these advanced coordinates the formula
`q i / √(1 + y²)`, `y = e^{-u i} ρ`, extends it smoothly to every `ρ`; at `ρ = 0` it is the point
of the second piece (`TauCeti.quarticGluingLate_zero`). -/
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

/-- With equal endpoints `p = q` the early point is the constant trajectory at `p`. -/
@[simp]
theorem quarticGluingEarly_same (p r : ι → ℝ) (ρ : ℝ) (u : ι → ℝ) :
    quarticGluingEarly p r p ρ u = p := by
  funext i
  simp

/-- With equal endpoints `p = q` the late point is the constant trajectory at `p`. -/
@[simp]
theorem quarticGluingLate_same (p r : ι → ℝ) (ρ : ℝ) (u : ι → ℝ) :
    quarticGluingLate p r p ρ u = p := by
  funext i
  simp

/-- With the break at the end, `r = q`, the early point is the trajectory point with time
coordinates `u` from `p` to `q`. -/
@[simp]
theorem quarticGluingEarly_same_right (p q : ι → ℝ) (ρ : ℝ) (u : ι → ℝ) :
    quarticGluingEarly p q q ρ u = quarticTrajectoryPoint p q u := by
  funext i
  by_cases h : p i = q i <;> simp [h]

/-- With the break at the start, `r = p`, the late point is the trajectory point with time
coordinates `u` from `p` to `q`. -/
@[simp]
theorem quarticGluingLate_same_left (p q : ι → ℝ) (ρ : ℝ) (u : ι → ℝ) :
    quarticGluingLate p p q ρ u = quarticTrajectoryPoint p q u := by
  funext i
  simp

/-- The early point lies in the cube `[-1, 1]^ι` when the endpoint `q` does. -/
theorem quarticGluingEarly_mem_Icc (p r : ι → ℝ) {q : ι → ℝ} (hq : q ∈ Icc (-1) 1) (ρ : ℝ)
    (u : ι → ℝ) : quarticGluingEarly p r q ρ u ∈ Icc (-1) 1 := by
  have ht := quarticTrajectoryPoint_mem_Icc p hq u
  rw [← pi_univ_Icc]
  refine fun i _ ↦ abs_le.1 ?_
  have hti : |quarticTrajectoryPoint p q u i| ≤ 1 := abs_le.2 ⟨ht.1 i, ht.2 i⟩
  rw [quarticTrajectoryPoint_apply] at hti
  rw [quarticGluingEarly_apply]
  split_ifs at hti ⊢
  · exact hti
  · rw [abs_mul, ← div_eq_mul_inv]
    exact (mul_le_of_le_one_left (abs_nonneg _) (abs_le.2 ⟨hq.1 i, hq.2 i⟩)).trans
      (Real.abs_div_sqrt_one_add_sq_le_one _)
  · exact hti

/-- The late point lies in the cube `[-1, 1]^ι` when the endpoint `q` does. -/
theorem quarticGluingLate_mem_Icc (p r : ι → ℝ) {q : ι → ℝ} (hq : q ∈ Icc (-1) 1) (ρ : ℝ)
    (u : ι → ℝ) : quarticGluingLate p r q ρ u ∈ Icc (-1) 1 := by
  have ht := quarticTrajectoryPoint_mem_Icc p hq u
  rw [← pi_univ_Icc]
  refine fun i _ ↦ abs_le.1 ?_
  have hti : |quarticTrajectoryPoint p q u i| ≤ 1 := abs_le.2 ⟨ht.1 i, ht.2 i⟩
  rw [quarticTrajectoryPoint_apply] at hti
  rw [quarticGluingLate_apply]
  split_ifs at hti ⊢
  · exact hti
  · exact hti
  · rw [abs_mul, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_of_le_one_left (by positivity) (abs_le.2 ⟨hq.1 i, hq.2 i⟩)).trans
      (inv_le_one_of_one_le₀ (Real.one_le_sqrt_one_add_sq _))

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

/-- The flow of the quartic translates all time coordinates of the early point at once, for every
gluing parameter `ρ`, including the break `ρ = 0`. -/
theorem quarticWellSumFlow_quarticGluingEarly {p r q : ι → ℝ}
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (s ρ : ℝ) (u : ι → ℝ) :
    quarticWellSumFlow s (quarticGluingEarly p r q ρ u) =
      quarticGluingEarly p r q ρ fun i ↦ s + u i := by
  funext i
  simp only [quarticWellSumFlow_apply, quarticGluingEarly_apply]
  split_ifs with hpq
  · rw [hpq]
    rcases hq i with h | h | h <;> simp [h]
  · rw [Real.exp_add, mul_assoc (Real.exp s)]
    rcases hq i with h | h | h <;>
      simp [h, intervalBaseFlow_neg, intervalBaseFlow_one_mul_inv_sqrt_one_add_sq]
  · exact intervalBaseFlow_mul_intervalBaseOrbit 1 s (hq i) (u i)

/-- The flow of the quartic translates all time coordinates of the late point at once, for every
gluing parameter `ρ`, including the break `ρ = 0`. -/
theorem quarticWellSumFlow_quarticGluingLate {p r q : ι → ℝ}
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (s ρ : ℝ) (u : ι → ℝ) :
    quarticWellSumFlow s (quarticGluingLate p r q ρ u) =
      quarticGluingLate p r q ρ fun i ↦ s + u i := by
  funext i
  simp only [quarticWellSumFlow_apply, quarticGluingLate_apply]
  split_ifs with hpq
  · rw [hpq]
    rcases hq i with h | h | h <;> simp [h]
  · exact intervalBaseFlow_mul_intervalBaseOrbit 1 s (hq i) (u i)
  · rw [neg_add, Real.exp_add, mul_assoc (Real.exp (-s))]
    rcases hq i with h | h | h <;>
      simp [h, intervalBaseFlow_neg, intervalBaseFlow_one_inv_sqrt_one_add_sq]

/-- **The glued pair lies on one trajectory.** For `ρ > 0` the flow for time `-log ρ` carries the
early point to the late point. -/
theorem quarticWellSumFlow_neg_log_quarticGluingEarly {p r q : ι → ℝ}
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) {ρ : ℝ} (hρ : 0 < ρ) (u : ι → ℝ) :
    quarticWellSumFlow (-Real.log ρ) (quarticGluingEarly p r q ρ u) =
      quarticGluingLate p r q ρ u := by
  rw [quarticGluingEarly_of_pos p r q hρ, quarticWellSumFlow_quarticTrajectoryPoint hq,
    quarticGluingLate_of_pos p r q hρ, quarticTrajectoryPoint_eq_quarticTrajectoryPoint_iff]
  intro i _ _
  split_ifs <;> ring

/-- For `ρ > 0` the flow for time `log ρ` carries the late point back to the early point. -/
theorem quarticWellSumFlow_log_quarticGluingLate {p r q : ι → ℝ}
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) {ρ : ℝ} (hρ : 0 < ρ) (u : ι → ℝ) :
    quarticWellSumFlow (Real.log ρ) (quarticGluingLate p r q ρ u) =
      quarticGluingEarly p r q ρ u := by
  rw [quarticGluingLate_of_pos p r q hρ, quarticWellSumFlow_quarticTrajectoryPoint hq,
    quarticGluingEarly_of_pos p r q hρ, quarticTrajectoryPoint_eq_quarticTrajectoryPoint_iff]
  intro i _ _
  split_ifs <;> ring

/-- The coordinates moving along a glued trajectory start at `0`. -/
private theorem eq_zero_of_ne_of_break {p r q : ι → ℝ} (hpr : ∀ i, p i ≠ r i → p i = 0)
    (hrq : ∀ i, r i ≠ q i → r i = 0) (i : ι) (hi : p i ≠ q i) : p i = 0 := by
  by_cases h : p i = r i
  · exact h.trans (hrq i (h ▸ hi))
  · exact hpr i h

/-- For `ρ > 0` the glued trajectory runs from `p` to `q`, seen from the early point. -/
theorem tendsto_quarticWellSumFlow_quarticGluingEarly {p r q : ι → ℝ}
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (hpr : ∀ i, p i ≠ r i → p i = 0)
    (hrq : ∀ i, r i ≠ q i → r i = 0) {ρ : ℝ} (hρ : 0 < ρ) (u : ι → ℝ) :
    Tendsto (fun s ↦ quarticWellSumFlow s (quarticGluingEarly p r q ρ u)) atBot (𝓝 p) ∧
      Tendsto (fun s ↦ quarticWellSumFlow s (quarticGluingEarly p r q ρ u)) atTop (𝓝 q) := by
  rw [quarticGluingEarly_of_pos p r q hρ]
  exact tendsto_quarticWellSumFlow_quarticTrajectoryPoint hq (eq_zero_of_ne_of_break hpr hrq) _

/-- For `ρ > 0` the glued trajectory runs from `p` to `q`, seen from the late point. -/
theorem tendsto_quarticWellSumFlow_quarticGluingLate {p r q : ι → ℝ}
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (hpr : ∀ i, p i ≠ r i → p i = 0)
    (hrq : ∀ i, r i ≠ q i → r i = 0) {ρ : ℝ} (hρ : 0 < ρ) (u : ι → ℝ) :
    Tendsto (fun s ↦ quarticWellSumFlow s (quarticGluingLate p r q ρ u)) atBot (𝓝 p) ∧
      Tendsto (fun s ↦ quarticWellSumFlow s (quarticGluingLate p r q ρ u)) atTop (𝓝 q) := by
  rw [quarticGluingLate_of_pos p r q hρ]
  exact tendsto_quarticWellSumFlow_quarticTrajectoryPoint hq (eq_zero_of_ne_of_break hpr hrq) _

/-- **The broken end, early side.** At `ρ = 0` the early point is the point with time coordinates
`u` on the first piece, from `p` to `r`. -/
theorem quarticGluingEarly_zero {p r q : ι → ℝ} (hpr : ∀ i, p i ≠ r i → p i = 0)
    (hrq : ∀ i, r i ≠ q i → r i = 0) (u : ι → ℝ) :
    quarticGluingEarly p r q 0 u = quarticTrajectoryPoint p r u := by
  funext i
  simp only [quarticGluingEarly_apply, quarticTrajectoryPoint_apply]
  by_cases hpr' : p i = r i
  · have := hrq i
    split_ifs <;> simp_all
  · have h0 := hpr i hpr'
    have hrq' : r i = q i := by_contra fun h ↦ hpr' (h0.trans (hrq i h).symm)
    rw [hrq'] at hpr' ⊢
    simp [hpr']

/-- **The broken end, late side.** At `ρ = 0` the late point is the point with time coordinates
`u` on the second piece, from `r` to `q`. -/
theorem quarticGluingLate_zero {p r q : ι → ℝ} (hpr : ∀ i, p i ≠ r i → p i = 0)
    (hrq : ∀ i, r i ≠ q i → r i = 0) (u : ι → ℝ) :
    quarticGluingLate p r q 0 u = quarticTrajectoryPoint r q u := by
  funext i
  simp only [quarticGluingLate_apply, quarticTrajectoryPoint_apply]
  by_cases hpr' : p i = r i
  · split_ifs <;> simp_all
  · have h0 := hpr i hpr'
    have hrq' : r i = q i := by_contra fun h ↦ hpr' (h0.trans (hrq i h).symm)
    rw [hrq'] at hpr' ⊢
    simp [hpr']

/-- The late point depends on the gluing parameter only through `ρ²`: the arriving coordinates
approach `±1` at rate `2`. -/
@[simp]
theorem quarticGluingLate_neg (p r q : ι → ℝ) (ρ : ℝ) (u : ι → ℝ) :
    quarticGluingLate p r q (-ρ) u = quarticGluingLate p r q ρ u := by
  funext i
  simp only [quarticGluingLate_apply, mul_neg, neg_sq]

/-! ### Recovering the gluing parameter and the time coordinates -/

/-- On a coordinate moving between `p` and `r` towards `q i = ±1`, the time coordinate is
recovered from the early point. -/
theorem intervalBaseTimeCoordinate_abs_quarticGluingEarly {p r q : ι → ℝ} {i : ι}
    (hpq : p i ≠ q i) (hpr : p i ≠ r i) (hq : q i = -1 ∨ q i = 1) (ρ : ℝ) (u : ι → ℝ) :
    intervalBaseTimeCoordinate |quarticGluingEarly p r q ρ u i| = u i := by
  rw [← intervalBaseTimeCoordinate_abs_quarticTrajectoryPoint hpq hq u]
  simp [hpq, hpr]

/-- On a coordinate moving between `r` and `q` towards `q i = ±1`, the time coordinate is
recovered from the late point. -/
theorem intervalBaseTimeCoordinate_abs_quarticGluingLate {p r q : ι → ℝ} {i : ι}
    (hpq : p i ≠ q i) (hpr : p i = r i) (hq : q i = -1 ∨ q i = 1) (ρ : ℝ) (u : ι → ℝ) :
    intervalBaseTimeCoordinate |quarticGluingLate p r q ρ u i| = u i := by
  rw [← intervalBaseTimeCoordinate_abs_quarticTrajectoryPoint hpq hq u]
  simp [hpr]

/-- On a coordinate `i` moving between `r` and `q` towards `q i = ±1`, the gluing parameter is
recovered from the early point `y` and the time coordinate as `e^{-u i} q i y i / √(1 - y i²)`. -/
theorem exp_neg_mul_mul_quarticGluingEarly_div_sqrt_one_sub_sq {p r q : ι → ℝ} {i : ι}
    (hpq : p i ≠ q i) (hpr : p i = r i) (hq : q i = -1 ∨ q i = 1) (ρ : ℝ) (u : ι → ℝ) :
    Real.exp (-u i) * (q i * quarticGluingEarly p r q ρ u i /
      √(1 - quarticGluingEarly p r q ρ u i ^ 2)) = ρ := by
  rw [quarticGluingEarly_apply, ite_eq_right hpq, ite_eq_left hpr]
  rcases hq with h | h <;> simp only [h, neg_mul, one_mul, neg_neg, neg_sq,
    Real.mul_inv_sqrt_one_add_sq_div_sqrt_one_sub_sq] <;>
    simp [← mul_assoc, ← Real.exp_add]

/-- **The glued pair determines its parameters.** For gluing parameters `ρ₁, ρ₂ ≥ 0`, the glued
pairs agree exactly when the time coordinates agree on every coordinate that moves, and the
gluing parameters agree as soon as some coordinate moves. -/
theorem quarticGluingEarly_eq_and_quarticGluingLate_eq_iff {p r q : ι → ℝ} {ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) {u₁ u₂ : ι → ℝ} :
    quarticGluingEarly p r q ρ₁ u₁ = quarticGluingEarly p r q ρ₂ u₂ ∧
        quarticGluingLate p r q ρ₁ u₁ = quarticGluingLate p r q ρ₂ u₂ ↔
      ∀ i, p i ≠ q i → q i ≠ 0 → u₁ i = u₂ i ∧ ρ₁ = ρ₂ := by
  simp only [funext_iff, ← forall_and]
  refine forall_congr' fun i ↦ ?_
  by_cases hpq : p i = q i
  · simp [hpq]
  by_cases hq0 : q i = 0
  · simp [hq0]
  simp only [quarticGluingEarly_apply, quarticGluingLate_apply, ite_eq_right hpq]
  simp only [ne_eq, hpq, hq0, not_false_eq_true, forall_const]
  refine ⟨fun h ↦ ?_, fun ⟨h₁, h₂⟩ ↦ by simp [h₁, h₂]⟩
  by_cases hpr : p i = r i
  · simp only [hpr, ↓reduceIte, mul_right_inj' hq0,
      (intervalBaseOrbit_injective one_ne_zero).eq_iff] at h
    obtain ⟨h₁, h₂⟩ := h
    have h₃ := congrArg (fun y ↦ y / √(1 - y ^ 2)) h₁
    simp only [Real.mul_inv_sqrt_one_add_sq_div_sqrt_one_sub_sq, h₂] at h₃
    exact ⟨h₂, mul_left_cancel₀ (Real.exp_pos _).ne' h₃⟩
  · simp only [hpr, ↓reduceIte, mul_right_inj' hq0] at h
    rw [(intervalBaseOrbit_injective one_ne_zero).eq_iff, inv_inj,
      Real.sqrt_inj (by positivity) (by positivity), add_right_inj] at h
    obtain ⟨h₁, h₂⟩ := h
    rw [h₁, sq_eq_sq₀ (by positivity) (by positivity)] at h₂
    exact ⟨h₁, mul_left_cancel₀ (Real.exp_pos _).ne' h₂⟩

/-! ### Smoothness across the break -/

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
  · exact contDiff_const.mul (hx.mul hx.inv_sqrt_one_add_sq)
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
  · exact contDiff_const.mul ((ContDiff.exp hu.neg).mul hρ).inv_sqrt_one_add_sq

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

/-- The early point depends continuously on the gluing parameter and the time coordinates
jointly, including at the break `ρ = 0`. -/
theorem continuous_quarticGluingEarly (p r q : ι → ℝ) :
    Continuous fun x : ℝ × (ι → ℝ) ↦ quarticGluingEarly p r q x.1 x.2 :=
  continuous_pi fun i ↦
    (contDiff_quarticGluingEarly_apply (n := 0) (u := fun y _ ↦ y.2) p r q i contDiff_fst
      contDiff_snd).continuous.comp
        (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))

/-- The late point depends continuously on the gluing parameter and the time coordinates
jointly, including at the break `ρ = 0`. -/
theorem continuous_quarticGluingLate (p r q : ι → ℝ) :
    Continuous fun x : ℝ × (ι → ℝ) ↦ quarticGluingLate p r q x.1 x.2 :=
  continuous_pi fun i ↦
    (contDiff_quarticGluingLate_apply (n := 0) (u := fun y _ ↦ y.2) p r q i contDiff_fst
      contDiff_snd).continuous.comp
        (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))

/-- **Convergence to the broken trajectory, early side.** As the gluing parameter tends to `0`,
the early point tends to the point with time coordinates `u` on the first piece. -/
theorem tendsto_quarticGluingEarly_nhds_zero {p r q : ι → ℝ} (hpr : ∀ i, p i ≠ r i → p i = 0)
    (hrq : ∀ i, r i ≠ q i → r i = 0) (u : ι → ℝ) :
    Tendsto (fun ρ ↦ quarticGluingEarly p r q ρ u) (𝓝 0) (𝓝 (quarticTrajectoryPoint p r u)) := by
  rw [← quarticGluingEarly_zero hpr hrq u]
  exact ((continuous_quarticGluingEarly p r q).comp
    (continuous_id.prodMk continuous_const)).tendsto 0

/-- **Convergence to the broken trajectory, late side.** As the gluing parameter tends to `0`,
the late point tends to the point with time coordinates `u` on the second piece. -/
theorem tendsto_quarticGluingLate_nhds_zero {p r q : ι → ℝ} (hpr : ∀ i, p i ≠ r i → p i = 0)
    (hrq : ∀ i, r i ≠ q i → r i = 0) (u : ι → ℝ) :
    Tendsto (fun ρ ↦ quarticGluingLate p r q ρ u) (𝓝 0) (𝓝 (quarticTrajectoryPoint r q u)) := by
  rw [← quarticGluingLate_zero hpr hrq u]
  exact ((continuous_quarticGluingLate p r q).comp
    (continuous_id.prodMk continuous_const)).tendsto 0

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
      (((contDiff_const.mul contDiff_id).inv_sqrt_one_add_sq (n := 1)).differentiable
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
