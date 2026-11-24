/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Quartic.Trajectory
public import Mathlib.Data.Finset.Piecewise
import TauCeti.Analysis.Real.Sqrt
import TauCeti.Analysis.SpecialFunctions.Sqrt
import TauCeti.Order.Interval.Set.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Gluing parameters of the trajectory spaces of the Euclidean quartic

Let `p` and `q` be critical points of the Euclidean quartic `∑ i, (yᵢ² - 1)² / 4`, with `q`
obtained from `p` by replacing some zero coordinates by `±1`. The time-shift chart
`TauCeti.quarticTrajectoryPoint p q τ` parametrizes the points of the cube `[-1, 1]^ι` on
trajectories from `p` to `q`: its moving coordinates `i` are `qᵢ q(τᵢ)` for the unit-rate trajectory
`q(s) = 1 / √(1 + e^{-2s})` (`TauCeti.intervalBaseOrbit 1`), and the flow adds the same time to all
time shifts (`TauCeti.Analysis.Calculus.Morse.Quartic.Trajectory`). This file shows that the
trajectories converge to broken trajectories smoothly in gluing parameters.

### Slice evaluation

A broken trajectory appears when the time separations `τᵢ - τⱼ` of moving coordinates become
infinite. In the gluing parameter `ρ = e^{-T}` of a time separation `T`, the unit-rate trajectory
is smooth up to `ρ = 0` at both of its ends:

* near the maximum `0`, `q(a + log ρ) = ρ / √(ρ² + e^{-2a})`
  (`TauCeti.intervalBaseSourceGluing`), which leaves `0` to first order in `ρ`, matching the
  rate `1` of the flow at `0`;
* near the minimum `1`, `q(a - log ρ) = 1 / √(1 + e^{-2a} ρ²)`
  (`TauCeti.intervalBaseTargetGluing`), an even function of `ρ` reaching `1` to exactly second
  order, matching the rate `2` of the flow at `±1`.

Evaluate the trajectories on the slice `{|yⱼ| = c}` of a moving coordinate `j`, at a level
`0 < c < 1`. A set `A` of coordinates selects the target profile for its moving coordinates
`i ≠ j` and the source profile for the others. The slice point of the trajectory with time shifts
`τ` is `TauCeti.quarticSliceGluing p q j c A ρ`, at the gluing parameters `ρᵢ = e^{-(τᵢ - τⱼ)}`
for `i ∈ A` and `ρᵢ = e^{τᵢ - τⱼ}` otherwise
(`TauCeti.quarticWellSumFlow_quarticTrajectoryPoint_eq_quarticSliceGluing`). For a moving `i ≠ j`,
a parameter `0 < ρᵢ < 1` places `i` ahead of `j` if `i ∈ A` and behind `j` otherwise, `ρᵢ = 1` is a
tie, and `ρᵢ > 1` reverses the order. Positive parameters are exactly the trajectory points
(`TauCeti.quarticSliceGluing_eq_quarticTrajectoryPoint`), and they are recovered from the slice
point (`TauCeti.quarticSliceGluing_eq_quarticSliceGluing_iff`). The evaluation extends smoothly to
all real parameters (`TauCeti.contDiff_quarticSliceGluing`); only its nonnegative parameters
describe trajectories.

Zero parameters describe broken trajectories. A coordinate `i ∈ A` with `ρᵢ = 0` has already moved
to `qᵢ`, and one `i ∉ A` with `ρᵢ = 0` has not left `pᵢ`
(`TauCeti.quarticSliceGluing_eq_quarticTrajectoryPoint_of_eqOn_zero`). For `j ∉ A`, at `ρ = 0` the
slice evaluation is a point on the trajectory from the critical point `A.piecewise q p` to
`(insert j A).piecewise q p` (`TauCeti.quarticSliceGluing_zero`,
`TauCeti.tendsto_quarticWellSumFlow_quarticSliceGluing_zero_atBot_atTop`). When the gluing
parameters of trajectory points converge, their slice points converge to the slice evaluation at
the limit (`TauCeti.tendsto_quarticWellSumFlow_quarticTrajectoryPoint_nhds_quarticSliceGluing`), in
particular to a point of the broken trajectory when the time separations diverge
(`TauCeti.tendsto_quarticWellSumFlow_quarticTrajectoryPoint_nhds_quarticSliceGluing_zero`).

### Gluing at a break

The file also glues two trajectories at a break with the gluing parameter `ρ = e^{-T}`, where `T`
is the time separating the two pieces. The glued points take time coordinates `u : ι → ℝ` on all
coordinates, so that one family `u` restricts to the time shifts of both pieces and of the glued
trajectory.

Let `p → r → q` be a broken trajectory: the coordinates with `p i ≠ r i` move first, from `0` to
`r i = q i`, and those with `r i ≠ q i` move afterwards, from `0` to `q i`. Running the first block
a time `T = -log ρ` ahead of the second gives a trajectory from `p` to `q`. It is recorded at two
points: an early point, near the first piece, with the second block delayed by `T`
(`TauCeti.quarticGluingEarly`), and a late point, near the second piece, with the first block
advanced by `T` (`TauCeti.quarticGluingLate`). For `ρ > 0` these are two points of the same
trajectory, the late one the image of the early one under the flow for time `T`
(`TauCeti.quarticWellSumFlow_neg_log_quarticGluingEarly`), which runs from `p` to `q`
(`TauCeti.quarticGluingEarly_mem_quarticConnectingSet`,
`TauCeti.quarticGluingLate_mem_quarticConnectingSet`), and at `ρ = 0` they are the two pieces
of the broken trajectory (`TauCeti.quarticGluingEarly_zero`, `TauCeti.quarticGluingLate_zero`).
For every `ρ`, including `ρ = 0`, the flow translates the time coordinates of both points
(`TauCeti.quarticWellSumFlow_quarticGluingEarly`, `TauCeti.quarticWellSumFlow_quarticGluingLate`).
For `ρ ≥ 0` the glued pair determines the time coordinates of the moving coordinates with
`q i ≠ 0`, and the gluing parameter as soon as there is one
(`TauCeti.quarticGluingEarly_eq_and_quarticGluingLate_eq_iff`), and both are recovered
from it explicitly: the time coordinates
(`TauCeti.intervalBaseTimeCoordinate_abs_quarticGluingEarly`,
`TauCeti.intervalBaseTimeCoordinate_abs_quarticGluingLate`), the gluing parameter from the early
point on a coordinate moving on the second piece
(`TauCeti.exp_neg_mul_mul_quarticGluingEarly_div_sqrt_one_sub_sq`), and its absolute value from the
late point on a coordinate moving on the first piece
(`TauCeti.exp_mul_sqrt_one_sub_quarticGluingLate_sq_div_abs`).

Both maps are smooth in the gluing parameter and the time coordinates jointly, across `ρ = 0`
(`TauCeti.contDiff_quarticGluingEarly`, `TauCeti.contDiff_quarticGluingLate`). The parameter
enters with integer powers of `ρ` matching the two asymptotic rates `1` and `2` of the quartic. A
coordinate leaving `0` towards `q i = ±1`, at rate `1`, is `q i * x / √(1 + x²)` for
`x = e^{u i} ρ` (`TauCeti.intervalBaseOrbit_eq_exp_mul_inv_sqrt`), so the early point moves off
the first piece linearly in `ρ`, with nonzero speed in every coordinate of the second block
(`TauCeti.hasDerivAt_quarticGluingEarly_zero`). A coordinate arriving at `q i = ±1`, at rate `2`,
is `q i / √(1 + y²)` for `y = e^{-u i} ρ`
(`TauCeti.intervalBaseOrbit_eq_inv_sqrt_one_add_exp_sq`), so the late point depends on `ρ` only
through `ρ²` (`TauCeti.quarticGluingLate_neg`) and has derivative zero in `ρ` at the break
(`TauCeti.hasDerivAt_quarticGluingLate_zero`).

## Main definitions

* `TauCeti.quarticSliceGluing`: the slice evaluation of trajectories in gluing parameters.
* `TauCeti.quarticGluingEarly`, `TauCeti.quarticGluingLate`: the early and late points of the
  trajectory glued at a break `p → r → q` with gluing parameter `ρ`.

## Main results

* `TauCeti.contDiff_quarticSliceGluing`,
  `TauCeti.quarticWellSumFlow_quarticTrajectoryPoint_eq_quarticSliceGluing`,
  `TauCeti.quarticSliceGluing_eq_quarticSliceGluing_iff`: smooth slice evaluation, injective on
  positive parameters.
* `TauCeti.quarticSliceGluing_eq_quarticTrajectoryPoint_of_eqOn_zero`,
  `TauCeti.quarticSliceGluing_zero`,
  `TauCeti.tendsto_quarticWellSumFlow_quarticSliceGluing_zero_atBot_atTop`,
  `TauCeti.tendsto_quarticWellSumFlow_quarticTrajectoryPoint_nhds_quarticSliceGluing`: the slice
  evaluation up to the broken trajectories.
* `TauCeti.quarticWellSumFlow_neg_log_quarticGluingEarly`,
  `TauCeti.quarticGluingEarly_mem_quarticConnectingSet`, `TauCeti.quarticGluingEarly_zero`,
  `TauCeti.quarticGluingLate_zero`: the glued pair lies on one trajectory from `p` to `q` for
  `ρ > 0` and is the broken pair at `ρ = 0`.
* `TauCeti.quarticWellSumFlow_quarticGluingEarly`, `TauCeti.quarticWellSumFlow_quarticGluingLate`:
  the flow translates the time coordinates of the glued pair, across `ρ = 0`.
* `TauCeti.quarticGluingEarly_eq_and_quarticGluingLate_eq_iff`: the glued pair determines its
  parameters on the moving coordinates with `q i ≠ 0`.
* `TauCeti.contDiff_quarticGluingEarly`, `TauCeti.contDiff_quarticGluingLate`: smoothness across
  the break.
* `TauCeti.hasDerivAt_quarticGluingEarly_zero`, `TauCeti.hasDerivAt_quarticGluingLate_zero`,
  `TauCeti.quarticGluingLate_neg`: the departing coordinates move linearly in `ρ`; the late point
  is even in `ρ` and has derivative zero at `ρ = 0`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2 (spaces of trajectories, their compactification by broken
  trajectories in §2.2, and their gluing) and §3 (the comparison with cellular homology, which this
  quartic on the cube models).
* K. Wehrheim, *Smooth structures on Morse trajectory spaces, featuring finite ends and associative
  gluing*, Geometry & Topology Monographs 18 (2012), arXiv:1205.0713, §1 and §2 (gluing parameters
  `e^{-T}`, smoothness of evaluation maps up to the broken ends, and gluing near Euclidean critical
  points).
-/

public section

noncomputable section

open Real Set Filter Topology

namespace TauCeti

variable {ι : Type*} {p q : ι → ℝ} [DecidableEq ι]

/-- The **slice evaluation in gluing parameters**. For a moving coordinate `j`, a level
`0 < c < 1` and a set `A` selecting the target profile, this is the point on the slice
`{|yⱼ| = c}` whose moving coordinates `i ≠ j` are `qᵢ` times the target profile
`TauCeti.intervalBaseTargetGluing` at `U(c)` and `ρᵢ` if `i ∈ A`, and times the source profile
`TauCeti.intervalBaseSourceGluing` otherwise. For positive `ρ` it is the point of the trajectory
from `p` to `q` whose coordinates `i` are separated from `j` by the times `-log ρᵢ` if `i ∈ A` and
`log ρᵢ` otherwise (`TauCeti.quarticSliceGluing_eq_quarticTrajectoryPoint`). It is smooth in `ρ`
(`TauCeti.contDiff_quarticSliceGluing`) and extends to the broken trajectories at `ρᵢ = 0`
(`TauCeti.quarticSliceGluing_eq_quarticTrajectoryPoint_of_eqOn_zero`). The parameters at `j` and
at the fixed coordinates are not used (`TauCeti.quarticSliceGluing_congr`); they keep the parameter
space the whole of `ℝ^ι`. -/
def quarticSliceGluing (p q : ι → ℝ) (j : ι) (c : ℝ) (A : Finset ι) (ρ : ι → ℝ) : ι → ℝ :=
  fun i ↦ if p i = q i then p i else if i = j then q i * c else
    q i * if i ∈ A then intervalBaseTargetGluing (intervalBaseTimeCoordinate c) (ρ i)
      else intervalBaseSourceGluing (intervalBaseTimeCoordinate c) (ρ i)

theorem quarticSliceGluing_apply (p q : ι → ℝ) (j : ι) (c : ℝ) (A : Finset ι) (ρ : ι → ℝ)
    (i : ι) :
    quarticSliceGluing p q j c A ρ i = if p i = q i then p i else if i = j then q i * c else
      q i * if i ∈ A then intervalBaseTargetGluing (intervalBaseTimeCoordinate c) (ρ i)
        else intervalBaseSourceGluing (intervalBaseTimeCoordinate c) (ρ i) :=
  (rfl)

@[simp]
theorem quarticSliceGluing_apply_of_eq (j : ι) (c : ℝ) (A : Finset ι) (ρ : ι → ℝ) {i : ι}
    (h : p i = q i) : quarticSliceGluing p q j c A ρ i = p i := by
  simp [quarticSliceGluing_apply, h]

@[simp]
theorem quarticSliceGluing_apply_self {j : ι} (c : ℝ) (A : Finset ι) (ρ : ι → ℝ)
    (h : p j ≠ q j) : quarticSliceGluing p q j c A ρ j = q j * c := by
  simp [quarticSliceGluing_apply, h]

@[simp]
theorem quarticSliceGluing_apply_of_mem {j : ι} (c : ℝ) {A : Finset ι} (ρ : ι → ℝ) {i : ι}
    (h : p i ≠ q i) (hij : i ≠ j) (hA : i ∈ A) :
    quarticSliceGluing p q j c A ρ i =
      q i * intervalBaseTargetGluing (intervalBaseTimeCoordinate c) (ρ i) := by
  simp [quarticSliceGluing_apply, h, hij, hA]

@[simp]
theorem quarticSliceGluing_apply_of_notMem {j : ι} (c : ℝ) {A : Finset ι} (ρ : ι → ℝ) {i : ι}
    (h : p i ≠ q i) (hij : i ≠ j) (hA : i ∉ A) :
    quarticSliceGluing p q j c A ρ i =
      q i * intervalBaseSourceGluing (intervalBaseTimeCoordinate c) (ρ i) := by
  simp [quarticSliceGluing_apply, h, hij, hA]

/-- The slice evaluation reads only the gluing parameters of the moving coordinates other
than `j`. -/
theorem quarticSliceGluing_congr (p q : ι → ℝ) (j : ι) (c : ℝ) (A : Finset ι) {ρ ρ' : ι → ℝ}
    (h : ∀ i, p i ≠ q i → i ≠ j → ρ i = ρ' i) :
    quarticSliceGluing p q j c A ρ = quarticSliceGluing p q j c A ρ' := by
  funext i
  by_cases hpq : p i = q i
  · simp [hpq]
  by_cases hij : i = j
  · simp [quarticSliceGluing_apply, hij]
  · simp [quarticSliceGluing_apply, h i hpq hij]

/-- Whether `j` itself lies in `A` does not change the slice evaluation. -/
@[simp]
theorem quarticSliceGluing_erase (p q : ι → ℝ) (j : ι) (c : ℝ) (A : Finset ι) :
    quarticSliceGluing p q j c (A.erase j) = quarticSliceGluing p q j c A := by
  funext ρ i
  by_cases hij : i = j <;> simp [quarticSliceGluing_apply, hij]

/-- Coordinate `i` of the slice evaluation reads only the gluing parameter `ρ i`: it agrees with
the slice evaluation at the constant parameter family `ρ i`. -/
theorem quarticSliceGluing_apply_eq_apply_const (p q : ι → ℝ) (j : ι) (c : ℝ) (A : Finset ι)
    (ρ : ι → ℝ) (i : ι) :
    quarticSliceGluing p q j c A ρ i = quarticSliceGluing p q j c A (fun _ ↦ ρ i) i := by
  simp only [quarticSliceGluing_apply]

/-- A coordinate of the slice evaluation is a smooth function of the gluing parameter of that
coordinate alone. -/
theorem contDiff_quarticSliceGluing_const_apply (p q : ι → ℝ) (j : ι) (c : ℝ) (A : Finset ι)
    (i : ι) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun t : ℝ ↦ quarticSliceGluing p q j c A (fun _ ↦ t) i := by
  simp only [quarticSliceGluing_apply]
  split_ifs
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_const.mul (contDiff_intervalBaseTargetGluing _)
  · exact contDiff_const.mul (contDiff_intervalBaseSourceGluing _)

/-- The slice evaluation is continuous in the gluing parameters, for any set of coordinates. -/
theorem continuous_quarticSliceGluing (p q : ι → ℝ) (j : ι) (c : ℝ) (A : Finset ι) :
    Continuous (quarticSliceGluing p q j c A) :=
  continuous_pi fun i ↦ by
    rw [funext (quarticSliceGluing_apply_eq_apply_const p q j c A · i)]
    exact (contDiff_quarticSliceGluing_const_apply p q j c A i (n := 0)).continuous.comp
      (continuous_apply i)

/-- **The slice evaluation is smooth in the gluing parameters**, including at the broken
trajectories `ρᵢ = 0`. -/
theorem contDiff_quarticSliceGluing [Fintype ι] (p q : ι → ℝ) (j : ι) (c : ℝ) (A : Finset ι)
    {n : WithTop ℕ∞} : ContDiff ℝ n (quarticSliceGluing p q j c A) :=
  contDiff_pi.2 fun i ↦ by
    rw [funext (quarticSliceGluing_apply_eq_apply_const p q j c A · i)]
    exact (contDiff_quarticSliceGluing_const_apply p q j c A i).comp (contDiff_apply _ _ i)

/-- **Positive gluing parameters give trajectory points.** At gluing parameters which are positive
on the moving coordinates other than `j`, the slice evaluation is the point with time shift `U(c)`
at `j`, `U(c) - log ρᵢ` at the coordinates `i ∈ A`, and `U(c) + log ρᵢ` at the others. -/
theorem quarticSliceGluing_eq_quarticTrajectoryPoint (j : ι) {c : ℝ} (hc : c ∈ Ioo 0 1)
    (A : Finset ι) {ρ : ι → ℝ} (hρ : ∀ i : {i // p i ≠ q i}, (i : ι) ≠ j → 0 < ρ i) :
    quarticSliceGluing p q j c A ρ = quarticTrajectoryPoint p q fun i ↦
      if (i : ι) = j then intervalBaseTimeCoordinate c else if (i : ι) ∈ A then
        intervalBaseTimeCoordinate c - log (ρ i) else intervalBaseTimeCoordinate c + log (ρ i) := by
  funext i
  by_cases h : p i = q i
  · simp [quarticTrajectoryPoint_apply_of_eq _ h, h]
  rw [quarticTrajectoryPoint_apply_of_ne _ h]
  by_cases hij : i = j
  · subst hij
    simp [h, intervalBaseOrbit_one_intervalBaseTimeCoordinate hc]
  by_cases hA : i ∈ A
  · simp [h, hij, hA, intervalBaseOrbit_one_sub_log _ (hρ ⟨i, h⟩ hij)]
  · simp [h, hij, hA, intervalBaseOrbit_one_add_log _ (hρ ⟨i, h⟩ hij)]

/-- **The time shifts of the slice evaluation.** At gluing parameters which are positive on the
moving coordinates other than `j`, the slice evaluation has time shift `U(c)` at `j`,
`U(c) - log ρᵢ` at the coordinates `i ∈ A`, and `U(c) + log ρᵢ` at the others. -/
theorem quarticTimeShift_quarticSliceGluing (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0) (j : ι) {c : ℝ} (hc : c ∈ Ioo 0 1) (A : Finset ι)
    {ρ : ι → ℝ} (hρ : ∀ i : {i // p i ≠ q i}, (i : ι) ≠ j → 0 < ρ i) :
    quarticTimeShift p q (quarticSliceGluing p q j c A ρ) = fun i : {i // p i ≠ q i} ↦
      if (i : ι) = j then intervalBaseTimeCoordinate c else if (i : ι) ∈ A then
        intervalBaseTimeCoordinate c - log (ρ i) else intervalBaseTimeCoordinate c + log (ρ i) := by
  rw [quarticSliceGluing_eq_quarticTrajectoryPoint j hc A hρ,
    quarticTimeShift_quarticTrajectoryPoint hq hpq]

/-- **Positive gluing parameters are determined by the slice point.** Two families of gluing
parameters which are positive on the moving coordinates other than `j` give the same slice point
exactly when they agree on these coordinates. -/
theorem quarticSliceGluing_eq_quarticSliceGluing_iff (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0) {j : ι} {c : ℝ} (hc : c ∈ Ioo 0 1) (A : Finset ι)
    {ρ ρ' : ι → ℝ} (hρ : ∀ i : {i // p i ≠ q i}, (i : ι) ≠ j → 0 < ρ i)
    (hρ' : ∀ i : {i // p i ≠ q i}, (i : ι) ≠ j → 0 < ρ' i) :
    quarticSliceGluing p q j c A ρ = quarticSliceGluing p q j c A ρ' ↔
      ∀ i, p i ≠ q i → i ≠ j → ρ i = ρ' i := by
  refine ⟨fun h i hi hij ↦ ?_, quarticSliceGluing_congr p q j c A⟩
  have hτ := congrFun (congrArg (quarticTimeShift p q) h) ⟨i, hi⟩
  rw [quarticTimeShift_quarticSliceGluing hq hpq j hc A hρ,
    quarticTimeShift_quarticSliceGluing hq hpq j hc A hρ'] at hτ
  refine log_injOn_pos (hρ ⟨i, hi⟩ hij) (hρ' ⟨i, hi⟩ hij) ?_
  by_cases hA : i ∈ A <;> simp only [hij, hA, ↓reduceIte] at hτ <;> linarith

/-- **Faces of zero gluing parameters.** Let the gluing parameters vanish on a set `Z` of
coordinates not containing `j`. Freezing the coordinates of `Z` in `A` at `q` and the other
coordinates of `Z` at `p` does not change the slice evaluation: it is the slice evaluation for the
endpoints obtained from `p` and `q` in this way, whose moving coordinates avoid `Z`. -/
theorem quarticSliceGluing_eq_quarticSliceGluing_of_eqOn_zero {j : ι} {c : ℝ} {A : Finset ι}
    {ρ : ι → ℝ} {Z : Set ι} [DecidablePred (· ∈ Z)] (hjZ : j ∉ Z) (hZ : EqOn ρ 0 Z)
    (hpq : ∀ i ∈ Z, i ∉ A → p i ≠ q i → p i = 0) :
    quarticSliceGluing p q j c A ρ =
      quarticSliceGluing (fun i ↦ if i ∈ Z ∧ i ∈ A then q i else p i)
        (fun i ↦ if i ∈ Z ∧ i ∉ A then p i else q i) j c A ρ := by
  funext i
  by_cases hiZ : i ∈ Z
  · have hij : i ≠ j := ne_of_mem_of_not_mem hiZ hjZ
    by_cases hA : i ∈ A
    · simp [quarticSliceGluing_apply, hiZ, hA, hij, hZ hiZ]
    · simpa [quarticSliceGluing_apply, hiZ, hA, hij, hZ hiZ, eq_comm] using hpq i hiZ hA
  · simp [quarticSliceGluing_apply, hiZ]

/-- **Zero gluing parameters give points of broken trajectories.** Let the gluing parameters vanish
on a set `Z` of coordinates not containing `j`, and be positive on the other moving coordinates
`i ≠ j`. Then the slice evaluation is the point with time shift `U(c)` at `j`, `U(c) - log ρᵢ` at
the coordinates `i ∈ A` and `U(c) + log ρᵢ` at the others, on the trajectories between the
endpoints obtained from `p` and `q` by freezing the coordinates of `Z` in `A` at `q` (they have
already moved) and the other coordinates of `Z` at `p` (they have not yet moved). -/
theorem quarticSliceGluing_eq_quarticTrajectoryPoint_of_eqOn_zero {j : ι} {c : ℝ}
    (hc : c ∈ Ioo 0 1) {A : Finset ι} {ρ : ι → ℝ} {Z : Set ι} [DecidablePred (· ∈ Z)]
    (hjZ : j ∉ Z) (hZ : EqOn ρ 0 Z) (hpq : ∀ i ∈ Z, i ∉ A → p i ≠ q i → p i = 0)
    (hρ : ∀ i : {i // p i ≠ q i}, (i : ι) ≠ j → (i : ι) ∉ Z → 0 < ρ i) :
    quarticSliceGluing p q j c A ρ =
      quarticTrajectoryPoint (fun i ↦ if i ∈ Z ∧ i ∈ A then q i else p i)
        (fun i ↦ if i ∈ Z ∧ i ∉ A then p i else q i) fun i ↦
        if (i : ι) = j then intervalBaseTimeCoordinate c else if (i : ι) ∈ A then
          intervalBaseTimeCoordinate c - log (ρ i)
        else intervalBaseTimeCoordinate c + log (ρ i) := by
  rw [quarticSliceGluing_eq_quarticSliceGluing_of_eqOn_zero hjZ hZ hpq]
  refine quarticSliceGluing_eq_quarticTrajectoryPoint j hc A fun i hij ↦ ?_
  -- A moving coordinate of the frozen endpoints lies outside `Z`, so it moves for `p` and `q`.
  have hiZ : (i : ι) ∉ Z := fun hiZ ↦
    i.property (by by_cases hA : (i : ι) ∈ A <;> simp [hiZ, hA])
  exact hρ ⟨i, by simpa [hiZ] using i.property⟩ hij hiZ

/-- **The slice point of a trajectory in gluing parameters.** Flowing the point with time shifts
`τ` for time `U(c) - τⱼ`, for a moving coordinate `j`, gives the slice evaluation with gluing
parameters `e^{-(τᵢ - τⱼ)}` for the moving coordinates `i ∈ A` and `e^{τᵢ - τⱼ}` for the other
moving coordinates; the parameters at the fixed coordinates do not matter. This is where the
trajectory reaches the slice `{|yⱼ| = c}`. -/
theorem quarticWellSumFlow_quarticTrajectoryPoint_eq_quarticSliceGluing
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (j : {i // p i ≠ q i}) {c : ℝ} (hc : c ∈ Ioo 0 1)
    (A : Finset ι) (τ : {i // p i ≠ q i} → ℝ) :
    quarticWellSumFlow (intervalBaseTimeCoordinate c - τ j) (quarticTrajectoryPoint p q τ) =
      quarticSliceGluing p q j c A fun i ↦ if h : p i = q i then 0 else
        if i ∈ A then exp (-(τ ⟨i, h⟩ - τ j)) else exp (τ ⟨i, h⟩ - τ j) := by
  rw [quarticWellSumFlow_quarticTrajectoryPoint hq,
    quarticSliceGluing_eq_quarticTrajectoryPoint (j : ι) hc A fun i _ ↦ by
      rw [dite_eq_right i.property]
      split_ifs <;> exact exp_pos _]
  -- Both time functions are `τᵢ + U(c) - τⱼ`.
  congr 1
  funext i
  rw [dite_eq_right i.property]
  split_ifs with hij hA
  · rw [Subtype.ext hij, sub_add_cancel]
  · rw [log_exp]
    ring
  · rw [log_exp]
    ring

/-- **The broken trajectory at zero gluing parameters.** For `j ∉ A`, at `ρ = 0` the slice
evaluation is the point with all time shifts `U(c)` on the trajectories from `A.piecewise q p` to
`(insert j A).piecewise q p`. These differ at most in the coordinate `j`; when `pⱼ ≠ qⱼ`, the
coordinates in `A` have already moved in the first and `j` has moved too in the second. When
`pⱼ = qⱼ` the two coincide and the evaluation is `A.piecewise q p` itself. -/
theorem quarticSliceGluing_zero {j : ι} {c : ℝ} (hc : c ∈ Ioo 0 1) {A : Finset ι} (hjA : j ∉ A)
    (hpq : ∀ i, i ∉ A → i ≠ j → p i ≠ q i → p i = 0) :
    quarticSliceGluing p q j c A 0 = quarticTrajectoryPoint (A.piecewise q p)
      ((insert j A).piecewise q p) fun _ ↦ intervalBaseTimeCoordinate c := by
  have h₁ : (fun i ↦ if i ∈ {i | i ≠ j} ∧ i ∈ A then q i else p i) = A.piecewise q p := by
    funext i
    by_cases hA : i ∈ A
    · simp [Finset.piecewise, hA, ne_of_mem_of_not_mem hA hjA]
    · simp [Finset.piecewise, hA]
  have h₂ : (fun i ↦ if i ∈ {i | i ≠ j} ∧ i ∉ A then p i else q i) =
      (insert j A).piecewise q p := by
    funext i
    by_cases hij : i = j <;> by_cases hA : i ∈ A <;> simp [Finset.piecewise, hij, hA]
  -- The time shifts depend on the endpoints through their subtype, so substitute both at once.
  have key : ∀ P Q : ι → ℝ, P = A.piecewise q p → Q = (insert j A).piecewise q p →
      (quarticTrajectoryPoint P Q fun _ ↦ intervalBaseTimeCoordinate c) =
        quarticTrajectoryPoint (A.piecewise q p) ((insert j A).piecewise q p) fun _ ↦
          intervalBaseTimeCoordinate c := by
    rintro P Q rfl rfl
    rfl
  rw [quarticSliceGluing_eq_quarticTrajectoryPoint_of_eqOn_zero (Z := {i | i ≠ j}) hc (by simp)
    (fun _ _ ↦ rfl) (fun i hij hA ↦ hpq i hA hij) (fun i hij hiZ ↦ absurd hij (by simpa using hiZ))]
  -- At `ρ = 0` every time shift is `U(c)`, as `log 0 = 0`.
  simp only [Pi.zero_apply, log_zero, sub_zero, add_zero, ite_self]
  exact key _ _ h₁ h₂

/-- **The slice evaluation at zero gluing parameters lies on the broken trajectory.** For `j ∉ A`,
at `ρ = 0` the slice evaluation lies on a trajectory from the critical point `A.piecewise q p` to
`(insert j A).piecewise q p`. When `j` is a moving coordinate, `pⱼ ≠ qⱼ`, this is the piece through
the slice `{|yⱼ| = c}` of the broken trajectory from `p` to `q` on which the coordinates in `A` move
before `j`, and the other moving coordinates after it. When `pⱼ = qⱼ` the two critical points
coincide and the trajectory is stationary. -/
theorem tendsto_quarticWellSumFlow_quarticSliceGluing_zero_atBot_atTop
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) {j : ι} {c : ℝ} (hc : c ∈ Ioo 0 1) {A : Finset ι}
    (hjA : j ∉ A) (hpq : ∀ i, i ∉ A → p i ≠ q i → p i = 0) :
    Tendsto (fun s ↦ quarticWellSumFlow s (quarticSliceGluing p q j c A 0)) atBot
        (𝓝 (A.piecewise q p)) ∧
      Tendsto (fun s ↦ quarticWellSumFlow s (quarticSliceGluing p q j c A 0)) atTop
        (𝓝 ((insert j A).piecewise q p)) := by
  rw [quarticSliceGluing_zero hc hjA fun i hiA _ ↦ hpq i hiA]
  refine (mem_quarticConnectingSet.1
    (quarticTrajectoryPoint_mem_quarticConnectingSet (fun i ↦ ?_) (fun i hi ↦ ?_) _)).2
  · -- Off `insert j A` the endpoint is `p`, whose coordinates there are those of `q` or `0`.
    by_cases hi : i ∈ insert j A
    · rw [Finset.piecewise_eq_of_mem _ _ _ hi]
      exact hq i
    rw [Finset.piecewise_eq_of_notMem _ _ _ hi]
    by_cases h : p i = q i
    · exact h ▸ hq i
    · exact .inr (.inl (hpq i (fun hA ↦ hi (Finset.mem_insert_of_mem hA)) h))
  · -- Only `j` changes between the two critical points, and it has not moved in the first.
    by_cases hij : i = j
    · subst hij
      rw [A.piecewise_eq_of_notMem _ _ hjA] at hi ⊢
      rw [Finset.piecewise_insert_self] at hi
      exact hpq i hjA hi
    · exact absurd (Finset.piecewise_insert_of_ne _ _ _ hij).symm hi

/-- **Convergence of slice points.** Let points on the trajectories from `p` to `q` have gluing
parameters `e^{-(τᵢ - τⱼ)}` for the moving coordinates `i ∈ A` and `e^{τᵢ - τⱼ}` for the other
moving coordinates `i ≠ j` converging to `ρᵢ`. Then their flows for time `U(c) - τⱼ`, their slice
points on `{|yⱼ| = c}`, converge to the slice evaluation at `ρ`. -/
theorem tendsto_quarticWellSumFlow_quarticTrajectoryPoint_nhds_quarticSliceGluing
    {α : Type*} {l : Filter α} (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    {j : {i // p i ≠ q i}} {c : ℝ} (hc : c ∈ Ioo 0 1) {A : Finset ι}
    {τ : α → {i // p i ≠ q i} → ℝ} {ρ : ι → ℝ}
    (hA : ∀ i : {i // p i ≠ q i}, (i : ι) ∈ A → i ≠ j →
      Tendsto (fun n ↦ exp (-(τ n i - τ n j))) l (𝓝 (ρ i)))
    (hA' : ∀ i : {i // p i ≠ q i}, (i : ι) ∉ A → i ≠ j →
      Tendsto (fun n ↦ exp (τ n i - τ n j)) l (𝓝 (ρ i))) :
    Tendsto (fun n ↦ quarticWellSumFlow (intervalBaseTimeCoordinate c - τ n j)
      (quarticTrajectoryPoint p q (τ n))) l (𝓝 (quarticSliceGluing p q j c A ρ)) := by
  simp only [quarticWellSumFlow_quarticTrajectoryPoint_eq_quarticSliceGluing hq j hc A]
  -- Replace the parameters which the slice evaluation ignores by those of `ρ`; the resulting
  -- parameters converge to `ρ`.
  have hσ : Tendsto (fun n i ↦ if h : p i = q i then ρ i else if i = j then ρ i else
      if i ∈ A then exp (-(τ n ⟨i, h⟩ - τ n j)) else exp (τ n ⟨i, h⟩ - τ n j)) l (𝓝 ρ) := by
    refine tendsto_pi_nhds.2 fun i ↦ ?_
    by_cases h : p i = q i
    · simpa [h] using tendsto_const_nhds
    by_cases hij : i = j
    · simpa [h, hij] using tendsto_const_nhds
    have hij' : (⟨i, h⟩ : {i // p i ≠ q i}) ≠ j := fun e ↦ hij (congrArg Subtype.val e)
    by_cases hiA : i ∈ A
    · simpa [h, hij, hiA] using hA ⟨i, h⟩ hiA hij'
    · simpa [h, hij, hiA] using hA' ⟨i, h⟩ hiA hij'
  refine (((continuous_quarticSliceGluing p q j c A).tendsto ρ).comp hσ).congr fun n ↦
    quarticSliceGluing_congr p q j c A fun i h hij ↦ ?_
  simp [h, hij]

/-- **Convergence to the broken trajectory.** Let points on the trajectories from `p` to `q` have
time separations `τᵢ - τⱼ` tending to `+∞` for the moving coordinates `i ∈ A` and to `-∞` for the
other moving coordinates `i ≠ j`. Then their slice points on `{|yⱼ| = c}` converge to the slice
evaluation at zero gluing parameters. Since `j` itself is ignored
(`TauCeti.quarticSliceGluing_erase`), this is the slice evaluation for `A.erase j`, a point of the
broken trajectory (`TauCeti.tendsto_quarticWellSumFlow_quarticSliceGluing_zero_atBot_atTop`). -/
theorem tendsto_quarticWellSumFlow_quarticTrajectoryPoint_nhds_quarticSliceGluing_zero
    {α : Type*} {l : Filter α} (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    {j : {i // p i ≠ q i}} {c : ℝ} (hc : c ∈ Ioo 0 1) {A : Finset ι}
    {τ : α → {i // p i ≠ q i} → ℝ}
    (hA : ∀ i : {i // p i ≠ q i}, (i : ι) ∈ A → i ≠ j →
      Tendsto (fun n ↦ τ n i - τ n j) l atTop)
    (hA' : ∀ i : {i // p i ≠ q i}, (i : ι) ∉ A → i ≠ j →
      Tendsto (fun n ↦ τ n i - τ n j) l atBot) :
    Tendsto (fun n ↦ quarticWellSumFlow (intervalBaseTimeCoordinate c - τ n j)
      (quarticTrajectoryPoint p q (τ n))) l (𝓝 (quarticSliceGluing p q j c A 0)) :=
  tendsto_quarticWellSumFlow_quarticTrajectoryPoint_nhds_quarticSliceGluing hq hc
    (fun i hiA hij ↦ tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (hA i hiA hij)))
    (fun i hiA hij ↦ tendsto_exp_atBot.comp (hA' i hiA hij))

end TauCeti

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
    quarticGluingEarly p q q ρ u = quarticTrajectoryPoint p q fun j ↦ u j := by
  funext i
  by_cases h : p i = q i
  · simp [quarticTrajectoryPoint_apply_of_eq _ h, h]
  · simp [quarticTrajectoryPoint_apply_of_ne _ h, h]

/-- With the break at the start, `r = p`, the late point is the trajectory point with time
coordinates `u` from `p` to `q`. -/
@[simp]
theorem quarticGluingLate_same_left (p q : ι → ℝ) (ρ : ℝ) (u : ι → ℝ) :
    quarticGluingLate p p q ρ u = quarticTrajectoryPoint p q fun j ↦ u j := by
  funext i
  by_cases h : p i = q i
  · simp [quarticTrajectoryPoint_apply_of_eq _ h, h]
  · simp [quarticTrajectoryPoint_apply_of_ne _ h, h]

/-- Scaling a coordinate `a` of the cube by a factor `t` with `|t| ≤ 1` keeps it in `[-1, 1]`. -/
private theorem abs_mul_le_one_of_abs_le_one {a t : ℝ} (ha : |a| ≤ 1) (ht : |t| ≤ 1) :
    |a * t| ≤ 1 :=
  (abs_mul a t).trans_le ((mul_le_of_le_one_left (abs_nonneg t) ha).trans ht)

/-- The early point lies in the cube `[-1, 1]^ι` when the endpoint `q` does. -/
theorem quarticGluingEarly_mem_Icc (p r : ι → ℝ) {q : ι → ℝ} (hq : q ∈ Icc (-1) 1) (ρ : ℝ)
    (u : ι → ℝ) : quarticGluingEarly p r q ρ u ∈ Icc (-1) 1 :=
  mem_Icc_neg_iff_forall_abs_le.2 fun i ↦ by
    have hq' := mem_Icc_neg_iff_forall_abs_le.1 hq i
    have ho := intervalBaseOrbit_mem_Ioo 1 (u i)
    rw [quarticGluingEarly_apply]
    split_ifs with hpq
    · exact hpq ▸ hq'
    · refine abs_mul_le_one_of_abs_le_one hq' ?_
      have h := Real.abs_div_sqrt_sq_add_le_one zero_le_one (Real.exp (u i) * ρ)
      rwa [add_comm, div_eq_mul_inv] at h
    · exact abs_mul_le_one_of_abs_le_one hq' ((abs_of_pos ho.1).trans_le ho.2.le)

/-- The late point lies in the cube `[-1, 1]^ι` when the endpoint `q` does. -/
theorem quarticGluingLate_mem_Icc (p r : ι → ℝ) {q : ι → ℝ} (hq : q ∈ Icc (-1) 1) (ρ : ℝ)
    (u : ι → ℝ) : quarticGluingLate p r q ρ u ∈ Icc (-1) 1 :=
  mem_Icc_neg_iff_forall_abs_le.2 fun i ↦ by
    have hq' := mem_Icc_neg_iff_forall_abs_le.1 hq i
    have ho := intervalBaseOrbit_mem_Ioo 1 (u i)
    rw [quarticGluingLate_apply]
    split_ifs with hpq
    · exact hpq ▸ hq'
    · exact abs_mul_le_one_of_abs_le_one hq' ((abs_of_pos ho.1).trans_le ho.2.le)
    · refine abs_mul_le_one_of_abs_le_one hq' ?_
      rw [abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact inv_le_one_of_one_le₀ (Real.one_le_sqrt_one_add_sq _)

/-- For `ρ > 0` the early point is the trajectory point with the second block delayed by
`-log ρ`. -/
theorem quarticGluingEarly_of_pos (p r q : ι → ℝ) {ρ : ℝ} (hρ : 0 < ρ) (u : ι → ℝ) :
    quarticGluingEarly p r q ρ u =
      quarticTrajectoryPoint p q fun j ↦ if p j = r j then u j + Real.log ρ else u j := by
  funext i
  by_cases hpq : p i = q i
  · simp [quarticTrajectoryPoint_apply_of_eq _ hpq, hpq]
  · rw [quarticTrajectoryPoint_apply_of_ne _ hpq, quarticGluingEarly_apply, ite_eq_right hpq]
    dsimp only
    split_ifs
    · rw [← div_one (Real.log ρ), intervalBaseOrbit_add_log_div one_ne_zero hρ, one_mul]
    · rfl

/-- For `ρ > 0` the late point is the trajectory point with the first block advanced by
`-log ρ`. -/
theorem quarticGluingLate_of_pos (p r q : ι → ℝ) {ρ : ℝ} (hρ : 0 < ρ) (u : ι → ℝ) :
    quarticGluingLate p r q ρ u =
      quarticTrajectoryPoint p q fun j ↦ if p j = r j then u j else u j - Real.log ρ := by
  funext i
  by_cases hpq : p i = q i
  · simp [quarticTrajectoryPoint_apply_of_eq _ hpq, hpq]
  · rw [quarticTrajectoryPoint_apply_of_ne _ hpq, quarticGluingLate_apply, ite_eq_right hpq]
    dsimp only
    split_ifs
    · rfl
    · rw [← div_one (Real.log ρ), intervalBaseOrbit_sub_log_div one_ne_zero hρ, one_mul]

/-- The flow of the quartic translates all time coordinates of the early point at once, for every
gluing parameter `ρ`, including the break `ρ = 0`. -/
theorem quarticWellSumFlow_quarticGluingEarly {p r q : ι → ℝ}
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (s ρ : ℝ) (u : ι → ℝ) :
    quarticWellSumFlow s (quarticGluingEarly p r q ρ u) =
      quarticGluingEarly p r q ρ fun i ↦ s + u i := by
  funext i
  simp only [quarticWellSumFlow_apply, quarticGluingEarly_apply]
  split_ifs with hpq
  · simpa [hpq] using intervalBaseFlow_mul 1 s (hq i) 1
  · rw [Real.exp_add, mul_assoc (Real.exp s), intervalBaseFlow_mul 1 s (hq i),
      intervalBaseFlow_mul_inv_sqrt_one_add_sq, one_mul]
  · simp [intervalBaseFlow_mul 1 s (hq i)]

/-- The flow of the quartic translates all time coordinates of the late point at once, for every
gluing parameter `ρ`, including the break `ρ = 0`. -/
theorem quarticWellSumFlow_quarticGluingLate {p r q : ι → ℝ}
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (s ρ : ℝ) (u : ι → ℝ) :
    quarticWellSumFlow s (quarticGluingLate p r q ρ u) =
      quarticGluingLate p r q ρ fun i ↦ s + u i := by
  funext i
  simp only [quarticWellSumFlow_apply, quarticGluingLate_apply]
  split_ifs with hpq
  · simpa [hpq] using intervalBaseFlow_mul 1 s (hq i) 1
  · simp [intervalBaseFlow_mul 1 s (hq i)]
  · rw [intervalBaseFlow_mul 1 s (hq i), intervalBaseFlow_inv_sqrt_one_add_sq, one_mul, neg_add,
      Real.exp_add, mul_assoc (Real.exp (-s))]

/-- **The glued pair lies on one trajectory.** For `ρ > 0` the flow for time `-log ρ` carries the
early point to the late point. -/
theorem quarticWellSumFlow_neg_log_quarticGluingEarly {p r q : ι → ℝ}
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) {ρ : ℝ} (hρ : 0 < ρ) (u : ι → ℝ) :
    quarticWellSumFlow (-Real.log ρ) (quarticGluingEarly p r q ρ u) =
      quarticGluingLate p r q ρ u := by
  rw [quarticWellSumFlow_quarticGluingEarly hq, quarticGluingEarly_of_pos p r q hρ,
    quarticGluingLate_of_pos p r q hρ]
  congr 1
  funext j
  split_ifs <;> ring

/-- For `ρ > 0` the flow for time `log ρ` carries the late point back to the early point. -/
theorem quarticWellSumFlow_log_quarticGluingLate {p r q : ι → ℝ}
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) {ρ : ℝ} (hρ : 0 < ρ) (u : ι → ℝ) :
    quarticWellSumFlow (Real.log ρ) (quarticGluingLate p r q ρ u) =
      quarticGluingEarly p r q ρ u := by
  rw [quarticWellSumFlow_quarticGluingLate hq, quarticGluingLate_of_pos p r q hρ,
    quarticGluingEarly_of_pos p r q hρ]
  congr 1
  funext j
  split_ifs <;> ring

/-- For `ρ > 0` the early point lies on a trajectory from `p` to `q`. -/
theorem quarticGluingEarly_mem_quarticConnectingSet {p r q : ι → ℝ}
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (hpq : ∀ i, p i ≠ q i → p i = 0) {ρ : ℝ}
    (hρ : 0 < ρ) (u : ι → ℝ) : quarticGluingEarly p r q ρ u ∈ quarticConnectingSet p q := by
  rw [quarticGluingEarly_of_pos p r q hρ]
  exact quarticTrajectoryPoint_mem_quarticConnectingSet hq hpq _

/-- For `ρ > 0` the late point lies on a trajectory from `p` to `q`. -/
theorem quarticGluingLate_mem_quarticConnectingSet {p r q : ι → ℝ}
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (hpq : ∀ i, p i ≠ q i → p i = 0) {ρ : ℝ}
    (hρ : 0 < ρ) (u : ι → ℝ) : quarticGluingLate p r q ρ u ∈ quarticConnectingSet p q := by
  rw [quarticGluingLate_of_pos p r q hρ]
  exact quarticTrajectoryPoint_mem_quarticConnectingSet hq hpq _

/-- **The broken end, early side.** At `ρ = 0` the early point is the point with time coordinates
`u` on the first piece, from `p` to `r`, when the coordinates moving on the second piece start at
`0` and those moving on the first piece stay put on the second. -/
@[simp]
theorem quarticGluingEarly_zero {p r q : ι → ℝ} (hpr : ∀ i, p i ≠ r i → r i = q i)
    (hrq : ∀ i, r i ≠ q i → r i = 0) (u : ι → ℝ) :
    quarticGluingEarly p r q 0 u = quarticTrajectoryPoint p r fun j ↦ u j := by
  funext i
  by_cases hpr' : p i = r i
  · rw [quarticTrajectoryPoint_apply_of_eq _ hpr', quarticGluingEarly_apply]
    have := hrq i
    clear hpr hrq
    split_ifs <;> simp_all
  · rw [quarticTrajectoryPoint_apply_of_ne _ hpr', quarticGluingEarly_apply,
      ← hpr i hpr', ite_eq_right hpr', ite_eq_right hpr']

/-- **The broken end, late side.** At `ρ = 0` the late point is the point with time coordinates
`u` on the second piece, from `r` to `q`, when the coordinates moving on the first piece stay put on
the second. -/
@[simp]
theorem quarticGluingLate_zero {p r q : ι → ℝ} (hpr : ∀ i, p i ≠ r i → r i = q i) (u : ι → ℝ) :
    quarticGluingLate p r q 0 u = quarticTrajectoryPoint r q fun j ↦ u j := by
  funext i
  by_cases hpr' : p i = r i
  · by_cases hpq : p i = q i
    · rw [quarticGluingLate_apply, ite_eq_left hpq,
        quarticTrajectoryPoint_apply_of_eq _ (hpr'.symm.trans hpq), hpr']
    · rw [quarticGluingLate_apply, ite_eq_right hpq, ite_eq_left hpr',
        quarticTrajectoryPoint_apply_of_ne _ fun h ↦ hpq (hpr'.trans h)]
  · have hrq' := hpr i hpr'
    rw [quarticTrajectoryPoint_apply_of_eq _ hrq', quarticGluingLate_apply,
      ite_eq_right fun h ↦ hpr' (h.trans hrq'.symm), ite_eq_right hpr']
    simp [hrq']

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
  rw [quarticGluingEarly_apply, ite_eq_right hpq, ite_eq_right hpr,
    intervalBaseTimeCoordinate_abs_mul_intervalBaseOrbit hq, one_mul]

/-- On a coordinate moving between `r` and `q` towards `q i = ±1`, the time coordinate is
recovered from the late point. -/
theorem intervalBaseTimeCoordinate_abs_quarticGluingLate {p r q : ι → ℝ} {i : ι}
    (hpq : p i ≠ q i) (hpr : p i = r i) (hq : q i = -1 ∨ q i = 1) (ρ : ℝ) (u : ι → ℝ) :
    intervalBaseTimeCoordinate |quarticGluingLate p r q ρ u i| = u i := by
  rw [quarticGluingLate_apply, ite_eq_right hpq, ite_eq_left hpr,
    intervalBaseTimeCoordinate_abs_mul_intervalBaseOrbit hq, one_mul]

/-- On a coordinate `i` moving between `r` and `q` towards `q i = ±1`, the gluing parameter is
recovered from the early point `y` and the time coordinate as `e^{-u i} q i y i / √(1 - y i²)`. -/
theorem exp_neg_mul_mul_quarticGluingEarly_div_sqrt_one_sub_sq {p r q : ι → ℝ} {i : ι}
    (hpq : p i ≠ q i) (hpr : p i = r i) (hq : q i = -1 ∨ q i = 1) (ρ : ℝ) (u : ι → ℝ) :
    Real.exp (-u i) * (q i * quarticGluingEarly p r q ρ u i /
      √(1 - quarticGluingEarly p r q ρ u i ^ 2)) = ρ := by
  rw [quarticGluingEarly_apply, ite_eq_right hpq, ite_eq_left hpr]
  rcases hq with h | h <;> simp only [h, neg_one_mul, neg_neg, neg_sq, one_mul] <;>
    simp [Real.mul_inv_sqrt_one_add_sq_div_sqrt_one_sub_sq, Real.exp_neg]

/-- On a coordinate `i` moving between `p` and `r` towards `q i = ±1`, the absolute value of the
gluing parameter is recovered from the late point `y` and the time coordinate as
`e^{u i} √(1 - y i²) / |y i|`. -/
theorem exp_mul_sqrt_one_sub_quarticGluingLate_sq_div_abs {p r q : ι → ℝ} {i : ι}
    (hpq : p i ≠ q i) (hpr : p i ≠ r i) (hq : q i = -1 ∨ q i = 1) (ρ : ℝ) (u : ι → ℝ) :
    Real.exp (u i) * (√(1 - quarticGluingLate p r q ρ u i ^ 2) /
      |quarticGluingLate p r q ρ u i|) = |ρ| := by
  rw [quarticGluingLate_apply, ite_eq_right hpq, ite_eq_right hpr]
  rcases hq with h | h <;>
  · simp only [h, neg_one_mul, neg_sq, one_mul, abs_neg]
    rw [abs_of_pos (by positivity), Real.sqrt_one_sub_sq_div_inv_sqrt_one_add_sq]
    simp [abs_mul, Real.exp_neg]

/-- **The glued pair determines its parameters.** For gluing parameters `ρ₁, ρ₂ ≥ 0`, the glued
pairs agree exactly when the time coordinates agree on every moving coordinate with `q i ≠ 0`,
and the gluing parameters agree as soon as some coordinate moves towards a nonzero `q i`. On a
moving coordinate with `q i = 0` both points vanish whatever the parameters. -/
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
  · simp only [hpr, ↓reduceIte, mul_right_inj' hq0,
      (intervalBaseOrbit_injective one_ne_zero).eq_iff] at h
    obtain ⟨h₁, h₂⟩ := h
    have h₃ := congrArg (fun y ↦ √(1 - y ^ 2) / y) h₂
    simp only [Real.sqrt_one_sub_sq_div_inv_sqrt_one_add_sq, abs_mul, Real.abs_exp,
      abs_of_nonneg hρ₁, abs_of_nonneg hρ₂, h₁] at h₃
    exact ⟨h₁, mul_left_cancel₀ (Real.exp_pos _).ne' h₃⟩

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

/-- Coordinate `i` of the early point depends on the time coordinates only through `u i`. The
continuity theorems below use this to apply the smoothness of one coordinate on `ℝ × ℝ`, since
`ι → ℝ` carries no normed space structure without `Fintype ι`. -/
private theorem quarticGluingEarly_apply_const (p r q : ι → ℝ) (ρ : ℝ) (u : ι → ℝ) (i : ι) :
    quarticGluingEarly p r q ρ (fun _ ↦ u i) i = quarticGluingEarly p r q ρ u i := by
  simp only [quarticGluingEarly_apply]

/-- Coordinate `i` of the late point depends on the time coordinates only through `u i`. -/
private theorem quarticGluingLate_apply_const (p r q : ι → ℝ) (ρ : ℝ) (u : ι → ℝ) (i : ι) :
    quarticGluingLate p r q ρ (fun _ ↦ u i) i = quarticGluingLate p r q ρ u i := by
  simp only [quarticGluingLate_apply]

/-- The early point depends continuously on the gluing parameter and the time coordinates
jointly, including at the break `ρ = 0`. -/
theorem continuous_quarticGluingEarly (p r q : ι → ℝ) :
    Continuous fun x : ℝ × (ι → ℝ) ↦ quarticGluingEarly p r q x.1 x.2 :=
  continuous_pi fun i ↦
    ((contDiff_quarticGluingEarly_apply (n := 0) p r q i (u := fun y : ℝ × ℝ ↦ fun _ ↦ y.2)
      contDiff_fst contDiff_snd).continuous.comp
        (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))).congr
      fun x ↦ quarticGluingEarly_apply_const p r q x.1 x.2 i

/-- The late point depends continuously on the gluing parameter and the time coordinates
jointly, including at the break `ρ = 0`. -/
theorem continuous_quarticGluingLate (p r q : ι → ℝ) :
    Continuous fun x : ℝ × (ι → ℝ) ↦ quarticGluingLate p r q x.1 x.2 :=
  continuous_pi fun i ↦
    ((contDiff_quarticGluingLate_apply (n := 0) p r q i (u := fun y : ℝ × ℝ ↦ fun _ ↦ y.2)
      contDiff_fst contDiff_snd).continuous.comp
        (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))).congr
      fun x ↦ quarticGluingLate_apply_const p r q x.1 x.2 i

/-- **Convergence to the broken trajectory, early side.** As the gluing parameter tends to `0`,
the early point tends to the point with time coordinates `u` on the first piece. -/
theorem tendsto_quarticGluingEarly_nhds_zero {p r q : ι → ℝ} (hpr : ∀ i, p i ≠ r i → r i = q i)
    (hrq : ∀ i, r i ≠ q i → r i = 0) (u : ι → ℝ) :
    Tendsto (fun ρ ↦ quarticGluingEarly p r q ρ u) (𝓝 0)
      (𝓝 (quarticTrajectoryPoint p r fun j ↦ u j)) := by
  rw [← quarticGluingEarly_zero hpr hrq u]
  exact ((continuous_quarticGluingEarly p r q).comp
    (continuous_id.prodMk continuous_const)).tendsto 0

/-- **Convergence to the broken trajectory, late side.** As the gluing parameter tends to `0`,
the late point tends to the point with time coordinates `u` on the second piece. -/
theorem tendsto_quarticGluingLate_nhds_zero {p r q : ι → ℝ} (hpr : ∀ i, p i ≠ r i → r i = q i)
    (u : ι → ℝ) :
    Tendsto (fun ρ ↦ quarticGluingLate p r q ρ u) (𝓝 0)
      (𝓝 (quarticTrajectoryPoint r q fun j ↦ u j)) := by
  rw [← quarticGluingLate_zero hpr u]
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
