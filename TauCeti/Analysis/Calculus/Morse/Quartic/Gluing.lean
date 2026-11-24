/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Quartic.Trajectory
public import Mathlib.Data.Finset.Piecewise

/-!
# Gluing parameters of the trajectory spaces of the Euclidean quartic

Let `p` and `q` be critical points of the Euclidean quartic `∑ i, (yᵢ² - 1)² / 4`, with `q`
obtained from `p` by replacing some zero coordinates by `±1`. The time-shift chart
`TauCeti.quarticTrajectoryPoint p q τ` parametrizes the points of the cube `[-1, 1]^ι` on
trajectories from `p` to `q`: its moving coordinates `i` are `qᵢ q(τᵢ)` for the unit-rate trajectory
`q(s) = 1 / √(1 + e^{-2s})` (`TauCeti.intervalBaseOrbit 1`), and the flow adds the same time to all
time shifts (`TauCeti.Analysis.Calculus.Morse.Quartic.Trajectory`). This file shows that the
trajectories converge to broken trajectories smoothly in gluing parameters.

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

## Main definitions

* `TauCeti.quarticSliceGluing`: the slice evaluation of trajectories in gluing parameters.

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

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.2 (spaces of trajectories and their compactification by
  broken trajectories) and §3 (the comparison with cellular homology, which this quartic on the cube
  models).
* K. Wehrheim, *Smooth structures on Morse trajectory spaces, featuring finite ends and associative
  gluing*, Geometry & Topology Monographs 18 (2012), arXiv:1205.0713, §1 and §2 (gluing parameters
  `e^{-T}` and smoothness of evaluation maps up to the broken ends).
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
