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
  (`TauCeti.intervalBaseTargetGluing`), an even function of `ρ` with vanishing derivative at `0`,
  matching the rate `2` of the flow at `±1`.

Evaluate the trajectories on the slice `{|yⱼ| = c}` of a moving coordinate `j`, at a level
`0 < c < 1`. Let `A` be the set of coordinates ahead of `j`. The slice point of the trajectory with
time shifts `τ` is `TauCeti.quarticSliceGluing p q j c A ρ`, at the gluing parameters
`ρᵢ = e^{-(τᵢ - τⱼ)}` for `i ∈ A` and `ρᵢ = e^{τᵢ - τⱼ}` otherwise
(`TauCeti.quarticWellSumFlow_quarticTrajectoryPoint_eq_quarticSliceGluing`). This evaluation is
smooth in `ρ` on all of `ℝ^ι` (`TauCeti.contDiff_quarticSliceGluing`). At `ρ = 0` it is the slice
point of the broken trajectory whose coordinates in `A` have already moved and whose other moving
coordinates have not: a point on the trajectory from the critical point `A.piecewise q p` to
`(insert j A).piecewise q p`
(`TauCeti.tendsto_quarticWellSumFlow_quarticSliceGluing_zero_atBot_atTop`). When the time
separations tend to infinity with these signs, the slice points converge to it
(`TauCeti.tendsto_quarticWellSumFlow_quarticTrajectoryPoint_nhds_quarticSliceGluing_zero`).

## Main definitions

* `TauCeti.quarticSliceGluing`: the slice evaluation of trajectories in gluing parameters.

## Main results

* `TauCeti.contDiff_quarticSliceGluing`,
  `TauCeti.quarticWellSumFlow_quarticTrajectoryPoint_eq_quarticSliceGluing`,
  `TauCeti.tendsto_quarticWellSumFlow_quarticSliceGluing_zero_atBot_atTop`,
  `TauCeti.tendsto_quarticWellSumFlow_quarticTrajectoryPoint_nhds_quarticSliceGluing_zero`: smooth
  slice evaluation up to the broken trajectories.

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
`0 < c < 1` and a set `A` of coordinates ahead of `j`, this is the point on the slice `{|yⱼ| = c}`
of the trajectory from `p` to `q` whose other moving coordinates `i` are separated from `j` by the
times `-log ρᵢ` if `i ∈ A` and `log ρᵢ` otherwise
(`TauCeti.quarticWellSumFlow_quarticTrajectoryPoint_eq_quarticSliceGluing`). Its coordinates are
the gluing profiles `TauCeti.intervalBaseTargetGluing` and `TauCeti.intervalBaseSourceGluing` at
`U(c)`, so it is smooth in `ρ` (`TauCeti.contDiff_quarticSliceGluing`) and extends to the broken
trajectories at `ρᵢ = 0`. -/
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
  rw [quarticSliceGluing_apply, ite_eq_left h]

@[simp]
theorem quarticSliceGluing_apply_self {j : ι} (c : ℝ) (A : Finset ι) (ρ : ι → ℝ)
    (h : p j ≠ q j) : quarticSliceGluing p q j c A ρ j = q j * c := by
  rw [quarticSliceGluing_apply, ite_eq_right h, ite_eq_left rfl]

@[simp]
theorem quarticSliceGluing_apply_of_mem {j : ι} (c : ℝ) {A : Finset ι} (ρ : ι → ℝ) {i : ι}
    (h : p i ≠ q i) (hij : i ≠ j) (hA : i ∈ A) :
    quarticSliceGluing p q j c A ρ i =
      q i * intervalBaseTargetGluing (intervalBaseTimeCoordinate c) (ρ i) := by
  rw [quarticSliceGluing_apply, ite_eq_right h, ite_eq_right hij, ite_eq_left hA]

@[simp]
theorem quarticSliceGluing_apply_of_notMem {j : ι} (c : ℝ) {A : Finset ι} (ρ : ι → ℝ) {i : ι}
    (h : p i ≠ q i) (hij : i ≠ j) (hA : i ∉ A) :
    quarticSliceGluing p q j c A ρ i =
      q i * intervalBaseSourceGluing (intervalBaseTimeCoordinate c) (ρ i) := by
  rw [quarticSliceGluing_apply, ite_eq_right h, ite_eq_right hij, ite_eq_right hA]

/-- **The slice evaluation is smooth in the gluing parameters**, including at the broken
trajectories `ρᵢ = 0`. -/
theorem contDiff_quarticSliceGluing [Fintype ι] (p q : ι → ℝ) (j : ι) (c : ℝ) (A : Finset ι)
    {n : WithTop ℕ∞} : ContDiff ℝ n (quarticSliceGluing p q j c A) := by
  refine contDiff_pi.2 fun i ↦ ?_
  simp only [quarticSliceGluing_apply]
  split_ifs
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_const.mul ((contDiff_intervalBaseTargetGluing _).comp (contDiff_apply _ _ i))
  · exact contDiff_const.mul ((contDiff_intervalBaseSourceGluing _).comp (contDiff_apply _ _ i))

/-- **Positive gluing parameters give trajectory points.** At gluing parameters which are positive
on the moving coordinates other than `j`, the slice evaluation is the point with time shift `U(c)`
at `j`, `U(c) - log ρᵢ` at the coordinates `i ∈ A` ahead of `j`, and `U(c) + log ρᵢ` at the
others. -/
theorem quarticSliceGluing_eq_quarticTrajectoryPoint (j : ι) {c : ℝ} (hc : c ∈ Ioo 0 1)
    (A : Finset ι) {ρ : ι → ℝ} (hρ : ∀ i : {i // p i ≠ q i}, (i : ι) ≠ j → 0 < ρ i) :
    quarticSliceGluing p q j c A ρ = quarticTrajectoryPoint p q fun i ↦
      if (i : ι) = j then intervalBaseTimeCoordinate c else if (i : ι) ∈ A then
        intervalBaseTimeCoordinate c - log (ρ i) else intervalBaseTimeCoordinate c + log (ρ i) := by
  funext i
  by_cases h : p i = q i
  · rw [quarticTrajectoryPoint_apply_of_eq _ h, quarticSliceGluing_apply_of_eq _ _ _ _ h]
  rw [quarticTrajectoryPoint_apply_of_ne _ h]
  by_cases hij : i = j
  · subst hij
    rw [quarticSliceGluing_apply_self _ _ _ h, ite_eq_left rfl,
      intervalBaseOrbit_one_intervalBaseTimeCoordinate hc]
  by_cases hA : i ∈ A
  · rw [quarticSliceGluing_apply_of_mem _ _ h hij hA, ite_eq_right hij, ite_eq_left hA,
      intervalBaseOrbit_one_sub_log _ (hρ ⟨i, h⟩ hij)]
  · rw [quarticSliceGluing_apply_of_notMem _ _ h hij hA, ite_eq_right hij, ite_eq_right hA,
      intervalBaseOrbit_one_add_log _ (hρ ⟨i, h⟩ hij)]

/-- **The slice point of a trajectory in gluing parameters.** Flowing the point with time shifts
`τ` for time `U(c) - τⱼ`, for a moving coordinate `j`, gives the slice evaluation with gluing
parameters `e^{-(τᵢ - τⱼ)}` for the moving coordinates `i ∈ A` and `e^{τᵢ - τⱼ}` for the other
moving coordinates; the parameters at the fixed coordinates do not matter. This is where the
trajectory reaches the slice `{|yⱼ| = c}`, and `A` plays the role of the coordinates ahead
of `j`. -/
theorem quarticWellSumFlow_quarticTrajectoryPoint_eq_quarticSliceGluing
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (hpq : ∀ i, p i ≠ q i → p i = 0)
    (j : {i // p i ≠ q i}) {c : ℝ} (hc : c ∈ Ioo 0 1) (A : Finset ι) (τ : {i // p i ≠ q i} → ℝ) :
    quarticWellSumFlow (intervalBaseTimeCoordinate c - τ j) (quarticTrajectoryPoint p q τ) =
      quarticSliceGluing p q j c A fun i ↦ if h : p i = q i then 0 else
        if i ∈ A then exp (-(τ ⟨i, h⟩ - τ j)) else exp (τ ⟨i, h⟩ - τ j) := by
  rw [quarticWellSumFlow_quarticTrajectoryPoint hq hpq,
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

/-- **The broken trajectory at zero gluing parameters.** At `ρ = 0` the slice evaluation is the
point with all time shifts `U(c)` on the trajectories from `A.piecewise q p` to
`(insert j A).piecewise q p`. These differ at most in the coordinate `j`; when `pⱼ ≠ qⱼ`, the
coordinates in `A` have already moved in the first and `j` has moved too in the second. When
`pⱼ = qⱼ` the two coincide and the evaluation is `A.piecewise q p` itself. -/
theorem quarticSliceGluing_zero (hpq : ∀ i, p i ≠ q i → p i = 0) {j : ι} {c : ℝ}
    (hc : c ∈ Ioo 0 1) {A : Finset ι} (hjA : j ∉ A) :
    quarticSliceGluing p q j c A 0 = quarticTrajectoryPoint (A.piecewise q p)
      ((insert j A).piecewise q p) fun _ ↦ intervalBaseTimeCoordinate c := by
  funext i
  by_cases hij : i = j
  · subst hij
    have hj : (insert i A).piecewise q p i = q i := Finset.piecewise_insert_self _ _ _
    have hj' : A.piecewise q p i = p i := A.piecewise_eq_of_notMem _ _ hjA
    by_cases h : p i = q i
    · rw [quarticSliceGluing_apply_of_eq _ _ _ _ h,
        quarticTrajectoryPoint_apply_of_eq _ (by rw [hj, hj', h]), hj']
    · rw [quarticSliceGluing_apply_self _ _ _ h,
        quarticTrajectoryPoint_apply_of_ne _ (by rwa [hj, hj']), hj,
        intervalBaseOrbit_one_intervalBaseTimeCoordinate hc]
  rw [quarticTrajectoryPoint_apply_of_eq _ (Finset.piecewise_insert_of_ne _ _ _ hij).symm]
  by_cases hA : i ∈ A
  · rw [A.piecewise_eq_of_mem _ _ hA]
    by_cases h : p i = q i
    · rw [quarticSliceGluing_apply_of_eq _ _ _ _ h, h]
    · rw [quarticSliceGluing_apply_of_mem _ _ h hij hA, Pi.zero_apply,
        intervalBaseTargetGluing_zero, mul_one]
  · rw [A.piecewise_eq_of_notMem _ _ hA]
    by_cases h : p i = q i
    · rw [quarticSliceGluing_apply_of_eq _ _ _ _ h]
    · rw [quarticSliceGluing_apply_of_notMem _ _ h hij hA, Pi.zero_apply,
        intervalBaseSourceGluing_zero, mul_zero, hpq i h]

/-- **The slice evaluation at zero gluing parameters lies on the broken trajectory.** At `ρ = 0`
the slice evaluation lies on a trajectory from the critical point `A.piecewise q p` to
`(insert j A).piecewise q p`. When `j` is a moving coordinate, `pⱼ ≠ qⱼ`, this is the piece through
the slice `{|yⱼ| = c}` of the broken trajectory from `p` to `q` on which the coordinates in `A` move
before `j`, and the other moving coordinates after it. When `pⱼ = qⱼ` the two critical points
coincide and the trajectory is stationary. -/
theorem tendsto_quarticWellSumFlow_quarticSliceGluing_zero_atBot_atTop
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (hpq : ∀ i, p i ≠ q i → p i = 0) {j : ι} {c : ℝ}
    (hc : c ∈ Ioo 0 1) {A : Finset ι} (hjA : j ∉ A) :
    Tendsto (fun s ↦ quarticWellSumFlow s (quarticSliceGluing p q j c A 0)) atBot
        (𝓝 (A.piecewise q p)) ∧
      Tendsto (fun s ↦ quarticWellSumFlow s (quarticSliceGluing p q j c A 0)) atTop
        (𝓝 ((insert j A).piecewise q p)) := by
  have hp := forall_eq_neg_one_or_eq_zero_or_eq_one_left hq hpq
  rw [quarticSliceGluing_zero hpq hc hjA]
  refine (mem_quarticConnectingSet.1
    (quarticTrajectoryPoint_mem_quarticConnectingSet (fun i ↦ ?_) (fun i hi ↦ ?_) _)).2
  · exact Finset.piecewise_cases _ _ _ (fun t ↦ t = -1 ∨ t = 0 ∨ t = 1) (hq i) (hp i)
  · -- Only `j` changes between the two critical points, and it has not moved in the first.
    by_cases hij : i = j
    · subst hij
      rw [A.piecewise_eq_of_notMem _ _ hjA] at hi ⊢
      rw [Finset.piecewise_insert_self] at hi
      exact hpq i hi
    · exact absurd (Finset.piecewise_insert_of_ne _ _ _ hij).symm hi

/-- **Convergence to the broken trajectory.** Let points on the trajectories from `p` to `q` have
time separations `τᵢ - τⱼ` tending to `+∞` for the moving coordinates `i ∈ A` and to `-∞` for the
other moving coordinates `i ≠ j`. Then their flows for time `U(c) - τⱼ`, their slice points on
`{|yⱼ| = c}`, converge to the slice evaluation at zero gluing parameters, a point of the broken
trajectory (`TauCeti.tendsto_quarticWellSumFlow_quarticSliceGluing_zero_atBot_atTop`). -/
theorem tendsto_quarticWellSumFlow_quarticTrajectoryPoint_nhds_quarticSliceGluing_zero
    {α : Type*} {l : Filter α} (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0) {j : {i // p i ≠ q i}} {c : ℝ} (hc : c ∈ Ioo 0 1)
    {A : Finset ι} {τ : α → {i // p i ≠ q i} → ℝ}
    (hA : ∀ i : {i // p i ≠ q i}, (i : ι) ∈ A → i ≠ j →
      Tendsto (fun n ↦ τ n i - τ n j) l atTop)
    (hA' : ∀ i : {i // p i ≠ q i}, (i : ι) ∉ A → i ≠ j →
      Tendsto (fun n ↦ τ n i - τ n j) l atBot) :
    Tendsto (fun n ↦ quarticWellSumFlow (intervalBaseTimeCoordinate c - τ n j)
      (quarticTrajectoryPoint p q (τ n))) l (𝓝 (quarticSliceGluing p q j c A 0)) := by
  simp only [quarticWellSumFlow_quarticTrajectoryPoint_eq_quarticSliceGluing hq hpq j hc A]
  refine tendsto_pi_nhds.2 fun i ↦ ?_
  by_cases h : p i = q i
  · simp only [quarticSliceGluing_apply_of_eq _ _ _ _ h]
    exact tendsto_const_nhds
  by_cases hij : i = j
  · subst hij
    simp only [quarticSliceGluing_apply_self _ _ _ h]
    exact tendsto_const_nhds
  have hij' : (⟨i, h⟩ : {i // p i ≠ q i}) ≠ j := fun e ↦ hij (congrArg Subtype.val e)
  by_cases hiA : i ∈ A
  · simp only [quarticSliceGluing_apply_of_mem _ _ h hij hiA, dite_eq_right h, ite_eq_left hiA,
      Pi.zero_apply]
    refine tendsto_const_nhds.mul ?_
    exact (contDiff_intervalBaseTargetGluing _ (n := 0)).continuous.continuousAt.tendsto.comp
      (tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (hA ⟨i, h⟩ hiA hij')))
  · simp only [quarticSliceGluing_apply_of_notMem _ _ h hij hiA, dite_eq_right h, ite_eq_right hiA,
      Pi.zero_apply]
    refine tendsto_const_nhds.mul ?_
    exact (contDiff_intervalBaseSourceGluing _ (n := 0)).continuous.continuousAt.tendsto.comp
      (tendsto_exp_atBot.comp (hA' ⟨i, h⟩ hiA hij'))

end TauCeti
