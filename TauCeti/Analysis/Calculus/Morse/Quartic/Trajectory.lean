/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import TauCeti.Analysis.Calculus.Morse.Quartic.Basic

/-!
# Trajectory spaces of the Euclidean quartic in time-shift coordinates

The Euclidean quartic `quarticWellSum y = ∑ i, (yᵢ² - 1)² / 4` on `ι → ℝ` has the points of
`{-1, 0, 1}^ι` as critical points, and its negative gradient flow keeps the cube `[-1, 1]^ι`
invariant, acting by the one-dimensional flow `TauCeti.intervalBaseFlow 1` in each coordinate
(`TauCeti.Analysis.Calculus.Morse.Quartic.Basic`). This file describes its spaces of connecting
trajectories in the cube explicitly.

Let `p` and `q` be critical points. The set of points of the cube whose trajectory runs from `p`
to `q` (`TauCeti.quarticConnectingSet p q`, the intersection of the unstable set of `p` and the
stable set of `q` with the cube) is nonempty exactly when `q` is obtained from `p` by replacing
some zero coordinates by `±1` (`TauCeti.quarticConnectingSet_nonempty_iff`). The coordinates in
which `p` and `q` differ, `{i // p i ≠ q i}`, are the *moving* coordinates: along a trajectory
from `p` to `q` each of them travels from `0` to `q i` along the reference orbit
`TauCeti.intervalBaseOrbit 1`, while the other coordinates stay at `p i`. A point of the
connecting set is therefore determined by the times `τ j` at which its moving coordinates sit on
the reference orbit:

`quarticTrajectoryPoint p q τ i = q i * intervalBaseOrbit 1 (τ i)` for `p i ≠ q i`,

and `p i` otherwise. These *time shifts* are recovered by the time coordinate
`U(t) = log t - (1 / 2) log (1 - t²)` of the one-dimensional flow, applied to `|y i| = q i * y i`
(`TauCeti.quarticTimeShift`). The time-shift chart is a bijection from `{i // p i ≠ q i} → ℝ`
onto the connecting set (`TauCeti.bijOn_quarticTrajectoryPoint`), and the flow acts on it by
translation along the diagonal (`TauCeti.quarticWellSumFlow_quarticTrajectoryPoint`): every
coordinate advances at unit rate, which is the rate of `U` along the flow. Consequently:

* every negative gradient trajectory of the quartic from `p` to `q` staying in the cube is
  `t ↦ quarticTrajectoryPoint p q (t + τ)` for unique time shifts `τ`
  (`TauCeti.existsUnique_eq_quarticTrajectoryPoint_of_isIntegralCurve`);
* two points of the connecting set lie on the same trajectory exactly when their time shifts
  differ by a constant (`TauCeti.exists_quarticWellSumFlow_eq_iff`), so the space of
  unparametrized trajectories from `p` to `q` is the quotient of `{i // p i ≠ q i} → ℝ` by the
  line of constant vectors (`TauCeti.quarticConnectingOrbitEquiv`);
* the number of moving coordinates is the index difference
  `morseIndex quarticWellSum p - morseIndex quarticWellSum q`
  (`TauCeti.ncard_setOf_ne_add_morseIndex_quarticWellSum`), so for `p ≠ q` the space of
  unparametrized trajectories has dimension `morseIndex p - morseIndex q - 1`
  (`TauCeti.finrank_quotient_span_one_add_one_add_morseIndex_quarticWellSum`).

These are the open strata of the compactified trajectory spaces of the quartic on the cube, the
standard model for the comparison of Morse chains with cellular chains: a trajectory breaks when
some moving coordinates reach their target long before the others, that is, when differences of
time shifts tend to infinity.

## Main definitions

* `TauCeti.quarticConnectingSet p q`: the points of the cube on trajectories from `p` to `q`.
* `TauCeti.quarticTrajectoryPoint p q τ` and `TauCeti.quarticTimeShift p q y`: the time-shift chart
  of the connecting set and its inverse.
* `TauCeti.quarticTimeShiftEquiv`: the time-shift chart as an equivalence between the connecting
  set and `{i // p i ≠ q i} → ℝ`.
* `TauCeti.quarticConnectingOrbitSetoid p q`: lying on the same trajectory.

## Main results

* `TauCeti.quarticConnectingSet_nonempty_iff`: which critical points are joined by trajectories.
* `TauCeti.bijOn_quarticTrajectoryPoint`, `TauCeti.invOn_quarticTimeShift_quarticTrajectoryPoint`:
  the time-shift chart.
* `TauCeti.quarticWellSumFlow_quarticTrajectoryPoint`: the flow translates the time shifts.
* `TauCeti.existsUnique_eq_quarticTrajectoryPoint_of_isIntegralCurve`,
  `TauCeti.isIntegralCurve_quarticTrajectoryPoint`: the parametrized trajectories.
* `TauCeti.quarticConnectingOrbitEquiv`: the unparametrized trajectories are the time shifts
  modulo constants.
* `TauCeti.finrank_quotient_span_one_add_one_add_morseIndex_quarticWellSum`: their dimension is
  the index difference minus one.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.2 (spaces of unparametrized trajectories and their
  dimension) and §3 (the comparison with cellular homology, which the quartic on the cube models).
-/

public section

noncomputable section

open Set Filter Topology Module
open scoped Gradient

namespace TauCeti

variable {ι : Type*} {p q y : ι → ℝ}

/-! ### The time-shift chart -/

/-- The **time-shift chart** of the trajectories from `p` to `q` of the Euclidean quartic: the
point whose coordinates `i` with `p i ≠ q i` are `q i * intervalBaseOrbit 1 (τ i)`, and whose
other coordinates are `p i`. For critical points with `q` obtained from `p` by replacing zero
coordinates by `±1`, it parametrizes the points of the cube on trajectories from `p` to `q`
(`TauCeti.bijOn_quarticTrajectoryPoint`). -/
def quarticTrajectoryPoint (p q : ι → ℝ) (τ : {i // p i ≠ q i} → ℝ) : ι → ℝ :=
  fun i ↦ if h : p i = q i then p i else q i * intervalBaseOrbit 1 (τ ⟨i, h⟩)

theorem quarticTrajectoryPoint_apply_of_eq (τ : {i // p i ≠ q i} → ℝ) {i : ι} (h : p i = q i) :
    quarticTrajectoryPoint p q τ i = p i := by
  simp [quarticTrajectoryPoint, h]

theorem quarticTrajectoryPoint_apply_of_ne (τ : {i // p i ≠ q i} → ℝ) {i : ι} (h : p i ≠ q i) :
    quarticTrajectoryPoint p q τ i = q i * intervalBaseOrbit 1 (τ ⟨i, h⟩) := by
  simp [quarticTrajectoryPoint, h]

/-- A moving coordinate of the time-shift chart lies on the reference orbit. -/
@[simp]
theorem quarticTrajectoryPoint_apply_coe (τ : {i // p i ≠ q i} → ℝ) (j : {i // p i ≠ q i}) :
    quarticTrajectoryPoint p q τ j = q j * intervalBaseOrbit 1 (τ j) :=
  quarticTrajectoryPoint_apply_of_ne τ j.property

/-- The **time shifts** of a point `y` on a trajectory from `p` to `q`: the time coordinate
`TauCeti.intervalBaseTimeCoordinate` of `|y j| = q j * y j` in each coordinate `j` with
`p j ≠ q j`. They invert the time-shift chart
(`TauCeti.invOn_quarticTimeShift_quarticTrajectoryPoint`). -/
def quarticTimeShift (p q y : ι → ℝ) : {i // p i ≠ q i} → ℝ :=
  fun j ↦ intervalBaseTimeCoordinate (q j * y j)

@[simp]
theorem quarticTimeShift_apply (p q y : ι → ℝ) (j : {i // p i ≠ q i}) :
    quarticTimeShift p q y j = intervalBaseTimeCoordinate (q j * y j) :=
  (rfl)

/-- A moving coordinate of a critical point `q` with `p i ≠ q i → p i = 0` is `±1`. -/
theorem eq_neg_one_or_eq_one_of_ne (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0) {i : ι} (h : p i ≠ q i) : q i = -1 ∨ q i = 1 := by
  rcases hq i with h' | h' | h'
  · exact .inl h'
  · exact absurd (hpq i h ▸ h'.symm) h
  · exact .inr h'

private theorem mul_self_eq_one_of_ne (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0) {i : ι} (h : p i ≠ q i) : q i * q i = 1 := by
  rcases eq_neg_one_or_eq_one_of_ne hq hpq h with h' | h' <;> norm_num [h']

/-- If `q` is a critical point of the quartic and `p` agrees with `q` off its zero coordinates,
then `p` is a critical point too. -/
theorem forall_eq_neg_one_or_eq_zero_or_eq_one_left
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (hpq : ∀ i, p i ≠ q i → p i = 0) :
    ∀ i, p i = -1 ∨ p i = 0 ∨ p i = 1 := fun i ↦ by
  by_cases h : p i = q i
  · exact h ▸ hq i
  · exact .inr (.inl (hpq i h))

/-- The time shifts of the point with time shifts `τ` are `τ`. -/
@[simp]
theorem quarticTimeShift_quarticTrajectoryPoint (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0) (τ : {i // p i ≠ q i} → ℝ) :
    quarticTimeShift p q (quarticTrajectoryPoint p q τ) = τ := by
  funext j
  simp [← mul_assoc, mul_self_eq_one_of_ne hq hpq j.property]

/-- The time-shift chart is injective. -/
theorem quarticTrajectoryPoint_injective (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0) : Function.Injective (quarticTrajectoryPoint p q) :=
  Function.LeftInverse.injective (quarticTimeShift_quarticTrajectoryPoint hq hpq)

/-! ### Connecting trajectories -/

/-- The points of the cube `[-1, 1]^ι` whose trajectory under the negative gradient flow of the
Euclidean quartic runs from `p` to `q`: the intersection of the cube with the unstable set of `p`
and the stable set of `q`. -/
def quarticConnectingSet (p q : ι → ℝ) : Set (ι → ℝ) :=
  {y | y ∈ Icc (-1) 1 ∧ Tendsto (fun s ↦ quarticWellSumFlow s y) atBot (𝓝 p) ∧
    Tendsto (fun s ↦ quarticWellSumFlow s y) atTop (𝓝 q)}

theorem mem_quarticConnectingSet :
    y ∈ quarticConnectingSet p q ↔ y ∈ Icc (-1) 1 ∧
      Tendsto (fun s ↦ quarticWellSumFlow s y) atBot (𝓝 p) ∧
      Tendsto (fun s ↦ quarticWellSumFlow s y) atTop (𝓝 q) :=
  Iff.rfl

theorem mem_Icc_of_mem_quarticConnectingSet (hy : y ∈ quarticConnectingSet p q) :
    y ∈ Icc (-1) 1 :=
  hy.1

/-- A coordinate in which the ends of a trajectory in the cube agree stays constant. -/
theorem apply_eq_of_mem_quarticConnectingSet (hy : y ∈ quarticConnectingSet p q) {i : ι}
    (h : p i = q i) : y i = p i := by
  rcases (tendsto_quarticWellSumFlow_atBot_atTop_iff hy.1).1 hy.2 i with ⟨-, h0, hs⟩ | ⟨-, h1, -⟩
  · have hsign : SignType.sign (y i) = 0 := by
      cases hs' : SignType.sign (y i) <;> simp_all
    rw [sign_eq_zero_iff.1 hsign, h0]
  · exact h1.symm

/-- A moving coordinate of a point on a trajectory in the cube satisfies
`q i * y i = |y i| ∈ (0, 1)`. -/
theorem mul_mem_Ioo_of_mem_quarticConnectingSet (hy : y ∈ quarticConnectingSet p q) {i : ι}
    (h : p i ≠ q i) : q i * y i ∈ Ioo 0 1 := by
  rcases (tendsto_quarticWellSumFlow_atBot_atTop_iff hy.1).1 hy.2 i with ⟨hy', h0, hs⟩ | ⟨-, h1, h2⟩
  · have hne : y i ≠ 0 := fun h' ↦ h (by simp [h0, hs, h'])
    rw [hs, sign_mul_self]
    exact ⟨abs_pos.2 hne, abs_lt.2 hy'⟩
  · exact absurd (h1.trans h2.symm) h

/-- The target of a trajectory in the cube is a critical point of the quartic, obtained from the
source by replacing some zero coordinates by `±1`; so the source is a critical point too
(`TauCeti.forall_eq_neg_one_or_eq_zero_or_eq_one_left`). -/
theorem forall_eq_or_eq_of_mem_quarticConnectingSet (hy : y ∈ quarticConnectingSet p q) :
    (∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) ∧ ∀ i, p i ≠ q i → p i = 0 := by
  have h := (tendsto_quarticWellSumFlow_atBot_atTop_iff hy.1).1 hy.2
  refine ⟨fun i ↦ ?_, fun i hi ↦ ?_⟩
  · rcases h i with ⟨-, -, h0⟩ | ⟨h1 | h1, -, h2⟩
    · rw [h0]
      cases SignType.sign (y i) <;> simp
    · exact .inl (h2.trans h1)
    · exact .inr (.inr (h2.trans h1))
  · rcases h i with ⟨-, h0, -⟩ | ⟨-, h1, h2⟩
    · exact h0
    · exact absurd (h1.trans h2.symm) hi

/-- The point with time shifts `τ` lies in the cube. -/
theorem quarticTrajectoryPoint_mem_Icc (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0)
    (τ : {i // p i ≠ q i} → ℝ) : quarticTrajectoryPoint p q τ ∈ Icc (-1) 1 := by
  have hp := forall_eq_neg_one_or_eq_zero_or_eq_one_left hq hpq
  have hmem : ∀ i, quarticTrajectoryPoint p q τ i ∈ Icc (-1) 1 := fun i ↦ by
    by_cases h : p i = q i
    · rw [quarticTrajectoryPoint_apply_of_eq τ h]
      rcases hp i with h' | h' | h' <;> norm_num [h']
    · have ho := intervalBaseOrbit_mem_Ioo 1 (τ ⟨i, h⟩)
      rw [quarticTrajectoryPoint_apply_of_ne τ h]
      rcases eq_neg_one_or_eq_one_of_ne hq hpq h with h' | h' <;>
        simp only [h', mem_Icc] <;> constructor <;> linarith [ho.1, ho.2]
  exact ⟨fun i ↦ (hmem i).1, fun i ↦ (hmem i).2⟩

/-- **The flow translates the time shifts**: flowing for time `s` adds `s` to every time shift. -/
theorem quarticWellSumFlow_quarticTrajectoryPoint (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (s : ℝ) (τ : {i // p i ≠ q i} → ℝ) :
    quarticWellSumFlow s (quarticTrajectoryPoint p q τ) =
      quarticTrajectoryPoint p q fun j ↦ s + τ j := by
  funext i
  rw [quarticWellSumFlow_apply]
  by_cases h : p i = q i
  · rw [quarticTrajectoryPoint_apply_of_eq _ h, quarticTrajectoryPoint_apply_of_eq _ h, h]
    rcases hq i with h' | h' | h' <;> simp [h']
  · rw [quarticTrajectoryPoint_apply_of_ne _ h, quarticTrajectoryPoint_apply_of_ne _ h]
    rcases hq i with h' | h' | h' <;> simp [h', intervalBaseFlow_neg]

/-- The point with time shifts `τ` lies on a trajectory from `p` to `q`. -/
theorem quarticTrajectoryPoint_mem_quarticConnectingSet (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0)
    (τ : {i // p i ≠ q i} → ℝ) : quarticTrajectoryPoint p q τ ∈ quarticConnectingSet p q := by
  have hp := forall_eq_neg_one_or_eq_zero_or_eq_one_left hq hpq
  have hmem := quarticTrajectoryPoint_mem_Icc hq hpq τ
  refine ⟨hmem, (tendsto_quarticWellSumFlow_atBot_atTop_iff hmem).2 fun i ↦ ?_⟩
  by_cases h : p i = q i
  · rw [quarticTrajectoryPoint_apply_of_eq τ h]
    rcases hp i with h' | h' | h'
    · exact .inr ⟨.inl h', rfl, h.symm⟩
    · exact .inl ⟨by norm_num [h'], h', by simp [← h, h']⟩
    · exact .inr ⟨.inr h', rfl, h.symm⟩
  · have ho := intervalBaseOrbit_mem_Ioo 1 (τ ⟨i, h⟩)
    rw [quarticTrajectoryPoint_apply_of_ne τ h]
    rcases eq_neg_one_or_eq_one_of_ne hq hpq h with h' | h' <;> rw [h']
    · refine .inl ⟨⟨by linarith [ho.2], by linarith [ho.1]⟩, hpq i h, ?_⟩
      rw [sign_neg (by linarith [ho.1])]
      norm_num
    · refine .inl ⟨⟨by linarith [ho.1], by linarith [ho.2]⟩, hpq i h, ?_⟩
      rw [sign_pos (by linarith [ho.1])]
      norm_num

/-- **Points on connecting trajectories are given by their time shifts.** -/
@[simp]
theorem quarticTrajectoryPoint_quarticTimeShift (hy : y ∈ quarticConnectingSet p q) :
    quarticTrajectoryPoint p q (quarticTimeShift p q y) = y := by
  obtain ⟨hq, hpq⟩ := forall_eq_or_eq_of_mem_quarticConnectingSet hy
  funext i
  by_cases hi : p i = q i
  · rw [quarticTrajectoryPoint_apply_of_eq _ hi, apply_eq_of_mem_quarticConnectingSet hy hi]
  · rw [quarticTrajectoryPoint_apply_of_ne _ hi, quarticTimeShift_apply,
      intervalBaseOrbit_one_intervalBaseTimeCoordinate
        (mul_mem_Ioo_of_mem_quarticConnectingSet hy hi),
      ← mul_assoc, mul_self_eq_one_of_ne hq hpq hi, one_mul]

/-- The time shifts and the time-shift chart are inverse bijections between the connecting set
and `{i // p i ≠ q i} → ℝ`. -/
theorem invOn_quarticTimeShift_quarticTrajectoryPoint (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0) :
    InvOn (quarticTimeShift p q) (quarticTrajectoryPoint p q) univ (quarticConnectingSet p q) :=
  ⟨fun τ _ ↦ quarticTimeShift_quarticTrajectoryPoint hq hpq τ,
    fun _ hy ↦ quarticTrajectoryPoint_quarticTimeShift hy⟩

/-- **The time-shift chart of the connecting trajectories.** For critical points `p` and `q` of
the Euclidean quartic, with `q` obtained from `p` by replacing some zero coordinates by `±1`, the
time-shift chart is a bijection from `{i // p i ≠ q i} → ℝ` onto the points of the cube on
trajectories from `p` to `q`. -/
theorem bijOn_quarticTrajectoryPoint (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0) :
    BijOn (quarticTrajectoryPoint p q) univ (quarticConnectingSet p q) :=
  (invOn_quarticTimeShift_quarticTrajectoryPoint hq hpq).bijOn
    (fun τ _ ↦ quarticTrajectoryPoint_mem_quarticConnectingSet hq hpq τ) (mapsTo_univ _ _)

/-- **Critical points joined by trajectories in the cube.** There is a trajectory from `p` to `q`
in the cube exactly when `q` is a critical point of the Euclidean quartic obtained from `p` by
replacing some zero coordinates by `±1`; then `p` is a critical point too
(`TauCeti.forall_eq_neg_one_or_eq_zero_or_eq_one_left`). -/
theorem quarticConnectingSet_nonempty_iff :
    (quarticConnectingSet p q).Nonempty ↔
      (∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) ∧ ∀ i, p i ≠ q i → p i = 0 :=
  ⟨fun ⟨_, hy⟩ ↦ forall_eq_or_eq_of_mem_quarticConnectingSet hy, fun ⟨hq, hpq⟩ ↦
    ⟨_, quarticTrajectoryPoint_mem_quarticConnectingSet hq hpq 0⟩⟩

/-- Along the flow the time shifts of a point advance at unit rate. -/
theorem quarticTimeShift_quarticWellSumFlow (hy : y ∈ quarticConnectingSet p q) (s : ℝ) :
    quarticTimeShift p q (quarticWellSumFlow s y) = fun j ↦ s + quarticTimeShift p q y j := by
  obtain ⟨hq, hpq⟩ := forall_eq_or_eq_of_mem_quarticConnectingSet hy
  conv_lhs => rw [← quarticTrajectoryPoint_quarticTimeShift hy,
    quarticWellSumFlow_quarticTrajectoryPoint hq]
  exact quarticTimeShift_quarticTrajectoryPoint hq hpq _

/-! ### Parametrized trajectories -/

section Parametrized

variable [Fintype ι]

/-- A negative gradient trajectory of the Euclidean quartic staying in the cube `[-1, 1]^ι` and
running from `p` to `q` passes at time `0` through the connecting set. -/
theorem mem_quarticConnectingSet_of_isIntegralCurve {γ : ℝ → ι → ℝ}
    (hγ : IsIntegralCurve γ (fun _ z i ↦ -∇ (intervalBasePotential 1) (z i)))
    (hmem : ∀ t, γ t ∈ Icc (-1) 1) (hbot : Tendsto γ atBot (𝓝 p))
    (htop : Tendsto γ atTop (𝓝 q)) : γ 0 ∈ quarticConnectingSet p q := by
  have hγ' := eq_quarticWellSumFlow_of_isIntegralCurve hγ hmem
  exact ⟨hmem 0, hγ' ▸ hbot, hγ' ▸ htop⟩

/-- The curve `t ↦ quarticTrajectoryPoint p q (t + τ)` is a negative gradient trajectory of the
Euclidean quartic: the flow line through the point with time shifts `τ`. -/
theorem isIntegralCurve_quarticTrajectoryPoint (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0) (τ : {i // p i ≠ q i} → ℝ) :
    IsIntegralCurve (fun t ↦ quarticTrajectoryPoint p q fun j ↦ t + τ j)
      (fun _ z i ↦ -∇ (intervalBasePotential 1) (z i)) := by
  simpa only [quarticWellSumFlow_quarticTrajectoryPoint hq] using
    isIntegralCurve_quarticWellSumFlow (quarticTrajectoryPoint_mem_Icc hq hpq τ)

/-- **The parametrized trajectories from `p` to `q`.** A negative gradient trajectory of the
Euclidean quartic staying in the cube `[-1, 1]^ι` and running from `p` to `q` is
`t ↦ quarticTrajectoryPoint p q (t + τ)` for its time shifts `τ` at time `0`; these are the only
time shifts with this property (`TauCeti.quarticTrajectoryPoint_injective`). -/
theorem eq_quarticTrajectoryPoint_of_isIntegralCurve {γ : ℝ → ι → ℝ}
    (hγ : IsIntegralCurve γ (fun _ z i ↦ -∇ (intervalBasePotential 1) (z i)))
    (hmem : ∀ t, γ t ∈ Icc (-1) 1) (hbot : Tendsto γ atBot (𝓝 p))
    (htop : Tendsto γ atTop (𝓝 q)) :
    γ = fun t ↦ quarticTrajectoryPoint p q fun j ↦ t + quarticTimeShift p q (γ 0) j := by
  have h0 := mem_quarticConnectingSet_of_isIntegralCurve hγ hmem hbot htop
  obtain ⟨hq, -⟩ := forall_eq_or_eq_of_mem_quarticConnectingSet h0
  conv_lhs => rw [eq_quarticWellSumFlow_of_isIntegralCurve hγ hmem,
    ← quarticTrajectoryPoint_quarticTimeShift h0]
  simp only [quarticWellSumFlow_quarticTrajectoryPoint hq]

/-- Every negative gradient trajectory of the Euclidean quartic from `p` to `q` staying in the cube
is `t ↦ quarticTrajectoryPoint p q (t + τ)` for unique time shifts `τ`. -/
theorem existsUnique_eq_quarticTrajectoryPoint_of_isIntegralCurve {γ : ℝ → ι → ℝ}
    (hγ : IsIntegralCurve γ (fun _ z i ↦ -∇ (intervalBasePotential 1) (z i)))
    (hmem : ∀ t, γ t ∈ Icc (-1) 1) (hbot : Tendsto γ atBot (𝓝 p))
    (htop : Tendsto γ atTop (𝓝 q)) :
    ∃! τ : {i // p i ≠ q i} → ℝ, γ = fun t ↦ quarticTrajectoryPoint p q fun j ↦ t + τ j := by
  refine ⟨_, eq_quarticTrajectoryPoint_of_isIntegralCurve hγ hmem hbot htop, fun τ hτ ↦ ?_⟩
  obtain ⟨hq, hpq⟩ := forall_eq_or_eq_of_mem_quarticConnectingSet
    (mem_quarticConnectingSet_of_isIntegralCurve hγ hmem hbot htop)
  rw [hτ]
  simp [quarticTimeShift_quarticTrajectoryPoint hq hpq]

end Parametrized

/-! ### Unparametrized trajectories -/

/-- Two points of the connecting set lie on the same trajectory when the flow carries one to the
other. -/
def quarticConnectingOrbitSetoid (p q : ι → ℝ) : Setoid (quarticConnectingSet p q) where
  r y y' := ∃ s, quarticWellSumFlow s (y : ι → ℝ) = y'
  iseqv :=
    ⟨fun _ ↦ ⟨0, quarticWellSumFlow_zero_left _⟩,
      fun {_ y'} ⟨s, hs⟩ ↦ ⟨-s, by
        rw [← hs, ← quarticWellSumFlow_add (mem_Icc_of_mem_quarticConnectingSet (Subtype.prop _)),
          neg_add_cancel, quarticWellSumFlow_zero_left]⟩,
      fun {y _ _} ⟨s, hs⟩ ⟨r, hr⟩ ↦ ⟨r + s, by
        rw [quarticWellSumFlow_add (mem_Icc_of_mem_quarticConnectingSet y.property), hs, hr]⟩⟩

theorem quarticConnectingOrbitSetoid_apply {y y' : quarticConnectingSet p q} :
    quarticConnectingOrbitSetoid p q y y' ↔ ∃ s, quarticWellSumFlow s (y : ι → ℝ) = y' :=
  Iff.rfl

/-- **Points on the same trajectory.** Two points of the connecting set lie on the same trajectory
exactly when their time shifts differ by a constant vector. -/
theorem exists_quarticWellSumFlow_eq_iff (hy : y ∈ quarticConnectingSet p q) {y' : ι → ℝ}
    (hy' : y' ∈ quarticConnectingSet p q) :
    (∃ s, quarticWellSumFlow s y = y') ↔
      quarticTimeShift p q y' - quarticTimeShift p q y ∈ ℝ ∙ (1 : {i // p i ≠ q i} → ℝ) := by
  obtain ⟨hq, -⟩ := forall_eq_or_eq_of_mem_quarticConnectingSet hy
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨s, ?_⟩
    rw [quarticTimeShift_quarticWellSumFlow hy]
    funext j
    simp
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    rw [← quarticTrajectoryPoint_quarticTimeShift hy, ← quarticTrajectoryPoint_quarticTimeShift hy',
      quarticWellSumFlow_quarticTrajectoryPoint hq]
    congr 1
    funext j
    have := congrFun hs j
    simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, Pi.sub_apply] at this
    linarith

/-- **The time-shift chart as an equivalence.** The time shifts identify the connecting set with
`{i // p i ≠ q i} → ℝ`, with inverse the time-shift chart `TauCeti.quarticTrajectoryPoint`. -/
def quarticTimeShiftEquiv (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0) :
    quarticConnectingSet p q ≃ ({i // p i ≠ q i} → ℝ) where
  toFun y := quarticTimeShift p q y
  invFun τ := ⟨_, quarticTrajectoryPoint_mem_quarticConnectingSet hq hpq τ⟩
  left_inv y := Subtype.ext (quarticTrajectoryPoint_quarticTimeShift y.property)
  right_inv := quarticTimeShift_quarticTrajectoryPoint hq hpq

@[simp]
theorem quarticTimeShiftEquiv_apply (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0) (y : quarticConnectingSet p q) :
    quarticTimeShiftEquiv hq hpq y = quarticTimeShift p q y :=
  (rfl)

@[simp]
theorem quarticTimeShiftEquiv_symm_apply (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0) (τ : {i // p i ≠ q i} → ℝ) :
    ((quarticTimeShiftEquiv hq hpq).symm τ : ι → ℝ) = quarticTrajectoryPoint p q τ :=
  (rfl)

/-- **The space of unparametrized trajectories from `p` to `q`.** The time shifts identify the
trajectories of the Euclidean quartic from `p` to `q` in the cube, that is, the points of the
connecting set up to the flow, with the time shifts modulo the line of constant vectors. -/
def quarticConnectingOrbitEquiv (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0) :
    Quotient (quarticConnectingOrbitSetoid p q) ≃
      ({i // p i ≠ q i} → ℝ) ⧸ ℝ ∙ (1 : {i // p i ≠ q i} → ℝ) :=
  Quotient.congr (quarticTimeShiftEquiv hq hpq) fun y y' ↦ by
    rw [quarticConnectingOrbitSetoid_apply, exists_quarticWellSumFlow_eq_iff y.property y'.property,
      Submodule.quotientRel_def, quarticTimeShiftEquiv_apply, quarticTimeShiftEquiv_apply,
      ← neg_sub (quarticTimeShift p q y), Submodule.neg_mem_iff]

@[simp]
theorem quarticConnectingOrbitEquiv_mk (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0) (y : quarticConnectingSet p q) :
    quarticConnectingOrbitEquiv hq hpq ⟦y⟧ = Submodule.Quotient.mk (quarticTimeShift p q y) :=
  (rfl)

@[simp]
theorem quarticConnectingOrbitEquiv_symm_mk (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0) (τ : {i // p i ≠ q i} → ℝ) :
    (quarticConnectingOrbitEquiv hq hpq).symm (Submodule.Quotient.mk τ) =
      ⟦⟨_, quarticTrajectoryPoint_mem_quarticConnectingSet hq hpq τ⟩⟧ :=
  (rfl)

/-! ### Dimension -/

variable [Fintype ι]

/-- **The moving coordinates count the index difference.** For critical points `p` and `q` of the
Euclidean quartic with `q` obtained from `p` by replacing some zero coordinates by `±1`, the
number of coordinates in which they differ is `morseIndex p - morseIndex q`. -/
theorem ncard_setOf_ne_add_morseIndex_quarticWellSum (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0) :
    {i | p i ≠ q i}.ncard + morseIndex quarticWellSum q = morseIndex quarticWellSum p := by
  have hp := forall_eq_neg_one_or_eq_zero_or_eq_one_left hq hpq
  rw [morseIndex_quarticWellSum hp, morseIndex_quarticWellSum hq, add_comm,
    ← ncard_union_eq _ (toFinite _) (toFinite _)]
  · congr 1
    ext i
    simp only [mem_union, mem_ofPred_eq]
    by_cases h : p i = q i
    · simp [h]
    · exact iff_of_true (.inr h) (hpq i h)
  · rw [disjoint_left]
    intro i hi h
    exact h (by rw [hpq i h, hi])

/-- **The dimension of the space of unparametrized trajectories.** For distinct critical points `p`
and `q` of the Euclidean quartic with `q` obtained from `p` by replacing some zero coordinates by
`±1`, the time shifts modulo constants, which parametrize the unparametrized trajectories from `p`
to `q` (`TauCeti.quarticConnectingOrbitEquiv`), form a space of dimension
`morseIndex p - morseIndex q - 1`. -/
theorem finrank_quotient_span_one_add_one_add_morseIndex_quarticWellSum
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (hpq : ∀ i, p i ≠ q i → p i = 0)
    (hne : p ≠ q) :
    finrank ℝ (({i // p i ≠ q i} → ℝ) ⧸ ℝ ∙ (1 : {i // p i ≠ q i} → ℝ)) + 1 +
      morseIndex quarticWellSum q = morseIndex quarticWellSum p := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  have : Nonempty {i // p i ≠ q i} := ⟨⟨i, hi⟩⟩
  have hquot : finrank ℝ (({i // p i ≠ q i} → ℝ) ⧸ ℝ ∙ (1 : {i // p i ≠ q i} → ℝ)) + 1 =
      Fintype.card {i // p i ≠ q i} := by
    rw [← finrank_span_singleton (K := ℝ) (one_ne_zero : (1 : {i // p i ≠ q i} → ℝ) ≠ 0),
      Submodule.finrank_quotient_add_finrank, finrank_fintype_fun_eq_card]
  have hcard : Fintype.card {i // p i ≠ q i} = {i | p i ≠ q i}.ncard := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_coe_set_eq {i | p i ≠ q i}
  have := ncard_setOf_ne_add_morseIndex_quarticWellSum hq hpq
  omega

end TauCeti
