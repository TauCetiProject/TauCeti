/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Quartic

/-!
# Trajectory spaces of the Euclidean quartic in time coordinates

The Euclidean quartic `TauCeti.quarticWellSum y = ∑ i, (yᵢ² - 1)² / 4` on `ι → ℝ` has its critical
points at `{-1, 0, 1}^ι`, and its negative gradient flow `TauCeti.quarticWellSumFlow` acts
coordinatewise on the invariant cube `[-1, 1]^ι` by the flow `x' = x (1 - x²)` on `[-1, 1]`
(`TauCeti.Analysis.Calculus.Morse.Quartic`). This file describes its spaces of trajectories between
two critical points `p` and `q`, the strata from which the compactified trajectory spaces of the
cube are assembled.

Along a flow line in `(-1, 0) ∪ (0, 1)` the time coordinate
`u = log |x| - (1 / 2) log (1 - x²)` (`TauCeti.intervalBaseTimeCoordinate`) advances at unit rate,
and the unit-rate reference trajectory `q₁(u) = 1 / √(1 + e^{-2u})`
(`TauCeti.intervalBaseOrbit 1`) inverts it on `(0, 1)`. So a point of a trajectory from `p` to `q`
is described by the time coordinates of its moving coordinates, those with `p i = 0 ≠ q i`.
The point with time coordinates `τ` is `TauCeti.quarticTrajectoryPoint p q τ`, equal to
`q i * q₁(τ i)` where `p i = 0` and to `p i` elsewhere.

* **Trajectory spaces.** A trajectory from `p` to `q` in the cube exists exactly when `q` is a
  critical point and every nonzero coordinate of `p` is the corresponding coordinate of `q`
  (`TauCeti.exists_tendsto_quarticWellSumFlow_iff`), that is, when the open face of the cube
  centred at `q` lies in the closed face centred at `p`. Its points are then exactly the points
  `quarticTrajectoryPoint p q τ` (`TauCeti.tendsto_quarticWellSumFlow_iff_exists_eq`).
* **Time coordinates.** The point `quarticTrajectoryPoint p q τ` determines `τ` on the moving
  coordinates (`TauCeti.quarticTrajectoryPoint_eq_iff`), where its time coordinates are `τ`
  (`TauCeti.intervalBaseTimeCoordinate_quarticTrajectoryPoint`). The flow translates every
  time coordinate by the same amount
  (`TauCeti.quarticWellSumFlow_quarticTrajectoryPoint`), so two points lie on one trajectory
  exactly when their time coordinates differ by a constant on the moving coordinates
  (`TauCeti.exists_quarticWellSumFlow_quarticTrajectoryPoint_eq_iff`), and for `p ≠ q` the
  translation action is free (`TauCeti.quarticWellSumFlow_quarticTrajectoryPoint_eq_self_iff`).
  Hence the parametrized trajectories from `p` to `q` are the vectors of time coordinates on the
  moving coordinates, and the unparametrized ones are these vectors modulo the constants.
* **Dimension.** The number of moving coordinates is the index difference `ind p - ind q`
  (`TauCeti.ncard_setOf_eq_zero_and_ne_zero_add_morseIndex_quarticWellSum`), so for `p ≠ q` the
  space of unparametrized trajectories has dimension `ind p - ind q - 1`.
* **Level slices.** For `p ≠ q` the quartic strictly decreases along every trajectory from `p` to
  `q` (`TauCeti.strictAnti_quarticWellSum_quarticWellSumFlow_quarticTrajectoryPoint`), from its
  value at `p` to its value at `q`, and each trajectory crosses every level strictly between these
  values exactly once (`TauCeti.existsUnique_quarticWellSum_quarticWellSumFlow_eq_iff`). So the
  unparametrized trajectories are also the points of such a level slice.
* **End charts.** In the gluing parameter `ε = e^{u}` near the source `0` the reference
  trajectory is `ε / √(1 + ε²)`, and in the gluing parameter `ε = e^{-u}` near the sink `1` it is
  `1 - ε² / (√(1 + ε²) (√(1 + ε²) + 1))` (`TauCeti.intervalBaseOrbit_eq_exp_mul_inv_sqrt`,
  `TauCeti.intervalBaseOrbit_eq_one_sub_exp_sq_mul`, in
  `TauCeti.Analysis.Calculus.Morse.IntervalBase`). These closed forms are what is formalized
  here. Read off from them, though not proved in this file: both are smooth functions of `ε` on
  all of `ℝ`, the first vanishes to order exactly `1` at `ε = 0`, and the second differs from `1`
  by `ε²` times a smooth factor equal to `1 / 2` there. So in the gluing parameter each moving
  coordinate of a trajectory extends smoothly to the ends of its time interval, and the exponents
  `1` and `2` are the rates at which it leaves `0` and approaches `±1`.

## Main definitions

* `TauCeti.quarticTrajectoryPoint`: the point with prescribed time coordinates on the trajectories
  from `p` to `q`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.2 (the translation quotient and its dimension) and §3 (the
  comparison of the Morse complex with cellular homology, which this quartic on the cube models).
* K. Wehrheim, *Smooth structures on Morse trajectory spaces, featuring finite ends and associative
  gluing*, Geom. Topol. Monogr. **18** (2012), arXiv:1205.0713 (gluing parameters at the ends of
  Morse trajectories).
-/

public section

open Filter Set
open scoped Topology

namespace TauCeti

variable {ι : Type*} {p q : ι → ℝ}

/-! ### The points with prescribed time coordinates -/

/-- The point with time coordinates `τ` on the trajectories of the Euclidean quartic from `p` to
`q`: in each coordinate with `p i = 0` it is `q i` times the unit-rate reference trajectory
`TauCeti.intervalBaseOrbit 1` at time `τ i`, and in the other coordinates it is `p i`. Only the
values of `τ` on the moving coordinates, those with `p i = 0 ≠ q i`, matter. -/
noncomputable def quarticTrajectoryPoint (p q τ : ι → ℝ) : ι → ℝ :=
  fun i ↦ if p i = 0 then q i * intervalBaseOrbit 1 (τ i) else p i

theorem quarticTrajectoryPoint_apply (p q τ : ι → ℝ) (i : ι) :
    quarticTrajectoryPoint p q τ i = if p i = 0 then q i * intervalBaseOrbit 1 (τ i) else p i :=
  (rfl)

@[simp]
theorem quarticTrajectoryPoint_apply_of_eq_zero {i : ι} (hi : p i = 0) (τ : ι → ℝ) :
    quarticTrajectoryPoint p q τ i = q i * intervalBaseOrbit 1 (τ i) := by
  simp [quarticTrajectoryPoint, hi]

@[simp]
theorem quarticTrajectoryPoint_apply_of_ne_zero {i : ι} (hi : p i ≠ 0) (τ : ι → ℝ) :
    quarticTrajectoryPoint p q τ i = p i := by
  simp [quarticTrajectoryPoint, hi]

/-- On a moving coordinate, the time coordinate of `quarticTrajectoryPoint p q τ` is `τ i`. -/
theorem intervalBaseTimeCoordinate_quarticTrajectoryPoint {i : ι} (hpi : p i = 0)
    (hqi : q i = -1 ∨ q i = 1) (τ : ι → ℝ) :
    intervalBaseTimeCoordinate (quarticTrajectoryPoint p q τ i) = τ i := by
  rw [quarticTrajectoryPoint_apply_of_eq_zero hpi]
  rcases hqi with h | h <;>
    simp [h, intervalBaseTimeCoordinate_neg, intervalBaseTimeCoordinate_intervalBaseOrbit]

/-- **The time coordinates determine the point**: two points with prescribed time coordinates
agree exactly when their time coordinates agree on the moving coordinates. -/
theorem quarticTrajectoryPoint_eq_iff {τ τ' : ι → ℝ} :
    quarticTrajectoryPoint p q τ = quarticTrajectoryPoint p q τ' ↔
      ∀ i, p i = 0 → q i ≠ 0 → τ i = τ' i := by
  refine ⟨fun h i hpi hqi ↦ ?_, fun h ↦ funext fun i ↦ ?_⟩
  · -- The reference trajectory is injective, being inverted by the time coordinate.
    have h' := congrFun h i
    rw [quarticTrajectoryPoint_apply_of_eq_zero hpi, quarticTrajectoryPoint_apply_of_eq_zero hpi,
      mul_right_inj' hqi] at h'
    simpa [intervalBaseTimeCoordinate_intervalBaseOrbit] using
      congrArg intervalBaseTimeCoordinate h'
  · by_cases hpi : p i = 0
    · by_cases hqi : q i = 0
      · simp [hpi, hqi]
      · simp [hpi, h i hpi hqi]
    · simp [hpi]

/-- The points with prescribed time coordinates lie in the cube `[-1, 1]^ι`. -/
theorem quarticTrajectoryPoint_mem_Icc (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i = 0 ∨ p i = q i) (τ : ι → ℝ) :
    quarticTrajectoryPoint p q τ ∈ Icc (-1) 1 := by
  have h := fun i ↦ intervalBaseOrbit_mem_Ioo 1 (τ i)
  refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩ <;> simp only [Pi.neg_apply, Pi.one_apply] <;>
  · by_cases hpi : p i = 0
    · rw [quarticTrajectoryPoint_apply_of_eq_zero hpi]
      rcases hq i with hqi | hqi | hqi <;> simp only [hqi] <;> linarith [(h i).1, (h i).2]
    · rw [quarticTrajectoryPoint_apply_of_ne_zero hpi, (hpq i).resolve_left hpi]
      rcases hq i with hqi | hqi | hqi <;> simp only [hqi] <;> norm_num

/-- **The flow translates the time coordinates**: flowing for time `s` adds `s` to every time
coordinate. -/
theorem quarticWellSumFlow_quarticTrajectoryPoint (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i = 0 ∨ p i = q i) (s : ℝ) (τ : ι → ℝ) :
    quarticWellSumFlow s (quarticTrajectoryPoint p q τ) =
      quarticTrajectoryPoint p q fun i ↦ τ i + s := by
  funext i
  rw [quarticWellSumFlow_apply]
  by_cases hpi : p i = 0
  · rw [quarticTrajectoryPoint_apply_of_eq_zero hpi, quarticTrajectoryPoint_apply_of_eq_zero hpi,
      add_comm]
    rcases hq i with hqi | hqi | hqi <;> rw [hqi]
    · rw [neg_one_mul, neg_one_mul, intervalBaseFlow_neg, intervalBaseFlow_intervalBaseOrbit]
    · rw [zero_mul, zero_mul, intervalBaseFlow_apply_zero]
    · rw [one_mul, one_mul, intervalBaseFlow_intervalBaseOrbit]
  · rw [quarticTrajectoryPoint_apply_of_ne_zero hpi, quarticTrajectoryPoint_apply_of_ne_zero hpi,
      (hpq i).resolve_left hpi]
    rcases hq i with hqi | hqi | hqi <;> rw [hqi]
    · exact intervalBaseFlow_apply_neg_one 1 s
    · exact intervalBaseFlow_apply_zero 1 s
    · exact intervalBaseFlow_apply_one 1 s

/-! ### The trajectories from `p` to `q` -/

/-- The point with time coordinates `τ` lies on a trajectory from `p` to `q`. -/
theorem tendsto_quarticWellSumFlow_quarticTrajectoryPoint
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (hpq : ∀ i, p i = 0 ∨ p i = q i) (τ : ι → ℝ) :
    Tendsto (fun s ↦ quarticWellSumFlow s (quarticTrajectoryPoint p q τ)) atBot (𝓝 p) ∧
      Tendsto (fun s ↦ quarticWellSumFlow s (quarticTrajectoryPoint p q τ)) atTop (𝓝 q) := by
  refine (tendsto_quarticWellSumFlow_atBot_atTop_iff
    (quarticTrajectoryPoint_mem_Icc hq hpq τ)).2 fun i ↦ ?_
  have h := intervalBaseOrbit_mem_Ioo 1 (τ i)
  by_cases hpi : p i = 0
  · rw [quarticTrajectoryPoint_apply_of_eq_zero hpi]
    refine Or.inl ⟨?_, hpi, ?_⟩ <;> rcases hq i with hqi | hqi | hqi <;> rw [hqi]
    · exact ⟨by linarith [h.2], by linarith [h.1]⟩
    · simp
    · exact ⟨by linarith [h.1], by linarith [h.2]⟩
    · simp [h.1]
    · simp
    · simp [h.1]
  · rw [quarticTrajectoryPoint_apply_of_ne_zero hpi]
    have hpq' := (hpq i).resolve_left hpi
    refine Or.inr ⟨?_, rfl, hpq'.symm⟩
    rcases hq i with hqi | hqi | hqi
    · exact Or.inl (hpq'.trans hqi)
    · exact absurd (hpq'.trans hqi) hpi
    · exact Or.inr (hpq'.trans hqi)

/-- A point of the cube on a trajectory from `p` to `q` is the point with its own time coordinates
on the trajectories from `p` to `q`. -/
theorem eq_quarticTrajectoryPoint_of_tendsto {y : ι → ℝ} (hy : y ∈ Icc (-1) 1)
    (h : Tendsto (fun s ↦ quarticWellSumFlow s y) atBot (𝓝 p) ∧
      Tendsto (fun s ↦ quarticWellSumFlow s y) atTop (𝓝 q)) :
    y = quarticTrajectoryPoint p q fun i ↦ intervalBaseTimeCoordinate (y i) := by
  funext i
  rcases (tendsto_quarticWellSumFlow_atBot_atTop_iff hy).1 h i with
    ⟨hyi, hpi, hqi⟩ | ⟨hyi, hpi, -⟩
  · rw [quarticTrajectoryPoint_apply_of_eq_zero hpi, hqi]
    rcases lt_trichotomy (y i) 0 with hneg | hzero | hpos
    · have hmem : -y i ∈ Ioo 0 1 := ⟨by linarith, by linarith [hyi.1]⟩
      rw [sign_neg hneg, ← intervalBaseTimeCoordinate_neg,
        intervalBaseOrbit_one_intervalBaseTimeCoordinate hmem]
      simp
    · simp [hzero]
    · rw [sign_pos hpos, intervalBaseOrbit_one_intervalBaseTimeCoordinate ⟨hpos, hyi.2⟩]
      simp
  · have hp : p i ≠ 0 := by rcases hyi with h' | h' <;> rw [hpi, h'] <;> norm_num
    rw [quarticTrajectoryPoint_apply_of_ne_zero hp, hpi]

/-- **The trajectory space from `p` to `q` in time coordinates.** A point of the cube `[-1, 1]^ι`
lies on a trajectory from `p` to `q` exactly when `q` is a critical point, every nonzero coordinate
of `p` is the corresponding coordinate of `q`, and the point is a point with prescribed time
coordinates on the trajectories from `p` to `q`. -/
theorem tendsto_quarticWellSumFlow_iff_exists_eq {y : ι → ℝ} (hy : y ∈ Icc (-1) 1) :
    (Tendsto (fun s ↦ quarticWellSumFlow s y) atBot (𝓝 p) ∧
        Tendsto (fun s ↦ quarticWellSumFlow s y) atTop (𝓝 q)) ↔
      (∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) ∧ (∀ i, p i = 0 ∨ p i = q i) ∧
        ∃ τ, y = quarticTrajectoryPoint p q τ := by
  refine ⟨fun h ↦ ⟨fun i ↦ ?_, fun i ↦ ?_, _, eq_quarticTrajectoryPoint_of_tendsto hy h⟩,
    fun ⟨hq, hpq, τ, hτ⟩ ↦ hτ ▸ tendsto_quarticWellSumFlow_quarticTrajectoryPoint hq hpq τ⟩ <;>
  rcases (tendsto_quarticWellSumFlow_atBot_atTop_iff hy).1 h i with
    ⟨-, hpi, hqi⟩ | ⟨hyi, hpi, hqi⟩
  · rw [hqi]
    rcases lt_trichotomy (y i) 0 with h' | h' | h' <;> simp [h']
  · rw [hqi]
    rcases hyi with hyi | hyi <;> simp [hyi]
  · exact Or.inl hpi
  · exact Or.inr (hpi.trans hqi.symm)

/-- **Nonempty trajectory spaces.** Some point of the cube `[-1, 1]^ι` lies on a trajectory from
`p` to `q` exactly when `q` is a critical point and every nonzero coordinate of `p` is the
corresponding coordinate of `q`. -/
theorem exists_tendsto_quarticWellSumFlow_iff :
    (∃ y ∈ Icc (-1 : ι → ℝ) 1, Tendsto (fun s ↦ quarticWellSumFlow s y) atBot (𝓝 p) ∧
        Tendsto (fun s ↦ quarticWellSumFlow s y) atTop (𝓝 q)) ↔
      (∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) ∧ ∀ i, p i = 0 ∨ p i = q i :=
  ⟨fun ⟨_, hy, h⟩ ↦ ⟨((tendsto_quarticWellSumFlow_iff_exists_eq hy).1 h).1,
      ((tendsto_quarticWellSumFlow_iff_exists_eq hy).1 h).2.1⟩,
    fun ⟨hq, hpq⟩ ↦ ⟨_, quarticTrajectoryPoint_mem_Icc hq hpq 0,
      tendsto_quarticWellSumFlow_quarticTrajectoryPoint hq hpq 0⟩⟩

/-- **The unparametrized trajectories.** Two points with prescribed time coordinates on the
trajectories from `p` to `q` lie on one trajectory exactly when their time coordinates differ by a
constant on the moving coordinates. So the unparametrized trajectories from `p` to `q` are the
vectors of time coordinates on the moving coordinates modulo the constant vectors. -/
theorem exists_quarticWellSumFlow_quarticTrajectoryPoint_eq_iff
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (hpq : ∀ i, p i = 0 ∨ p i = q i)
    {τ τ' : ι → ℝ} :
    (∃ s, quarticWellSumFlow s (quarticTrajectoryPoint p q τ) = quarticTrajectoryPoint p q τ') ↔
      ∃ s, ∀ i, p i = 0 → q i ≠ 0 → τ' i = τ i + s := by
  simp_rw [quarticWellSumFlow_quarticTrajectoryPoint hq hpq, quarticTrajectoryPoint_eq_iff,
    eq_comm (a := τ' _)]

/-- For `p ≠ q`, some coordinate moves along the trajectories from `p` to `q`. -/
private theorem exists_eq_zero_and_ne_zero_of_ne (hpq : ∀ i, p i = 0 ∨ p i = q i) (hne : p ≠ q) :
    ∃ i, p i = 0 ∧ q i ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  have hpi := (hpq i).resolve_right hi
  exact ⟨i, hpi, fun h ↦ hi (hpi.trans h.symm)⟩

/-- **The translation action is free**: for `p ≠ q`, the flow moves every point of a trajectory
from `p` to `q` for every nonzero time. -/
theorem quarticWellSumFlow_quarticTrajectoryPoint_eq_self_iff
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (hpq : ∀ i, p i = 0 ∨ p i = q i) (hne : p ≠ q)
    {s : ℝ} {τ : ι → ℝ} :
    quarticWellSumFlow s (quarticTrajectoryPoint p q τ) = quarticTrajectoryPoint p q τ ↔
      s = 0 := by
  rw [quarticWellSumFlow_quarticTrajectoryPoint hq hpq, quarticTrajectoryPoint_eq_iff]
  refine ⟨fun h ↦ ?_, fun h i _ _ ↦ by rw [h, add_zero]⟩
  obtain ⟨i, hpi, hqi⟩ := exists_eq_zero_and_ne_zero_of_ne hpq hne
  linarith [h i hpi hqi]

/-! ### The dimension of the trajectory spaces -/

/-- **The dimension of the trajectory spaces.** The number of moving coordinates of the
trajectories from `p` to `q` is the index difference `ind p - ind q`. So for `p ≠ q` the
unparametrized trajectories, the vectors of their time coordinates modulo the constants, form a
space of dimension `ind p - ind q - 1`. -/
theorem ncard_setOf_eq_zero_and_ne_zero_add_morseIndex_quarticWellSum [Fintype ι]
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (hpq : ∀ i, p i = 0 ∨ p i = q i) :
    {i | p i = 0 ∧ q i ≠ 0}.ncard + morseIndex quarticWellSum q =
      morseIndex quarticWellSum p := by
  have hp : ∀ i, p i = -1 ∨ p i = 0 ∨ p i = 1 := fun i ↦ by
    rcases hpq i with h | h
    · exact Or.inr (Or.inl h)
    · exact h ▸ hq i
  have hdisj : Disjoint {i | p i = 0 ∧ q i ≠ 0} {i | q i = 0} :=
    Set.disjoint_left.2 fun i (hi : p i = 0 ∧ q i ≠ 0) (hi' : q i = 0) ↦ hi.2 hi'
  rw [morseIndex_quarticWellSum hq, morseIndex_quarticWellSum hp,
    ← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
  congr 1
  ext i
  simp only [mem_union, mem_ofPred_eq]
  constructor
  · rintro (⟨h, -⟩ | h)
    · exact h
    · rcases hpq i with h' | h'
      · exact h'
      · exact h'.trans h
  · intro h
    by_cases hqi : q i = 0
    · exact Or.inr hqi
    · exact Or.inl ⟨h, hqi⟩

/-! ### Level slices -/

/-- On a moving coordinate the quartic summand of `quarticTrajectoryPoint p q τ` is
`σ(-2 τ i)² / 4`, for the sigmoid `σ`. -/
private theorem intervalBasePotential_quarticTrajectoryPoint {i : ι} (hpi : p i = 0)
    (hqi : q i = -1 ∨ q i = 1) (τ : ι → ℝ) :
    intervalBasePotential 1 (quarticTrajectoryPoint p q τ i) =
      Real.sigmoid (-(2 * 1 * τ i)) ^ 2 / 4 := by
  have hsq : quarticTrajectoryPoint p q τ i ^ 2 = intervalBaseOrbit 1 (τ i) ^ 2 := by
    rw [quarticTrajectoryPoint_apply_of_eq_zero hpi]
    rcases hqi with h | h <;> rw [h] <;> ring
  rw [intervalBasePotential_apply, hsq, ← one_sub_intervalBaseOrbit_sq]
  ring

/-- Off the moving coordinates, `quarticTrajectoryPoint p q τ` does not depend on `τ`. -/
private theorem quarticTrajectoryPoint_apply_of_not_moving {i : ι}
    (hi : ¬(p i = 0 ∧ q i ≠ 0)) (τ τ' : ι → ℝ) :
    quarticTrajectoryPoint p q τ i = quarticTrajectoryPoint p q τ' i := by
  by_cases hpi : p i = 0
  · have hqi : q i = 0 := not_not.1 fun h ↦ hi ⟨hpi, h⟩
    simp [hpi, hqi]
  · simp [hpi]

/-- **The quartic decreases strictly along the trajectories** from `p` to `q`, for `p ≠ q`. -/
theorem strictAnti_quarticWellSum_quarticWellSumFlow_quarticTrajectoryPoint [Fintype ι]
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (hpq : ∀ i, p i = 0 ∨ p i = q i) (hne : p ≠ q)
    (τ : ι → ℝ) :
    StrictAnti fun s ↦ quarticWellSum (quarticWellSumFlow s (quarticTrajectoryPoint p q τ)) := by
  intro s r hsr
  simp only [quarticWellSumFlow_quarticTrajectoryPoint hq hpq, quarticWellSum_def]
  obtain ⟨j, hpj, hqj⟩ := exists_eq_zero_and_ne_zero_of_ne hpq hne
  -- On a moving coordinate the summand `σ(-2 (τ i + s))² / 4` decreases strictly.
  have hlt : ∀ i, p i = 0 → q i ≠ 0 →
      Real.sigmoid (-(2 * 1 * (τ i + r))) ^ 2 / 4 < Real.sigmoid (-(2 * 1 * (τ i + s))) ^ 2 / 4 :=
    fun i _ _ ↦ by
      have h := Real.sigmoid_strictMono (show -(2 * 1 * (τ i + r)) < -(2 * 1 * (τ i + s)) by
        linarith)
      have h0 := Real.sigmoid_pos (-(2 * 1 * (τ i + r)))
      gcongr
  refine Finset.sum_lt_sum (fun i _ ↦ ?_) ⟨j, Finset.mem_univ j, ?_⟩
  · by_cases hi : p i = 0 ∧ q i ≠ 0
    · have hqi := (hq i).imp_right (Or.resolve_left · hi.2)
      rw [intervalBasePotential_quarticTrajectoryPoint hi.1 hqi,
        intervalBasePotential_quarticTrajectoryPoint hi.1 hqi]
      exact (hlt i hi.1 hi.2).le
    · rw [quarticTrajectoryPoint_apply_of_not_moving hi _ fun i ↦ τ i + s]
  · have hqj' := (hq j).imp_right (Or.resolve_left · hqj)
    rw [intervalBasePotential_quarticTrajectoryPoint hpj hqj',
      intervalBasePotential_quarticTrajectoryPoint hpj hqj']
    exact hlt j hpj hqj

/-- **Level slices of the trajectory spaces.** For `p ≠ q`, the quartic takes along each
trajectory from `p` to `q` exactly the values strictly between its values at `q` and at `p`, each
exactly once. So every such level slices the trajectory space from `p` to `q`, and its points on
that space are the unparametrized trajectories from `p` to `q`. -/
theorem existsUnique_quarticWellSum_quarticWellSumFlow_eq_iff [Fintype ι]
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (hpq : ∀ i, p i = 0 ∨ p i = q i) (hne : p ≠ q)
    (τ : ι → ℝ) {c : ℝ} :
    (∃! s, quarticWellSum (quarticWellSumFlow s (quarticTrajectoryPoint p q τ)) = c) ↔
      c ∈ Ioo (quarticWellSum q) (quarticWellSum p) := by
  set g := fun s ↦ quarticWellSum (quarticWellSumFlow s (quarticTrajectoryPoint p q τ))
  have hanti : StrictAnti g :=
    strictAnti_quarticWellSum_quarticWellSumFlow_quarticTrajectoryPoint hq hpq hne τ
  have hlim := tendsto_quarticWellSumFlow_quarticTrajectoryPoint hq hpq τ
  have hbot : Tendsto g atBot (𝓝 (quarticWellSum p)) :=
    (continuous_quarticWellSum.tendsto p).comp hlim.1
  have htop : Tendsto g atTop (𝓝 (quarticWellSum q)) :=
    (continuous_quarticWellSum.tendsto q).comp hlim.2
  have hcont : Continuous g := continuous_quarticWellSum.comp (continuous_iff_continuousAt.2 fun s ↦
    (hasDerivAt_quarticWellSumFlow (quarticTrajectoryPoint_mem_Icc hq hpq τ) s).continuousAt)
  refine ⟨fun ⟨s, hs, _⟩ ↦ hs ▸ ⟨?_, ?_⟩, fun hc ↦ ?_⟩
  · exact (hanti.antitone.le_of_tendsto htop (s + 1)).trans_lt (hanti (lt_add_one s))
  · exact (hanti (sub_one_lt s)).trans_le (hanti.antitone.ge_of_tendsto hbot (s - 1))
  · obtain ⟨a, ha⟩ := (hbot.eventually (lt_mem_nhds hc.2)).exists
    obtain ⟨b, hb⟩ := (htop.eventually (gt_mem_nhds hc.1)).exists
    obtain ⟨s, hs⟩ := intermediate_value_univ b a hcont ⟨hb.le, ha.le⟩
    exact ⟨s, hs, fun r hr ↦ hanti.injective (hr.trans hs.symm)⟩

end TauCeti
