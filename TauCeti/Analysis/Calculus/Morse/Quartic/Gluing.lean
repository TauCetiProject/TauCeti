/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Quartic.Basic
public import Mathlib.Data.Finset.Piecewise

/-!
# Trajectory spaces of the Euclidean quartic and their gluing parameters

The negative gradient flow of the Euclidean quartic `∑ i, (yᵢ² - 1)² / 4` on the cube `[-1, 1]^ι`
acts coordinatewise (`TauCeti.quarticWellSumFlow`), and a coordinate which moves along a trajectory
runs from the maximum `0` of `(t² - 1)² / 4` to one of its minima `±1`. Along every such coordinate
the time coordinate `U(t) = log t - (1 / 2) log (1 - t²)` of `|yᵢ|` advances at unit rate, and its
inverse is the unit-rate trajectory `q(s) = 1 / √(1 + e^{-2s})` (`TauCeti.intervalBaseOrbit 1`).
This makes the spaces of trajectories of the quartic explicit, together with their convergence to
broken trajectories in gluing parameters.

**Trajectory spaces.** Let `p` and `q` be critical points, that is points of `{-1, 0, 1}^ι`, such
that every coordinate in which they differ has `pᵢ = 0`. The points of the cube on trajectories from
`p` to `q` are exactly the points `TauCeti.quarticTrajectoryPoint p q u`, whose coordinates with
`pᵢ = qᵢ` stay fixed and whose other coordinates are `qᵢ q(uᵢ)`
(`TauCeti.setOf_tendsto_quarticWellSumFlow_eq_range`). The time coordinates `uᵢ` of the moving
coordinates determine the point (`TauCeti.quarticTrajectoryPoint_eq_iff`), the flow adds the same
time to all of them (`TauCeti.quarticWellSumFlow_quarticTrajectoryPoint`), and two points lie on one
trajectory exactly when their time coordinates differ by a common shift
(`TauCeti.exists_quarticWellSumFlow_quarticTrajectoryPoint_eq_iff`). So the trajectories from `p`
to `q` are parametrized by `ℝ^S`, for the set `S` of moving coordinates, and the unparametrized
trajectories by `ℝ^S / ℝ`. The number of moving coordinates is the index difference
(`TauCeti.ncard_setOf_ne_add_ncard_setOf_eq_zero`, with `TauCeti.morseIndex_quarticWellSum`).

**Gluing parameters.** A broken trajectory appears when the time separations `uᵢ - uⱼ` of moving
coordinates become infinite. In the gluing parameter `ρ = e^{-T}` of a time separation `T`, the
unit-rate trajectory is smooth up to `ρ = 0` at both of its ends:

* near the maximum `0`, `q(a + log ρ) = ρ / √(ρ² + e^{-2a})`
  (`TauCeti.intervalBaseSourceGluing`), which leaves `0` to first order in `ρ`, matching the
  rate `1` of the flow at `0`;
* near the minimum `1`, `q(a - log ρ) = 1 / √(1 + e^{-2a} ρ²)`
  (`TauCeti.intervalBaseTargetGluing`), an even function of `ρ` with vanishing derivative at `0`,
  matching the rate `2` of the flow at `±1`.

Evaluate the trajectories on the slice `{|yⱼ| = c}` of a moving coordinate `j`, at a level
`0 < c < 1`. Let `A` be the set of coordinates ahead of `j`. The slice point of the trajectory with
time coordinates `u` is `TauCeti.quarticSliceGluing p q j c A ρ`, at the gluing parameters
`ρᵢ = e^{-(uᵢ - uⱼ)}` for `i ∈ A` and `ρᵢ = e^{uᵢ - uⱼ}` otherwise
(`TauCeti.quarticWellSumFlow_quarticTrajectoryPoint_eq_quarticSliceGluing`). This evaluation is
smooth in `ρ` on all of `ℝ^ι` (`TauCeti.contDiff_quarticSliceGluing`). At `ρ = 0` it is the slice
point of the broken trajectory whose coordinates in `A` have already moved and whose other moving
coordinates have not: a point on the trajectory from the critical point `A.piecewise q p` to
`(insert j A).piecewise q p`
(`TauCeti.tendsto_quarticWellSumFlow_quarticSliceGluing_zero_atBot_atTop`). When the time
separations tend to infinity with these signs, the slice points converge to it
(`TauCeti.tendsto_quarticWellSumFlow_quarticTrajectoryPoint_nhds_quarticSliceGluing_zero`).

## Main definitions

* `TauCeti.quarticTimeCoordinate`: the time coordinates of a point of the cube.
* `TauCeti.quarticTrajectoryPoint`: the point with prescribed time coordinates on the trajectories
  between two critical points.
* `TauCeti.quarticSliceGluing`: the slice evaluation of trajectories in gluing parameters.

## Main results

* `TauCeti.setOf_tendsto_quarticWellSumFlow_eq_range`,
  `TauCeti.exists_quarticWellSumFlow_quarticTrajectoryPoint_eq_iff`: the trajectory spaces.
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

/-! ### Trajectory spaces of the quartic on the cube -/

section Cube

variable {ι : Type*} {p q : ι → ℝ}

/-- The time coordinates `U(|yᵢ|)` of a point `y` of the cube, for the time coordinate
`U(t) = log t - (1 / 2) log (1 - t²)` of `TauCeti.intervalBaseTimeCoordinate`. They are meaningful
on the coordinates in `(-1, 1)` other than `0`, those which move along the trajectory through `y`;
there the flow advances them all at unit rate
(`TauCeti.quarticTimeCoordinate_quarticWellSumFlow`). -/
def quarticTimeCoordinate (y : ι → ℝ) (i : ι) : ℝ := intervalBaseTimeCoordinate |y i|

theorem quarticTimeCoordinate_apply (y : ι → ℝ) (i : ι) :
    quarticTimeCoordinate y i = intervalBaseTimeCoordinate |y i| := (rfl)

/-- **The flow advances the time coordinates at unit rate.** -/
theorem quarticTimeCoordinate_quarticWellSumFlow (s : ℝ) {y : ι → ℝ} {i : ι}
    (hi : y i ∈ Ioo (-1) 1) (hi₀ : y i ≠ 0) :
    quarticTimeCoordinate (quarticWellSumFlow s y) i = quarticTimeCoordinate y i + s := by
  rw [quarticTimeCoordinate_apply, quarticWellSumFlow_apply, abs_intervalBaseFlow,
    intervalBaseTimeCoordinate_intervalBaseFlow 1 s ⟨abs_pos.2 hi₀, abs_lt.2 hi⟩, one_mul,
    quarticTimeCoordinate_apply]

/-- The point with time coordinates `u` on the trajectories of the Euclidean quartic from `p` to
`q`: its coordinates with `pᵢ = qᵢ` stay at `pᵢ`, and each other coordinate is `qᵢ q(uᵢ)` for the
unit-rate trajectory `q = TauCeti.intervalBaseOrbit 1` from `0` to `1`. When `p` and `q` are
critical points and every coordinate in which they differ has `pᵢ = 0`, these are exactly the points
of the cube on trajectories from `p` to `q` (`TauCeti.setOf_tendsto_quarticWellSumFlow_eq_range`).
-/
def quarticTrajectoryPoint (p q u : ι → ℝ) : ι → ℝ :=
  fun i ↦ if p i = q i then p i else q i * intervalBaseOrbit 1 (u i)

theorem quarticTrajectoryPoint_apply (p q u : ι → ℝ) (i : ι) :
    quarticTrajectoryPoint p q u i = if p i = q i then p i else q i * intervalBaseOrbit 1 (u i) :=
  (rfl)

@[simp]
theorem quarticTrajectoryPoint_apply_of_eq (u : ι → ℝ) {i : ι} (h : p i = q i) :
    quarticTrajectoryPoint p q u i = p i := by
  rw [quarticTrajectoryPoint_apply, ite_eq_left h]

@[simp]
theorem quarticTrajectoryPoint_apply_of_ne (u : ι → ℝ) {i : ι} (h : p i ≠ q i) :
    quarticTrajectoryPoint p q u i = q i * intervalBaseOrbit 1 (u i) := by
  rw [quarticTrajectoryPoint_apply, ite_eq_right h]

/-- A coordinate in which `p` and `q` differ moves from `0` to `qᵢ = ±1`. -/
private theorem eq_neg_one_or_eq_one_of_ne (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0) {i : ι} (h : p i ≠ q i) : q i = -1 ∨ q i = 1 := by
  rcases hq i with hi | hi | hi
  · exact .inl hi
  · exact absurd (hpq i h ▸ hi.symm) h
  · exact .inr hi

/-- The moving coordinate `±q(t)` of a trajectory point lies in `(-1, 1)`. -/
private theorem mul_intervalBaseOrbit_mem_Ioo {σ : ℝ} (hσ : σ = -1 ∨ σ = 1) (t : ℝ) :
    σ * intervalBaseOrbit 1 t ∈ Ioo (-1) 1 := by
  obtain ⟨h0, h1⟩ := intervalBaseOrbit_mem_Ioo 1 t
  rcases hσ with rfl | rfl <;> constructor <;> linarith

/-- The moving coordinate `±q(t)` of a trajectory point has absolute value `q(t)`. -/
private theorem abs_mul_intervalBaseOrbit {σ : ℝ} (hσ : σ = -1 ∨ σ = 1) (t : ℝ) :
    |σ * intervalBaseOrbit 1 t| = intervalBaseOrbit 1 t := by
  rcases hσ with rfl | rfl <;> simp [abs_of_pos (intervalBaseOrbit_mem_Ioo 1 t).1]

/-- The moving coordinate `±q(t)` of a trajectory point has sign `±1`. -/
private theorem sign_mul_intervalBaseOrbit {σ : ℝ} (hσ : σ = -1 ∨ σ = 1) (t : ℝ) :
    (SignType.sign (σ * intervalBaseOrbit 1 t) : ℝ) = σ := by
  have h0 := (intervalBaseOrbit_mem_Ioo 1 t).1
  rcases hσ with rfl | rfl
  · simp [sign_neg (neg_neg_of_pos h0 : -intervalBaseOrbit 1 t < 0)]
  · simp [sign_pos h0]

/-- A critical point of the quartic is fixed by its flow. -/
private theorem intervalBaseFlow_of_mem {t : ℝ} (ht : t = -1 ∨ t = 0 ∨ t = 1) (s : ℝ) :
    intervalBaseFlow 1 s t = t := by
  rcases ht with rfl | rfl | rfl <;> simp

/-- The trajectory points lie in the cube. -/
theorem quarticTrajectoryPoint_mem_Icc (hp : ∀ i, p i = -1 ∨ p i = 0 ∨ p i = 1)
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (u : ι → ℝ) :
    quarticTrajectoryPoint p q u ∈ Icc (-1) 1 := by
  have h : ∀ i, quarticTrajectoryPoint p q u i ∈ Icc (-1) 1 := fun i ↦ by
    by_cases h : p i = q i
    · rw [quarticTrajectoryPoint_apply_of_eq u h]
      rcases hp i with hi | hi | hi <;> rw [hi] <;> norm_num
    · rw [quarticTrajectoryPoint_apply_of_ne u h]
      obtain ⟨h0, h1⟩ := intervalBaseOrbit_mem_Ioo 1 (u i)
      rcases hq i with hi | hi | hi <;> rw [hi] <;> constructor <;> linarith
  exact ⟨fun i ↦ (h i).1, fun i ↦ (h i).2⟩

/-- **The flow translates the time coordinates**: flowing a trajectory point for time `s` adds `s`
to each of its time coordinates. -/
theorem quarticWellSumFlow_quarticTrajectoryPoint (hp : ∀ i, p i = -1 ∨ p i = 0 ∨ p i = 1)
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (s : ℝ) (u : ι → ℝ) :
    quarticWellSumFlow s (quarticTrajectoryPoint p q u) =
      quarticTrajectoryPoint p q fun i ↦ s + u i := by
  funext i
  rw [quarticWellSumFlow_apply]
  by_cases h : p i = q i
  · rw [quarticTrajectoryPoint_apply_of_eq _ h, quarticTrajectoryPoint_apply_of_eq _ h,
      intervalBaseFlow_of_mem (hp i)]
  · rw [quarticTrajectoryPoint_apply_of_ne _ h, quarticTrajectoryPoint_apply_of_ne _ h]
    rcases hq i with hi | hi | hi <;> rw [hi]
    · rw [neg_one_mul, neg_one_mul, intervalBaseFlow_neg, intervalBaseFlow_intervalBaseOrbit]
    · simp
    · rw [one_mul, one_mul, intervalBaseFlow_intervalBaseOrbit]

/-- **The trajectory points lie on trajectories from `p` to `q`.** -/
theorem tendsto_quarticWellSumFlow_quarticTrajectoryPoint_atBot_atTop
    (hp : ∀ i, p i = -1 ∨ p i = 0 ∨ p i = 1) (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0) (u : ι → ℝ) :
    Tendsto (fun s ↦ quarticWellSumFlow s (quarticTrajectoryPoint p q u)) atBot (𝓝 p) ∧
      Tendsto (fun s ↦ quarticWellSumFlow s (quarticTrajectoryPoint p q u)) atTop (𝓝 q) := by
  refine (tendsto_quarticWellSumFlow_atBot_atTop_iff (quarticTrajectoryPoint_mem_Icc hp hq u)).2
    fun i ↦ ?_
  by_cases h : p i = q i
  · rw [quarticTrajectoryPoint_apply_of_eq u h]
    rcases hp i with hi | hi | hi
    · exact .inr ⟨.inl hi, rfl, h ▸ rfl⟩
    · exact .inl ⟨by rw [hi]; norm_num, hi, by rw [← h, hi]; simp⟩
    · exact .inr ⟨.inr hi, rfl, h ▸ rfl⟩
  · rw [quarticTrajectoryPoint_apply_of_ne u h]
    have hσ := eq_neg_one_or_eq_one_of_ne hq hpq h
    exact .inl ⟨mul_intervalBaseOrbit_mem_Ioo hσ (u i), hpq i h,
      (sign_mul_intervalBaseOrbit hσ (u i)).symm⟩

/-- **Every point on a trajectory from `p` to `q` is a trajectory point**, with its own time
coordinates. -/
theorem quarticTrajectoryPoint_quarticTimeCoordinate {y : ι → ℝ} (hy : y ∈ Icc (-1) 1)
    (hp : Tendsto (fun s ↦ quarticWellSumFlow s y) atBot (𝓝 p))
    (hq : Tendsto (fun s ↦ quarticWellSumFlow s y) atTop (𝓝 q)) :
    quarticTrajectoryPoint p q (quarticTimeCoordinate y) = y := by
  have h := (tendsto_quarticWellSumFlow_atBot_atTop_iff hy).1 ⟨hp, hq⟩
  funext i
  rcases h i with ⟨hI, hpi, hqi⟩ | ⟨-, hpi, hqi⟩
  · by_cases h0 : y i = 0
    · rw [quarticTrajectoryPoint_apply_of_eq _ (by rw [hpi, hqi, h0]; simp), hpi, h0]
    · have hne : p i ≠ q i := by
        rw [hpi, hqi]
        rcases lt_or_gt_of_ne h0 with h | h
        · simp [sign_neg h]
        · simp [sign_pos h]
      rw [quarticTrajectoryPoint_apply_of_ne _ hne, hqi, quarticTimeCoordinate_apply,
        intervalBaseOrbit_one_intervalBaseTimeCoordinate ⟨abs_pos.2 h0, abs_lt.2 hI⟩, sign_mul_abs]
  · rw [quarticTrajectoryPoint_apply_of_eq _ (hpi.trans hqi.symm), hpi]

/-- **The trajectory space from `p` to `q`.** For critical points `p` and `q` of the quartic such
that every coordinate in which they differ has `pᵢ = 0`, the points of the cube on trajectories from
`p` to `q` are exactly the trajectory points. -/
theorem setOf_tendsto_quarticWellSumFlow_eq_range (hp : ∀ i, p i = -1 ∨ p i = 0 ∨ p i = 1)
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (hpq : ∀ i, p i ≠ q i → p i = 0) :
    {y | y ∈ Icc (-1) 1 ∧ Tendsto (fun s ↦ quarticWellSumFlow s y) atBot (𝓝 p) ∧
      Tendsto (fun s ↦ quarticWellSumFlow s y) atTop (𝓝 q)} = range (quarticTrajectoryPoint p q) :=
  Subset.antisymm
    (fun _ ⟨hy, hp', hq'⟩ ↦ ⟨_, quarticTrajectoryPoint_quarticTimeCoordinate hy hp' hq'⟩)
    (range_subset_iff.2 fun u ↦ ⟨quarticTrajectoryPoint_mem_Icc hp hq u,
      tendsto_quarticWellSumFlow_quarticTrajectoryPoint_atBot_atTop hp hq hpq u⟩)

/-- The time coordinates of a trajectory point, in its moving coordinates, are the prescribed
ones. -/
theorem quarticTimeCoordinate_quarticTrajectoryPoint (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0) (u : ι → ℝ) {i : ι} (hi : p i ≠ q i) :
    quarticTimeCoordinate (quarticTrajectoryPoint p q u) i = u i := by
  rw [quarticTimeCoordinate_apply, quarticTrajectoryPoint_apply_of_ne u hi,
    abs_mul_intervalBaseOrbit (eq_neg_one_or_eq_one_of_ne hq hpq hi) (u i),
    intervalBaseTimeCoordinate_intervalBaseOrbit, one_mul]

/-- **The time coordinates of the moving coordinates determine a trajectory point.** -/
theorem quarticTrajectoryPoint_eq_iff (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0) {u u' : ι → ℝ} :
    quarticTrajectoryPoint p q u = quarticTrajectoryPoint p q u' ↔ ∀ i, p i ≠ q i → u i = u' i := by
  refine ⟨fun h i hi ↦ ?_, fun h ↦ funext fun i ↦ ?_⟩
  · rw [← quarticTimeCoordinate_quarticTrajectoryPoint hq hpq u hi, h,
      quarticTimeCoordinate_quarticTrajectoryPoint hq hpq u' hi]
  · by_cases hi : p i = q i
    · rw [quarticTrajectoryPoint_apply_of_eq _ hi, quarticTrajectoryPoint_apply_of_eq _ hi]
    · rw [quarticTrajectoryPoint_apply_of_ne _ hi, quarticTrajectoryPoint_apply_of_ne _ hi, h i hi]

/-- **The unparametrized trajectories from `p` to `q`.** Two trajectory points lie on one trajectory
exactly when the time coordinates of their moving coordinates differ by a common shift. So the
trajectories from `p` to `q` are the classes of `ℝ^S` modulo the diagonal, for the set `S` of moving
coordinates. -/
theorem exists_quarticWellSumFlow_quarticTrajectoryPoint_eq_iff
    (hp : ∀ i, p i = -1 ∨ p i = 0 ∨ p i = 1) (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0) {u u' : ι → ℝ} :
    (∃ s, quarticWellSumFlow s (quarticTrajectoryPoint p q u) = quarticTrajectoryPoint p q u') ↔
      ∃ s, ∀ i, p i ≠ q i → u' i = s + u i := by
  simp only [quarticWellSumFlow_quarticTrajectoryPoint hp hq, quarticTrajectoryPoint_eq_iff hq hpq]
  exact exists_congr fun s ↦ forall₂_congr fun _ _ ↦ eq_comm

/-- **The dimension of the trajectory space is the index difference.** The coordinates in which `p`
and `q` differ are as many as the zero coordinates of `p`, its Morse index
(`TauCeti.morseIndex_quarticWellSum`), minus those of `q`. -/
theorem ncard_setOf_ne_add_ncard_setOf_eq_zero [Finite ι] (hpq : ∀ i, p i ≠ q i → p i = 0) :
    {i | p i ≠ q i}.ncard + {i | q i = 0}.ncard = {i | p i = 0}.ncard := by
  have hunion : {i | p i = 0} = {i | p i ≠ q i} ∪ {i | q i = 0} := by
    ext i
    simp only [mem_ofPred_eq, mem_union]
    refine ⟨fun h ↦ ?_, fun h ↦ h.elim (hpq i) fun h' ↦ ?_⟩
    · by_cases hi : q i = 0
      · exact .inr hi
      · exact .inl (h ▸ Ne.symm hi)
    · by_contra hne
      exact hne (hpq i fun h ↦ hne (h ▸ h')) |>.elim
  rw [hunion, ncard_union_eq (disjoint_left.2 fun i (hi : p i ≠ q i) (hi' : q i = 0) ↦
    hi (by rw [hpq i hi, hi']))]

/-! ### Slice evaluation in gluing parameters -/

variable [DecidableEq ι]

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

/-- **The slice point of a trajectory in gluing parameters.** The trajectory point with time
coordinates `u` reaches the slice `{|yⱼ| = c}` after time `U(c) - uⱼ`, at the slice evaluation with
gluing parameters `e^{-(uᵢ - uⱼ)}` for the coordinates `i ∈ A` ahead of `j` and `e^{uᵢ - uⱼ}` for
the others. -/
theorem quarticWellSumFlow_quarticTrajectoryPoint_eq_quarticSliceGluing
    (hp : ∀ i, p i = -1 ∨ p i = 0 ∨ p i = 1) (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (j : ι)
    {c : ℝ} (hc : c ∈ Ioo 0 1) (A : Finset ι) (u : ι → ℝ) :
    quarticWellSumFlow (intervalBaseTimeCoordinate c - u j) (quarticTrajectoryPoint p q u) =
      quarticSliceGluing p q j c A
        fun i ↦ if i ∈ A then exp (-(u i - u j)) else exp (u i - u j) := by
  rw [quarticWellSumFlow_quarticTrajectoryPoint hp hq]
  funext i
  rw [quarticSliceGluing_apply]
  by_cases h : p i = q i
  · rw [quarticTrajectoryPoint_apply_of_eq _ h, ite_eq_left h]
  rw [quarticTrajectoryPoint_apply_of_ne _ h, ite_eq_right h]
  by_cases hij : i = j
  · rw [ite_eq_left hij, hij, sub_add_cancel, intervalBaseOrbit_one_intervalBaseTimeCoordinate hc]
  rw [ite_eq_right hij]
  by_cases hA : i ∈ A
  · rw [ite_eq_left hA, ite_eq_left hA, ← intervalBaseOrbit_one_sub_log _ (exp_pos _), log_exp]
    ring_nf
  · rw [ite_eq_right hA, ite_eq_right hA, ← intervalBaseOrbit_one_add_log _ (exp_pos _), log_exp]
    ring_nf

/-- **Positive gluing parameters give trajectory points.** At gluing parameters which are positive
on the moving coordinates other than `j`, the slice evaluation is the trajectory point with time
coordinate `U(c)` at `j`, `U(c) - log ρᵢ` at the coordinates `i ∈ A` ahead of `j`, and
`U(c) + log ρᵢ` at the others. -/
theorem quarticSliceGluing_eq_quarticTrajectoryPoint (j : ι) {c : ℝ} (hc : c ∈ Ioo 0 1)
    (A : Finset ι) {ρ : ι → ℝ} (hρ : ∀ i, p i ≠ q i → i ≠ j → 0 < ρ i) :
    quarticSliceGluing p q j c A ρ = quarticTrajectoryPoint p q fun i ↦
      if i = j then intervalBaseTimeCoordinate c else if i ∈ A then
        intervalBaseTimeCoordinate c - log (ρ i) else intervalBaseTimeCoordinate c + log (ρ i) := by
  funext i
  rw [quarticSliceGluing_apply]
  by_cases h : p i = q i
  · rw [quarticTrajectoryPoint_apply_of_eq _ h, ite_eq_left h]
  rw [quarticTrajectoryPoint_apply_of_ne _ h, ite_eq_right h]
  by_cases hij : i = j
  · rw [ite_eq_left hij, ite_eq_left hij, intervalBaseOrbit_one_intervalBaseTimeCoordinate hc]
  rw [ite_eq_right hij, ite_eq_right hij]
  by_cases hA : i ∈ A
  · rw [ite_eq_left hA, ite_eq_left hA, intervalBaseOrbit_one_sub_log _ (hρ i h hij)]
  · rw [ite_eq_right hA, ite_eq_right hA, intervalBaseOrbit_one_add_log _ (hρ i h hij)]

/-- **The broken trajectory at zero gluing parameters.** At `ρ = 0` the slice evaluation is the
point with time coordinate `U(c)` on the trajectories from `A.piecewise q p`, where the coordinates
in `A` have already moved, to `(insert j A).piecewise q p`, where `j` has moved too. -/
theorem quarticSliceGluing_zero (hpq : ∀ i, p i ≠ q i → p i = 0) {j : ι} {c : ℝ}
    (hc : c ∈ Ioo 0 1) {A : Finset ι} (hjA : j ∉ A) :
    quarticSliceGluing p q j c A 0 = quarticTrajectoryPoint (A.piecewise q p)
      ((insert j A).piecewise q p) fun _ ↦ intervalBaseTimeCoordinate c := by
  funext i
  rw [quarticSliceGluing_apply]
  by_cases hij : i = j
  · subst hij
    rw [quarticTrajectoryPoint_apply, Finset.piecewise_insert_self,
      A.piecewise_eq_of_notMem _ _ hjA]
    by_cases h : p i = q i
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_left rfl,
        intervalBaseOrbit_one_intervalBaseTimeCoordinate hc]
  rw [quarticTrajectoryPoint_apply_of_eq _ (Finset.piecewise_insert_of_ne _ _ _ hij).symm,
    ite_eq_right hij]
  by_cases hA : i ∈ A
  · rw [A.piecewise_eq_of_mem _ _ hA, ite_eq_left hA, Pi.zero_apply, intervalBaseTargetGluing_zero,
      mul_one, ite_eq_right_iff]
    exact id
  · rw [A.piecewise_eq_of_notMem _ _ hA, ite_eq_right hA, Pi.zero_apply,
      intervalBaseSourceGluing_zero, mul_zero, ite_eq_left_iff]
    exact fun h ↦ (hpq i h).symm

/-- **The slice evaluation at zero gluing parameters lies on the broken trajectory.** At `ρ = 0`
the slice evaluation lies on a trajectory from the critical point `A.piecewise q p` to
`(insert j A).piecewise q p`: the piece through the slice of the broken trajectory from `p` to `q`
on which the coordinates in `A` move before `j`, and the other moving coordinates after it. -/
theorem tendsto_quarticWellSumFlow_quarticSliceGluing_zero_atBot_atTop
    (hp : ∀ i, p i = -1 ∨ p i = 0 ∨ p i = 1) (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1)
    (hpq : ∀ i, p i ≠ q i → p i = 0) {j : ι} {c : ℝ} (hc : c ∈ Ioo 0 1) {A : Finset ι}
    (hjA : j ∉ A) :
    Tendsto (fun s ↦ quarticWellSumFlow s (quarticSliceGluing p q j c A 0)) atBot
        (𝓝 (A.piecewise q p)) ∧
      Tendsto (fun s ↦ quarticWellSumFlow s (quarticSliceGluing p q j c A 0)) atTop
        (𝓝 ((insert j A).piecewise q p)) := by
  rw [quarticSliceGluing_zero hpq hc hjA]
  refine tendsto_quarticWellSumFlow_quarticTrajectoryPoint_atBot_atTop (fun i ↦ ?_)
    (fun i ↦ ?_) (fun i hi ↦ ?_) _
  · exact Finset.piecewise_cases _ _ _ (fun t ↦ t = -1 ∨ t = 0 ∨ t = 1) (hq i) (hp i)
  · exact Finset.piecewise_cases _ _ _ (fun t ↦ t = -1 ∨ t = 0 ∨ t = 1) (hq i) (hp i)
  · -- Only `j` changes between the two critical points, and it has not moved in the first.
    by_cases hij : i = j
    · subst hij
      rw [A.piecewise_eq_of_notMem _ _ hjA] at hi ⊢
      rw [Finset.piecewise_insert_self] at hi
      exact hpq i hi
    · exact absurd (Finset.piecewise_insert_of_ne _ _ _ hij).symm hi

/-- **Convergence to the broken trajectory.** Let trajectory points from `p` to `q` have time
separations `uᵢ - uⱼ` tending to `+∞` for the moving coordinates `i ∈ A` and to `-∞` for the other
moving coordinates `i ≠ j`. Then their slice points on `{|yⱼ| = c}` converge to the slice evaluation
at zero gluing parameters, a point of the broken trajectory
(`TauCeti.tendsto_quarticWellSumFlow_quarticSliceGluing_zero_atBot_atTop`). -/
theorem tendsto_quarticWellSumFlow_quarticTrajectoryPoint_nhds_quarticSliceGluing_zero
    {α : Type*} {l : Filter α} (hp : ∀ i, p i = -1 ∨ p i = 0 ∨ p i = 1)
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) {j : ι} {c : ℝ} (hc : c ∈ Ioo 0 1) {A : Finset ι}
    {u : α → ι → ℝ}
    (hA : ∀ i ∈ A, p i ≠ q i → i ≠ j → Tendsto (fun n ↦ u n i - u n j) l atTop)
    (hA' : ∀ i ∉ A, p i ≠ q i → i ≠ j → Tendsto (fun n ↦ u n i - u n j) l atBot) :
    Tendsto (fun n ↦ quarticWellSumFlow (intervalBaseTimeCoordinate c - u n j)
      (quarticTrajectoryPoint p q (u n))) l (𝓝 (quarticSliceGluing p q j c A 0)) := by
  simp only [quarticWellSumFlow_quarticTrajectoryPoint_eq_quarticSliceGluing hp hq j hc A]
  refine tendsto_pi_nhds.2 fun i ↦ ?_
  simp only [quarticSliceGluing_apply, Pi.zero_apply]
  by_cases h : p i = q i
  · simp only [ite_eq_left h]
    exact tendsto_const_nhds
  by_cases hij : i = j
  · simp only [ite_eq_right h, ite_eq_left hij]
    exact tendsto_const_nhds
  simp only [ite_eq_right h, ite_eq_right hij]
  by_cases hiA : i ∈ A
  · simp only [ite_eq_left hiA]
    refine tendsto_const_nhds.mul ?_
    exact (contDiff_intervalBaseTargetGluing _ (n := 0)).continuous.continuousAt.tendsto.comp
      (tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (hA i hiA h hij)))
  · simp only [ite_eq_right hiA]
    refine tendsto_const_nhds.mul ?_
    exact (contDiff_intervalBaseSourceGluing _ (n := 0)).continuous.continuousAt.tendsto.comp
      (tendsto_exp_atBot.comp (hA' i hiA h hij))

end Cube

end TauCeti
