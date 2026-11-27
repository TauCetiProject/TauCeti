/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Cluster.Basic
import Mathlib.Order.Interval.Set.Union
import Mathlib.Order.SuccPred.IntervalSucc
import TauCeti.Analysis.BoundedVariation.Ball
import TauCeti.Analysis.BoundedVariation.Submodularity
import TauCeti.Analysis.BoundedVariation.Weighted.Frontier
import TauCeti.MeasureTheory.Measure.BallRadius
import TauCeti.Topology.Instances.ENNReal

/-!
# The isoperimetric profile of clusters

Let `W` be a weight on a finite-dimensional real inner product space `E`, with measure
`μ = e^{−W} · volume`. For `q ≥ 1` and a vector `v ∈ ℝ^q`, the **isoperimetric profile**
`I_μ^{(q−1)}(v)` (`TauCeti.isoperimetricProfile W q v`) is the infimum of the total perimeters of
the `q`-clusters whose cells have the measures `v_1, …, v_q`, in `[0, ∞]`. When `μ(E) = 1` the
relevant vectors lie on the probability simplex `Δ^{(q−1)}`, and a cluster attaining the profile
at its own measure vector is a minimizing cluster.

* The profile is at most the total perimeter of each competitor
  (`TauCeti.isoperimetricProfile_le`, `TauCeti.le_isoperimetricProfile_iff`), and it is finite
  exactly when some cluster has the prescribed cell measures
  (`TauCeti.isoperimetricProfile_lt_top_iff`).
* It is invariant under permuting the coordinates of `v`
  (`TauCeti.isoperimetricProfile_comp_perm`).
* For a `C¹` weight, grouping cells along `f : Fin p → Fin q` does not increase the perimeter, so
  for nonnegative `w` the profile at the grouped vector `k ↦ Σ_{f j = k} w_j` is at most the
  profile at `w` (`TauCeti.isoperimetricProfile_sum_fiber_le`). Two special cases: padding a
  vector with zero coordinates (`TauCeti.isoperimetricProfile_le_comp`), and, for a finite
  measure, the vanishing of the profile at the vectors `μ(E) e_i`, the vertices of the simplex
  when `μ(E) = 1` (`TauCeti.isoperimetricProfile_pi_single`).
* For two cells, a `C¹` weight and a finite measure, the profile at `(v_1, v_2)` with `0 ≤ v_1`
  and `v_1 + v_2 = μ(E)` is the infimum of the weighted perimeters of sets of measure `v_1`
  (`TauCeti.isoperimetricProfile_two`).
* In dimension at least one, for a `C¹` weight whose measure is finite, every nonnegative `v`
  with `Σ v_i = μ(E)` is the measure vector of a cluster, so the profile is finite there
  (`TauCeti.exists_cluster_weightedMeasure_cell_eq`, `TauCeti.isoperimetricProfile_lt_top`). The
  cells are concentric annuli `{r_{i−1} ≤ ‖x‖ < r_i}`: the measure of the ball `B(0, r)` is
  continuous and strictly increasing in `r`, spheres being null and `e^{−W}` positive
  (`MeasureTheory.Measure.continuous_measure_ball_of_measure_sphere_eq_zero`,
  `TauCeti.strictMonoOn_weightedMeasure_ball`), so the radii can be chosen by the intermediate
  value theorem; each annulus has finite weighted
  perimeter since its frontier lies on two spheres, on which `e^{−W}` is bounded.

## References

* E. Milman, J. Neeman, *The Gaussian double-bubble and multi-bubble conjectures*, Ann. of Math.
  (2022), Sections 1 and 4.
-/

public section

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {W : E → ℝ} {p q : ℕ} {v : Fin q → ℝ}

/-- The **isoperimetric profile** `I_μ^{(q−1)}(v)`: the infimum of the total perimeters of the
`q`-clusters whose cells have the measures `v_1, …, v_q` for `μ = e^{−W} · volume`. It is `∞`
when no cluster has these cell measures. -/
def isoperimetricProfile (W : E → ℝ) (q : ℕ) (v : Fin q → ℝ) : ℝ≥0∞ :=
  ⨅ (Ω : Cluster W q) (_ : ∀ i, weightedMeasure W (Ω.cell i) = ENNReal.ofReal (v i)),
    Ω.perimeter

/-- Unfolding `TauCeti.isoperimetricProfile`. -/
theorem isoperimetricProfile_def :
    isoperimetricProfile W q v =
      ⨅ (Ω : Cluster W q) (_ : ∀ i, weightedMeasure W (Ω.cell i) = ENNReal.ofReal (v i)),
        Ω.perimeter :=
  (rfl)

/-- The isoperimetric profile is at most the total perimeter of every cluster with the prescribed
cell measures. -/
theorem isoperimetricProfile_le (Ω : Cluster W q)
    (hΩ : ∀ i, weightedMeasure W (Ω.cell i) = ENNReal.ofReal (v i)) :
    isoperimetricProfile W q v ≤ Ω.perimeter :=
  iInf₂_le Ω hΩ

/-- A lower bound for the isoperimetric profile is a lower bound for the total perimeter of every
cluster with the prescribed cell measures. -/
theorem le_isoperimetricProfile_iff {c : ℝ≥0∞} :
    c ≤ isoperimetricProfile W q v ↔
      ∀ Ω : Cluster W q, (∀ i, weightedMeasure W (Ω.cell i) = ENNReal.ofReal (v i)) →
        c ≤ Ω.perimeter :=
  le_iInf₂_iff

/-- The isoperimetric profile is finite exactly when some cluster has the prescribed cell
measures. -/
theorem isoperimetricProfile_lt_top_iff :
    isoperimetricProfile W q v < ⊤ ↔
      ∃ Ω : Cluster W q, ∀ i, weightedMeasure W (Ω.cell i) = ENNReal.ofReal (v i) := by
  refine ⟨fun h => ?_, fun ⟨Ω, hΩ⟩ => (isoperimetricProfile_le Ω hΩ).trans_lt Ω.perimeter_lt_top⟩
  by_contra hne
  exact h.ne (iInf₂_eq_top.2 fun Ω hΩ => (hne ⟨Ω, hΩ⟩).elim)

/-- The isoperimetric profile is invariant under permuting the coordinates of the measure
vector. -/
@[simp]
theorem isoperimetricProfile_comp_perm (σ : Equiv.Perm (Fin q)) :
    isoperimetricProfile W q (v ∘ σ) = isoperimetricProfile W q v := by
  suffices h : ∀ (v : Fin q → ℝ) (σ : Equiv.Perm (Fin q)),
      isoperimetricProfile W q (v ∘ σ) ≤ isoperimetricProfile W q v by
    refine le_antisymm (h v σ) ?_
    simpa [Function.comp_assoc] using h (v ∘ σ) σ.symm
  intro v σ
  refine le_isoperimetricProfile_iff.2 fun Ω hΩ => ?_
  rw [← Ω.perimeter_permute σ]
  exact isoperimetricProfile_le _ fun i => by simp [hΩ]

/-! ### Grouping and padding -/

/-- **Grouping cells.** For a `C¹` weight, a map `f : Fin p → Fin q` and a nonnegative
`w : Fin p → ℝ`, the profile at the grouped vector `k ↦ Σ_{f j = k} w_j` is at most the profile at
`w`: grouping the cells of a `p`-cluster along `f` gives a `q`-cluster with these cell measures and
no larger total perimeter. -/
theorem isoperimetricProfile_sum_fiber_le (hW : ContDiff ℝ 1 W) (f : Fin p → Fin q)
    {w : Fin p → ℝ} (hw : ∀ j, 0 ≤ w j) :
    isoperimetricProfile W q (fun k => ∑ j ∈ Finset.univ.filter (f · = k), w j) ≤
      isoperimetricProfile W p w := by
  refine le_isoperimetricProfile_iff.2 fun Ω hΩ => ?_
  refine (isoperimetricProfile_le (Ω.coarsen hW f) fun k => ?_).trans (Ω.perimeter_coarsen_le hW f)
  rw [Cluster.coarsen_cell, Ω.weightedMeasure_biUnion_cell,
    ENNReal.ofReal_sum_of_nonneg fun j _ => hw j]
  exact Finset.sum_congr rfl fun j _ => hΩ j

/-- **Padding with empty cells.** For a `C¹` weight, if `v` vanishes off the range of an injective
map `f : Fin p → Fin q`, then `I_μ^{(q−1)}(v) ≤ I_μ^{(p−1)}(v ∘ f)`: placing the cells of a
`p`-cluster at the indices `f j` and leaving the other cells empty gives a `q`-cluster. -/
theorem isoperimetricProfile_le_comp (hW : ContDiff ℝ 1 W) {f : Fin p → Fin q}
    (hf : Function.Injective f) (hv₀ : ∀ k, k ∉ range f → v k = 0) :
    isoperimetricProfile W q v ≤ isoperimetricProfile W p (v ∘ f) := by
  refine le_isoperimetricProfile_iff.2 fun Ω hΩ => ?_
  refine (isoperimetricProfile_le (Ω.coarsen hW f) fun k => ?_).trans (Ω.perimeter_coarsen_le hW f)
  rw [Cluster.coarsen_cell, Ω.weightedMeasure_biUnion_cell]
  by_cases hk : k ∈ range f
  · obtain ⟨j, rfl⟩ := hk
    simp [hf.eq_iff, Finset.filter_eq', hΩ]
  · rw [hv₀ k hk, ENNReal.ofReal_zero]
    exact Finset.sum_eq_zero fun j hj => (hk ⟨j, (Finset.mem_filter.1 hj).2⟩).elim

/-- **The profile vanishes at the vertices.** For a `C¹` weight whose measure `μ` is finite, the
profile at the vertex `μ(E) e_i` is `0`, attained by the cluster with `i`-th cell `E` and all other
cells empty. When `μ` is a probability measure, these are the vertices `e_i` of the simplex. -/
@[simp]
theorem isoperimetricProfile_pi_single (hW : ContDiff ℝ 1 W)
    [IsFiniteMeasure (weightedMeasure W)] (i : Fin q) :
    isoperimetricProfile W q (Pi.single i ((weightedMeasure W).real univ)) = 0 := by
  have h1 : isoperimetricProfile W 1 (fun _ => (weightedMeasure W).real univ) = 0 :=
    nonpos_iff_eq_zero.1 <| (isoperimetricProfile_le (Cluster.univ hW) fun _ => by
      simp [ofReal_measureReal (measure_ne_top _ _)]).trans
      (Cluster.perimeter_eq_zero_of_one hW _).le
  refine nonpos_iff_eq_zero.1 (le_of_le_of_eq ((congrArg (isoperimetricProfile W q)
    (funext fun k => ?_)).trans_le
      (isoperimetricProfile_sum_fiber_le hW (fun _ : Fin 1 => i) fun _ => measureReal_nonneg))
      h1)
  rcases eq_or_ne k i with rfl | hk
  · simp
  · simp [hk, hk.symm]

/-! ### Two cells -/

/-- **The two-cell profile.** For a `C¹` weight whose measure `μ` is finite and a vector
`(v_1, v_2)` with `0 ≤ v_1` and `v_1 + v_2 = μ(E)`, such as a point of the simplex when `μ` is a
probability measure, the profile is the infimum of the weighted perimeters of Lebesgue-measurable
sets of measure `v_1`. -/
theorem isoperimetricProfile_two (hW : ContDiff ℝ 1 W) [IsFiniteMeasure (weightedMeasure W)]
    {v : Fin 2 → ℝ} (hv : 0 ≤ v 0) (hsum : v 0 + v 1 = (weightedMeasure W).real univ) :
    isoperimetricProfile W 2 v =
      ⨅ (U : Set E) (_ : NullMeasurableSet U) (_ : weightedMeasure W U = ENNReal.ofReal (v 0)),
        weightedPerimeter W ⊤ U := by
  refine le_antisymm (le_iInf₂ fun U hU => le_iInf fun hUv => ?_)
    (le_isoperimetricProfile_iff.2 fun Ω hΩ => ?_)
  · -- A set `U` of finite perimeter and its complement form a `2`-cluster.
    rcases lt_or_ge (weightedPerimeter W ⊤ U) ⊤ with hP | hP
    swap
    · exact le_top.trans hP
    let Ω : Cluster W 2 :=
      { cell := ![U, Uᶜ]
        nullMeasurableSet_cell := Fin.forall_fin_two.2 ⟨hU, hU.compl⟩
        pairwise_disjoint := by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp_all [disjoint_compl_left, disjoint_compl_right]
        volume_compl_iUnion := by
          rw [show (⋃ i, ![U, Uᶜ] i) = univ from eq_univ_of_forall fun x => mem_iUnion.2 <| by
            by_cases hx : x ∈ U
            exacts [⟨0, hx⟩, ⟨1, hx⟩], compl_univ, measure_empty]
        weightedPerimeter_lt_top := Fin.forall_fin_two.2
          ⟨hP, by simpa [weightedPerimeter_compl hW] using hP⟩ }
    have hΩ : ∀ i, weightedMeasure W (Ω.cell i) = ENNReal.ofReal (v i) := by
      refine Fin.forall_fin_two.2 ⟨hUv, ?_⟩
      have hUμ : NullMeasurableSet U (weightedMeasure W) :=
        hU.mono_ac weightedMeasure_absolutelyContinuous
      simp only [Ω, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [measure_compl₀ hUμ (measure_ne_top _ _), hUv,
        ← ofReal_measureReal (measure_ne_top _ univ), ← ENNReal.ofReal_sub _ hv]
      congr 1
      linarith
    refine (isoperimetricProfile_le Ω hΩ).trans_eq ?_
    exact Ω.perimeter_eq_weightedPerimeter_cell_zero hW
  · -- The first cell of a `2`-cluster is a competitor.
    rw [Ω.perimeter_eq_weightedPerimeter_cell_zero hW]
    exact iInf₂_le_of_le _ (Ω.nullMeasurableSet_cell 0) (iInf_le _ (hΩ 0))

/-! ### Finiteness: concentric annuli -/

section Annuli

variable [Nontrivial E]

variable (W) in
/-- The measure `x ↦ μ(B(0, ‖x‖))` of the ball through `x` about the origin. Its sublevel sets
are balls about the origin. -/
private def radialMass (x : E) : ℝ :=
  (weightedMeasure W).real (ball 0 ‖x‖)

/-- For an almost everywhere measurable weight with finite measure, every ball about the origin
has measure less than `μ(E)`. -/
private theorem radialMass_lt (hW : AEMeasurable W volume) [IsFiniteMeasure (weightedMeasure W)]
    (x : E) : radialMass W x < (weightedMeasure W).real univ := by
  rw [radialMass, measureReal_def, measureReal_def]
  exact (ENNReal.toReal_strict_mono (measure_ne_top _ _)
    (strictMonoOn_weightedMeasure_ball hW 0 (mem_Ici.2 (norm_nonneg x))
      (mem_Ici.2 (by positivity)) (lt_add_one ‖x‖))).trans_le
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _)))

/-- For a `C¹` weight with finite measure and `0 ≤ t ≤ μ(E)`, the sublevel set
`{x | μ(B(0, ‖x‖)) < t}` is a ball about the origin or the whole space: it is measurable, has
measure `t` and finite Euclidean perimeter, and its frontier is bounded. -/
private theorem setOf_radialMass_lt (hW : ContDiff ℝ 1 W) [IsFiniteMeasure (weightedMeasure W)]
    {t : ℝ} (ht : 0 ≤ t) (htm : t ≤ (weightedMeasure W).real univ) :
    MeasurableSet {x | radialMass W x < t} ∧
      weightedMeasure W {x | radialMass W x < t} = ENNReal.ofReal t ∧
      perimeter volume ⊤ {x | radialMass W x < t} ≠ ⊤ ∧
      ∃ R, frontier {x | radialMass W x < t} ⊆ closedBall 0 R := by
  set f : ℝ → ℝ := fun r => (weightedMeasure W).real (ball (0 : E) r)
  have hrad (x : E) : radialMass W x = f ‖x‖ := by rw [radialMass]
  have hf : Continuous f := by
    simp only [f, measureReal_def]
    refine .ennreal_toReal ?_ fun _ => measure_ne_top _ _
    exact Measure.continuous_measure_ball_of_measure_sphere_eq_zero (weightedMeasure W) 0
      fun r => weightedMeasure_absolutelyContinuous (Measure.addHaar_sphere volume 0 r)
  have hmono : StrictMonoOn f (Ici 0) := fun r hr r' hr' hrr => by
    simp only [f, measureReal_def]
    exact ENNReal.toReal_strict_mono (measure_ne_top _ _)
      (strictMonoOn_weightedMeasure_ball hW.continuous.aemeasurable 0 hr hr' hrr)
  rcases htm.lt_or_eq with htm | rfl
  · -- For `t < μ(E)` the sublevel set is a ball `B(0, r)` with `μ(B(0, r)) = t`.
    have hlim : Tendsto (fun n : ℕ => f n) atTop (𝓝 ((weightedMeasure W).real univ)) := by
      have hb : Monotone fun n : ℕ => ball (0 : E) n := fun m n h =>
        ball_subset_ball (Nat.cast_le.2 h)
      have := tendsto_measure_iUnion_atTop (μ := weightedMeasure W) hb
      rw [iUnion_ball_nat] at this
      exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this
    obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).1 t htm).exists
    obtain ⟨r, ⟨hr0, -⟩, hrt⟩ := intermediate_value_Icc (Nat.cast_nonneg n) hf.continuousOn
      ⟨by simp [f, ht], hn.le⟩
    have hball : {x | radialMass W x < t} = ball 0 r := by
      ext x
      rw [mem_ofPred_eq, mem_ball_zero_iff, ← hrt, hrad]
      exact hmono.lt_iff_lt (norm_nonneg x) hr0
    rw [hball]
    refine ⟨measurableSet_ball, by rw [← hrt, ofReal_measureReal], ?_, r,
      frontier_subset_closure.trans closure_ball_subset_closedBall⟩
    rw [perimeter_ball_eq_ofReal_div_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
  · -- For `t = μ(E)` the sublevel set is the whole space.
    have huniv : {x | radialMass W x < (weightedMeasure W).real univ} = univ :=
      eq_univ_of_forall fun x => radialMass_lt hW.continuous.aemeasurable x
    rw [huniv]
    exact ⟨.univ, (ofReal_measureReal (measure_ne_top _ _)).symm, by simp [perimeter_univ], 0,
      by simp⟩

variable (W) in
/-- The annulus `{x | a ≤ μ(B(0, ‖x‖)) < b}`. -/
private def annulus (a b : ℝ) : Set E :=
  {x | radialMass W x < b} \ {x | radialMass W x < a}

/-- For a `C¹` weight with finite measure and `0 ≤ a ≤ b ≤ μ(E)`, the annulus
`{a ≤ μ(B(0, ‖x‖)) < b}` is measurable, has measure `b − a` and finite weighted perimeter. -/
private theorem annulus_spec (hW : ContDiff ℝ 1 W) [IsFiniteMeasure (weightedMeasure W)]
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ (weightedMeasure W).real univ) :
    MeasurableSet (annulus W a b) ∧ weightedMeasure W (annulus W a b) = ENNReal.ofReal (b - a) ∧
      weightedPerimeter W ⊤ (annulus W a b) < ⊤ := by
  obtain ⟨hAm, hAμ, hAP, R, hR⟩ := setOf_radialMass_lt hW ha (hab.trans hb)
  obtain ⟨hBm, hBμ, hBP, R', hR'⟩ := setOf_radialMass_lt hW (ha.trans hab) hb
  have hsub : {x | radialMass W x < a} ⊆ {x | radialMass W x < b} := fun x hx =>
    lt_of_lt_of_le hx hab
  refine ⟨hBm.diff hAm, ?_, ?_⟩
  · rw [annulus, measure_sdiff hsub hAm.nullMeasurableSet (measure_ne_top _ _), hAμ, hBμ,
      ENNReal.ofReal_sub _ ha]
  -- The frontier lies in the frontiers of the two sublevel sets, on which `e^{−W}` is bounded.
  have hfr : frontier (annulus W a b) ⊆ closedBall 0 (max R R') := by
    rw [annulus, sdiff_eq]
    refine (frontier_inter_subset _ _).trans (union_subset ?_ ?_)
    · exact inter_subset_left.trans (hR'.trans (closedBall_subset_closedBall (le_max_right _ _)))
    · refine inter_subset_right.trans ?_
      rw [frontier_compl]
      exact hR.trans (closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) (max R R')).exists_bound_of_continuousOn
    hW.continuous.neg.rexp.continuousOn
  have hP : perimeter volume ⊤ (annulus W a b) ≠ ⊤ :=
    ((perimeter_diff_le hBm.nullMeasurableSet hAm.nullMeasurableSet).trans_lt
      (ENNReal.add_lt_top.2 ⟨hBP.lt_top, hAP.lt_top⟩)).ne
  have hCb (x : E) (hx : x ∈ frontier (annulus W a b) ∩ (⊤ : TopologicalSpace.Opens E)) :
      Real.exp (-W x) ≤ C := by
    simpa [Real.norm_of_nonneg (Real.exp_pos _).le] using hC x (hfr hx.1)
  exact (weightedPerimeter_le_ofReal_mul_perimeter hW (hBm.diff hAm).nullMeasurableSet
    hCb).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hP.lt_top)

/-- **Clusters with prescribed cell measures.** In dimension at least one, for a `C¹` weight whose
measure `μ` is finite, every nonnegative `v` with `Σ v_i = μ(E)` is the vector of cell measures of
a cluster. The cells are the concentric annuli
`{Σ_{j < i} v_j ≤ μ(B(0, ‖x‖)) < Σ_{j ≤ i} v_j}`. -/
theorem exists_cluster_weightedMeasure_cell_eq (hW : ContDiff ℝ 1 W)
    [IsFiniteMeasure (weightedMeasure W)] (hv : ∀ i, 0 ≤ v i)
    (hsum : ∑ i, v i = (weightedMeasure W).real univ) :
    ∃ Ω : Cluster W q, ∀ i, weightedMeasure W (Ω.cell i) = ENNReal.ofReal (v i) := by
  classical
  -- The partial sums `S k = Σ_{j < k} v_j` increase from `0` to `μ(E)`.
  set S : ℕ → ℝ := fun k => ∑ j ∈ Finset.univ.filter (fun j : Fin q => (j : ℕ) < k), v j
  have hS0 : S 0 = 0 := by simp [S]
  have hSq : S q = (weightedMeasure W).real univ := by simp [S, hsum]
  have hSmono : Monotone S := fun k l hkl =>
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun j hj => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact hj.trans_le hkl)
      fun j _ _ => hv j
  have hSnonneg (k : ℕ) : 0 ≤ S k := Finset.sum_nonneg fun j _ => hv j
  have hSle (k : ℕ) : S k ≤ (weightedMeasure W).real univ :=
    hsum ▸ Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun j _ _ => hv j
  have hSsucc (i : Fin q) : S (i + 1) = S i + v i := by
    have h : Finset.univ.filter (fun j : Fin q => (j : ℕ) < i + 1) =
        insert i (Finset.univ.filter fun j : Fin q => (j : ℕ) < i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    simp only [S, h, Finset.sum_insert (by simp : i ∉ Finset.univ.filter fun j : Fin q =>
      (j : ℕ) < i), add_comm]
  have hspec (i : Fin q) := annulus_spec hW (hSnonneg i) (hSmono (Nat.le_add_right (i : ℕ) 1))
    (hSle (i + 1))
  have hmem (i : Fin q) (x : E) :
      x ∈ annulus W (S i) (S (i + 1)) ↔ radialMass W x ∈ Ico (S i) (S (i + 1)) := by
    simp [annulus, and_comm]
  refine ⟨{ cell := fun i => annulus W (S i) (S (i + 1))
            nullMeasurableSet_cell := fun i => (hspec i).1.nullMeasurableSet
            pairwise_disjoint := fun i j hij => ?_
            volume_compl_iUnion := ?_
            weightedPerimeter_lt_top := fun i => (hspec i).2.2 }, fun i => ?_⟩
  · -- Annuli of distinct indices are disjoint, the intervals of the partial sums being so.
    have hd := hSmono.pairwise_disjoint_on_Ico_succ (Fin.val_injective.ne hij)
    simp only [Function.onFun, Order.succ_eq_add_one] at hd
    exact Set.disjoint_left.2 fun x hxi hxj =>
      Set.disjoint_left.1 hd ((hmem i x).1 hxi) ((hmem j x).1 hxj)
  · -- Every point lies in some annulus: `0 ≤ μ(B(0, ‖x‖)) < μ(E)`.
    rw [show (⋃ i : Fin q, annulus W (S i) (S (i + 1))) = univ from eq_univ_of_forall fun x => ?_,
      compl_univ, measure_empty]
    have hx : radialMass W x ∈ Ico (S 0) (S q) := by
      rw [hS0, hSq]
      refine ⟨?_, radialMass_lt hW.continuous.aemeasurable x⟩
      rw [radialMass]
      exact measureReal_nonneg
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (Ico_subset_biUnion_Ico q S hx)
    exact mem_iUnion.2 ⟨⟨i, Finset.mem_range.1 hi⟩, (hmem _ x).2 hxi⟩
  · rw [(hspec i).2.1, hSsucc i, add_sub_cancel_left]

/-- **Finiteness of the profile.** In dimension at least one, for a `C¹` weight whose measure `μ`
is finite, the isoperimetric profile is finite at every nonnegative `v` with `Σ v_i = μ(E)`. -/
theorem isoperimetricProfile_lt_top (hW : ContDiff ℝ 1 W) [IsFiniteMeasure (weightedMeasure W)]
    (hv : ∀ i, 0 ≤ v i) (hsum : ∑ i, v i = (weightedMeasure W).real univ) :
    isoperimetricProfile W q v < ⊤ :=
  isoperimetricProfile_lt_top_iff.2 (exists_cluster_weightedMeasure_cell_eq hW hv hsum)

end Annuli

end TauCeti
