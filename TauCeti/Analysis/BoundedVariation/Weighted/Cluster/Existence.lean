/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Cluster.Profile
import TauCeti.Analysis.BoundedVariation.Weighted.Compactness
import TauCeti.Analysis.BoundedVariation.Weighted.LowerSemicontinuity
import TauCeti.MeasureTheory.OuterMeasure.SymmDiff
import TauCeti.Topology.Instances.ENNReal

/-!
# Existence of minimizing clusters

Let `W` be a `C¹` weight on a finite-dimensional real inner product space `E` whose measure
`μ = e^{−W} · volume` is finite. Whenever the isoperimetric profile `I_μ^{(q−1)}(v)`
(`TauCeti.isoperimetricProfile`) is finite, some `q`-cluster with cell measures `v` attains it
(`TauCeti.exists_cluster_perimeter_eq_isoperimetricProfile_of_ne_top`). In dimension at least
one the profile is finite at every nonnegative `v` with `Σ v_i = μ(E)`, so minimizing clusters
exist for all such `v` (`TauCeti.exists_cluster_perimeter_eq_isoperimetricProfile`); when `μ` is
a probability measure, these are the points of the probability simplex `Δ^{(q−1)}`.

The proof is the direct method. Along a minimizing sequence of clusters every cell has weighted
perimeter at most twice the total perimeter of the first cluster, so by compactness
(`TauCeti.exists_subseq_forall_tendsto_withDensity_symmDiff_of_weightedPerimeter_le`) the cells
converge in `L¹(μ)` along a common subsequence. The limits keep the cell measures and are
disjoint up to null sets, so a null modification of them is a cluster
(`TauCeti.exists_cluster_ae_eq`); lower semicontinuity of the weighted perimeter
(`TauCeti.weightedPerimeter_le_liminf_of_tendsto_weightedMeasure_symmDiff`) and superadditivity of
the lower limit bound its total perimeter by the profile.

The proof uses finiteness of `μ` for compactness, which fails for infinite measures: for the
weight `0` on `ℝ`, the intervals `(k, k + 1)` all have measure `1` and perimeter `2`, but no
subsequence converges in `L¹`.

## References

* E. Milman, J. Neeman, *The Gaussian double-bubble and multi-bubble conjectures*, Ann. of Math.
  (2022), Theorem 4.1 (i).
* F. Maggi, *Sets of finite perimeter and geometric variational problems*, Cambridge University
  Press (2012), Part IV.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology symmDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {W : E → ℝ} {q : ℕ} {v : Fin q → ℝ}

/-- **A minimizing sequence.** If the isoperimetric profile at `v` is finite, there are clusters
with cell measures `v` whose total perimeters decrease to the profile. -/
private theorem exists_seq_cluster_tendsto_isoperimetricProfile
    (h : isoperimetricProfile W q v ≠ ⊤) :
    ∃ Ω : ℕ → Cluster W q, (∀ n i, weightedMeasure W ((Ω n).cell i) = ENNReal.ofReal (v i)) ∧
      Antitone (fun n => (Ω n).perimeter) ∧
      Tendsto (fun n => (Ω n).perimeter) atTop (𝓝 (isoperimetricProfile W q v)) := by
  set S : Set ℝ≥0∞ := {c | ∃ Ω : Cluster W q,
    (∀ i, weightedMeasure W (Ω.cell i) = ENNReal.ofReal (v i)) ∧ Ω.perimeter = c}
  have hS : isoperimetricProfile W q v = sInf S :=
    le_antisymm (le_sInf fun _ ⟨Ω, hΩ, hc⟩ => hc ▸ isoperimetricProfile_le Ω hΩ)
      (le_isoperimetricProfile_iff.2 fun Ω hΩ => sInf_le ⟨Ω, hΩ, rfl⟩)
  obtain ⟨Ω₀, hΩ₀⟩ := isoperimetricProfile_lt_top_iff.1 (lt_top_iff_ne_top.2 h)
  obtain ⟨u, hu, hlim, hmem⟩ := exists_seq_tendsto_sInf (S := S) ⟨Ω₀.perimeter, Ω₀, hΩ₀, rfl⟩
    (OrderBot.bddBelow S)
  choose Ω hΩ hΩu using hmem
  have hΩu' : (fun n => (Ω n).perimeter) = u := funext hΩu
  exact ⟨Ω, hΩ, hΩu' ▸ hu, hΩu' ▸ hS ▸ hlim⟩

/-- **Limits of cells.** For a `C¹` weight with finite measure, clusters `Ω n` with cell measures
`v` whose cells have weighted perimeters at most `M` have, along a common subsequence `φ`, cells
converging in `L¹(μ)` to measurable sets `t i`. The limits keep the cell measures and pairwise
meet in null sets. -/
private theorem exists_subseq_tendsto_cell (hW : ContDiff ℝ 1 W)
    [IsFiniteMeasure (weightedMeasure W)] {Ω : ℕ → Cluster W q}
    (hΩ : ∀ n i, weightedMeasure W ((Ω n).cell i) = ENNReal.ofReal (v i)) {M : ℝ≥0}
    (hM : ∀ i n, weightedPerimeter W ⊤ ((Ω n).cell i) ≤ M) :
    ∃ t : Fin q → Set E, (∀ i, MeasurableSet (t i)) ∧
      (∀ i, weightedMeasure W (t i) = ENNReal.ofReal (v i)) ∧
      (Pairwise fun i k => volume (t i ∩ t k) = 0) ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ i, Tendsto (fun j => weightedMeasure W ((Ω (φ j)).cell i ∆ t i)) atTop (𝓝 0) := by
  have : IsFiniteMeasure (volume.withDensity fun x => ENNReal.ofReal (Real.exp (-W x))) := by
    rw [← weightedMeasure_def]
    infer_instance
  obtain ⟨t, ht, φ, hφ, hconv⟩ :=
    exists_subseq_forall_tendsto_withDensity_symmDiff_of_weightedPerimeter_le hW
      (s := fun i n => (Ω n).cell i) (fun i n => (Ω n).nullMeasurableSet_cell i) hM
  simp only [← weightedMeasure_def] at hconv
  refine ⟨t, ht, fun i => ?_, fun i k hik => ?_, φ, hφ, hconv⟩
  · -- The limits keep the cell measures.
    exact TauCeti.MeasureTheory.measure_eq_of_tendsto_measure_symmDiff
      (.of_forall fun j => hΩ (φ j) i) (hconv i)
  · -- The limits of distinct cells meet in a null set, the cells being disjoint.
    have hsub (j : ℕ) : t i ∩ t k ⊆ (Ω (φ j)).cell i ∆ t i ∪ (Ω (φ j)).cell k ∆ t k := by
      intro x hx
      by_cases hxi : x ∈ (Ω (φ j)).cell i
      · exact .inr (Set.mem_symmDiff.2 (.inr ⟨hx.2,
          Set.disjoint_left.1 ((Ω (φ j)).pairwise_disjoint hik) hxi⟩))
      · exact .inl (Set.mem_symmDiff.2 (.inr ⟨hx.1, hxi⟩))
    refine volume_absolutelyContinuous_weightedMeasure hW.continuous.aemeasurable
      (nonpos_iff_eq_zero.1 ?_)
    simpa using ge_of_tendsto' ((hconv i).add (hconv k)) fun j =>
      (measure_mono (hsub j)).trans (measure_union_le _ _)

/-- **Existence of minimizing clusters for a finite profile.** For a `C¹` weight whose measure
`μ = e^{−W} · volume` is finite, if the isoperimetric profile at `v` is finite, that is some
`q`-cluster has the cell measures `v`, then some `q`-cluster with these cell measures attains the
profile. -/
theorem exists_cluster_perimeter_eq_isoperimetricProfile_of_ne_top (hW : ContDiff ℝ 1 W)
    [IsFiniteMeasure (weightedMeasure W)] (h : isoperimetricProfile W q v ≠ ⊤) :
    ∃ Ω : Cluster W q, (∀ i, weightedMeasure W (Ω.cell i) = ENNReal.ofReal (v i)) ∧
      Ω.perimeter = isoperimetricProfile W q v := by
  obtain ⟨Ω, hΩ, hanti, hlim⟩ := exists_seq_cluster_tendsto_isoperimetricProfile h
  -- Every cell along the sequence has weighted perimeter at most `M = 2 P_μ(Ω 0)`.
  have hsum (n : ℕ) : ∑ i, weightedPerimeter W ⊤ ((Ω n).cell i) = 2 * (Ω n).perimeter := by
    rw [Cluster.perimeter_def, ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top]
  set M : ℝ≥0 := (2 * (Ω 0).perimeter).toNNReal
  have hM (i : Fin q) (n : ℕ) : weightedPerimeter W ⊤ ((Ω n).cell i) ≤ M := by
    rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (Ω 0).perimeter_lt_top.ne),
      ← hsum]
    refine (Finset.single_le_sum (fun j _ => zero_le) (Finset.mem_univ i)).trans
      (((hsum n).trans_le ?_).trans_eq (hsum 0).symm)
    gcongr
    exact hanti (Nat.zero_le n)
  obtain ⟨t, ht, hmeas, hdisj, φ, hφ, hconv⟩ := exists_subseq_tendsto_cell hW hΩ hM
  -- Lower semicontinuity bounds the perimeters of the limits.
  have hlsc (i : Fin q) : weightedPerimeter W ⊤ (t i) ≤
      liminf (fun j => weightedPerimeter W ⊤ ((Ω (φ j)).cell i)) atTop :=
    weightedPerimeter_le_liminf_of_tendsto_weightedMeasure_symmDiff hW.contDiffOn
      (.of_forall fun j => ((Ω (φ j)).nullMeasurableSet_cell i).mono Measure.restrict_le_self)
      (ht i).nullMeasurableSet (hconv i)
  have htot : ∑ i, weightedPerimeter W ⊤ (t i) ≤ 2 * isoperimetricProfile W q v := by
    have hlim' : Tendsto (fun j => ∑ i, weightedPerimeter W ⊤ ((Ω (φ j)).cell i)) atTop
        (𝓝 (2 * isoperimetricProfile W q v)) := by
      simpa only [hsum, Function.comp_apply] using
        ENNReal.Tendsto.const_mul (hlim.comp hφ.tendsto_atTop) (Or.inr ENNReal.ofNat_ne_top)
    exact (Finset.sum_le_sum fun i _ => hlsc i).trans
      ((ENNReal.sum_liminf_le_liminf_sum _ _).trans_eq hlim'.liminf_eq)
  -- A null modification of the limits is a cluster attaining the profile.
  obtain ⟨Ω', hΩ'⟩ := exists_cluster_ae_eq hW.continuous.aemeasurable
    (fun i => (ht i).nullMeasurableSet) hdisj
    (by rw [← (Ω 0).sum_weightedMeasure_cell]; simp [hmeas, hΩ])
    fun i => ((hlsc i).trans ((liminf_le_liminf (.of_forall fun j => hM i (φ j))).trans_eq
      (liminf_const (M : ℝ≥0∞)))).trans_lt ENNReal.coe_lt_top
  have hμ' (i : Fin q) : weightedMeasure W (Ω'.cell i) = ENNReal.ofReal (v i) := by
    rw [measure_congr (weightedMeasure_absolutelyContinuous.ae_le (hΩ' i)), hmeas]
  refine ⟨Ω', hμ', le_antisymm ?_ (isoperimetricProfile_le Ω' hμ')⟩
  have hcell (i : Fin q) : weightedPerimeter W ⊤ (Ω'.cell i) = weightedPerimeter W ⊤ (t i) :=
    weightedPerimeter_congr_ae (by simpa using hΩ' i)
  rw [Cluster.perimeter_def, ENNReal.div_le_iff two_ne_zero ENNReal.ofNat_ne_top, mul_comm]
  simpa only [hcell] using htot

/-- **Existence of minimizing clusters.** In dimension at least one, for a `C¹` weight whose
measure `μ = e^{−W} · volume` is finite and every nonnegative `v` with `Σ v_i = μ(E)`, some
`q`-cluster with cell measures `v` attains the isoperimetric profile at `v`. When `μ` is a
probability measure, this holds at every point `v` of the probability simplex `Δ^{(q−1)}`. -/
theorem exists_cluster_perimeter_eq_isoperimetricProfile [Nontrivial E] (hW : ContDiff ℝ 1 W)
    [IsFiniteMeasure (weightedMeasure W)] (hv : ∀ i, 0 ≤ v i)
    (hsum : ∑ i, v i = (weightedMeasure W).real univ) :
    ∃ Ω : Cluster W q, (∀ i, weightedMeasure W (Ω.cell i) = ENNReal.ofReal (v i)) ∧
      Ω.perimeter = isoperimetricProfile W q v :=
  exists_cluster_perimeter_eq_isoperimetricProfile_of_ne_top hW
    (isoperimetricProfile_lt_top hW hv hsum).ne

end TauCeti
