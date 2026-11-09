/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Order.SuccPred.IntervalSucc

/-!
# Tagged sums for vector measures

Tagged sums on real intervals converge to the vector-measure integral of a continuous
integrand whenever the mesh tends to zero. The integrator may have atoms: the cells are
open on the left and closed on the right, so terminal jumps are retained and the initial
atom is excluded. Repeated partition points and empty partitions are allowed.

The quantitative estimate bounds the error by the oscillation of the integrand on the
cells, times the norm of the bilinear pairing and the variation of the measure. Applying
this to the derivative vector measure of a right-continuous bounded-variation path gives
the usual tagged Riemann–Stieltjes sums. These limits interpret finite-variation terms in
change-of-variables formulas.

## References

* Philip Protter, *Stochastic Integration and Differential Equations*, second edition,
  Chapter I, finite-variation integration.
-/

public section

open MeasureTheory Set Filter Topology
open scoped BigOperators Function

namespace MeasureTheory.VectorMeasure

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {μ : VectorMeasure ℝ F} [IsFiniteMeasure μ.variation]
  {B : E →L[ℝ] F →L[ℝ] G} {f : ℝ → E}

/-- The error of a tagged sum is bounded by the oscillation on each cell, times the
pairing norm and the total variation on the interval. -/
theorem norm_sum_sub_setIntegral_Ioc_le {n : ℕ} {τ ξ : ℕ → ℝ}
    (hτ : Monotone τ) (hf : μ.IntegrableOn f (Ioc (τ 0) (τ n))) {ε : ℝ}
    (hosc : ∀ i < n, ∀ x ∈ Ioc (τ i) (τ (i + 1)), ‖f (ξ i) - f x‖ ≤ ε) :
    ‖(∑ i ∈ Finset.range n, B (f (ξ i)) (μ (Ioc (τ i) (τ (i + 1))))) -
      ∫ᵛ x in Ioc (τ 0) (τ n), f x ∂[B; μ]‖ ≤
        ε * ‖B‖ * μ.variation.real (Ioc (τ 0) (τ n)) := by
  have hcover : (⋃ i ∈ Finset.range n, Ioc (τ i) (τ (i + 1))) = Ioc (τ 0) (τ n) := by
    simpa [Finset.mem_range] using hτ.biUnion_Ico_Ioc_map_succ 0 n
  have hd : Set.Pairwise (↑(Finset.range n))
      (Disjoint on fun i ↦ Ioc (τ i) (τ (i + 1))) :=
    hτ.pairwise_disjoint_on_Ioc_succ.set_pairwise _
  have hfi (i : ℕ) (hi : i ∈ Finset.range n) :
      μ.IntegrableOn f (Ioc (τ i) (τ (i + 1))) :=
    hf.mono measurableSet_Ioc (Ioc_subset_Ioc (hτ (Nat.zero_le _))
      (hτ (by simpa using hi)))
  rw [← hcover, setIntegral_biUnion_finset _ (fun _ _ ↦ measurableSet_Ioc) hd hfi,
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        ‖B (f (ξ i)) (μ (Ioc (τ i) (τ (i + 1)))) -
          ∫ᵛ x in Ioc (τ i) (τ (i + 1)), f x ∂[B; μ]‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, ε * ‖B‖ * μ.variation.real (Ioc (τ i) (τ (i + 1))) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← setIntegral_const, ← integral_sub
        (integrable_const _) (hfi i hi)]
      exact norm_setIntegral_le_of_norm_le_const (hosc i (Finset.mem_range.1 hi))
    _ = ε * ‖B‖ * μ.variation.real (⋃ i ∈ Finset.range n, Ioc (τ i) (τ (i + 1))) := by
      rw [measureReal_biUnion_finset hd (fun _ _ ↦ measurableSet_Ioc)
        (fun _ _ ↦ measure_ne_top _ _), Finset.mul_sum]

/-- Tagged sums for a finite-variation vector measure converge along every family of
partitions with vanishing mesh. Tags may be either endpoint or any point between them. -/
theorem tendsto_sum_tagged_Ioc {ι : Type*} {l : Filter ι} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) {n : ι → ℕ} {τ ξ : ι → ℕ → ℝ}
    (hτ : ∀ k, Monotone (τ k)) (h₀ : ∀ k, τ k 0 = a) (hn : ∀ k, τ k (n k) = b)
    (hξ : ∀ k i, i < n k → ξ k i ∈ Icc (τ k i) (τ k (i + 1)))
    {δ : ι → ℝ} (hmesh : ∀ k i, i < n k → τ k (i + 1) - τ k i ≤ δ k)
    (hδ : Tendsto δ l (𝓝 0)) :
    Tendsto (fun k ↦ ∑ i ∈ Finset.range (n k),
      B (f (ξ k i)) (μ (Ioc (τ k i) (τ k (i + 1))))) l
        (𝓝 (∫ᵛ x in Ioc a b, f x ∂[B; μ])) := by
  -- Uniform continuity controls the cell oscillations; finite variation sums their errors.
  let C := ‖B‖ * μ.variation.real (Ioc a b)
  have hC : 0 ≤ C := by positivity
  have hfi : μ.IntegrableOn f (Ioc a b) := by
    apply (integrable_indicator_iff measurableSet_Ioc).1
    exact (MeasureTheory.integrable_indicator_iff measurableSet_Ioc).2
      ((hf.integrableOn_Icc (μ := μ.variation)).mono_set Ioc_subset_Icc_self)
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨d, hd, hosc⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) (ε / (C + 1)) (by positivity)
  filter_upwards [hδ.eventually (gt_mem_nhds hd)] with k hk
  have hcell (i : ℕ) (hi : i ≤ n k) : τ k i ∈ Icc a b := by
    simpa only [h₀ k, hn k] using (hτ k).mapsTo_Icc ⟨Nat.zero_le i, hi⟩
  have hosc' (i : ℕ) (hi : i < n k) (x : ℝ)
      (hx : x ∈ Ioc (τ k i) (τ k (i + 1))) : ‖f (ξ k i) - f x‖ ≤ ε / (C + 1) := by
    have ht := hξ k i hi
    have hx' : x ∈ Icc a b := ⟨(hcell i hi.le).1.trans hx.1.le,
      hx.2.trans (hcell (i + 1) hi).2⟩
    have ht' : ξ k i ∈ Icc a b := ⟨(hcell i hi.le).1.trans ht.1,
      ht.2.trans (hcell (i + 1) hi).2⟩
    rw [← dist_eq_norm]
    apply (hosc _ ht' _ hx' ?_).le
    rw [Real.dist_eq, abs_lt]
    have hlen := (hmesh k i hi).trans_lt hk
    constructor <;> linarith [ht.1, ht.2, hx.1, hx.2]
  have hfi' : μ.IntegrableOn f (Ioc (τ k 0) (τ k (n k))) := by
    simpa only [h₀ k, hn k] using hfi
  have herr := norm_sum_sub_setIntegral_Ioc_le (B := B) (hτ k) hfi' hosc'
  simp only [h₀ k, hn k] at herr
  rw [dist_eq_norm]
  apply herr.trans_lt
  calc
    ε / (C + 1) * ‖B‖ * μ.variation.real (Ioc a b) = ε / (C + 1) * C := by
      dsimp [C]
      ring
    _ < ε := by
      have hC₁ : 0 < C + 1 := by positivity
      rw [div_mul_eq_mul_div, div_lt_iff₀ hC₁]
      nlinarith [hε]

end MeasureTheory.VectorMeasure

/-- Tagged Riemann–Stieltjes sums for a right-continuous bounded-variation path converge
to its vector-measure integral. No continuity of the integrator across jumps is required.
The interval convention excludes the initial atom and includes the terminal jump. -/
theorem BoundedVariationOn.tendsto_sum_tagged_sub
    {E F G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {g : ℝ → F} (hg : BoundedVariationOn g univ) {f : ℝ → E} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hgr : ∀ x ∈ Icc a b, ContinuousWithinAt g (Ici x) x)
    (B : E →L[ℝ] F →L[ℝ] G) {l : Filter ι} {n : ι → ℕ} {τ ξ : ι → ℕ → ℝ}
    (hτ : ∀ k, Monotone (τ k)) (h₀ : ∀ k, τ k 0 = a) (hn : ∀ k, τ k (n k) = b)
    (hξ : ∀ k i, i < n k → ξ k i ∈ Icc (τ k i) (τ k (i + 1)))
    {δ : ι → ℝ} (hmesh : ∀ k i, i < n k → τ k (i + 1) - τ k i ≤ δ k)
    (hδ : Tendsto δ l (𝓝 0)) :
    Tendsto (fun k ↦ ∑ i ∈ Finset.range (n k),
      B (f (ξ k i)) (g (τ k (i + 1)) - g (τ k i))) l
        (𝓝 (∫ᵛ x in Ioc a b, f x ∂[B; hg.vectorMeasure])) := by
  have hcell (k : ι) (i : ℕ) (hi : i ≤ n k) : τ k i ∈ Icc a b := by
    simpa only [h₀ k, hn k] using (hτ k).mapsTo_Icc ⟨Nat.zero_le i, hi⟩
  have heq (k : ι) :
      (∑ i ∈ Finset.range (n k),
        B (f (ξ k i)) (hg.vectorMeasure (Ioc (τ k i) (τ k (i + 1))))) =
      ∑ i ∈ Finset.range (n k), B (f (ξ k i)) (g (τ k (i + 1)) - g (τ k i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hg.vectorMeasure_Ioc (hτ k (Nat.le_succ i)),
      (hgr _ (hcell k (i + 1) (Finset.mem_range.1 hi))).rightLim_eq,
      (hgr _ (hcell k i (Finset.mem_range.1 hi).le)).rightLim_eq]
  simpa only [heq] using
    (MeasureTheory.VectorMeasure.tendsto_sum_tagged_Ioc (μ := hg.vectorMeasure) (B := B)
      hf hτ h₀ hn hξ hmesh hδ)
