/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.UniformOn
public import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.Distance
import Mathlib.Probability.Independence.InfinitePi
import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.OfMatrixGrid
import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.Triangle
import TauCeti.Combinatorics.DenseGraphLimits.Graphon.StandardBorelModel
import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.Approximation
import TauCeti.MeasureTheory.MeasurableSpace.Finpartition
import TauCeti.Probability.Moments.Pi
import TauCeti.Probability.Process.EmpiricalMeasure

/-!
# Point sampling of a graphon

Draw `n + 1` independent points `y 0, …, y n` of the carrier of a graphon `W`. The **`W`-random
weighted graph** `H(y, W)` has vertex set `Fin (n + 1)`, all vertices of weight `1 / (n + 1)`,
and edge weights `W (y i) (y j)`; as a graphon it is the pullback `W.comap y` of `W` to the
uniform carrier on `Fin (n + 1)`. This file proves that it converges to `W` in cut distance in
probability:

`P(ε ≤ δ□(H(y, W), W)) → 0` as `n → ∞`, for every `ε > 0`,

over an arbitrary probability carrier. Together with the Bernoulli edge rounding
(`TauCeti.DenseGraphLimits.exposedSample_cutDist_comap_concentration`), which compares `H(y, W)`
with the sampled simple graph `G(n, W)`, it gives the second sampling lemma
`TauCeti.DenseGraphLimits.sampleGraph_cutDist_tendsto_inProbability`: `δ□(G(n, W), W) → 0` in
probability.

The proof compares `W` with a step graphon `U` close to it in `L¹`.

* Sampling does not increase the `L¹` distance on average: the expected `L¹` distance between the
  sampled graphs `H(y, W)` and `H(y, U)` is at most `‖W - U‖₁ + 1 / (n + 1)`, the `1 / (n + 1)`
  accounting for the diagonal pairs `(y i, y i)`. By Markov's inequality `H(y, W)` and `H(y, U)`
  are close with high probability.
* The sample `H(y, U)` of a step graphon is again a weighted graph with the same block values,
  whose vertex weights are the empirical frequencies of the blocks among the sample points.
  Changing the vertex weights of a weighted graph costs at most twice their `ℓ¹` distance
  (`TauCeti.DenseGraphLimits.cutDist_ofMatrix_le_two_mul_sum_abs`), and the frequencies
  concentrate at the block measures by the weak law of large numbers
  (`TauCeti.meas_ge_le_variance_div_card_mul_sq_pi`).

On a countably generated carrier the block averages along a refining sequence of finite partitions
converge to `W` in `L¹` (`TauCeti.DenseGraphLimits.tendsto_eLpNorm_countableStepGraphonAvg`), which
supplies `U`; an arbitrary graphon is the pullback of one on the Cantor space
(`TauCeti.DenseGraphLimits.Graphon.exists_comap_natBool`), and the sampled graphs pull back along.

## Main result

* `TauCeti.DenseGraphLimits.cutDist_comap_tendsto_inProbability` — the weighted sampled graph
  `H(y, W)` converges to `W` in cut distance in probability.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §10.1 and
  Lemma 10.16: the `W`-random weighted graphs `H(n, W)` and the second sampling lemma.
* C. Borgs, J. Chayes, L. Lovász, V. Sós, K. Vesztergombi, *Convergent sequences of dense graphs
  I: Subgraph frequencies, metric properties and testing*, Adv. Math. 219 (2008), 1801–1851,
  §4: sampling from a graphon.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory TauCeti.Probability

open scoped ENNReal Topology

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

section Sampled

variable {n : ℕ} [NeZero n]

/-- The cut distance of two sampled weighted graphs on the same sample points is at most their
`L¹` distance, the average of `|U - W|` over the `n²` pairs of sample points. -/
private theorem cutDist_comap_comap_le (U W : Graphon Ω μ) (y : Fin n → Ω) :
    cutDist (U.comap y (measurable_of_finite y) (uniformOn Set.univ))
        (W.comap y (measurable_of_finite y) (uniformOn Set.univ)) ≤
      (∑ a, ∑ b, |U (y a) (y b) - W (y a) (y b)|) / (n : ℝ) ^ 2 := by
  classical
  set K := (U.comap y (measurable_of_finite y) (uniformOn Set.univ)).toSymmKernel -
    (W.comap y (measurable_of_finite y) (uniformOn Set.univ)).toSymmKernel
  let A : SymmKernel (Fin n) (uniformOn Set.univ) :=
    ⟨fun a b => |K a b|, fun a b => by rw [K.symm],
      continuous_abs.measurable.comp K.measurable,
      by obtain ⟨C, hC⟩ := K.exists_bound
         exact ⟨C, fun a b => by simpa only [abs_abs] using hC a b⟩⟩
  refine (cutDist_le_cutNorm_sub _ _).trans
    ((cutNorm_le_integral_abs _ K).trans ?_)
  have hsum := SymmKernel.rectIntegral_uniformOn_univ A Finset.univ Finset.univ
  exact le_of_eq (by simpa [SymmKernel.rectIntegral_univ_univ, A, K] using hsum)

/-- **Sampling does not increase the `L¹` distance on average.** The expected `L¹` distance between
the sampled weighted graphs of `U` and `W` is at most `‖U - W‖₁ + 1 / n`: two distinct sample
points are independent, so each off-diagonal pair contributes exactly `‖U - W‖₁`, and the `n`
diagonal pairs contribute at most `1` each. -/
private theorem integral_sum_abs_sub_div_le (U W : Graphon Ω μ) :
    ∫ y, (∑ a : Fin n, ∑ b, |U (y a) (y b) - W (y a) (y b)|) / (n : ℝ) ^ 2
        ∂(Measure.pi fun _ => μ) ≤
      ∫ p, |U p.1 p.2 - W p.1 p.2| ∂(μ.prod μ) + 1 / n := by
  set L := ∫ p, |U p.1 p.2 - W p.1 p.2| ∂(μ.prod μ)
  have hL : 0 ≤ L := integral_nonneg fun _ => abs_nonneg _
  have hf : Measurable fun p : Ω × Ω => |U p.1 p.2 - W p.1 p.2| :=
    continuous_abs.measurable.comp (U.measurable.sub W.measurable)
  have hbound : ∀ x x' : Ω, |U x x' - W x x'| ≤ 1 := fun x x' =>
    abs_sub_le_iff.2 ⟨by linarith [U.le_one x x', W.nonneg x x'],
      by linarith [W.le_one x x', U.nonneg x x']⟩
  have hint : ∀ a b : Fin n, Integrable (fun y : Fin n → Ω => |U (y a) (y b) - W (y a) (y b)|)
      (Measure.pi fun _ => μ) := fun a b => by
    have hm : Measurable fun y : Fin n → Ω => |U (y a) (y b) - W (y a) (y b)| :=
      Measurable.comp (f := fun y : Fin n → Ω => (y a, y b)) hf
        ((measurable_pi_apply a).prodMk (measurable_pi_apply b))
    exact (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs, abs_abs]; exact hbound _ _)
  have hterm : ∀ a b : Fin n,
      ∫ y, |U (y a) (y b) - W (y a) (y b)| ∂(Measure.pi fun _ => μ) ≤
        L + if a = b then 1 else 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab
      have h1 : ∫ y, |U (y a) (y a) - W (y a) (y a)| ∂(Measure.pi fun _ => μ) ≤ 1 :=
        (integral_mono (hint a a) (integrable_const 1) fun y => hbound _ _).trans_eq (by simp)
      simp only [ite_true]
      linarith
    · have hmap : (Measure.pi fun _ : Fin n => μ).map (fun y => (y a, y b)) = μ.prod μ := by
        rw [← Measure.infinitePi_eq_pi]
        exact Measure.infinitePi_map_eval_prod hab
      have h := integral_map (μ := Measure.pi fun _ : Fin n => μ)
        (φ := fun y : Fin n → Ω => (y a, y b)) (by fun_prop)
        (f := fun p : Ω × Ω => |U p.1 p.2 - W p.1 p.2|)
        (by rw [hmap]; exact hf.aestronglyMeasurable)
      rw [hmap] at h
      simp only [hab, ite_false, add_zero]
      exact h.symm.le
  have hdiag : ∑ a : Fin n, ∑ b : Fin n, (L + if a = b then (1 : ℝ) else 0) = n ^ 2 * L + n := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, nsmul_eq_mul]
    ring
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  rw [integral_div, integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hint a b]
  simp_rw [integral_finsetSum _ fun b _ => hint _ b]
  calc (∑ a : Fin n, ∑ b, ∫ y, |U (y a) (y b) - W (y a) (y b)| ∂(Measure.pi fun _ => μ)) /
        (n : ℝ) ^ 2
      ≤ (n ^ 2 * L + n) / (n : ℝ) ^ 2 := by
        rw [← hdiag]
        gcongr with a _ b _
        exact hterm a b
    _ = L + 1 / n := by field_simp

/-- The sampled weighted graph of a graphon that factors through a measurable map `g` into a finite
discrete space is within twice the `ℓ¹` distance between the empirical law of `g` on the sample
points and the law of `g`. Both graphons are weighted graphs with the same block values on the
values of `g`, with these two laws as vertex weights. -/
private theorem cutDist_comap_le_of_factorsThrough {κ : Type*} [Fintype κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (U : Graphon Ω μ) {g : Ω → κ} (hg : Measurable g)
    (hfac : ∀ x x' z z', g x = g z → g x' = g z' → U x x' = U z z') (y : Fin n → Ω) :
    cutDist (U.comap y (measurable_of_finite y) (uniformOn Set.univ)) U ≤
      2 * ∑ k, |((uniformOn Set.univ : Measure (Fin n)).map (g ∘ y)).real {k} -
        (μ.map g).real {k}| := by
  set ν : Measure κ := (uniformOn Set.univ : Measure (Fin n)).map (g ∘ y)
  obtain ⟨b, hb, hU⟩ := exists_ofMatrix_eq_comap_of_factorsThrough (ν := μ.map g) U hg hfac
  have hmp₁ : MeasurePreserving (g ∘ y) (uniformOn Set.univ) ν := ⟨measurable_of_finite _, rfl⟩
  have hmp₂ : MeasurePreserving g μ (μ.map g) := ⟨hg, rfl⟩
  have hsample : U.comap y (measurable_of_finite y) (uniformOn Set.univ) =
      (Graphon.ofMatrix ν b hb).comap (g ∘ y) hmp₁.measurable (uniformOn Set.univ) := by
    ext a c
    rw [hU]
    simp
  calc cutDist (U.comap y (measurable_of_finite y) (uniformOn Set.univ)) U
      = cutDist ((Graphon.ofMatrix ν b hb).comap (g ∘ y) hmp₁.measurable (uniformOn Set.univ))
          ((Graphon.ofMatrix (μ.map g) b hb).comap g hmp₂.measurable μ) := by
        rw [hsample]
        conv_lhs => rw [hU]
    _ = cutDist (Graphon.ofMatrix ν b hb) (Graphon.ofMatrix (μ.map g) b hb) := by
        rw [cutDist_comap_right _ _ hmp₂, cutDist_comm, cutDist_comap_right _ _ hmp₁,
          cutDist_comm]
    _ ≤ _ := cutDist_ofMatrix_le_two_mul_sum_abs b hb

/-- **The block frequencies of a sample concentrate.** For a graphon that factors through a
measurable map `g` into a finite discrete space with `c` points, the sampled weighted graph is at
cut distance at least `η` from it with probability at most `c³ / (n η²)`: each of the `c` block
frequencies is an average of `n` independent indicators, of variance at most `1 / 4`. -/
private theorem measureReal_le_cutDist_comap_le_of_factorsThrough {κ : Type*} [Fintype κ]
    [MeasurableSpace κ] [MeasurableSingletonClass κ] (U : Graphon Ω μ) {g : Ω → κ}
    (hg : Measurable g) (hfac : ∀ x x' z z', g x = g z → g x' = g z' → U x x' = U z z')
    {η : ℝ} (hη : 0 < η) :
    (Measure.pi fun _ : Fin n => μ).real
        {y | η ≤ cutDist (U.comap y (measurable_of_finite y) (uniformOn Set.univ)) U} ≤
      (Fintype.card κ : ℝ) ^ 3 / (n * η ^ 2) := by
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure μ
  have : Nonempty κ := ⟨g x₀⟩
  set c : ℝ := (Fintype.card κ : ℝ)
  have hc : 0 < c := Nat.cast_pos.2 Fintype.card_pos
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  -- The frequency of the block `k` is the average of the indicator statistic `f k`.
  set f : κ → Ω → ℝ := fun k x => ({k} : Set κ).indicator 1 (g x)
  have hfm : ∀ k, Measurable (f k) := fun k =>
    (measurable_of_countable (({k} : Set κ).indicator (1 : κ → ℝ))).comp hg
  have hf01 : ∀ k x, f k x ∈ Set.Icc (0 : ℝ) 1 := fun k x => by
    by_cases hx : g x = k <;> simp [f, hx]
  have hfreq : ∀ (y : Fin n → Ω) k,
      ((uniformOn Set.univ : Measure (Fin n)).map (g ∘ y)).real {k} =
        (∑ i, f k (y i)) / Fintype.card (Fin n) := fun y k => by
    rw [← integral_indicator_one (measurableSet_singleton k),
      ← empiricalMeasureOfFintype_eq_map_uniformOn,
      integral_empiricalMeasureOfFintype (measurable_of_countable _).stronglyMeasurable,
      smul_eq_mul, inv_mul_eq_div]
    simp only [f, Function.comp_apply]
  have hmean : ∀ k, (μ.map g).real {k} = ∫ x, f k x ∂μ := fun k => by
    rw [← integral_indicator_one (measurableSet_singleton k),
      integral_map hg.aemeasurable (measurable_of_countable _).aestronglyMeasurable]
  -- A large cut distance forces one block frequency to deviate by `η / (2c)`.
  have hsub : {y : Fin n → Ω | η ≤ cutDist (U.comap y (measurable_of_finite y)
      (uniformOn Set.univ)) U} ⊆ ⋃ k, {y | η / (2 * c) ≤
        |(∑ i, f k (y i)) / Fintype.card (Fin n) - ∫ x, f k x ∂μ|} := by
    intro y hy
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hnot
    have hlt : ∑ k, |((uniformOn Set.univ : Measure (Fin n)).map (g ∘ y)).real {k} -
        (μ.map g).real {k}| < ∑ _k : κ, η / (2 * c) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun k _ => by
        rw [hfreq, hmean]
        exact hnot k
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hlt
    have hcη : c * (η / (2 * c)) = η / 2 := by field_simp
    have := cutDist_comap_le_of_factorsThrough U hg hfac y
    simp only [Set.mem_ofPred_eq] at hy
    linarith
  -- Each deviation is controlled by the weak law of large numbers.
  have hdev : ∀ k, (Measure.pi fun _ : Fin n => μ).real {y | η / (2 * c) ≤
      |(∑ i, f k (y i)) / Fintype.card (Fin n) - ∫ x, f k x ∂μ|} ≤ c ^ 2 / (n * η ^ 2) := by
    intro k
    have hvar : Var[f k; μ] ≤ 1 / 4 := by
      have := variance_le_sq_of_bounded (ae_of_all μ (hf01 k)) (hfm k).aemeasurable
      norm_num at this
      exact this
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    refine (meas_ge_le_variance_div_card_mul_sq_pi
      (memLp_of_bounded (ae_of_all μ (hf01 k)) (hfm k).aestronglyMeasurable 2)
      (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [Fintype.card_fin]
    calc Var[f k; μ] / (n * (η / (2 * c)) ^ 2) ≤ 1 / 4 / (n * (η / (2 * c)) ^ 2) := by gcongr
      _ = c ^ 2 / (n * η ^ 2) := by field_simp; ring
  calc (Measure.pi fun _ : Fin n => μ).real _
      ≤ (Measure.pi fun _ : Fin n => μ).real (⋃ k, {y | η / (2 * c) ≤
          |(∑ i, f k (y i)) / Fintype.card (Fin n) - ∫ x, f k x ∂μ|}) := measureReal_mono hsub
    _ ≤ ∑ k, (Measure.pi fun _ : Fin n => μ).real {y | η / (2 * c) ≤
          |(∑ i, f k (y i)) / Fintype.card (Fin n) - ∫ x, f k x ∂μ|} :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ _k : κ, c ^ 2 / (n * η ^ 2) := Finset.sum_le_sum fun k _ => hdev k
    _ = c ^ 3 / (n * η ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- **Point sampling against a step approximation.** If `U` factors through a measurable map into a
finite discrete space with `c` points and is within `L < ε / 3` of `W` in `L¹`, the sampled
weighted graph of `W` is at cut distance at least `ε` from `W` with probability at most
`3 (L + 1 / n) / ε + 9 c³ / (n ε²)`. -/
private theorem measureReal_le_cutDist_comap_le {κ : Type*} [Fintype κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (W U : Graphon Ω μ) {g : Ω → κ} (hg : Measurable g)
    (hfac : ∀ x x' z z', g x = g z → g x' = g z' → U x x' = U z z') {ε : ℝ} (hε : 0 < ε)
    (hUW : ∫ p, |U p.1 p.2 - W p.1 p.2| ∂(μ.prod μ) < ε / 3) :
    (Measure.pi fun _ : Fin n => μ).real
        {y | ε ≤ cutDist (W.comap y (measurable_of_finite y) (uniformOn Set.univ)) W} ≤
      3 * (∫ p, |U p.1 p.2 - W p.1 p.2| ∂(μ.prod μ) + 1 / n) / ε +
        9 * (Fintype.card κ : ℝ) ^ 3 / (n * ε ^ 2) := by
  set L := ∫ p, |U p.1 p.2 - W p.1 p.2| ∂(μ.prod μ)
  set D : (Fin n → Ω) → ℝ := fun y => (∑ a, ∑ b, |U (y a) (y b) - W (y a) (y b)|) / (n : ℝ) ^ 2
  have hη : 0 < ε / 3 := by positivity
  -- A large cut distance splits between the two sampled graphs and the two samples.
  have hsub : {y : Fin n → Ω | ε ≤ cutDist (W.comap y (measurable_of_finite y)
      (uniformOn Set.univ)) W} ⊆ {y | ε / 3 ≤ D y} ∪
        {y | ε / 3 ≤ cutDist (U.comap y (measurable_of_finite y) (uniformOn Set.univ)) U} := by
    intro y hy
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hnot hy
    have h₁ := cutDist_triangle (W.comap y (measurable_of_finite y) (uniformOn Set.univ))
      (U.comap y (measurable_of_finite y) (uniformOn Set.univ)) W
    have h₂ := cutDist_triangle (U.comap y (measurable_of_finite y) (uniformOn Set.univ)) U W
    have h₃ := cutDist_comap_comap_le U W y
    rw [cutDist_comm] at h₃
    have h₄ := (cutDist_le_cutNorm_sub U W).trans (cutNorm_le_integral_abs μ _)
    simp only [SymmKernel.coe_sub, Pi.sub_apply, Graphon.coe_toSymmKernel] at h₄
    linarith
  -- Markov's inequality for the sampled `L¹` distance.
  have hD : (Measure.pi fun _ : Fin n => μ).real {y | ε / 3 ≤ D y} ≤ 3 * (L + 1 / n) / ε := by
    have hint : Integrable D (Measure.pi fun _ : Fin n => μ) := by
      refine (integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => ?_).div_const _
      have hm : Measurable fun y : Fin n → Ω => |U (y a) (y b) - W (y a) (y b)| :=
        Measurable.comp (f := fun y : Fin n → Ω => (y a, y b))
          (continuous_abs.measurable.comp (U.measurable.sub W.measurable))
          ((measurable_pi_apply a).prodMk (measurable_pi_apply b))
      exact (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_abs]
        exact abs_sub_le_iff.2 ⟨by linarith [U.le_one (y a) (y b), W.nonneg (y a) (y b)],
          by linarith [W.le_one (y a) (y b), U.nonneg (y a) (y b)]⟩)
    have hmarkov := mul_meas_ge_le_integral_of_nonneg
      (ae_of_all _ fun y => div_nonneg (Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => abs_nonneg _) (sq_nonneg _)) hint (ε / 3)
    have hE := integral_sum_abs_sub_div_le (n := n) U W
    rw [le_div_iff₀ hε]
    nlinarith
  calc (Measure.pi fun _ : Fin n => μ).real _
      ≤ (Measure.pi fun _ : Fin n => μ).real ({y | ε / 3 ≤ D y} ∪
          {y | ε / 3 ≤ cutDist (U.comap y (measurable_of_finite y) (uniformOn Set.univ)) U}) :=
        measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ 3 * (L + 1 / n) / ε + (Fintype.card κ : ℝ) ^ 3 / (n * (ε / 3) ^ 2) :=
        add_le_add hD (measureReal_le_cutDist_comap_le_of_factorsThrough U hg hfac hη)
    _ = _ := by ring

end Sampled

/-- Point sampling on a countably generated carrier, where block averages along the canonical
refining finite partitions approximate the graphon in `L¹`. -/
private theorem cutDist_comap_tendsto_inProbability_of_countablyGenerated
    [MeasurableSpace.CountablyGenerated Ω] (W : Graphon Ω μ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin (n + 1) => μ).real
      {y | ε ≤ cutDist (W.comap y (measurable_of_finite y) (uniformOn Set.univ)) W})
      atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.2 fun δ hδ => ?_
  -- A block average `L¹`-close to `W`.
  set τ := min (ε / 3) (ε * δ / 12)
  have hτ : 0 < τ := lt_min (by positivity) (by positivity)
  obtain ⟨k, hk⟩ := ((tendsto_eLpNorm_countableStepGraphonAvg W).eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.2 hτ))).exists
  set U := countableStepGraphonAvg W k
  have hL : ∫ p, |U p.1 p.2 - W p.1 p.2| ∂(μ.prod μ) < τ := by
    have h := ENNReal.toReal_lt_of_lt_ofReal hk
    rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm
      (f := (fun z : Ω × Ω => U z.1 z.2) - fun z : Ω × Ω => W z.1 z.2)
      (U.measurable.sub W.measurable).aestronglyMeasurable] at h
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using h
  -- It factors through the part index of its partition.
  set P := Finpartition.countablePartition Ω k
  have hP : ∀ p ∈ P.parts, MeasurableSet p :=
    fun _ hp => Finpartition.measurableSet_of_mem_countablePartition Ω k hp
  let _ : MeasurableSpace P.parts := ⊤
  have : MeasurableSingletonClass P.parts := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hg : Measurable P.indexedPartition.index :=
    Finpartition.measurable_indexedPartition_index P hP
  have hfac : ∀ x x' z z', P.indexedPartition.index x = P.indexedPartition.index z →
      P.indexedPartition.index x' = P.indexedPartition.index z' → U x x' = U z z' := by
    intro x x' z z' hx hx'
    simp only [U, countableStepGraphonAvg_apply]
    rw [stepGraphonAvg_apply P hP W (P.indexedPartition.mem_index x)
        (P.indexedPartition.mem_index x'),
      stepGraphonAvg_apply P hP W (P.indexedPartition.mem_index z)
        (P.indexedPartition.mem_index z'), hx, hx']
  -- The sampling error beyond `3 L / ε` decays like `1 / n`.
  set A := 3 / ε + 9 * (Fintype.card P.parts : ℝ) ^ 3 / ε ^ 2 with hAdef
  have hA : 0 ≤ A := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * A / δ)
  refine ⟨N, fun n hn => ?_⟩
  have hn1 : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hbound := measureReal_le_cutDist_comap_le (n := n + 1) W U hg hfac hε
    (hL.trans_le (min_le_left _ _))
  have hsplit : 3 * (∫ p, |U p.1 p.2 - W p.1 p.2| ∂(μ.prod μ) + 1 / ((n + 1 : ℕ) : ℝ)) / ε +
      9 * (Fintype.card P.parts : ℝ) ^ 3 / (((n + 1 : ℕ) : ℝ) * ε ^ 2) =
      3 * (∫ p, |U p.1 p.2 - W p.1 p.2| ∂(μ.prod μ)) / ε + A / ((n + 1 : ℕ) : ℝ) := by
    rw [hAdef]
    field_simp
    ring
  have hfirst : 3 * (∫ p, |U p.1 p.2 - W p.1 p.2| ∂(μ.prod μ)) / ε < δ / 4 := by
    rw [div_lt_iff₀ hε]
    nlinarith [min_le_right (ε / 3) (ε * δ / 12)]
  have hsecond : A / ((n + 1 : ℕ) : ℝ) < δ / 2 := by
    rw [div_lt_iff₀ hn1]
    have : (N : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.lt_succ_of_le hn
    rw [div_lt_iff₀ hδ] at hN
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  linarith

/-- **Point sampling converges in cut distance, in probability.** Sample `n + 1` independent
points `y` of the carrier of a graphon `W`. The weighted graph `H(y, W)` on `Fin (n + 1)` with
uniform vertex weights and edge weights `W (y i) (y j)` — the pullback of `W` to the uniform
carrier on `Fin (n + 1)` —
is at cut distance at least `ε` from `W` with probability tending to zero as `n → ∞`, for every
`ε > 0`. The carrier is an arbitrary probability space. -/
theorem cutDist_comap_tendsto_inProbability (W : Graphon Ω μ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin (n + 1) => μ).real
      {y | ε ≤ cutDist (W.comap y (measurable_of_finite y) (uniformOn Set.univ)) W})
      atTop (𝓝 0) := by
  -- Reduce to the Cantor space, where the carrier is countably generated.
  obtain ⟨q, hq, V, rfl⟩ := W.exists_comap_natBool
  have hmp : MeasurePreserving q μ (μ.map q) := ⟨hq, rfl⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (cutDist_comap_tendsto_inProbability_of_countablyGenerated V hε)
    (fun _ => measureReal_nonneg) fun n => ?_
  have hset : {y : Fin (n + 1) → Ω | ε ≤ cutDist ((V.comap q hq μ).comap y (measurable_of_finite y)
      (uniformOn Set.univ)) (V.comap q hq μ)} = (fun y i => q (y i)) ⁻¹'
        {z | ε ≤ cutDist (V.comap z (measurable_of_finite z) (uniformOn Set.univ)) V} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [cutDist_comap_right _ _ hmp]
    congr! 2
    ext a b
    simp
  have hmeas : Measurable fun (y : Fin (n + 1) → Ω) (i : Fin (n + 1)) => q (y i) :=
    measurable_pi_iff.2 fun i => hq.comp (measurable_pi_apply i)
  have hmap : (Measure.pi fun _ : Fin (n + 1) => μ).map (fun y i => q (y i)) =
      Measure.pi fun _ => μ.map q := Measure.pi_map_pi fun _ => hq.aemeasurable
  rw [hset, measureReal_def, measureReal_def, ← hmap]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (Measure.le_map_apply hmeas.aemeasurable _)

end DenseGraphLimits

end TauCeti
