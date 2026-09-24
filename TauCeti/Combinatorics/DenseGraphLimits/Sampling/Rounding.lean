/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.Distance
public import TauCeti.Combinatorics.DenseGraphLimits.Sampling.Exposure
public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.FiniteGraph.Basic
import Mathlib.Probability.ProductMeasure
import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.Triangle
import TauCeti.Combinatorics.DenseGraphLimits.Graphon.OfMatrix
import TauCeti.Probability.McDiarmid

/-!
# Bernoulli edge rounding of a sampled graph

The `W`-random graph `G(n, W)` is produced in two stages. First `n` independent positions `y i` are
drawn from the carrier of the graphon; then every pair `{i, j}` becomes an edge independently, with
probability `W (y i) (y j)`. Between the two stages the sample is the *weighted* graph `H(y, W)` on
`n` equally weighted vertices with edge weights `W (y i) (y j)`, which is the pullback
`W.comap y` of `W` to the uniform carrier on `Fin n`. The second stage rounds every weight to an
edge or a non-edge by an independent coin, and this file shows that the rounding moves the sample
only a little in cut distance: for the padded exposure of `G(n, W)`, whose first coordinates are
the positions,

`P(ε ≤ δ□(G(n, W), H(y, W))) ≤ 2 · 4ⁿ · exp (-(εn - 1)² / 2)` whenever `1 ≤ εn`.

The right-hand side tends to zero as `n → ∞` for every fixed `ε > 0`. It is the rounding half of
the second sampling lemma `δ□(G(n, W), W) → 0`; the other half compares `H(y, W)` with `W` and
involves the positions only.

The proof fixes the positions and a rectangle `S × T` of vertices. The number of edges of the
sample inside `S × T` is then a function of the independent uniform coins of the exposure, and
changing one coin changes it by at most `2`, since a coin decides one pair `{i, j}` and `S × T`
contains at most two orderings of that pair. McDiarmid's inequality makes the count sub-Gaussian
around its mean, the total weight of the off-diagonal pairs of `S × T`. On a finite carrier the
cut norm is attained at a rectangle, so a large cut distance forces a large deviation at one of the
`4ⁿ` rectangles, and a union bound concludes. The diagonal, where the sample has no loops while
`H(y, W)` carries the weights `W (y i) (y i)`, contributes at most `1 / n`: that is the `-1` in the
exponent.

## Main result

* `TauCeti.DenseGraphLimits.exposedSample_cutDist_comap_concentration` — the rounding estimate
  above.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), Chapter 10:
  the `W`-random graphs `H(n, W)` and `G(n, W)`, and the second sampling lemma (Lemma 10.16),
  whose proof passes from `H(n, W)` to `G(n, W)` by this rounding.
* C. McDiarmid, *On the method of bounded differences*, Surveys in Combinatorics 141 (1989),
  148–188.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.unitInterval

open scoped ENNReal NNReal unitInterval

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}

section Deterministic

variable [NeZero n]

open scoped Classical in
/-- A graph on `Fin n` as a graphon on the uniform carrier on `Fin n`. -/
private def finGraphon (G : SimpleGraph (Fin n)) : Graphon (Fin n) (uniformOn Set.univ) :=
  Graphon.ofMatrix _ (fun i j => if G.Adj i j then 1 else 0) fun i j => by
    simp only [G.adj_comm]

open scoped Classical in
private theorem finGraphon_apply (G : SimpleGraph (Fin n)) (i j : Fin n) :
    finGraphon G i j = if G.Adj i j then 1 else 0 := by
  simp [finGraphon, apply_ite Subtype.val]

open scoped Classical in
/-- The graphon of a finite graph is the pullback of its uniform-carrier graphon along the cells of
the unit interval. -/
private theorem finiteGraphGraphon_eq_comap (G : SimpleGraph (Fin n)) :
    finiteGraphGraphon G = (finGraphon G).comap (cellFin n) measurable_cellFin volume := by
  ext x y
  have hcell : ∀ z : I, cellFin n z = ⟨cellIdx n z, cellIdx_lt (NeZero.pos n) z⟩ := fun z =>
    Fin.ext (coe_cellFin z)
  rw [finiteGraphGraphon_apply_fin G (NeZero.pos n), Graphon.comap_apply, finGraphon_apply,
    hcell, hcell]

open scoped Classical in
/-- A graph at cut distance at least `ε` from a graphon on the uniform carrier on `Fin n` has a
rectangle of vertices on which its edge count differs from the total weight by at least `εn²`. -/
private theorem exists_le_abs_sum_of_le_cutDist (W : Graphon Ω μ) (G : SimpleGraph (Fin n))
    (y : Fin n → Ω) {ε : ℝ}
    (h : ε ≤ cutDist (finiteGraphGraphon G)
      (W.comap y (measurable_of_finite y) (uniformOn Set.univ))) :
    ∃ S T : Finset (Fin n),
      ε * n ^ 2 ≤ |∑ i ∈ S, ∑ j ∈ T, ((if G.Adj i j then 1 else 0) - W (y i) (y j))| := by
  rw [finiteGraphGraphon_eq_comap, cutDist_comm,
    cutDist_comap_right (hf := measurePreserving_cellFin), cutDist_comm] at h
  obtain ⟨S, T, hST⟩ := exists_cutNorm_eq_abs_rectIntegral _
    ((finGraphon G).toSymmKernel - (W.comap y (measurable_of_finite y) _).toSymmKernel)
  have hle := (h.trans (cutDist_le_cutNorm_sub _ _)).trans_eq hST
  have hn : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
    positivity
  refine ⟨S.toFinite.toFinset, T.toFinite.toFinset, ?_⟩
  rw [← S.toFinite.coe_toFinset, ← T.toFinite.coe_toFinset, SymmKernel.rectIntegral_uniformOn_univ,
    abs_div, Fintype.card_fin, abs_of_pos hn, le_div_iff₀ hn] at hle
  simpa [finGraphon_apply] using hle

end Deterministic

section Coins

open Classical in
/-- The number of ordered pairs of `S × T` joined in `G`. -/
private def rectEdgeCount (S T : Finset (Fin n)) (G : SimpleGraph (Fin n)) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ T, if G.Adj i j then 1 else 0

/-- The total weight of the off-diagonal pairs of `S × T` at the positions `y`: the mean of
`rectEdgeCount` under the coins. -/
private def rectWeight (W : Graphon Ω μ) (S T : Finset (Fin n)) (y : Fin n → Ω) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ T, if i = j then 0 else W (y i) (y j)

private theorem measurable_rectWeight (W : Graphon Ω μ) (S T : Finset (Fin n)) :
    Measurable (rectWeight W S T) := by
  unfold rectWeight
  refine Finset.measurable_sum S fun i _ => Finset.measurable_sum T fun j _ => ?_
  split_ifs
  · exact measurable_const
  · exact W.measurable.comp (f := fun y : Fin n → Ω => (y i, y j)) (by fun_prop)

/-- The coins of the exposure, indexed by ordered pairs of vertices. -/
private abbrev coinLaw (n : ℕ) : Measure (Fin n × Fin n → ℝ) :=
  Measure.pi fun _ : Fin n × Fin n => Probability.uniformMeasure 0 1

/-- The graph read off positions `y` and a family of coins indexed by ordered pairs. -/
private abbrev coinSample (W : Graphon Ω μ) (y : Fin n → Ω) (u : Fin n × Fin n → ℝ) :
    SimpleGraph (Fin n) :=
  exposedSample W fun i => (y i, fun j => u (i, j))

private theorem measurable_coinSample (W : Graphon Ω μ) (y : Fin n → Ω) :
    Measurable (coinSample W y) :=
  (measurable_exposedSample W).comp (by fun_prop)

/-- A pair `(i, j)` whose designated coin is `p` is one of the two orderings of `p`. -/
private theorem eq_or_swap_eq_of_max_min_eq {p : Fin n × Fin n} {i j : Fin n}
    (h : (max i j, min i j) = p) : (i, j) = p ∨ (i, j) = p.swap := by
  subst h
  rcases le_total i j with hij | hij
  · simp [max_eq_right hij, min_eq_left hij]
  · simp [max_eq_left hij, min_eq_right hij]

/-- Changing one coin changes the edge count of a rectangle by at most `2`. -/
private theorem abs_rectEdgeCount_sub_le (W : Graphon Ω μ) (y : Fin n → Ω) (S T : Finset (Fin n))
    (p : Fin n × Fin n) (u u' : Fin n × Fin n → ℝ) (huu' : ∀ q, q ≠ p → u q = u' q) :
    |rectEdgeCount S T (coinSample W y u) - rectEdgeCount S T (coinSample W y u')| ≤ 2 := by
  classical
  -- only the two orderings of `p` can change adjacency
  set d : Fin n × Fin n → ℝ := fun q =>
    (if (coinSample W y u).Adj q.1 q.2 then 1 else 0) -
      (if (coinSample W y u').Adj q.1 q.2 then 1 else 0) with hd
  have hd0 : ∀ q, q ≠ p → q ≠ p.swap → d q = 0 := by
    intro q hp hs
    have hq : (max q.1 q.2, min q.1 q.2) ≠ p := fun h =>
      (eq_or_swap_eq_of_max_min_eq h).elim hp hs
    simp [hd, huu' _ hq]
  have hd1 : ∀ q, |d q| ≤ 1 := by
    intro q
    simp only [hd]
    split_ifs <;> norm_num
  have hsum : rectEdgeCount S T (coinSample W y u) - rectEdgeCount S T (coinSample W y u') =
      ∑ q ∈ S ×ˢ T, d q := by
    simp only [rectEdgeCount, ← Finset.sum_sub_distrib, Finset.sum_product, hd]
  rw [hsum]
  calc |∑ q ∈ S ×ˢ T, d q| ≤ ∑ q ∈ S ×ˢ T, |d q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q, |d q| := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun q _ _ => abs_nonneg _
    _ = ∑ q ∈ ({p, p.swap} : Finset (Fin n × Fin n)), |d q| := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun q _ hq => ?_).symm
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq
        rw [hd0 q hq.1 hq.2, abs_zero]
    _ ≤ ∑ q ∈ ({p, p.swap} : Finset (Fin n × Fin n)), (1 : ℝ) := Finset.sum_le_sum fun q _ => hd1 q
    _ ≤ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast Finset.card_le_two

private theorem measurableSet_adj_coinSample (W : Graphon Ω μ) (y : Fin n → Ω) (i j : Fin n) :
    MeasurableSet {u | (coinSample W y u).Adj i j} :=
  measurable_coinSample W y
    (MeasurableSet.of_discrete : MeasurableSet {G : SimpleGraph (Fin n) | G.Adj i j})

open Classical in
private theorem ite_adj_coinSample_eq_indicator (W : Graphon Ω μ) (y : Fin n → Ω) (i j : Fin n) :
    (fun u => if (coinSample W y u).Adj i j then (1 : ℝ) else 0) =
      {u | (coinSample W y u).Adj i j}.indicator 1 := by
  ext u
  simp [Set.indicator_apply]

open Classical in
/-- Each coin falls below the weight of its pair with probability that weight. -/
private theorem integral_adj_coinSample (W : Graphon Ω μ) (y : Fin n → Ω) (i j : Fin n) :
    ∫ u, (if (coinSample W y u).Adj i j then (1 : ℝ) else 0) ∂coinLaw n =
      if i = j then 0 else W (y i) (y j) := by
  rw [ite_adj_coinSample_eq_indicator,
    integral_indicator_one (measurableSet_adj_coinSample W y i j)]
  split_ifs with hij
  · subst hij
    simp
  · have hset : {u | (coinSample W y u).Adj i j} =
        Function.eval (max i j, min i j) ⁻¹' Set.Iio (W (y i) (y j)) := by
      ext u
      simp [coinSample, hij]
    rw [hset, measureReal_def, (measurePreserving_eval _ (max i j, min i j)).measure_preimage
      measurableSet_Iio.nullMeasurableSet,
      Probability.uniformMeasure_Iio zero_lt_one (W.le_one _ _)]
    simp [W.nonneg]

/-- The mean edge count of a rectangle is its off-diagonal weight. -/
private theorem integral_rectEdgeCount (W : Graphon Ω μ) (y : Fin n → Ω) (S T : Finset (Fin n)) :
    ∫ u, rectEdgeCount S T (coinSample W y u) ∂coinLaw n = rectWeight W S T y := by
  classical
  have hint : ∀ i j, Integrable
      (fun u => if (coinSample W y u).Adj i j then (1 : ℝ) else 0) (coinLaw n) := fun i j => by
    rw [ite_adj_coinSample_eq_indicator]
    exact (integrable_const 1).indicator (measurableSet_adj_coinSample W y i j)
  simp only [rectEdgeCount, rectWeight]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j]
  exact Finset.sum_congr rfl fun j _ => integral_adj_coinSample W y i j

/-- **Rounding one rectangle at fixed positions.** The edge count of a rectangle deviates from its
mean by `s` with probability at most `2 exp (-s² / (2n²))`: McDiarmid's inequality over the `n²`
coins, each of which moves the count by at most `2`. -/
private theorem coinLaw_le_abs_rectEdgeCount_sub_le (W : Graphon Ω μ) (y : Fin n → Ω)
    (S T : Finset (Fin n)) {s : ℝ} (hs : 0 ≤ s) :
    coinLaw n {u | s ≤ |rectEdgeCount S T (coinSample W y u) - rectWeight W S T y|} ≤
      ENNReal.ofReal (2 * Real.exp (-s ^ 2 / (2 * n ^ 2))) := by
  set f : (Fin n × Fin n → ℝ) → ℝ := fun u => rectEdgeCount S T (coinSample W y u)
  have hf : Measurable f :=
    (measurable_of_finite (rectEdgeCount S T)).comp (measurable_coinSample W y)
  have hsub := Probability.hasSubgaussianMGF_of_bounded_differences
    (Probability.uniformMeasure 0 1) f hf (fun _ => 2)
    fun p u u' h => abs_rectEdgeCount_sub_le W y S T p u u' h
  have hmean : ∫ u, f u ∂coinLaw n = rectWeight W S T y := integral_rectEdgeCount W y S T
  rw [hmean] at hsub
  have hσ : ((∑ _ : Fin n × Fin n, (2 : ℝ).toNNReal ^ 2 / 4 : ℝ≥0) : ℝ) = n ^ 2 := by
    simp [Finset.card_univ, Fintype.card_prod, sq]
    ring
  have htail : ∀ t : Set (Fin n × Fin n → ℝ),
      (coinLaw n).real t ≤ Real.exp (-s ^ 2 / (2 * n ^ 2)) →
        coinLaw n t ≤ ENNReal.ofReal (Real.exp (-s ^ 2 / (2 * n ^ 2))) := fun t ht => by
    rw [← ofReal_measureReal (measure_ne_top _ t)]
    exact ENNReal.ofReal_le_ofReal ht
  have h₁ := htail _ ((hsub.measure_ge_le hs).trans_eq (by rw [hσ]))
  have h₂ := htail _ ((hsub.neg.measure_ge_le hs).trans_eq (by rw [hσ]))
  calc coinLaw n {u | s ≤ |f u - rectWeight W S T y|}
      ≤ coinLaw n ({u | s ≤ f u - rectWeight W S T y} ∪
          {u | s ≤ (-fun u => f u - rectWeight W S T y) u}) := by
        refine measure_mono fun u (hu : s ≤ |f u - rectWeight W S T y|) => ?_
        rcases le_abs'.mp hu with h | h
        · exact Or.inr (by simp only [Pi.neg_apply, Set.mem_ofPred_eq]; linarith)
        · exact Or.inl h
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add h₁ h₂
    _ = ENNReal.ofReal (2 * Real.exp (-s ^ 2 / (2 * n ^ 2))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, ← two_mul]

open Classical in
/-- The loopless graph and the weights differ on the diagonal only, so replacing the rectangle sum
of `1_G - W` by the deviation of the edge count from its off-diagonal weight costs at most `n`. -/
private theorem abs_sum_sub_sub_le (W : Graphon Ω μ) (G : SimpleGraph (Fin n)) (y : Fin n → Ω)
    (S T : Finset (Fin n)) :
    |(∑ i ∈ S, ∑ j ∈ T, ((if G.Adj i j then 1 else 0) - W (y i) (y j))) -
        (rectEdgeCount S T G - rectWeight W S T y)| ≤ n := by
  have heq : (∑ i ∈ S, ∑ j ∈ T, ((if G.Adj i j then 1 else 0) - W (y i) (y j))) -
      (rectEdgeCount S T G - rectWeight W S T y) =
        -∑ i ∈ S, ∑ j ∈ T, if i = j then W (y i) (y j) else 0 := by
    simp only [rectEdgeCount, rectWeight, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  rw [heq, abs_neg]
  calc |∑ i ∈ S, ∑ j ∈ T, if i = j then W (y i) (y j) else 0|
      ≤ ∑ i ∈ S, ∑ j ∈ T, if i = j then (1 : ℝ) else 0 := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        split_ifs
        · rw [abs_of_nonneg (W.nonneg _ _)]
          exact W.le_one _ _
        · simp
    _ ≤ ∑ _i ∈ S, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        rw [Finset.sum_ite_eq]
        split_ifs <;> norm_num
    _ ≤ n := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast (Finset.card_le_univ S).trans_eq (Fintype.card_fin n)

/-- The positions and the rows of coins of the exposure, as the two factors of a product. -/
private abbrev rowLaw (n : ℕ) : Measure (Fin n → Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => Probability.uniformMeasure 0 1

/-- The event that the edge count of the rectangle `S × T` deviates from its off-diagonal weight
by at least `s`, on the product of the positions and the rows of coins. -/
private def rectEvent (W : Graphon Ω μ) (s : ℝ) (S T : Finset (Fin n)) :
    Set ((Fin n → Ω) × (Fin n → Fin n → ℝ)) :=
  {z | s ≤ |rectEdgeCount S T (exposedSample W fun i => (z.1 i, z.2 i)) - rectWeight W S T z.1|}

private theorem measurableSet_rectEvent (W : Graphon Ω μ) (s : ℝ) (S T : Finset (Fin n)) :
    MeasurableSet (rectEvent W s S T) :=
  measurableSet_le measurable_const (continuous_abs.measurable.comp (Measurable.sub
    ((measurable_of_finite (rectEdgeCount S T)).comp
      ((measurable_exposedSample W).comp (by fun_prop)))
    ((measurable_rectWeight W S T).comp measurable_fst)))

/-- **Rounding one rectangle.** The rectangle event has probability at most
`2 exp (-s² / (2n²))`, uniformly in the positions. -/
private theorem prod_rectEvent_le (W : Graphon Ω μ) {s : ℝ} (hs : 0 ≤ s) (S T : Finset (Fin n)) :
    ((Measure.pi fun _ : Fin n => μ).prod (rowLaw n)) (rectEvent W s S T) ≤
      ENNReal.ofReal (2 * Real.exp (-s ^ 2 / (2 * n ^ 2))) := by
  have hcurry : (coinLaw n).map (MeasurableEquiv.curry (Fin n) (Fin n) ℝ) = rowLaw n := by
    simpa only [Measure.infinitePi_eq_pi] using
      Measure.infinitePi_map_curry fun (_ : Fin n) (_ : Fin n) => Probability.uniformMeasure 0 1
  rw [Measure.prod_apply (measurableSet_rectEvent W s S T)]
  calc ∫⁻ y, rowLaw n (Prod.mk y ⁻¹' rectEvent W s S T) ∂(Measure.pi fun _ : Fin n => μ)
      ≤ ∫⁻ _y, ENNReal.ofReal (2 * Real.exp (-s ^ 2 / (2 * n ^ 2)))
          ∂(Measure.pi fun _ : Fin n => μ) := lintegral_mono fun y => by
        rw [← hcurry, MeasurableEquiv.map_apply]
        exact coinLaw_le_abs_rectEdgeCount_sub_le W y S T hs
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

/-- A sampled graph at cut distance at least `ε` from its weighted graph lies in the rectangle event
of some rectangle, at deviation `n (εn - 1)`: the exposure is read as positions and rows of coins
through `MeasurableEquiv.arrowProdEquivProdArrow`. -/
private theorem setOf_le_cutDist_subset_iUnion_rectEvent [NeZero n] (W : Graphon Ω μ) (ε : ℝ) :
    {x | ε ≤ cutDist (finiteGraphGraphon (exposedSample W x))
        (W.comap (fun i => (x i).1) (measurable_of_finite _) (uniformOn Set.univ))} ⊆
      ⋃ ST : Finset (Fin n) × Finset (Fin n),
        MeasurableEquiv.arrowProdEquivProdArrow Ω (Fin n → ℝ) (Fin n) ⁻¹'
          rectEvent W (n * (ε * n - 1)) ST.1 ST.2 := by
  classical
  intro x hx
  obtain ⟨S, T, hST⟩ := exists_le_abs_sum_of_le_cutDist W _ _ hx
  refine Set.mem_iUnion.2 ⟨(S, T), ?_⟩
  -- `MeasurableEquiv.arrowProdEquivProdArrow` has no evaluation lemma; it splits `x` into its two
  -- families of coordinates by definition
  have he : MeasurableEquiv.arrowProdEquivProdArrow Ω (Fin n → ℝ) (Fin n) x =
      (fun i => (x i).1, fun i => (x i).2) := rfl
  rw [Set.mem_preimage, he]
  simp only [rectEvent, Set.mem_ofPred_eq, Prod.mk.eta]
  have hdiag := abs_sum_sub_sub_le W (exposedSample W x) (fun i => (x i).1) S T
  have htri := abs_sub_abs_le_abs_sub
    (∑ i ∈ S, ∑ j ∈ T, ((if (exposedSample W x).Adj i j then 1 else 0) - W (x i).1 (x j).1))
    (rectEdgeCount S T (exposedSample W x) - rectWeight W S T fun i => (x i).1)
  linarith

/-- **Bernoulli edge rounding.** Sample `G(n, W)` through its padded exposure `x`, whose first
coordinates `(x i).1` are the positions of the vertices. The sampled graph is at cut distance at
least `ε` from the weighted graph `H(y, W)` — the pullback of `W` along the positions to the
uniform carrier on `Fin n` — with probability at most `2 · 4ⁿ · exp (-(εn - 1)² / 2)`, as soon as
`1 ≤ εn`. -/
theorem exposedSample_cutDist_comap_concentration [NeZero n] (W : Graphon Ω μ) {ε : ℝ}
    (hε : 1 ≤ ε * n) :
    (exposureMeasure μ n).real {x | ε ≤ cutDist (finiteGraphGraphon (exposedSample W x))
        (W.comap (fun i => (x i).1) (measurable_of_finite _) (uniformOn Set.univ))} ≤
      2 * 4 ^ n * Real.exp (-(ε * n - 1) ^ 2 / 2) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hs : 0 ≤ (n : ℝ) * (ε * n - 1) := mul_nonneg hn.le (by linarith)
  have hexp : -((n : ℝ) * (ε * n - 1)) ^ 2 / (2 * n ^ 2) = -(ε * n - 1) ^ 2 / 2 := by
    field_simp
  have hmp := measurePreserving_arrowProdEquivProdArrow Ω (Fin n → ℝ) (Fin n) (fun _ => μ)
    (fun _ => Measure.pi fun _ : Fin n => Probability.uniformMeasure 0 1)
  rw [exposureMeasure_def]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  calc _ ≤ _ := measure_mono (setOf_le_cutDist_subset_iUnion_rectEvent W ε)
    _ ≤ _ := measure_iUnion_fintype_le _ _
    _ = ∑ ST : Finset (Fin n) × Finset (Fin n),
          ((Measure.pi fun _ : Fin n => μ).prod (rowLaw n))
            (rectEvent W (n * (ε * n - 1)) ST.1 ST.2) :=
      Finset.sum_congr rfl fun ST _ =>
        hmp.measure_preimage (measurableSet_rectEvent W _ ST.1 ST.2).nullMeasurableSet
    _ ≤ ∑ _ST : Finset (Fin n) × Finset (Fin n),
          ENNReal.ofReal (2 * Real.exp (-(ε * n - 1) ^ 2 / 2)) :=
      Finset.sum_le_sum fun ST _ => (prod_rectEvent_le W hs ST.1 ST.2).trans_eq (by rw [hexp])
    _ = ENNReal.ofReal (2 * 4 ^ n * Real.exp (-(ε * n - 1) ^ 2 / 2)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_finset,
        Fintype.card_fin, nsmul_eq_mul, show (2 : ℝ) * 4 ^ n * Real.exp _ =
          ((2 ^ n * 2 ^ n : ℕ) : ℝ) * (2 * Real.exp (-(ε * n - 1) ^ 2 / 2)) by
            push_cast
            rw [← mul_pow]
            ring,
        ENNReal.ofReal_mul (p := ((2 ^ n * 2 ^ n : ℕ) : ℝ)) (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]

end Coins

end DenseGraphLimits

end TauCeti
