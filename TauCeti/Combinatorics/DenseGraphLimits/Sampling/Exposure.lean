/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Sampling.Finite
public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Oscillation
public import TauCeti.Probability.Distributions.Uniform
public import TauCeti.Combinatorics.SimpleGraph.Measurable

/-!
# The padded vertex exposure of a sampled graph

The finite sampling law `sampleGraph W n` is defined by its masses, so it does not present the
sampled graph as a function of independent coordinates. A bounded-differences inequality needs
exactly such a presentation: a product of independent coordinates, together with a bound on how
much the estimator moves when one coordinate changes. Changing one sampled vertex position alone
is not such a coordinate, because the edges at that vertex also carry their own independent
randomness.

The *padded exposure* supplies the product structure. Each of the `n` vertices carries its
position in the graphon's carrier together with a full row of `n` independent uniform coins, and
the exposure source is the `n`-fold product of these vertex coordinates. The edge `{i, j}` reads
its coin from one designated row: row `max i j`, column `min i j`, and it is present when that coin
falls below the graphon value at the two positions. Every coin on or above the diagonal is
padding that no edge reads. Since every edge reads a coin carried by one of its endpoints,
changing the coordinate of one vertex changes only the pairs at that vertex.

The two results of the file make this a genuine representation of `G(n, W)`:

* the law identification: the exposure source pushed through the exposed graph is the finite
  sampling law. At fixed positions the event that the exposed graph is a prescribed pattern is a
  box in the coins, whose uniform product is the conditional mass `sampleIntegrand W H`;
* the oscillation bound: changing one vertex coordinate moves the ordinary homomorphism density
  of the exposed graph by at most `|V(F)| / n`.

## Main definitions

* `TauCeti.DenseGraphLimits.exposureMeasure` — the product source of positions and coin rows;
* `TauCeti.DenseGraphLimits.exposedSample` — the graph read off an exposure.

## Main results

* `exposedSample_adj` — the designated-row rule for the edges;
* `map_exposedSample` — the exposure source induces the finite sampling law;
* `exposedSample_update_adj_iff` — updating one vertex coordinate only changes pairs at it;
* `abs_homDensityFin_exposedSample_update_le` — the bounded-differences estimate.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §10.1.
* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0, `Graphon/SampleExposure.lean`. The
  padded exposure source, the designated-row convention, the law identification and the `q / n`
  oscillation bound are formalized there. The construction here is adapted to Tau Ceti's strict
  graphon carrier and uses the uniform coin `TauCeti.Probability.uniformMeasure 0 1` and the strict
  comparison of the joint sampler `infiniteSampleLaw`; the law identification evaluates the mass of
  a single pattern as a box of coin intervals, and the oscillation bound is derived from a
  host-graph statement, `SimpleGraph.abs_homDensityFin_sub_le_of_adj_iff`.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

section Source

variable (μ) in
/-- The **exposure source** of the `n`-vertex sampled graph: `n` independent vertex coordinates,
each a position drawn from `μ` together with a row of `n` independent uniform coins on the unit
interval. -/
def exposureMeasure (n : ℕ) : Measure (Fin n → Ω × (Fin n → ℝ)) :=
  Measure.pi fun _ : Fin n => μ.prod (Measure.pi fun _ : Fin n => Probability.uniformMeasure 0 1)

omit [IsProbabilityMeasure μ] in
variable (μ) in
/-- The defining product of the exposure source. -/
theorem exposureMeasure_def (n : ℕ) :
    exposureMeasure μ n =
      Measure.pi fun _ : Fin n =>
        μ.prod (Measure.pi fun _ : Fin n => Probability.uniformMeasure 0 1) := (rfl)

instance exposureMeasure_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (exposureMeasure μ n) := by
  rw [exposureMeasure_def]
  infer_instance

end Source

section Graph

variable {n : ℕ}

/-- The **exposed sampled graph**: the pair `{i, j}` is an edge exactly when the coin in row
`max i j`, column `min i j` falls below the graphon value at the two positions. Every edge reads a
coin carried by one of its endpoints, so changing one vertex coordinate changes only the pairs at
that vertex. -/
def exposedSample (W : Graphon Ω μ) (x : Fin n → Ω × (Fin n → ℝ)) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ (x (max i j)).2 (min i j) < W (x i).1 (x j).1
  symm := ⟨fun i j h => ⟨h.1.symm, by rw [max_comm, min_comm, W.symm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- **The designated-row rule.** The edge `{i, j}` of the exposed graph is present exactly when the
coin in row `max i j`, column `min i j` falls below the graphon value at the two positions. -/
@[simp]
theorem exposedSample_adj (W : Graphon Ω μ) (x : Fin n → Ω × (Fin n → ℝ)) (i j : Fin n) :
    (exposedSample W x).Adj i j ↔ i ≠ j ∧ (x (max i j)).2 (min i j) < W (x i).1 (x j).1 :=
  Iff.rfl

/-- The exposed graph depends measurably on the exposure. -/
theorem measurable_exposedSample (W : Graphon Ω μ) :
    Measurable (exposedSample (n := n) W) := by
  rw [SimpleGraph.measurable_iff_adj]
  intro i j
  refine measurableSet_setOfPred.mp ?_
  by_cases hij : i = j
  · simp [hij]
  · have hcoin : Measurable fun x : Fin n → Ω × (Fin n → ℝ) => (x (max i j)).2 (min i j) :=
      (measurable_pi_apply _).comp (measurable_snd.comp (measurable_pi_apply _))
    have hvalue : Measurable fun x : Fin n → Ω × (Fin n → ℝ) => W (x i).1 (x j).1 :=
      W.measurable.comp ((measurable_fst.comp (measurable_pi_apply _)).prodMk
        (measurable_fst.comp (measurable_pi_apply _)))
    simpa [hij] using measurableSet_lt hcoin hvalue

/-- Updating the coordinate of the vertex `i` leaves every pair avoiding `i` unchanged: such a pair
reads its positions and its coin from vertices other than `i`. -/
theorem exposedSample_update_adj_iff (W : Graphon Ω μ) (x : Fin n → Ω × (Fin n → ℝ)) (i : Fin n)
    (y : Ω × (Fin n → ℝ)) {a b : Fin n} (ha : a ≠ i) (hb : b ≠ i) :
    (exposedSample W (Function.update x i y)).Adj a b ↔ (exposedSample W x).Adj a b := by
  have hmax : max a b ≠ i := by
    rcases max_choice a b with h | h <;> rw [h] <;> assumption
  simp only [exposedSample_adj, Function.update_of_ne ha, Function.update_of_ne hb,
    Function.update_of_ne hmax]

end Graph

section Law

variable {n : ℕ}

open Classical in
/-- The coins that make the exposed graph equal to the pattern `H` at the pair read from row `r`,
column `s`. Only the coins below the diagonal are read; the others are padding and unconstrained. -/
private def coinBox (W : Graphon Ω μ) (y : Fin n → Ω) (H : SimpleGraph (Fin n)) (r s : Fin n) :
    Set ℝ :=
  if s < r then {t | t < W (y r) (y s) ↔ H.Adj r s} else Set.univ

/-- At fixed positions, the exposed graph is the pattern `H` exactly when every coin lies in its
box. -/
private theorem setOfPred_exposedSample_eq (W : Graphon Ω μ) (y : Fin n → Ω)
    (H : SimpleGraph (Fin n)) :
    {c : Fin n → Fin n → ℝ | exposedSample W (fun i => (y i, c i)) = H} =
      Set.univ.pi fun r => Set.univ.pi fun s => coinBox W y H r s := by
  ext c
  simp only [Set.mem_ofPred_eq, Set.mem_univ_pi, coinBox]
  constructor
  · rintro rfl r s
    split_ifs with hsr
    · simp [hsr.ne', max_eq_left hsr.le, min_eq_right hsr.le]
    · trivial
  · intro h
    ext a b
    simp only [exposedSample_adj]
    rcases lt_trichotomy a b with hab | rfl | hab
    · have hba := h b a
      simp only [hab, ↓reduceIte] at hba
      rw [max_eq_right hab.le, min_eq_left hab.le, W.symm, H.adj_comm]
      simpa [hab.ne] using hba
    · simp
    · have hab' := h a b
      simp only [hab, ↓reduceIte] at hab'
      rw [max_eq_left hab.le, min_eq_right hab.le]
      simpa [hab.ne'] using hab'

open Classical in
/-- The uniform product of the coin boxes is the conditional mass of the pattern at the positions:
the boxes below the diagonal correspond to the pairs of `Fin n`, each contributing the graphon
value or its complement, and the padding boxes contribute `1`. -/
private theorem pi_pi_coinBox (W : Graphon Ω μ) (y : Fin n → Ω) (H : SimpleGraph (Fin n)) :
    (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => Probability.uniformMeasure 0 1)
        (Set.univ.pi fun r => Set.univ.pi fun s => coinBox W y H r s) =
      ENNReal.ofReal (sampleIntegrand W H y) := by
  set g : Sym2 (Fin n) → ℝ := fun e =>
    if e ∈ H.edgeFinset then edgeFactor W y e else 1 - edgeFactor W y e with hg
  have hbox : ∀ r s, Probability.uniformMeasure 0 1 (coinBox W y H r s) =
      if s < r then ENNReal.ofReal (g s(r, s)) else 1 := by
    intro r s
    rw [coinBox]
    split_ifs with hsr
    · by_cases hrs : H.Adj r s
      · have hset : {t : ℝ | t < W (y r) (y s) ↔ H.Adj r s} = Set.Iio (W (y r) (y s)) := by
          ext t
          simp [hrs]
        rw [hset, Probability.uniformMeasure_Iio zero_lt_one (W.le_one _ _)]
        simp [hg, SimpleGraph.mem_edgeFinset, hrs]
      · have hset : {t : ℝ | t < W (y r) (y s) ↔ H.Adj r s} = Set.Ici (W (y r) (y s)) := by
          ext t
          simp [hrs, not_lt]
        rw [hset, Probability.uniformMeasure_Ici zero_lt_one (W.nonneg _ _)]
        simp [hg, SimpleGraph.mem_edgeFinset, hrs]
    · exact measure_univ
  have hnonneg : ∀ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, 0 ≤ g e := by
    intro e _
    have h₀ := edgeFactor_nonneg W y e
    have h₁ := edgeFactor_le_one W y e
    simp only [hg]
    split_ifs <;> linarith
  simp_rw [Measure.pi_pi, hbox]
  rw [sampleIntegrand_eq_prod_edgeFinset_top, ENNReal.ofReal_prod_of_nonneg hnonneg,
    ← Finset.prod_product' (s := Finset.univ) (t := Finset.univ)
      (f := fun r s => if s < r then ENNReal.ofReal (g s(r, s)) else 1),
    ← Finset.prod_filter]
  refine Finset.prod_nbij (fun p => s(p.1, p.2)) ?_ ?_ ?_ ?_
  · intro p hp
    simpa using (Finset.mem_filter.mp hp).2.ne'
  · intro p hp q hq hpq
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    rcases Sym2.eq_iff.mp hpq with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Prod.ext h₁ h₂
    · exact absurd (hp'.trans (h₂ ▸ h₁ ▸ hq')) (lt_irrefl _)
  · intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : a ≠ b := by simpa using he
      rcases hab.lt_or_gt with h | h
      · exact ⟨(b, a), by simp [h], Sym2.eq_swap⟩
      · exact ⟨(a, b), by simp [h], rfl⟩
  · intro p _
    rfl

/-- **The law identification of the exposure.** Pushing the exposure source through the exposed
graph gives the finite sampling law `G(n, W)`: the exposure is a representation of the sampled
graph by independent vertex coordinates. -/
@[simp]
theorem map_exposedSample (W : Graphon Ω μ) (n : ℕ) :
    (exposureMeasure μ n).map (exposedSample W) = sampleGraph W n := by
  refine Measure.ext_of_singleton fun H => ?_
  set ν : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => Probability.uniformMeasure 0 1
  have hmp := measurePreserving_arrowProdEquivProdArrow Ω (Fin n → ℝ) (Fin n) (fun _ => μ)
    (fun _ => ν)
  have hfiber : MeasurableSet (exposedSample (n := n) W ⁻¹' {H}) :=
    measurable_exposedSample W (measurableSet_singleton H)
  rw [Measure.map_apply (measurable_exposedSample W) (measurableSet_singleton H),
    exposureMeasure_def, ← hmp.symm.measure_preimage_equiv,
    Measure.prod_apply (hfiber.preimage (by fun_prop)), sampleGraph_singleton]
  have hslice : ∀ y : Fin n → Ω,
      Prod.mk y ⁻¹' ((MeasurableEquiv.arrowProdEquivProdArrow Ω (Fin n → ℝ) (Fin n)).symm ⁻¹'
        (exposedSample W ⁻¹' {H})) =
      {c : Fin n → Fin n → ℝ | exposedSample W (fun i => (y i, c i)) = H} := fun _ => rfl
  simp_rw [hslice, setOfPred_exposedSample_eq, ν, pi_pi_coinBox]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_sampleIntegrand W H)
      (Filter.Eventually.of_forall (sampleIntegrand_nonneg W H)), sampleMass_def]

end Law

section Oscillation

variable {V : Type*} [Fintype V]

/-- **The bounded-differences estimate of the exposure.** Changing the coordinate of one exposed
vertex moves the ordinary homomorphism density of the exposed graph by at most `|V(F)| / n`. -/
theorem abs_homDensityFin_exposedSample_update_le (F : SimpleGraph V) (W : Graphon Ω μ) {n : ℕ}
    (x : Fin n → Ω × (Fin n → ℝ)) (i : Fin n) (y : Ω × (Fin n → ℝ)) :
    |homDensityFin F (exposedSample W (Function.update x i y)) -
        homDensityFin F (exposedSample W x)| ≤ (Fintype.card V : ℝ) / n := by
  simpa using F.abs_homDensityFin_sub_le_of_adj_iff i
    fun a b ha hb => exposedSample_update_adj_iff W x i y ha hb

end Oscillation

end DenseGraphLimits

end TauCeti
