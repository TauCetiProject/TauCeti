/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Extreme
public import TauCeti.Probability.Exchangeability.Arrays.Windows
public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Coordinates
public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Infinite
public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Dissociated

/-!
# Exchangeable graph laws as jointly exchangeable array laws

An exchangeable law on infinite graphs is the law of a symmetric `Bool`-valued array with `false`
on the diagonal, jointly exchangeable under simultaneous relabelling of both axes. This file is the
law-level adapter between the two: the array law `arrayLaw μ` of a law on graphs, the graph law
`graphLawOfArray ρ` of a law on arrays, the bundled equivalence `graphLawArrayLawEquiv` between
exchangeable laws on infinite graphs and the jointly exchangeable probability laws carried by the
symmetric `false`-diagonal arrays, and the dissociation compatibility that lets the array theory
speak about graph laws.

* **Dissociation.** The finite law attached to `L` is dissociated exactly when its array law is
  jointly dissociated (`isDissociated_iff_jointlyDissociated`). The graph notion is independence
  of two consecutive label windows; the array notion is independence of the arrays read along
  disjoint index sets; for a jointly exchangeable law consecutive windows suffice
  (`indepFun_restrict_of_forall_Ico`), and each window of a graph is the block restriction of its
  array.
* **Convex mixtures.** The array law is the pushforward along the adjacency array, so it is linear
  in the measure (`Measure.map_add`, `Measure.map_smul`), and the array laws of graph laws are
  exactly the jointly exchangeable probability laws carried by the symmetric `false`-diagonal
  arrays. Extremality among those laws is joint dissociation
  (`jointlyDissociated_iff_mem_extremePoints_on`), so dissociation of a graph law is extremality of
  its array law (`isDissociated_iff_arrayLaw_mem_extremePoints`).

The carrier-level encoding is the edge-coordinate equivalence `graphCoordEquiv`, read as an array
by placing `false` on the diagonal; decoding is `SimpleGraph.fromRel` of the array. The finite
graphs on `Fin n` are read on the block `[k, k + n)²` in the proofs.

## Main results

* `SimpleGraph.adjArray`, `TauCeti.DenseGraphLimits.graphOfArray` — the adjacency array of a
  graph and the graph of an array, measurable, mutually inverse on the symmetric `false`-diagonal
  arrays, and intertwining relabelling with the diagonal relabelling of arrays
  (`adjArray_comap`, `graphOfArray_pairReindex`).
* `TauCeti.DenseGraphLimits.arrayLaw`, `graphLawOfArray`, `infiniteGraphLawOfArray` — the
  law-level adapter with its two pushforward identities, and `graphLawArrayLawEquiv`, the bundled
  equivalence.
* `TauCeti.DenseGraphLimits.isDissociated_iff_jointlyDissociated` — dissociation compatibility.
* `TauCeti.DenseGraphLimits.isDissociated_iff_arrayLaw_mem_extremePoints` — dissociation of a
  graph law is extremality of its array law.

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33–61, Section 5.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
-/

public section

open MeasureTheory ProbabilityTheory Set TauCeti.Probability SimpleGraph
open scoped ENNReal

namespace TauCeti

namespace DenseGraphLimits

/-! ### The adjacency array of a graph and the graph of an array -/

/-- Edge coordinates read as an array: `false` on the diagonal, the coordinate at `s(i, j)`
elsewhere. -/
noncomputable def edgeCoordToArray (f : EdgeIndex → Bool) : ℕ × ℕ → Bool := fun p =>
  if h : s(p.1, p.2).IsDiag then false else f ⟨s(p.1, p.2), h⟩

/-- Off the diagonal, edge coordinates read as an array are the coordinates. -/
theorem edgeCoordToArray_apply_of_not_isDiag (f : EdgeIndex → Bool) {i j : ℕ}
    (h : ¬ s(i, j).IsDiag) : edgeCoordToArray f (i, j) = f ⟨s(i, j), h⟩ := by
  simp [edgeCoordToArray, h]

/-- On the diagonal, edge coordinates read as an array are `false`. -/
@[simp]
theorem edgeCoordToArray_diag (f : EdgeIndex → Bool) (i : ℕ) :
    edgeCoordToArray f (i, i) = false := by
  simp [edgeCoordToArray]

/-- Edge coordinates read as an array land in the symmetric arrays with `false` diagonal. -/
theorem edgeCoordToArray_mem_symmetricArraysWithDiag (f : EdgeIndex → Bool) :
    edgeCoordToArray f ∈ symmetricArraysWithDiag Bool false :=
  mem_symmetricArraysWithDiag_iff.2
    ⟨fun i j => by simp only [edgeCoordToArray, Sym2.eq_swap], fun i => edgeCoordToArray_diag f i⟩

/-- The adjacency array of a graph on `ℕ`, through its edge coordinates. -/
noncomputable def _root_.SimpleGraph.adjArray (G : SimpleGraph ℕ) : ℕ × ℕ → Bool :=
  edgeCoordToArray (graphCoordEquiv G)

open Classical in
/-- The adjacency array is `true` exactly on edges. -/
@[simp]
theorem _root_.SimpleGraph.adjArray_apply (G : SimpleGraph ℕ) (i j : ℕ) :
    G.adjArray (i, j) = decide (G.Adj i j) := by
  simp only [SimpleGraph.adjArray, edgeCoordToArray]
  by_cases h : s(i, j).IsDiag
  · have : i = j := Sym2.mk_isDiag_iff.mp h
    subst this; simp [h]
  · simp only [h, dite_false]
    rw [Bool.eq_iff_iff, SimpleGraph.graphCoordEquiv_apply]
    simp [SimpleGraph.mem_edgeSet]

open Classical in
/-- Reading a graph as an array is measurable. -/
theorem _root_.SimpleGraph.measurable_adjArray : Measurable SimpleGraph.adjArray := by
  refine Measurable.of_eval fun p => ?_
  obtain ⟨i, j⟩ := p
  simp only [SimpleGraph.adjArray_apply]
  exact (measurable_of_countable (fun q : Prop => decide q)).comp
    (measurable_iff_adj.1 measurable_id i j)

/-- The adjacency array of a graph is symmetric with `false` diagonal. -/
theorem _root_.SimpleGraph.adjArray_mem_symmetricArraysWithDiag (G : SimpleGraph ℕ) :
    G.adjArray ∈ symmetricArraysWithDiag Bool false :=
  edgeCoordToArray_mem_symmetricArraysWithDiag _

/-- Relabelling the graph is relabelling both axes of its adjacency array. -/
theorem _root_.SimpleGraph.adjArray_comap (σ : Equiv.Perm ℕ) (G : SimpleGraph ℕ) :
    (SimpleGraph.comap ⇑σ G).adjArray = pairReindex σ σ G.adjArray := by
  funext ⟨i, j⟩
  simp only [SimpleGraph.adjArray, edgeCoordToArray, pairReindex_apply]
  by_cases h : s(i, j).IsDiag
  · have h' : s(σ i, σ j).IsDiag := by
      simpa [Sym2.mk_isDiag_iff] using congrArg σ (Sym2.mk_isDiag_iff.mp h)
    simp [h, h']
  · have h' : ¬ s(σ i, σ j).IsDiag := fun h' =>
      h (Sym2.mk_isDiag_iff.mpr (σ.injective (Sym2.mk_isDiag_iff.mp h')))
    simp only [h, h', dite_false]
    rw [Equiv.Perm.graphCoordEquiv_comap]
    -- the relabelled edge coordinate is the coordinate of the relabelled pair
    exact congrArg (graphCoordEquiv G)
      (Subtype.ext (by simp only [Equiv.Perm.edgeIndexMap_val, Sym2.map_mk]))

/-- The graph of an array: `i` and `j` are adjacent when they are distinct and the array is
`true` at `(i, j)` or at `(j, i)`, so on a symmetric array at either. -/
def graphOfArray (x : ℕ × ℕ → Bool) : SimpleGraph ℕ :=
  SimpleGraph.fromRel fun i j => x (i, j) = true

/-- Adjacency in the graph of an array. -/
@[simp]
theorem graphOfArray_adj (x : ℕ × ℕ → Bool) (i j : ℕ) :
    (graphOfArray x).Adj i j ↔ i ≠ j ∧ (x (i, j) = true ∨ x (j, i) = true) :=
  SimpleGraph.fromRel_adj _ _ _

/-- Reading an array as a graph is measurable. -/
theorem measurable_graphOfArray : Measurable graphOfArray := by
  refine measurable_iff_adj.2 fun i j => ?_
  simp only [graphOfArray_adj]
  refine measurable_to_prop ?_
  by_cases hij : i = j
  · simp [hij]
  · have : (fun x : ℕ × ℕ → Bool => i ≠ j ∧ (x (i, j) = true ∨ x (j, i) = true)) ⁻¹' {True}
        = (fun x : ℕ × ℕ → Bool => x (i, j)) ⁻¹' {true} ∪
            (fun x : ℕ × ℕ → Bool => x (j, i)) ⁻¹' {true} := by
      ext x; simp [hij]
    rw [this]
    exact ((measurable_pi_apply _) (measurableSet_singleton _)).union
      ((measurable_pi_apply _) (measurableSet_singleton _))

/-- The graph of the adjacency array of a graph is the graph. -/
@[simp]
theorem _root_.SimpleGraph.graphOfArray_adjArray (G : SimpleGraph ℕ) :
    graphOfArray G.adjArray = G := by
  ext i j
  simp only [graphOfArray_adj, SimpleGraph.adjArray_apply, decide_eq_true_eq]
  exact ⟨fun ⟨_, h⟩ => h.elim id G.adj_symm, fun h => ⟨G.ne_of_adj h, Or.inl h⟩⟩

/-- The adjacency array of the graph of a symmetric `false`-diagonal array is the array. -/
@[simp]
theorem adjArray_graphOfArray {x : ℕ × ℕ → Bool} (hx : x ∈ symmetricArraysWithDiag Bool false) :
    (graphOfArray x).adjArray = x := by
  obtain ⟨hs, hd⟩ := mem_symmetricArraysWithDiag_iff.1 hx
  funext ⟨i, j⟩
  rw [SimpleGraph.adjArray_apply]
  by_cases hij : i = j
  · subst hij; simp [hd]
  · simp [graphOfArray_adj, hij, hs i j]

/-- The graph of a relabelled array is the relabelling of its graph. -/
theorem graphOfArray_pairReindex (σ : Equiv.Perm ℕ) (x : ℕ × ℕ → Bool) :
    graphOfArray (pairReindex σ σ x) = SimpleGraph.comap ⇑σ (graphOfArray x) := by
  ext i j
  simp [graphOfArray_adj, pairReindex_apply, σ.injective.ne_iff]

/-! ### The law-level adapter -/

/-- The array law of a law on graphs: its pushforward along the adjacency array. -/
noncomputable def arrayLaw (μ : Measure (SimpleGraph ℕ)) : Measure (ℕ × ℕ → Bool) :=
  μ.map SimpleGraph.adjArray

/-- The array law is the pushforward along the adjacency array. -/
theorem arrayLaw_def (μ : Measure (SimpleGraph ℕ)) : arrayLaw μ = μ.map SimpleGraph.adjArray :=
  (rfl)

instance (μ : Measure (SimpleGraph ℕ)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (arrayLaw μ) := by
  rw [arrayLaw_def]; infer_instance

/-- The array law of any law on graphs is carried by the symmetric `false`-diagonal arrays. -/
theorem arrayLaw_compl_symmetricArraysWithDiag_eq_zero (μ : Measure (SimpleGraph ℕ)) :
    arrayLaw μ (symmetricArraysWithDiag Bool false)ᶜ = 0 := by
  rw [arrayLaw_def, Measure.map_apply SimpleGraph.measurable_adjArray
    (measurableSet_symmetricArraysWithDiag _).compl]
  have : SimpleGraph.adjArray ⁻¹' (symmetricArraysWithDiag Bool false)ᶜ = ∅ := by
    ext G
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
    exact G.adjArray_mem_symmetricArraysWithDiag
  simp [this]

/-- The array law of an exchangeable law on infinite graphs is jointly exchangeable. -/
theorem jointlyExchangeable_arrayLaw (L : InfiniteExchangeableGraphLaw) :
    JointlyExchangeable (arrayLaw L.law) fun p x => x p := by
  rw [jointlyExchangeable_iff]
  intro σ
  rw [arrayLaw_def, Measure.map_map (by fun_prop) SimpleGraph.measurable_adjArray,
    Measure.map_map (by fun_prop) SimpleGraph.measurable_adjArray]
  have : ((fun x : ℕ × ℕ → Bool => fun p => x (σ p.1, σ p.2)) ∘ SimpleGraph.adjArray)
      = SimpleGraph.adjArray ∘ SimpleGraph.comap ⇑σ := by
    funext G; simp only [Function.comp, SimpleGraph.adjArray_comap, pairReindex_def]
  rw [this, ← Measure.map_map SimpleGraph.measurable_adjArray (SimpleGraph.measurable_comap _),
    L.exchangeable σ]
  rfl

/-- The array law of an exchangeable law on infinite graphs is a jointly exchangeable probability
law carried by the symmetric `false`-diagonal arrays. -/
theorem arrayLaw_mem_jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag
    (L : InfiniteExchangeableGraphLaw) :
    arrayLaw L.law ∈ jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag Bool false :=
  mem_jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag_iff.2
    ⟨mem_jointlyExchangeableProbabilityMeasures_iff.2
      ⟨jointlyExchangeable_arrayLaw L, inferInstance⟩,
      arrayLaw_compl_symmetricArraysWithDiag_eq_zero _⟩

/-- The graph law of a law on arrays: its pushforward along the graph of an array. -/
noncomputable def graphLawOfArray (ρ : Measure (ℕ × ℕ → Bool)) : Measure (SimpleGraph ℕ) :=
  ρ.map graphOfArray

/-- The graph law is the pushforward along the graph of an array. -/
theorem graphLawOfArray_def (ρ : Measure (ℕ × ℕ → Bool)) :
    graphLawOfArray ρ = ρ.map graphOfArray :=
  (rfl)

instance (ρ : Measure (ℕ × ℕ → Bool)) [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (graphLawOfArray ρ) := by
  rw [graphLawOfArray_def]; infer_instance

/-- The graph law of the array law of a law on graphs is the law. -/
@[simp]
theorem graphLawOfArray_arrayLaw (μ : Measure (SimpleGraph ℕ)) :
    graphLawOfArray (arrayLaw μ) = μ := by
  rw [graphLawOfArray_def, arrayLaw_def,
    Measure.map_map measurable_graphOfArray SimpleGraph.measurable_adjArray]
  have : graphOfArray ∘ SimpleGraph.adjArray = id := funext SimpleGraph.graphOfArray_adjArray
  rw [this, Measure.map_id]

/-- The array law of the graph law of a law carried by the symmetric `false`-diagonal arrays is
the law. -/
@[simp]
theorem arrayLaw_graphLawOfArray {ρ : Measure (ℕ × ℕ → Bool)}
    (hρ : ρ (symmetricArraysWithDiag Bool false)ᶜ = 0) :
    arrayLaw (graphLawOfArray ρ) = ρ := by
  rw [arrayLaw_def, graphLawOfArray_def,
    Measure.map_map SimpleGraph.measurable_adjArray measurable_graphOfArray]
  refine (Measure.map_congr ?_).trans Measure.map_id
  have hae : ∀ᵐ x ∂ρ, x ∈ symmetricArraysWithDiag Bool false := by
    rw [ae_iff]; exact hρ
  exact hae.mono fun x hx => by simp [Function.comp, adjArray_graphOfArray hx]

/-- The graph law of a diagonally invariant law on arrays is invariant under relabelling. -/
theorem graphLawOfArray_map_comap {ρ : Measure (ℕ × ℕ → Bool)} (σ : Equiv.Perm ℕ)
    (hρ : ρ.map (pairReindex σ σ) = ρ) :
    (graphLawOfArray ρ).map (SimpleGraph.comap ⇑σ) = graphLawOfArray ρ := by
  rw [graphLawOfArray_def, Measure.map_map (SimpleGraph.measurable_comap _) measurable_graphOfArray]
  conv_rhs => rw [← hρ]
  rw [Measure.map_map measurable_graphOfArray (measurable_pairReindex σ σ)]
  congr 1
  funext x
  simp only [Function.comp, graphOfArray_pairReindex]

/-- The exchangeable law on infinite graphs of a jointly exchangeable probability law carried by
the symmetric `false`-diagonal arrays. -/
noncomputable def infiniteGraphLawOfArray
    (ρ : {ρ : Measure (ℕ × ℕ → Bool) //
      ρ ∈ jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag Bool false}) :
    InfiniteExchangeableGraphLaw where
  law := graphLawOfArray ρ.1
  prob := by
    obtain ⟨hmem, -⟩ :=
      mem_jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag_iff.1 ρ.2
    obtain ⟨-, hp⟩ := mem_jointlyExchangeableProbabilityMeasures_iff.1 hmem
    infer_instance
  exchangeable σ := by
    obtain ⟨hmem, -⟩ :=
      mem_jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag_iff.1 ρ.2
    obtain ⟨hexch, -⟩ := mem_jointlyExchangeableProbabilityMeasures_iff.1 hmem
    exact graphLawOfArray_map_comap σ (hexch.map_pairReindex σ)

/-- The law of the bundled graph law of an array law. -/
theorem infiniteGraphLawOfArray_law
    (ρ : {ρ : Measure (ℕ × ℕ → Bool) //
      ρ ∈ jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag Bool false}) :
    (infiniteGraphLawOfArray ρ).law = graphLawOfArray ρ.1 :=
  (rfl)

/-- The array law of the bundled graph law of an array law is the array law. -/
@[simp]
theorem arrayLaw_infiniteGraphLawOfArray
    (ρ : {ρ : Measure (ℕ × ℕ → Bool) //
      ρ ∈ jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag Bool false}) :
    arrayLaw (infiniteGraphLawOfArray ρ).law = ρ.1 := by
  rw [infiniteGraphLawOfArray_law]
  exact arrayLaw_graphLawOfArray
    (mem_jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag_iff.1 ρ.2).2

/-- **Exchangeable graph laws are the jointly exchangeable array laws carried by the symmetric
`false`-diagonal arrays.** The bundled law-level adapter. -/
noncomputable def graphLawArrayLawEquiv :
    InfiniteExchangeableGraphLaw ≃
      {ρ : Measure (ℕ × ℕ → Bool) //
        ρ ∈ jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag Bool false} where
  toFun L := ⟨arrayLaw L.law,
    arrayLaw_mem_jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag L⟩
  invFun := infiniteGraphLawOfArray
  left_inv L := InfiniteExchangeableGraphLaw.ext (graphLawOfArray_arrayLaw L.law)
  right_inv ρ := Subtype.ext (arrayLaw_infiniteGraphLawOfArray ρ)

/-- The forward direction of the adapter is the array law. -/
@[simp]
theorem graphLawArrayLawEquiv_apply_coe (L : InfiniteExchangeableGraphLaw) :
    (graphLawArrayLawEquiv L : Measure (ℕ × ℕ → Bool)) = arrayLaw L.law :=
  (rfl)

/-- The inverse direction of the adapter is the bundled graph law of the array law. -/
@[simp]
theorem graphLawArrayLawEquiv_symm_apply
    (ρ : {ρ : Measure (ℕ × ℕ → Bool) //
      ρ ∈ jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag Bool false}) :
    graphLawArrayLawEquiv.symm ρ = infiniteGraphLawOfArray ρ :=
  (rfl)

/-! ### Dissociation -/

/-- An injective measurable map out of a countable type with measurable singletons is a
measurable embedding. -/
private theorem measurableEmbedding_of_countable {β γ : Type*} [MeasurableSpace β]
    [MeasurableSpace γ] [Countable β] [MeasurableSingletonClass γ] {f : β → γ}
    (hf : Measurable f) (hinj : Function.Injective f) : MeasurableEmbedding f where
  injective := hinj
  measurable := hf
  measurableSet_image' s _ := ((Set.to_countable s).image f).measurableSet

open Classical in
/-- A graph on `Fin n` read on the block `[0, n)²`. -/
private noncomputable def finGraphBlockZero (n : ℕ) (H : SimpleGraph (Fin n)) :
    (Finset.Ico 0 n ×ˢ Finset.Ico 0 n : Finset (ℕ × ℕ)) → Bool :=
  fun p => decide (H.Adj ⟨p.1.1, by have := (Finset.mem_product.1 p.2).1; simp at this; omega⟩
    ⟨p.1.2, by have := (Finset.mem_product.1 p.2).2; simp at this; omega⟩)

open Classical in
/-- A graph on `Fin n` read on the block `[k, k + n)²`. -/
private noncomputable def finGraphBlockAt (k n : ℕ) (H : SimpleGraph (Fin n)) :
    (Finset.Ico k (k + n) ×ˢ Finset.Ico k (k + n) : Finset (ℕ × ℕ)) → Bool :=
  fun p => decide (H.Adj ⟨p.1.1 - k, by have := (Finset.mem_product.1 p.2).1; simp at this; omega⟩
    ⟨p.1.2 - k, by have := (Finset.mem_product.1 p.2).2; simp at this; omega⟩)

open Classical in
private theorem measurableEmbedding_finGraphBlockZero (n : ℕ) :
    MeasurableEmbedding (finGraphBlockZero n) :=
  measurableEmbedding_of_countable
    (Measurable.of_eval fun _ => (measurable_of_countable (fun q : Prop => decide q)).comp
      (measurable_iff_adj.1 measurable_id _ _))
    (fun H H' h => by
      ext a b
      have := congrFun h ⟨(a, b), by simp⟩
      simpa [finGraphBlockZero] using this)

open Classical in
private theorem measurableEmbedding_finGraphBlockAt (k n : ℕ) :
    MeasurableEmbedding (finGraphBlockAt k n) :=
  measurableEmbedding_of_countable
    (Measurable.of_eval fun _ => (measurable_of_countable (fun q : Prop => decide q)).comp
      (measurable_iff_adj.1 measurable_id _ _))
    (fun H H' h => by
      ext a b
      have := congrFun h ⟨(k + a, k + b), by simp⟩
      simpa [finGraphBlockAt] using this)

/-- The block restriction of the adjacency array on `[0, n)²` is the window of length `n`. -/
private theorem restrict_adjArray_zero (n : ℕ) (G : SimpleGraph ℕ) :
    (Finset.Ico 0 n ×ˢ Finset.Ico 0 n).restrict G.adjArray
      = finGraphBlockZero n (G.restrictFin n) := by
  funext ⟨⟨a, b⟩, hab⟩
  simp [Finset.restrict, finGraphBlockZero, SimpleGraph.adjArray_apply, restrictFin_adj]

/-- The block restriction of the adjacency array on `[k, k + n)²` is the window at offset `k`. -/
private theorem restrict_adjArray (k n : ℕ) (G : SimpleGraph ℕ) :
    (Finset.Ico k (k + n) ×ˢ Finset.Ico k (k + n)).restrict G.adjArray
      = finGraphBlockAt k n (SimpleGraph.comap (fun i : Fin n => k + (i : ℕ)) G) := by
  funext ⟨⟨a, b⟩, hab⟩
  simp only [Finset.restrict, finGraphBlockAt, SimpleGraph.adjArray_apply, SimpleGraph.comap_adj]
  have ha : k ≤ a := by have := (Finset.mem_product.1 hab).1; simp at this; omega
  have hb : k ≤ b := by have := (Finset.mem_product.1 hab).2; simp at this; omega
  congr 1; simp [Nat.add_sub_cancel' ha, Nat.add_sub_cancel' hb]

/-- The dissociation identity of the finite law at `(k, l)` is block independence of the array
law at the windows `[0, k)²` and `[k, k + l)²`. -/
theorem isDissociated_iff_forall_indepFun_restrict (L : InfiniteExchangeableGraphLaw) :
    (exchangeableGraphLawEquivInfinite.symm L).IsDissociated ↔
      ∀ k l : ℕ, IndepFun
        (fun x : ℕ × ℕ → Bool => (Finset.Ico 0 k ×ˢ Finset.Ico 0 k).restrict x)
        (fun x : ℕ × ℕ → Bool => (Finset.Ico k (k + l) ×ˢ Finset.Ico k (k + l)).restrict x)
        (arrayLaw L.law) := by
  -- outline: both sides are product identities for the pair of windows; push the array side
  -- through the injective block encodings of the two windows, strip the encodings, and identify
  -- the two windows of the graph with the marginals of the finite law
  rw [ExchangeableGraphLaw.isDissociated_iff]
  refine forall_congr' fun k => forall_congr' fun l => ?_
  simp only [exchangeableGraphLawEquivInfinite_symm_law]
  rw [indepFun_iff_map_prod_eq_prod_map_map' (Finset.measurable_restrict _).aemeasurable
    (Finset.measurable_restrict _).aemeasurable inferInstance inferInstance, arrayLaw_def]
  rw [Measure.map_map ((Finset.measurable_restrict _).prodMk (Finset.measurable_restrict _))
      SimpleGraph.measurable_adjArray,
    Measure.map_map (Finset.measurable_restrict _) SimpleGraph.measurable_adjArray,
    Measure.map_map (Finset.measurable_restrict _) SimpleGraph.measurable_adjArray]
  have hw : Measurable fun G : SimpleGraph ℕ =>
      (SimpleGraph.comap (Fin.castAdd l) (G.restrictFin (k + l)),
        SimpleGraph.comap (Fin.natAdd k) (G.restrictFin (k + l))) := by fun_prop
  have e1 : (fun x : ℕ × ℕ → Bool =>
        ((Finset.Ico 0 k ×ˢ Finset.Ico 0 k).restrict x,
          (Finset.Ico k (k + l) ×ˢ Finset.Ico k (k + l)).restrict x)) ∘ SimpleGraph.adjArray
      = (Prod.map (finGraphBlockZero k) (finGraphBlockAt k l)) ∘ fun G : SimpleGraph ℕ =>
          (SimpleGraph.comap (Fin.castAdd l) (G.restrictFin (k + l)),
            SimpleGraph.comap (Fin.natAdd k) (G.restrictFin (k + l))) := by
    funext G
    simp only [Function.comp, Prod.map, restrictFin_comap_castAdd, restrictFin_comap_natAdd,
      restrict_adjArray_zero, restrict_adjArray]
  have e2 : (fun x : ℕ × ℕ → Bool => (Finset.Ico 0 k ×ˢ Finset.Ico 0 k).restrict x)
        ∘ SimpleGraph.adjArray
      = finGraphBlockZero k ∘ fun G : SimpleGraph ℕ =>
          SimpleGraph.comap (Fin.castAdd l) (G.restrictFin (k + l)) := by
    funext G; simp only [Function.comp, restrictFin_comap_castAdd, restrict_adjArray_zero]
  have e3 : (fun x : ℕ × ℕ → Bool => (Finset.Ico k (k + l) ×ˢ Finset.Ico k (k + l)).restrict x)
        ∘ SimpleGraph.adjArray
      = finGraphBlockAt k l ∘ fun G : SimpleGraph ℕ =>
          SimpleGraph.comap (Fin.natAdd k) (G.restrictFin (k + l)) := by
    funext G; simp only [Function.comp, restrictFin_comap_natAdd, restrict_adjArray]
  have hemb : MeasurableEmbedding (Prod.map (finGraphBlockZero k) (finGraphBlockAt k l)) :=
    (measurableEmbedding_finGraphBlockZero k).prodMap (measurableEmbedding_finGraphBlockAt k l)
  have hf : Measurable (finGraphBlockZero k) := (measurableEmbedding_finGraphBlockZero k).measurable
  have hg : Measurable (finGraphBlockAt k l) := (measurableEmbedding_finGraphBlockAt k l).measurable
  rw [e1, e2, e3, ← Measure.map_map hemb.measurable hw, ← Measure.map_map hf (by fun_prop),
    ← Measure.map_map hg (by fun_prop), Measure.map_prod_map _ _ hf hg,
    hemb.map_injective.eq_iff]
  -- the second window at offset `k` has the law of the initial window, by consistency
  have hsecond : L.law.map (fun G : SimpleGraph ℕ =>
      SimpleGraph.comap (Fin.natAdd k) (G.restrictFin (k + l))) = L.law.map (·.restrictFin l) := by
    have := (exchangeableGraphLawEquivInfinite.symm L).consistent
      (⟨Fin.natAdd k, fun a b h => by simpa using h⟩ : Fin l ↪ Fin (k + l))
    simp only [exchangeableGraphLawEquivInfinite_symm_law] at this
    rw [Measure.map_map (SimpleGraph.measurable_comap _) (SimpleGraph.measurable_restrictFin _)]
      at this
    exact this
  rw [hsecond, Measure.map_map (by fun_prop) (SimpleGraph.measurable_restrictFin _)]
  simp only [Function.comp_def, restrictFin_comap_castAdd]

/-- **Dissociation is joint dissociation of the array law.** -/
theorem isDissociated_iff_jointlyDissociated (L : InfiniteExchangeableGraphLaw) :
    (exchangeableGraphLawEquivInfinite.symm L).IsDissociated ↔
      JointlyDissociated (arrayLaw L.law) fun p x => x p := by
  rw [isDissociated_iff_forall_indepFun_restrict, jointlyDissociated_coord_iff_indepFun_restrict]
  refine ⟨fun h => indepFun_restrict_of_forall_Ico (jointlyExchangeable_arrayLaw L) h,
    fun h k l => h _ _ ?_⟩
  rw [Finset.disjoint_left]
  intro n hn hn'
  simp only [Finset.mem_Ico] at hn hn'
  omega

/-- **Dissociation is extremality** for exchangeable laws on infinite graphs, read through their
array laws. -/
theorem isDissociated_iff_arrayLaw_mem_extremePoints (L : InfiniteExchangeableGraphLaw) :
    (exchangeableGraphLawEquivInfinite.symm L).IsDissociated ↔
      arrayLaw L.law ∈ extremePoints ℝ≥0∞
        (jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag Bool false) := by
  rw [isDissociated_iff_jointlyDissociated,
    jointlyDissociated_iff_mem_extremePoints_on (jointlyExchangeable_arrayLaw L)
      (arrayLaw_compl_symmetricArraysWithDiag_eq_zero _)]
  -- the symmetric carried-law set is the carried-law set at the symmetric carrier; its body is
  -- not exposed across the module boundary, so the identity is read off the membership lemmas
  exact Iff.of_eq (congrArg (arrayLaw L.law ∈ extremePoints ℝ≥0∞ ·) (Set.ext fun _ =>
    mem_jointlyExchangeableProbabilityMeasuresOn_iff.trans
      mem_jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag_iff.symm))

end DenseGraphLimits

end TauCeti
