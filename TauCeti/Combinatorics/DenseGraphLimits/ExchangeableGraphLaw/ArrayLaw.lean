/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Windows
public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Coordinates
public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Infinite
public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Dissociated

/-!
# Exchangeable graph laws as jointly exchangeable array laws

An exchangeable law on infinite graphs is the law of a symmetric `Bool`-valued array with `false`
on the diagonal, jointly exchangeable under simultaneous relabelling of both axes. This file is the
law-level adapter between the two: the array law `arrayLaw L` of an exchangeable law on infinite
graphs, its inverse `graphLawOfArray`, the identification of exchangeability on the two sides,
and the two compatibilities that let the array theory speak about graph laws.

* **Dissociation.** The finite law attached to `L` is dissociated exactly when the array law is
  jointly dissociated (`isDissociated_iff_jointlyDissociated`). The graph notion is independence
  of consecutive label windows; the array notion is independence of the arrays read along
  disjoint index sets; for a jointly exchangeable law consecutive windows suffice
  (`indepFun_blockRestrict_of_forall_Ico`), and each window of the graph is the block restriction
  of its array.
* **Convex mixtures.** The array law is linear in the underlying measure
  (`arrayLaw_smul_add_smul`), and the array laws of graph laws are exactly the jointly
  exchangeable probability laws carried by the symmetric `false`-diagonal arrays. Extremality
  among those laws is joint dissociation (`jointlyDissociated_iff_mem_extremePoints_on`), so
  dissociation of a graph law is extremality of its array law
  (`isDissociated_iff_arrayLaw_mem_extremePoints`).

The carrier-level encoding is the edge-coordinate equivalence `graphCoordEquiv`, read as an array
by placing `false` on the diagonal; the finite graphs on `Fin n` are read on the block
`[k, k + n)²` by `finGraphBlockAt`.

## Main results

* `TauCeti.DenseGraphLimits.graphArray`, `arrayGraph` — the adjacency array of a graph and the
  graph of an array, measurable, mutually inverse on the symmetric `false`-diagonal arrays, and
  intertwining relabelling with the diagonal relabelling of arrays (`graphArray_comap`).
* `TauCeti.DenseGraphLimits.arrayLaw`, `graphLawOfArray` — the law-level adapter with its two
  pushforward identities; `arrayLaw_mem` places the array law among the jointly exchangeable laws
  carried by the symmetric arrays.
* `TauCeti.DenseGraphLimits.isDissociated_iff_jointlyDissociated` — dissociation compatibility.
* `TauCeti.DenseGraphLimits.arrayLaw_smul_add_smul` — convex-mixture compatibility.
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

/-- Edge coordinates read as an array: `false` on the diagonal, the coordinate at `s(i, j)`
elsewhere. -/
noncomputable def edgeCoordToArray (f : EdgeIndex → Bool) : ℕ × ℕ → Bool := fun p =>
  if h : s(p.1, p.2).IsDiag then false else f ⟨s(p.1, p.2), h⟩

/-- The adjacency array of a graph on `ℕ`, through its edge coordinates. -/
noncomputable def graphArray (G : SimpleGraph ℕ) : ℕ × ℕ → Bool :=
  edgeCoordToArray (graphCoordEquiv G)

open Classical in
/-- The adjacency array is `true` exactly on edges. -/
@[simp]
theorem graphArray_apply (G : SimpleGraph ℕ) (i j : ℕ) :
    graphArray G (i, j) = decide (G.Adj i j) := by
  simp only [graphArray, edgeCoordToArray]
  by_cases h : s(i, j).IsDiag
  · have : i = j := Sym2.mk_isDiag_iff.mp h
    subst this; simp [h]
  · simp only [h, dite_false]
    rw [Bool.eq_iff_iff, SimpleGraph.graphCoordEquiv_apply]
    simp [SimpleGraph.mem_edgeSet]

open Classical in
/-- Reading a graph as an array is measurable. -/
theorem measurable_graphArray : Measurable graphArray := by
  refine Measurable.of_eval fun p => ?_
  obtain ⟨i, j⟩ := p
  simp only [graphArray_apply]
  exact (measurable_of_countable (fun q : Prop => decide q)).comp
    (measurable_iff_adj.1 measurable_id i j)

/-- The array law of an exchangeable law on infinite graphs: the pushforward of the law along
the adjacency array. -/
noncomputable def arrayLaw (L : InfiniteExchangeableGraphLaw) : Measure (ℕ × ℕ → Bool) :=
  L.law.map graphArray

instance (L : InfiniteExchangeableGraphLaw) : IsProbabilityMeasure (arrayLaw L) := by
  unfold arrayLaw; infer_instance

open Classical in
/-- A graph on `Fin n` read on the block `[k, k + n)²`. -/
noncomputable def finGraphBlockAt (k n : ℕ) (H : SimpleGraph (Fin n)) :
    (↑(Finset.Ico k (k + n)) ×ˢ ↑(Finset.Ico k (k + n)) : Set (ℕ × ℕ)) → Bool :=
  fun p => decide (H.Adj ⟨p.1.1 - k, by have := p.2.1; simp at this; omega⟩
    ⟨p.1.2 - k, by have := p.2.2; simp at this; omega⟩)

/-- Reading a finite graph on a block is injective. -/
theorem finGraphBlockAt_injective (k n : ℕ) : Function.Injective (finGraphBlockAt k n) := by
  intro H H' h; ext a b
  have := congrFun h ⟨(k + a, k + b), by simp⟩
  simpa [finGraphBlockAt] using this

open Classical in
/-- Reading a finite graph on a block is measurable. -/
theorem measurable_finGraphBlockAt (k n : ℕ) : Measurable (finGraphBlockAt k n) :=
  Measurable.of_eval fun _ =>
    (measurable_of_countable (fun q : Prop => decide q)).comp
      (measurable_iff_adj.1 measurable_id _ _)

/-- Reading a finite graph on a block is a measurable embedding: the graphs on `Fin n` are
countable with measurable singletons. -/
theorem measurableEmbedding_finGraphBlockAt (k n : ℕ) :
    MeasurableEmbedding (finGraphBlockAt k n) where
  injective := finGraphBlockAt_injective k n
  measurable := measurable_finGraphBlockAt k n
  measurableSet_image' s _ := ((Set.to_countable s).image _).measurableSet

/-- The block restriction of the array of `G` on `[k, k + n)²` is the window of `G` at offset
`k`. -/
theorem blockRestrict_graphArray (k n : ℕ) (G : SimpleGraph ℕ) :
    blockRestrict (Finset.Ico k (k + n)) (graphArray G)
      = finGraphBlockAt k n (SimpleGraph.comap (fun i : Fin n => k + (i : ℕ)) G) := by
  funext ⟨⟨a, b⟩, hab⟩
  simp only [blockRestrict_apply, finGraphBlockAt, graphArray_apply, SimpleGraph.comap_adj]
  have ha : k ≤ a := by have := hab.1; simp at this; omega
  have hb : k ≤ b := by have := hab.2; simp at this; omega
  congr 1; simp [Nat.add_sub_cancel' ha, Nat.add_sub_cancel' hb]

/-- The first of two consecutive windows of a window. -/
theorem comap_castAdd_restrictFin (G : SimpleGraph ℕ) (k l : ℕ) :
    SimpleGraph.comap (Fin.castAdd l) (G.restrictFin (k + l))
      = SimpleGraph.comap (fun i : Fin k => 0 + (i : ℕ)) G := by
  ext a b; simp [restrictFin_adj]

/-- The second of two consecutive windows of a window. -/
theorem comap_natAdd_restrictFin (G : SimpleGraph ℕ) (k l : ℕ) :
    SimpleGraph.comap (Fin.natAdd k) (G.restrictFin (k + l))
      = SimpleGraph.comap (fun i : Fin l => k + (i : ℕ)) G := by
  ext a b; simp [restrictFin_adj]

/-- The dissociation identity of the finite law at `(k, l)` is block independence of the array
law at the windows `[0, k)²` and `[k, k + l)²`. -/
theorem isDissociated_iff_forall_indepFun_blockRestrict (L : InfiniteExchangeableGraphLaw) :
    (exchangeableGraphLawEquivInfinite.symm L).IsDissociated ↔
      ∀ k l : ℕ, IndepFun (blockRestrict (Finset.Ico 0 (0 + k)))
        (blockRestrict (Finset.Ico k (k + l))) (arrayLaw L) := by
  rw [ExchangeableGraphLaw.isDissociated_iff]
  refine forall_congr' fun k => forall_congr' fun l => ?_
  simp only [exchangeableGraphLawEquivInfinite_symm_law]
  rw [indepFun_iff_map_prod_eq_prod_map_map' (measurable_blockRestrict _).aemeasurable
    (measurable_blockRestrict _).aemeasurable inferInstance inferInstance]
  simp only [arrayLaw]
  rw [Measure.map_map ((measurable_blockRestrict _).prodMk (measurable_blockRestrict _))
      measurable_graphArray,
    Measure.map_map (measurable_blockRestrict _) measurable_graphArray,
    Measure.map_map (measurable_blockRestrict _) measurable_graphArray]
  have e1 : (fun x => (blockRestrict (Finset.Ico 0 (0 + k)) x,
      blockRestrict (Finset.Ico k (k + l)) x))
      ∘ graphArray = (Prod.map (finGraphBlockAt 0 k) (finGraphBlockAt k l))
        ∘ (fun G : SimpleGraph ℕ => (SimpleGraph.comap (Fin.castAdd l) (G.restrictFin (k + l)),
            SimpleGraph.comap (Fin.natAdd k) (G.restrictFin (k + l)))) := by
    funext G
    simp only [Function.comp, Prod.map, comap_castAdd_restrictFin, comap_natAdd_restrictFin,
      blockRestrict_graphArray]
  have e2 : blockRestrict (Finset.Ico 0 (0 + k)) ∘ graphArray
      = finGraphBlockAt 0 k ∘ (fun G : SimpleGraph ℕ =>
          SimpleGraph.comap (Fin.castAdd l) (G.restrictFin (k + l))) := by
    funext G; simp only [Function.comp, comap_castAdd_restrictFin, blockRestrict_graphArray]
  have e3 : blockRestrict (Finset.Ico k (k + l)) ∘ graphArray
      = finGraphBlockAt k l ∘ (fun G : SimpleGraph ℕ =>
          SimpleGraph.comap (Fin.natAdd k) (G.restrictFin (k + l))) := by
    funext G; simp only [Function.comp, comap_natAdd_restrictFin, blockRestrict_graphArray]
  have hemb : MeasurableEmbedding (Prod.map (finGraphBlockAt 0 k) (finGraphBlockAt k l)) :=
    (measurableEmbedding_finGraphBlockAt 0 k).prodMap (measurableEmbedding_finGraphBlockAt k l)
  have hf : Measurable (finGraphBlockAt 0 k) := (measurableEmbedding_finGraphBlockAt 0 k).measurable
  have hg : Measurable (finGraphBlockAt k l) := (measurableEmbedding_finGraphBlockAt k l).measurable
  have hw : Measurable fun G : SimpleGraph ℕ =>
      (SimpleGraph.comap (Fin.castAdd l) (G.restrictFin (k + l)),
        SimpleGraph.comap (Fin.natAdd k) (G.restrictFin (k + l))) := by fun_prop
  rw [e1, e2, e3, ← Measure.map_map hemb.measurable hw, ← Measure.map_map hf (by fun_prop),
    ← Measure.map_map hg (by fun_prop), Measure.map_prod_map _ _ hf hg,
    hemb.map_injective.eq_iff]
  -- both sides are now statements about the two windows of `L.law`; the second window at
  -- offset `k` has the law of the initial window by consistency of the finite law
  have hsecond : L.law.map (fun G : SimpleGraph ℕ =>
      SimpleGraph.comap (Fin.natAdd k) (G.restrictFin (k + l))) = L.law.map (·.restrictFin l) := by
    have := (exchangeableGraphLawEquivInfinite.symm L).consistent
      (⟨Fin.natAdd k, fun a b h => by simpa using h⟩ : Fin l ↪ Fin (k + l))
    simp only [exchangeableGraphLawEquivInfinite_symm_law] at this
    rw [Measure.map_map (SimpleGraph.measurable_comap _) (SimpleGraph.measurable_restrictFin _)]
      at this
    exact this
  have hfirst : (fun G : SimpleGraph ℕ => SimpleGraph.comap (Fin.castAdd l) (G.restrictFin (k + l)))
      = fun G => G.restrictFin k := by
    funext G; ext a b; simp [restrictFin_adj]
  rw [hfirst, hsecond, Measure.map_map (by fun_prop) (SimpleGraph.measurable_restrictFin _)]
  rfl

/-- An array read as edge coordinates, by evaluating at both orderings of each unordered pair. -/
noncomputable def arrayToEdgeCoord (x : ℕ × ℕ → Bool) : EdgeIndex → Bool := fun e =>
  Sym2.lift ⟨fun i j => x (i, j) && x (j, i), fun _ _ => Bool.and_comm _ _⟩ e.1

/-- Edge coordinates read as an array land in the symmetric arrays with `false` diagonal. -/
theorem edgeCoordToArray_mem (f : EdgeIndex → Bool) :
    edgeCoordToArray f ∈ symmetricArraysWithDiag Bool false := by
  refine mem_symmetricArraysWithDiag_iff.2 ⟨fun i j => ?_, fun i => ?_⟩
  · simp only [edgeCoordToArray, Sym2.eq_swap]
  · simp [edgeCoordToArray]

/-- Reading edge coordinates as an array and back is the identity. -/
theorem arrayToEdgeCoord_edgeCoordToArray (f : EdgeIndex → Bool) :
    arrayToEdgeCoord (edgeCoordToArray f) = f := by
  funext e
  obtain ⟨s, hs⟩ := e
  induction s using Sym2.ind with
  | _ i j =>
    have hij : i ≠ j := fun h => hs (Sym2.mk_isDiag_iff.mpr h)
    simp only [arrayToEdgeCoord, Sym2.lift_mk, edgeCoordToArray, hs, dite_false, Sym2.eq_swap]
    simp

/-- Reading a symmetric `false`-diagonal array as edge coordinates and back is the identity. -/
theorem edgeCoordToArray_arrayToEdgeCoord {x : ℕ × ℕ → Bool}
    (hx : x ∈ symmetricArraysWithDiag Bool false) : edgeCoordToArray (arrayToEdgeCoord x) = x := by
  obtain ⟨hs, hd⟩ := mem_symmetricArraysWithDiag_iff.1 hx
  funext ⟨i, j⟩
  by_cases hij : i = j
  · subst hij; simp [edgeCoordToArray, hd]
  · have : ¬ s(i, j).IsDiag := by simpa [Sym2.mk_isDiag_iff] using hij
    simp [edgeCoordToArray, this, arrayToEdgeCoord, hs i j]

/-- Reading an array as edge coordinates is measurable. -/
theorem measurable_arrayToEdgeCoord : Measurable arrayToEdgeCoord := by
  refine Measurable.of_eval fun e => ?_
  obtain ⟨s, hs⟩ := e
  induction s using Sym2.ind with
  | _ i j =>
    simp only [arrayToEdgeCoord, Sym2.lift_mk]
    have hm : Measurable fun x : ℕ × ℕ → Bool => (x (i, j), x (j, i)) :=
      (measurable_pi_apply (i, j)).prodMk (measurable_pi_apply (j, i))
    exact (measurable_of_countable (fun q : Bool × Bool => q.1 && q.2)).comp hm

/-- The graph of an array: the graph of its symmetric off-diagonal part. -/
noncomputable def arrayGraph (x : ℕ × ℕ → Bool) : SimpleGraph ℕ :=
  graphCoordEquiv.symm (arrayToEdgeCoord x)

/-- Reading an array as a graph is measurable. -/
theorem measurable_arrayGraph : Measurable arrayGraph :=
  measurable_graphCoordEquiv_symm.comp measurable_arrayToEdgeCoord

/-- The graph of the array of a graph is the graph. -/
@[simp]
theorem arrayGraph_graphArray (G : SimpleGraph ℕ) : arrayGraph (graphArray G) = G := by
  simp [arrayGraph, graphArray, arrayToEdgeCoord_edgeCoordToArray]

/-- The array of the graph of a symmetric `false`-diagonal array is the array. -/
theorem graphArray_arrayGraph {x : ℕ × ℕ → Bool} (hx : x ∈ symmetricArraysWithDiag Bool false) :
    graphArray (arrayGraph x) = x := by
  simp [arrayGraph, graphArray, edgeCoordToArray_arrayToEdgeCoord hx]

/-- The array of a graph is symmetric with `false` diagonal. -/
theorem graphArray_mem (G : SimpleGraph ℕ) : graphArray G ∈ symmetricArraysWithDiag Bool false :=
  edgeCoordToArray_mem _

/-- Relabelling the graph is relabelling both axes of its array. -/
theorem graphArray_comap (σ : Equiv.Perm ℕ) (G : SimpleGraph ℕ) :
    graphArray (SimpleGraph.comap ⇑σ G) = pairReindex σ σ (graphArray G) := by
  funext ⟨i, j⟩
  simp only [graphArray, edgeCoordToArray, pairReindex_apply]
  by_cases h : s(i, j).IsDiag
  · have h' : s(σ i, σ j).IsDiag := by
      simpa [Sym2.mk_isDiag_iff] using congrArg σ (Sym2.mk_isDiag_iff.mp h)
    simp [h, h']
  · have h' : ¬ s(σ i, σ j).IsDiag := fun h' =>
      h (Sym2.mk_isDiag_iff.mpr (σ.injective (Sym2.mk_isDiag_iff.mp h')))
    simp only [h, h', dite_false]
    rw [Equiv.Perm.graphCoordEquiv_comap]
    exact congrArg (graphCoordEquiv G)
      (Subtype.ext (by rw [Equiv.Perm.edgeIndexMap_val]; rfl))

/-- The array law is carried by the symmetric `false`-diagonal arrays. -/
theorem arrayLaw_compl_symmetric (L : InfiniteExchangeableGraphLaw) :
    arrayLaw L (symmetricArraysWithDiag Bool false)ᶜ = 0 := by
  rw [arrayLaw,
    Measure.map_apply measurable_graphArray (measurableSet_symmetricArraysWithDiag _).compl]
  have : graphArray ⁻¹' (symmetricArraysWithDiag Bool false)ᶜ = ∅ := by
    ext G; simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false,
      not_not]; exact graphArray_mem G
  simp [this]

/-- The array law of an exchangeable graph law is jointly exchangeable: relabelling the graph is
relabelling both axes of its array. -/
theorem jointlyExchangeable_arrayLaw (L : InfiniteExchangeableGraphLaw) :
    JointlyExchangeable (arrayLaw L) fun p x => x p := by
  rw [jointlyExchangeable_iff]
  intro σ
  simp only [arrayLaw]
  rw [Measure.map_map (by fun_prop) measurable_graphArray,
    Measure.map_map (by fun_prop) measurable_graphArray]
  have : ((fun x : ℕ × ℕ → Bool => fun p => x (σ p.1, σ p.2)) ∘ graphArray)
      = graphArray ∘ SimpleGraph.comap ⇑σ := by
    funext G; simp only [Function.comp, graphArray_comap, pairReindex_def]
  rw [this, ← Measure.map_map measurable_graphArray (SimpleGraph.measurable_comap _),
    L.exchangeable σ]
  rfl

/-- The array law is a jointly exchangeable probability law carried by the symmetric arrays. -/
theorem arrayLaw_mem (L : InfiniteExchangeableGraphLaw) :
    arrayLaw L ∈ jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag Bool false :=
  mem_jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag_iff.2
    ⟨mem_jointlyExchangeableProbabilityMeasures_iff.2
      ⟨jointlyExchangeable_arrayLaw L, inferInstance⟩, arrayLaw_compl_symmetric L⟩

/-- The graph law of an array law: the pushforward along the graph of an array. -/
noncomputable def graphLawOfArray (ρ : Measure (ℕ × ℕ → Bool)) : Measure (SimpleGraph ℕ) :=
  ρ.map arrayGraph

/-- The graph law of the array law of a graph law is the graph law. -/
@[simp]
theorem graphLawOfArray_arrayLaw (L : InfiniteExchangeableGraphLaw) :
    graphLawOfArray (arrayLaw L) = L.law := by
  simp only [graphLawOfArray, arrayLaw]
  rw [Measure.map_map measurable_arrayGraph measurable_graphArray]
  have : arrayGraph ∘ graphArray = id := funext arrayGraph_graphArray
  rw [this, Measure.map_id]

/-- The array law of the graph law of an array law carried by the symmetric arrays is the array
law. -/
theorem arrayLaw_graphLawOfArray {ρ : Measure (ℕ × ℕ → Bool)} [IsProbabilityMeasure ρ]
    (hρ : ρ (symmetricArraysWithDiag Bool false)ᶜ = 0) :
    (graphLawOfArray ρ).map graphArray = ρ := by
  simp only [graphLawOfArray]
  rw [Measure.map_map measurable_graphArray measurable_arrayGraph]
  refine (Measure.map_congr ?_).trans Measure.map_id
  have hae : ∀ᵐ x ∂ρ, x ∈ symmetricArraysWithDiag Bool false := by
    rw [ae_iff]; exact hρ
  exact hae.mono fun x hx => by simp [Function.comp, graphArray_arrayGraph hx]

/-! ### The adapter -/

/-- **Dissociation is joint dissociation of the array law.** -/
theorem isDissociated_iff_jointlyDissociated (L : InfiniteExchangeableGraphLaw) :
    (exchangeableGraphLawEquivInfinite.symm L).IsDissociated ↔
      JointlyDissociated (arrayLaw L) fun p x => x p := by
  rw [isDissociated_iff_forall_indepFun_blockRestrict,
    jointlyDissociated_coord_iff_indepFun_blockRestrict]
  refine ⟨fun h => indepFun_blockRestrict_of_forall_Ico (jointlyExchangeable_arrayLaw L) h,
    fun h k l => h _ _ ?_⟩
  rw [Finset.disjoint_left]
  intro n hn hn'
  simp only [Finset.mem_Ico] at hn hn'
  omega

/-- **Dissociation is extremality** for exchangeable laws on infinite graphs, read through their
array laws. -/
theorem isDissociated_iff_arrayLaw_mem_extremePoints (L : InfiniteExchangeableGraphLaw) :
    (exchangeableGraphLawEquivInfinite.symm L).IsDissociated ↔
      arrayLaw L ∈ extremePoints ℝ≥0∞
        (jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag Bool false) := by
  rw [isDissociated_iff_jointlyDissociated,
    jointlyDissociated_iff_mem_extremePoints_on (jointlyExchangeable_arrayLaw L)
      (arrayLaw_compl_symmetric L),
    jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag_eq]

/-- **Convex-mixture compatibility**: the pushforward along the adjacency array is linear on the
underlying measures. -/
theorem arrayLaw_smul_add_smul (L₁ L₂ : InfiniteExchangeableGraphLaw) (a b : ℝ≥0∞) :
    (a • L₁.law + b • L₂.law).map graphArray = a • arrayLaw L₁ + b • arrayLaw L₂ := by
  simp only [arrayLaw]
  rw [Measure.map_add _ _ measurable_graphArray,
    Measure.map_smul a measurable_graphArray.aemeasurable,
    Measure.map_smul b measurable_graphArray.aemeasurable]

end DenseGraphLimits

end TauCeti
