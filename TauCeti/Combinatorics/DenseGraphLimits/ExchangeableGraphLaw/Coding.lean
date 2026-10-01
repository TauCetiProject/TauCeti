/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.ArrayLaw
public import TauCeti.Combinatorics.DenseGraphLimits.Sampling.Infinite
public import TauCeti.Probability.Exchangeability.Arrays.AldousHoover.Dissociated
import TauCeti.MeasureTheory.Measure.GiryMonad
import TauCeti.MeasureTheory.Measure.ProductKernel
import TauCeti.Probability.Independence.InfinitePi

/-!
# Aldous–Hoover codings of graphs are graphon samples

A jointly exchangeable Aldous–Hoover coding with values in `Bool` reads off a graph on `ℕ`: the
pair `{i, j}` is an edge when the coding puts `true` at `(i, j)` or at `(j, i)`, the diagonal being
ignored. This file identifies the law of that graph with the graphon sampling laws: the graph law
of a coding is a mixture of joint sampling laws, and every joint sampling law on the unit interval
is the graph law of a coding.

For a coding `g : I × I × I → Bool` that ignores its global variable, the two entries at `(i, j)`
and `(j, i)` read the vertex variables `U i`, `U j` and the one shared cell variable `U {i, j}`.
Conditionally on the vertex variables, the cells are independent and the pair `{i, j}` is an edge
with probability
```text
codingGraphon g (x, y) = P(g (x, y, ξ) ∨ g (y, x, ξ)),   ξ uniform on I,
```
at `x = U i`, `y = U j`. This is a graphon on `(I, volume)`, symmetric by construction and with no
condition on `g` beyond measurability, and the graph read off the coding has the joint sampling law
`infiniteSampleLaw (codingGraphon g)`.

A coding that does use its global variable is a uniform mixture of the codings obtained by freezing
that variable (`TauCeti.Probability.AldousHoover.map_jointArray_eq_bind_frozen`), so its graph law
is the corresponding mixture of joint sampling laws. Conversely every graphon `W` on `(I, volume)`
has a coding, `graphonCoding W`, which joins two vertices when the cell variable falls below the
graphon value, and whose coding graphon is `W` itself.

## Main definitions

* `TauCeti.DenseGraphLimits.codingGraphon` — the graphon of a global-free `Bool`-valued coding.
* `TauCeti.DenseGraphLimits.graphonCoding` — the threshold coding of a graphon on `(I, volume)`.

## Main results

* `TauCeti.DenseGraphLimits.graphLawOfArray_map_jointArray_snd` — the graph law of a global-free
  coding is the joint sampling law of its coding graphon.
* `TauCeti.DenseGraphLimits.graphLawOfArray_map_jointArray` — the graph law of any joint coding is
  the uniform mixture, over the global variable, of the joint sampling laws of the frozen codings.
* `TauCeti.DenseGraphLimits.codingGraphon_graphonCoding` and
  `TauCeti.DenseGraphLimits.graphLawOfArray_map_jointArray_graphonCoding` — every graphon on the
  unit interval is the coding graphon of its threshold coding, so its joint sampling law is the
  graph law of a coding.

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33–61, Sections 5 and 7.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval TauCeti.Probability.AldousHoover

namespace TauCeti

namespace DenseGraphLimits

variable (g : I × I × I → Bool)

/-! ### The coding graphon -/

/-- The cell values at which a coding joins vertices with values `x` and `y`, in either
orientation. -/
private def pairCells (x y : I) : Set I :=
  {t | g (x, y, t) = true ∨ g (y, x, t) = true}

private theorem pairCells_comm (x y : I) : pairCells g x y = pairCells g y x :=
  Set.ext fun _ => or_comm

private theorem measurableSet_pairCells_uncurry (hg : Measurable g) :
    MeasurableSet {q : (I × I) × I | q.2 ∈ pairCells g q.1.1 q.1.2} :=
  (measurableSet_eq_fun (by fun_prop) measurable_const).union
    (measurableSet_eq_fun (by fun_prop) measurable_const)

private theorem measurableSet_pairCells (hg : Measurable g) (x y : I) :
    MeasurableSet (pairCells g x y) :=
  measurable_prodMk_left (x := (x, y)) (measurableSet_pairCells_uncurry g hg)

/-- **The graphon of a global-free coding.** For a coding `g` of the cell variable from two vertex
variables, the value at `(x, y)` is the probability, over a uniform cell variable `t`, that `g`
joins `x` and `y` in either orientation: `g (x, y, t)` or `g (y, x, t)`. This is the edge
probability of the graph read off the coding, conditionally on the two vertex variables. -/
def codingGraphon (hg : Measurable g) : Graphon I (volume : Measure I) where
  toFun x y := volume.real (pairCells g x y)
  symm' x y := by rw [pairCells_comm]
  meas' := (measurable_measure_prodMk_left (measurableSet_pairCells_uncurry g hg)).ennreal_toReal
  bdd' := ⟨1, fun _ _ => by
    rw [abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one⟩
  mem01' _ _ := ⟨measureReal_nonneg, measureReal_le_one⟩

/-- The value of the coding graphon is the probability that the coding joins the two vertex values
in either orientation. -/
@[simp]
theorem codingGraphon_apply (hg : Measurable g) (x y : I) :
    codingGraphon g hg x y = volume.real {t : I | g (x, y, t) = true ∨ g (y, x, t) = true} :=
  (rfl)

/-! ### The graph read off a coding -/

/-- The graph read off a global-free coding from vertex values `x` and cell values `ξ`: the graph
of the array `(i, j) ↦ g (x i, x j, ξ {i, j})`. -/
private def codingGraph (x : ℕ → I) (ξ : Sym2 ℕ → I) : SimpleGraph ℕ :=
  graphOfArray fun p => g (x p.1, x p.2, ξ s(p.1, p.2))

private theorem codingGraph_adj (x : ℕ → I) (ξ : Sym2 ℕ → I) (i j : ℕ) :
    (codingGraph g x ξ).Adj i j ↔ i ≠ j ∧ ξ s(i, j) ∈ pairCells g (x i) (x j) := by
  rw [codingGraph, graphOfArray_adj, Sym2.eq_swap (a := j), pairCells, Set.mem_ofPred_eq]

private theorem measurable_codingGraph (hg : Measurable g) :
    Measurable fun p : (ℕ → I) × (Sym2 ℕ → I) => codingGraph g p.1 p.2 :=
  measurable_graphOfArray.comp <| Measurable.of_eval fun q => by fun_prop

/-- The cells of the window pair `e` that reproduce the pattern `H` there: those at which the
coding joins the endpoints of `e` if `H` does, and the others if it does not. -/
private def cellTarget {n : ℕ} (y : Fin n → I) (H : SimpleGraph (Fin n)) (e : Sym2 (Fin n)) :
    Set I :=
  open Classical in
  if e ∈ H.edgeSet then Sym2.lift ⟨fun a b => pairCells g (y a) (y b),
      fun a b => pairCells_comm g (y a) (y b)⟩ e
  else (Sym2.lift ⟨fun a b => pairCells g (y a) (y b),
      fun a b => pairCells_comm g (y a) (y b)⟩ e)ᶜ

private theorem mem_cellTarget_mk {n : ℕ} (y : Fin n → I) (H : SimpleGraph (Fin n)) (a b : Fin n)
    (t : I) : t ∈ cellTarget g y H s(a, b) ↔ (t ∈ pairCells g (y a) (y b) ↔ H.Adj a b) := by
  classical
  rw [cellTarget]
  split_ifs with h <;> simp_all

/-- A window of the coding graph is a prescribed pattern exactly when the cell of every window
pair lands in its target. -/
private theorem restrictFin_codingGraph_eq_iff (x : ℕ → I) (ξ : Sym2 ℕ → I) {n : ℕ}
    (H : SimpleGraph (Fin n)) :
    (codingGraph g x ξ).restrictFin n = H ↔
      ∀ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
        ξ (Sym2.map Fin.val e) ∈ cellTarget g (fun i : Fin n => x i) H e := by
  constructor
  · rintro rfl e he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : a ≠ b := by simpa using he
      rw [Sym2.map_mk, mem_cellTarget_mk, SimpleGraph.restrictFin_adj, codingGraph_adj]
      simp [Fin.val_ne_iff.mpr hab]
  · intro h
    ext a b
    rw [SimpleGraph.restrictFin_adj, codingGraph_adj]
    by_cases hab : a = b
    · subst hab
      simp
    · have := h s(a, b) (by simpa using hab)
      rw [Sym2.map_mk, mem_cellTarget_mk] at this
      simp [Fin.val_ne_iff.mpr hab, this]

/-- The probability that a uniform cell lands in its target is the factor the sampling mass of the
coding graphon assigns to that pair. -/
private theorem volume_cellTarget (hg : Measurable g) {n : ℕ} (y : Fin n → I)
    (H : SimpleGraph (Fin n)) (e : Sym2 (Fin n)) :
    volume (cellTarget g y H e) = ENNReal.ofReal (open Classical in
      if e ∈ H.edgeFinset then edgeFactor (codingGraphon g hg) y e
      else 1 - edgeFactor (codingGraphon g hg) y e) := by
  classical
  induction e using Sym2.ind with
  | _ a b =>
    have hvol : volume (pairCells g (y a) (y b)) =
        ENNReal.ofReal (edgeFactor (codingGraphon g hg) y s(a, b)) := by
      rw [edgeFactor_mk, codingGraphon_apply, ← pairCells, ofReal_measureReal]
    rw [cellTarget]
    split_ifs with h h' h'
    · exact hvol
    · exact absurd (SimpleGraph.mem_edgeFinset.mpr h) h'
    · exact absurd (SimpleGraph.mem_edgeFinset.mp h') h
    · rw [Sym2.lift_mk, prob_compl_eq_one_sub (measurableSet_pairCells g hg _ _), hvol,
        ← ENNReal.ofReal_one, ENNReal.ofReal_sub _ (edgeFactor_nonneg _ y _)]

private theorem measurableSet_cellTarget (hg : Measurable g) {n : ℕ} (y : Fin n → I)
    (H : SimpleGraph (Fin n)) (e : Sym2 (Fin n)) : MeasurableSet (cellTarget g y H e) := by
  classical
  induction e using Sym2.ind with
  | _ a b =>
    rw [cellTarget]
    split_ifs
    · exact measurableSet_pairCells g hg _ _
    · exact (measurableSet_pairCells g hg _ _).compl

/-- At fixed vertex values, independent uniform cells reproduce a prescribed window of the coding
graph with probability the conditional sampling mass of the coding graphon. -/
private theorem infinitePi_setOf_restrictFin_codingGraph_eq (hg : Measurable g) (x : ℕ → I)
    {n : ℕ} (H : SimpleGraph (Fin n)) :
    (Measure.infinitePi fun _ : Sym2 ℕ => (volume : Measure I))
        {ξ | (codingGraph g x ξ).restrictFin n = H} =
      ENNReal.ofReal (sampleIntegrand (codingGraphon g hg) H fun i : Fin n => x i) := by
  classical
  set y : Fin n → I := fun i => x i
  set W := codingGraphon g hg
  have hφ : Measurable fun (ξ : Sym2 ℕ → I) (e : Sym2 (Fin n)) => ξ (Sym2.map Fin.val e) :=
    Measurable.of_eval fun _ => measurable_pi_apply _
  have hbox : MeasurableSet (Set.pi ((⊤ : SimpleGraph (Fin n)).edgeFinset : Set (Sym2 (Fin n)))
      (cellTarget g y H)) :=
    MeasurableSet.pi (Finset.countable_toSet _) fun e _ => measurableSet_cellTarget g hg y H e
  have hset : {ξ : Sym2 ℕ → I | (codingGraph g x ξ).restrictFin n = H} =
      (fun (ξ : Sym2 ℕ → I) (e : Sym2 (Fin n)) => ξ (Sym2.map Fin.val e)) ⁻¹'
        Set.pi ((⊤ : SimpleGraph (Fin n)).edgeFinset : Set (Sym2 (Fin n))) (cellTarget g y H) := by
    ext ξ
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Finset.mem_coe]
    exact restrictFin_codingGraph_eq_iff g x ξ H
  have hnonneg : ∀ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
      0 ≤ (if e ∈ H.edgeFinset then edgeFactor W y e else 1 - edgeFactor W y e) := by
    intro e _
    split_ifs
    · exact edgeFactor_nonneg W y e
    · linarith [edgeFactor_le_one W y e]
  rw [hset, ← Measure.map_apply hφ hbox,
    Measure.map_infinitePi_infinitePi_of_inj (Sym2.map.injective Fin.val_injective),
    Measure.infinitePi_pi _ fun e _ => measurableSet_cellTarget g hg y H e,
    sampleIntegrand_eq_prod_edgeFinset_top, ENNReal.ofReal_prod_of_nonneg hnonneg]
  exact Finset.prod_congr rfl fun e _ => volume_cellTarget g hg y H e

/-! ### The graph law of a coding -/

/-- Under the canonical noise law, the vertex and cell noise families are independent families of
independent uniform variables. -/
private theorem map_vertex_cell_noiseMeasure :
    (noiseMeasure Unit (Sym2 ℕ)).map
        (fun u => (fun i => u (.vertex () i), fun c => u (.cell c))) =
      (Measure.infinitePi fun _ : ℕ => (volume : Measure I)).prod
        (Measure.infinitePi fun _ : Sym2 ℕ => (volume : Measure I)) := by
  have hvertex : Function.Injective
      fun i : ℕ => (NoiseIndex.vertex () i : NoiseIndex Unit (Sym2 ℕ)) :=
    fun _ _ h => by cases h; rfl
  have hcell : Function.Injective
      fun c : Sym2 ℕ => (NoiseIndex.cell c : NoiseIndex Unit (Sym2 ℕ)) :=
    fun _ _ h => by cases h; rfl
  have hdisj : Disjoint (Set.range fun i : ℕ => (NoiseIndex.vertex () i : NoiseIndex Unit (Sym2 ℕ)))
      (Set.range fun c : Sym2 ℕ => (NoiseIndex.cell c : NoiseIndex Unit (Sym2 ℕ))) :=
    Set.disjoint_left.mpr fun _ ⟨_, hi⟩ ⟨_, hc⟩ => by subst hi; cases hc
  rw [noiseMeasure_def, TauCeti.Probability.infinitePi_map_pair_comp _ hcell hdisj,
    Measure.map_infinitePi_infinitePi_of_inj hvertex]

/-- **The graph law of a global-free coding is a joint sampling law.** The graph read off the joint
Aldous–Hoover coding `(i, j) ↦ g (U i, U j, U {i, j})`, which ignores the global variable, has the
law of the infinite `W`-random graph for the coding graphon `W = codingGraphon g`. -/
theorem graphLawOfArray_map_jointArray_snd (hg : Measurable g) :
    graphLawOfArray ((noiseMeasure Unit (Sym2 ℕ)).map fun u p => jointArray (fun q => g q.2) p u) =
      infiniteSampleLaw (codingGraphon g hg) := by
  classical
  set ψ : (NoiseIndex Unit (Sym2 ℕ) → I) → (ℕ → I) × (Sym2 ℕ → I) :=
    fun u => (fun i => u (.vertex () i), fun c => u (.cell c))
  have hψ : Measurable ψ := by fun_prop
  have hread : (graphOfArray ∘ fun u p => jointArray (fun q => g q.2) p u) =
      (fun p : (ℕ → I) × (Sym2 ℕ → I) => codingGraph g p.1 p.2) ∘ ψ := by
    funext u
    simp only [Function.comp_apply, jointArray_apply, codingGraph, ψ]
  rw [graphLawOfArray_def, Measure.map_map measurable_graphOfArray
      (measurable_jointArray (fun q => g q.2) (by fun_prop)), hread,
    ← Measure.map_map (measurable_codingGraph g hg) hψ, map_vertex_cell_noiseMeasure]
  refine measure_ext_of_map_restrictFin fun n => ?_
  rw [infiniteSampleLaw_map_restrictFin]
  refine Measure.ext_of_singleton fun H => ?_
  have hfiber : MeasurableSet ((fun G : SimpleGraph ℕ => G.restrictFin n) ⁻¹' {H}) :=
    SimpleGraph.measurable_restrictFin n (measurableSet_singleton H)
  rw [Measure.map_apply (SimpleGraph.measurable_restrictFin n) (measurableSet_singleton H),
    Measure.map_apply (measurable_codingGraph g hg) hfiber,
    Measure.prod_apply (measurable_codingGraph g hg hfiber), sampleGraph_singleton]
  have hslice : ∀ x : ℕ → I, Prod.mk x ⁻¹'
      ((fun p : (ℕ → I) × (Sym2 ℕ → I) => codingGraph g p.1 p.2) ⁻¹'
        ((fun G : SimpleGraph ℕ => G.restrictFin n) ⁻¹' {H})) =
      {ξ : Sym2 ℕ → I | (codingGraph g x ξ).restrictFin n = H} := fun _ => rfl
  simp_rw [hslice, infinitePi_setOf_restrictFin_codingGraph_eq g hg]
  -- average the conditional window masses over the vertex values, of which only the first `n`
  -- are read
  have hmap : (Measure.infinitePi fun _ : ℕ => (volume : Measure I)).map
      (fun x (i : Fin n) => x (i : ℕ)) = Measure.pi fun _ : Fin n => (volume : Measure I) :=
    TauCeti.MeasureTheory.map_prefixProj_infinitePi_const
      (⟨volume, inferInstance⟩ : ProbabilityMeasure I) n
  have hmeasurable : Measurable fun y : Fin n → I =>
      ENNReal.ofReal (sampleIntegrand (codingGraphon g hg) H y) :=
    (measurable_sampleIntegrand _ H).ennreal_ofReal
  rw [← lintegral_map hmeasurable (by fun_prop), hmap,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_sampleIntegrand _ H)
      (Filter.Eventually.of_forall (sampleIntegrand_nonneg _ H)), sampleMass_def]

/-- **The graph law of a joint coding is a mixture of joint sampling laws.** The graph read off the
joint Aldous–Hoover coding `(i, j) ↦ f (U, U i, U j, U {i, j})` has the law obtained by averaging,
over a uniform value `t` of the global variable, the joint sampling law of the coding graphon of
the frozen coding `(x, y, s) ↦ f (t, x, y, s)`. -/
theorem graphLawOfArray_map_jointArray {f : I × I × I × I → Bool} (hf : Measurable f) :
    graphLawOfArray ((noiseMeasure Unit (Sym2 ℕ)).map fun u p => jointArray f p u) =
      (volume : Measure I).bind fun t =>
        infiniteSampleLaw (codingGraphon (fun q => f (t, q)) (hf.comp measurable_prodMk_left)) := by
  have hΦ : Measurable fun x : I × (NoiseIndex Unit (Sym2 ℕ) → I) =>
      fun p => jointArray (fun q => f (x.1, q.2)) p x.2 :=
    Measurable.of_eval fun p => by simp only [jointArray_apply]; fun_prop
  have hκ : Measurable fun t : I =>
      (noiseMeasure Unit (Sym2 ℕ)).map fun u p => jointArray (fun q => f (t, q.2)) p u := by
    have hsection : (fun t : I =>
        (noiseMeasure Unit (Sym2 ℕ)).map fun u p => jointArray (fun q => f (t, q.2)) p u) =
          fun t => ((noiseMeasure Unit (Sym2 ℕ)).map (Prod.mk t)).map
            fun x : I × (NoiseIndex Unit (Sym2 ℕ) → I) =>
              fun p => jointArray (fun q => f (x.1, q.2)) p x.2 := by
      funext t
      rw [Measure.map_map hΦ measurable_prodMk_left]
      -- the composite with `Prod.mk t` is the frozen coding itself
      rfl
    rw [hsection]
    exact (Measure.measurable_map _ hΦ).comp Measurable.map_prodMk_left
  rw [map_jointArray_eq_bind_frozen hf, graphLawOfArray_def,
    TauCeti.MeasureTheory.map_bind hκ.aemeasurable measurable_graphOfArray]
  congr 1
  funext t
  rw [← graphLawOfArray_def]
  exact graphLawOfArray_map_jointArray_snd (fun q => f (t, q)) (hf.comp measurable_prodMk_left)

/-! ### The threshold coding of a graphon -/

/-- **The threshold coding of a graphon on the unit interval.** The coding joins two vertices with
values `x` and `y` when the cell variable falls below the graphon value `W x y`. -/
def graphonCoding (W : Graphon I (volume : Measure I)) : I × I × I → Bool :=
  fun q => decide (q.2.2 < ⟨W q.1 q.2.1, W.mem_Icc q.1 q.2.1⟩)

/-- The threshold coding is `true` exactly below the graphon value. -/
@[simp]
theorem graphonCoding_apply (W : Graphon I (volume : Measure I)) (x y t : I) :
    graphonCoding W (x, y, t) = decide ((t : ℝ) < W x y) :=
  (rfl)

/-- The threshold coding of a graphon is measurable. -/
theorem measurable_graphonCoding (W : Graphon I (volume : Measure I)) :
    Measurable (graphonCoding W) := by
  refine measurable_to_bool ?_
  have : graphonCoding W ⁻¹' {true} = {q : I × I × I | (q.2.2 : ℝ) < W q.1 q.2.1} := by
    ext ⟨x, y, t⟩
    simp
  rw [this]
  exact measurableSet_lt (by fun_prop)
    (W.measurable.comp (measurable_fst.prodMk measurable_snd.fst))

/-- **Every graphon on the unit interval is a coding graphon:** the coding graphon of the
threshold coding of `W` is `W`. -/
@[simp]
theorem codingGraphon_graphonCoding (W : Graphon I (volume : Measure I)) :
    codingGraphon (graphonCoding W) (measurable_graphonCoding W) = W := by
  ext x y
  have hcells : {t : I | graphonCoding W (x, y, t) = true ∨ graphonCoding W (y, x, t) = true} =
      Set.Iio ⟨W x y, W.mem_Icc x y⟩ := by
    ext t
    simp [W.symm y x, ← Subtype.coe_lt_coe]
  rw [codingGraphon_apply, hcells, measureReal_def, volume_Iio,
    ENNReal.toReal_ofReal (W.nonneg x y)]

/-- **Every joint sampling law on the unit interval is the graph law of a coding:** the graph read
off the threshold coding of `W` has the law of the infinite `W`-random graph. -/
theorem graphLawOfArray_map_jointArray_graphonCoding (W : Graphon I (volume : Measure I)) :
    graphLawOfArray ((noiseMeasure Unit (Sym2 ℕ)).map
        fun u p => jointArray (fun q => graphonCoding W q.2) p u) =
      infiniteSampleLaw W := by
  rw [graphLawOfArray_map_jointArray_snd _ (measurable_graphonCoding W),
    codingGraphon_graphonCoding]

end DenseGraphLimits

end TauCeti
