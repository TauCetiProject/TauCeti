/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration
public import Mathlib.ModelTheory.Graph
public import Mathlib.MeasureTheory.Constructions.SimpleGraph
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import TauCeti.Combinatorics.SimpleGraph.Maps
import Mathlib.Tactic.FinCases
import TauCeti.Combinatorics.SimpleGraph.Measurable

/-!
# Simple graphs as relational configurations

The language of graphs, `FirstOrder.Language.graph`, has a single binary relation symbol `adj`. A
relational configuration of it is a truth value for every atom `adj(u, v)`, including the diagonal
atoms `adj(v, v)`. The configurations that are symmetric and false on the diagonal are exactly the
simple graphs: this file identifies `SimpleGraph V` with them as a measurable equivalence, and
shows that pulling a graph back along a vertex map corresponds to restricting its configuration.
Forgetting the simple-graph conditions, a configuration is just its array of truth values on the
adjacency atoms (`TauCeti.RelationalConfiguration.adjArrayEquiv`), and the array of a simple graph
is its adjacency array.

## Main definitions

* `TauCeti.RelationalConfiguration.IsSimpleGraph` — a configuration of the language of graphs is
  symmetric and irreflexive;
* `SimpleGraph.toRelationalConfiguration` — the configuration of a simple graph;
* `SimpleGraph.relationalConfigurationEquiv` — the measurable equivalence between simple graphs and
  symmetric irreflexive configurations;
* `TauCeti.RelationalConfiguration.adjArrayEquiv` — the measurable equivalence between
  configurations of the language of graphs and `Bool`-valued arrays.

## Main results

* `SimpleGraph.measurableEmbedding_toRelationalConfiguration` — on a countable vertex type, the
  encoding is a measurable embedding onto the simple-graph configurations
  (`SimpleGraph.range_toRelationalConfiguration`);
* `SimpleGraph.map_comap_toRelationalConfiguration` — a law on configurations concentrated on
  simple graphs is the encoding of its pullback to simple graphs;
* `SimpleGraph.toRelationalConfiguration_comap` — encoding a pulled-back graph is restricting its
  encoding; for laws, `SimpleGraph.map_comap_comap_toRelationalConfiguration` — pulling back to
  simple graphs commutes with restriction;
* `TauCeti.RelationalConfiguration.IsSimpleGraph.restrict` — restriction preserves symmetry and
  irreflexivity, also along non-injective vertex maps;
* `SimpleGraph.adjArrayEquiv_toRelationalConfiguration` — the array of the configuration of a
  simple graph is its adjacency array;
* `SimpleGraph.relationalConfigurationEquiv_comap` and
  `SimpleGraph.relationalConfigurationEquiv_symm_restrict` — the equivalence commutes with
  restriction in both directions.
-/

public section

noncomputable section

open MeasureTheory

open _root_.FirstOrder (Language)

namespace TauCeti

namespace RelationalConfiguration

variable {V W : Type*}

/-- The adjacency atom `adj(u, v)`. -/
def adjAtom (u v : V) : Atom Language.graph V := atom Language.adj ![u, v]

@[simp]
theorem adjAtom_map (f : V → W) (u v : V) : (adjAtom u v).map f = adjAtom (f u) (f v) := by
  simp only [adjAtom, Atom.map_atom]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Every atom of the language of graphs is an adjacency atom. -/
@[elab_as_elim]
theorem Atom.induction_adjAtom {motive : Atom Language.graph V → Prop}
    (h : ∀ u v : V, motive (adjAtom u v)) (a : Atom Language.graph V) : motive a := by
  induction a using Atom.induction_atom with
  | h R x =>
    cases R
    have hx : x = ![x 0, x 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hx]
    exact h (x 0) (x 1)

/-- A configuration of the language of graphs **is a simple graph** when adjacency is symmetric and
false on the diagonal. -/
def IsSimpleGraph (c : RelationalConfiguration Language.graph V) : Prop :=
  (∀ u v, c.eval (adjAtom u v) = c.eval (adjAtom v u)) ∧ ∀ v, c.eval (adjAtom v v) = false

/-- A configuration is a simple graph exactly when adjacency is symmetric and false on the
diagonal. -/
theorem isSimpleGraph_iff {c : RelationalConfiguration Language.graph V} :
    IsSimpleGraph c ↔
      (∀ u v, c.eval (adjAtom u v) = c.eval (adjAtom v u)) ∧ ∀ v, c.eval (adjAtom v v) = false :=
  Iff.rfl

/-- The simple graph of a symmetric irreflexive configuration. -/
def toSimpleGraph (c : RelationalConfiguration Language.graph V) (hc : IsSimpleGraph c) :
    SimpleGraph V where
  Adj u v := c.eval (adjAtom u v) = true
  symm := ⟨fun _ _ h => (hc.1 _ _).symm.trans h⟩
  loopless := ⟨fun v h => by simp [hc.2 v] at h⟩

@[simp]
theorem toSimpleGraph_adj (c : RelationalConfiguration Language.graph V) (hc : IsSimpleGraph c)
    (u v : V) : (toSimpleGraph c hc).Adj u v ↔ c.eval (adjAtom u v) = true := Iff.rfl

/-- Restriction preserves symmetry and irreflexivity. The vertex map need not be injective: a pair
of distinct vertices with the same image reads a diagonal atom, which is false. -/
theorem IsSimpleGraph.restrict {c : RelationalConfiguration Language.graph W}
    (hc : IsSimpleGraph c) (f : V → W) : IsSimpleGraph (c.restrict f) :=
  ⟨fun u v => by simpa using hc.1 (f u) (f v), fun v => by simpa using hc.2 (f v)⟩

/-- On a countable vertex type, the simple-graph configurations form a measurable set: a countable
intersection of conditions on one or two atoms. -/
theorem measurableSet_setOf_isSimpleGraph [Countable V] :
    MeasurableSet {c : RelationalConfiguration Language.graph V | IsSimpleGraph c} := by
  simp only [IsSimpleGraph, Set.ofPred_and, Set.ofPred_forall]
  exact (MeasurableSet.iInter fun u => MeasurableSet.iInter fun v =>
      ((measurable_eval (adjAtom u v)).prodMk (measurable_eval (adjAtom v u)))
        (.of_discrete : MeasurableSet {p : Bool × Bool | p.1 = p.2})).inter
    (MeasurableSet.iInter fun v => measurable_eval (adjAtom v v) (measurableSet_singleton false))

/-- Restricting a law concentrated on simple graphs gives a law concentrated on simple graphs. -/
theorem ae_isSimpleGraph_map_restrict [Countable V] (f : V → W)
    {μ : Measure (RelationalConfiguration Language.graph W)} (hμ : ∀ᵐ c ∂μ, IsSimpleGraph c) :
    ∀ᵐ c ∂μ.map (restrict f), IsSimpleGraph c := by
  rw [ae_map_iff (measurable_restrict f).aemeasurable measurableSet_setOf_isSimpleGraph]
  filter_upwards [hμ] with c hc using hc.restrict f

/-! ### Configurations as arrays -/

/-- The structure of the language of graphs in which `adj(u, v)` holds exactly when the array
`x` is `true` at `(u, v)`. -/
@[instance_reducible]
private def arrayStructure (x : V × V → Bool) : Language.graph.Structure V where
  RelMap | .adj => fun v => x (v 0, v 1) = true

/-- In the structure of an array, `adj` holds at a pair of vertices exactly when the array is
`true` there. -/
private theorem relMap_adj_arrayStructure (x : V × V → Bool) (v : Fin 2 → V) :
    (arrayStructure x).RelMap .adj v ↔ x (v 0, v 1) = true := Iff.rfl

/-- The configuration of an array: `adj(u, v)` takes the value of the array at `(u, v)`. -/
private noncomputable def ofArray (x : V × V → Bool) : RelationalConfiguration Language.graph V :=
  @ofStructure Language.graph V (arrayStructure x)

private theorem eval_ofArray_adjAtom (x : V × V → Bool) (u v : V) :
    (ofArray x).eval (adjAtom u v) = x (u, v) := by
  rw [ofArray, adjAtom, @eval_ofStructure _ _ (arrayStructure x)]
  simp [relMap_adj_arrayStructure]

private theorem measurable_ofArray : Measurable (ofArray : (V × V → Bool) → _) :=
  measurable_iff.2 fun a => by
    induction a using Atom.induction_adjAtom with
    | h u v =>
      simp only [eval_ofArray_adjAtom]
      exact measurable_pi_apply _

/-- **Configurations of the language of graphs are `Bool`-valued arrays**: a configuration is
determined by its truth values on the adjacency atoms `adj(u, v)`, one for each ordered pair of
vertices, and these truth values can be prescribed freely. -/
noncomputable def adjArrayEquiv : RelationalConfiguration Language.graph V ≃ᵐ (V × V → Bool) where
  toFun c p := c.eval (adjAtom p.1 p.2)
  invFun := ofArray
  left_inv c := ext fun a => by
    induction a using Atom.induction_adjAtom with
    | h u v => exact eval_ofArray_adjAtom _ u v
  right_inv x := funext fun p => eval_ofArray_adjAtom x p.1 p.2
  measurable_toFun := measurable_pi_iff.2 fun _ => measurable_eval _
  measurable_invFun := measurable_ofArray

/-- The array of a configuration records its truth value on each adjacency atom. -/
@[simp]
theorem adjArrayEquiv_apply (c : RelationalConfiguration Language.graph V) (p : V × V) :
    adjArrayEquiv c p = c.eval (adjAtom p.1 p.2) := (rfl)

/-- The configuration of an array takes the prescribed truth value on each adjacency atom. -/
@[simp]
theorem eval_adjArrayEquiv_symm_adjAtom (x : V × V → Bool) (u v : V) :
    (adjArrayEquiv.symm x).eval (adjAtom u v) = x (u, v) :=
  eval_ofArray_adjAtom x u v

end RelationalConfiguration

end TauCeti

namespace SimpleGraph

open TauCeti TauCeti.RelationalConfiguration

variable {V W : Type*}

/-- The configuration of a simple graph, read off its first-order structure. -/
def toRelationalConfiguration (G : SimpleGraph V) : RelationalConfiguration Language.graph V :=
  @ofStructure Language.graph V G.structure

open Classical in
@[simp]
theorem eval_toRelationalConfiguration_adjAtom (G : SimpleGraph V) (u v : V) :
    G.toRelationalConfiguration.eval (adjAtom u v) = decide (G.Adj u v) := by
  simp only [toRelationalConfiguration, adjAtom, eval_ofStructure]
  rfl

theorem isSimpleGraph_toRelationalConfiguration (G : SimpleGraph V) :
    IsSimpleGraph G.toRelationalConfiguration := by
  classical
  refine ⟨fun u v => ?_, fun v => ?_⟩ <;> simp [G.adj_comm]

/-- **Simple graphs are the symmetric irreflexive configurations** of the language of graphs, as a
measurable equivalence. -/
def relationalConfigurationEquiv :
    SimpleGraph V ≃ᵐ {c : RelationalConfiguration Language.graph V // IsSimpleGraph c} where
  toFun G := ⟨G.toRelationalConfiguration, G.isSimpleGraph_toRelationalConfiguration⟩
  invFun c := toSimpleGraph c.1 c.2
  left_inv G := by
    classical
    ext u v
    simp
  right_inv c := by
    classical
    refine Subtype.ext (RelationalConfiguration.ext fun a => ?_)
    induction a using Atom.induction_adjAtom with
    | h u v => simp
  measurable_toFun := by
    classical
    refine Measurable.subtype_mk (measurable_iff.2 fun a => ?_)
    induction a using Atom.induction_adjAtom with
    | h u v =>
      simp only [eval_toRelationalConfiguration_adjAtom]
      exact (Measurable.of_discrete (f := fun p : Prop => decide p)).comp
        (measurable_iff_adj.1 measurable_id u v)
  measurable_invFun :=
    measurable_iff_adj.2 fun u v =>
      (Measurable.of_discrete (f := fun b : Bool => b = true)).comp
        ((measurable_eval (adjAtom u v)).comp measurable_subtype_coe)

/-- Encoding a simple graph as a configuration is measurable. -/
@[fun_prop]
theorem measurable_toRelationalConfiguration :
    Measurable
      (toRelationalConfiguration : SimpleGraph V → RelationalConfiguration Language.graph V) :=
  measurable_subtype_coe.comp relationalConfigurationEquiv.measurable

@[simp]
theorem coe_relationalConfigurationEquiv (G : SimpleGraph V) :
    (relationalConfigurationEquiv G : RelationalConfiguration Language.graph V) =
      G.toRelationalConfiguration := (rfl)

@[simp]
theorem relationalConfigurationEquiv_symm_apply
    (c : {c : RelationalConfiguration Language.graph V // IsSimpleGraph c}) :
    relationalConfigurationEquiv.symm c = toSimpleGraph c.1 c.2 := (rfl)

/-- The configurations of simple graphs are exactly the simple-graph configurations. -/
@[simp]
theorem range_toRelationalConfiguration :
    Set.range
        (toRelationalConfiguration : SimpleGraph V → RelationalConfiguration Language.graph V) =
      {c | IsSimpleGraph c} := by
  refine Set.Subset.antisymm (Set.range_subset_iff.2 isSimpleGraph_toRelationalConfiguration)
    fun c hc => ⟨relationalConfigurationEquiv.symm ⟨c, hc⟩,
      congrArg Subtype.val (relationalConfigurationEquiv.apply_symm_apply ⟨c, hc⟩)⟩

/-- On a countable vertex type, encoding simple graphs as configurations is a measurable embedding,
so laws on simple graphs are the laws on configurations concentrated on simple graphs. -/
theorem measurableEmbedding_toRelationalConfiguration [Countable V] :
    MeasurableEmbedding
      (toRelationalConfiguration : SimpleGraph V → RelationalConfiguration Language.graph V) :=
  (MeasurableEmbedding.subtype_coe measurableSet_setOf_isSimpleGraph).comp
    relationalConfigurationEquiv.measurableEmbedding

/-- The encoding of a law on simple graphs is concentrated on simple graphs. -/
theorem ae_isSimpleGraph_map_toRelationalConfiguration [Countable V] (μ : Measure (SimpleGraph V)) :
    ∀ᵐ c ∂μ.map toRelationalConfiguration, IsSimpleGraph c :=
  measurableEmbedding_toRelationalConfiguration.ae_map_iff.2
    (ae_of_all _ isSimpleGraph_toRelationalConfiguration)

/-- A law on configurations concentrated on simple graphs is the encoding of its pullback to
simple graphs. -/
theorem map_comap_toRelationalConfiguration [Countable V]
    {μ : Measure (RelationalConfiguration Language.graph V)} (hμ : ∀ᵐ c ∂μ, IsSimpleGraph c) :
    (μ.comap toRelationalConfiguration).map toRelationalConfiguration = μ := by
  rw [measurableEmbedding_toRelationalConfiguration.map_comap, range_toRelationalConfiguration]
  exact Measure.restrict_eq_self_of_ae_mem hμ

/-- The pullback to simple graphs of a probability law concentrated on simple graphs is a
probability law. -/
theorem isProbabilityMeasure_comap_toRelationalConfiguration [Countable V]
    {μ : Measure (RelationalConfiguration Language.graph V)} [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ c ∂μ, IsSimpleGraph c) :
    IsProbabilityMeasure (μ.comap toRelationalConfiguration) :=
  measurableEmbedding_toRelationalConfiguration.isProbabilityMeasure_comap <| by
    rwa [range_toRelationalConfiguration]

/-- The array of the configuration of a simple graph is its adjacency array. -/
@[simp]
theorem adjArrayEquiv_toRelationalConfiguration (G : SimpleGraph V) :
    adjArrayEquiv G.toRelationalConfiguration = G.adjArray := by
  classical
  funext ⟨u, v⟩
  simp

/-! ### Compatibility with restriction -/

/-- **Encoding commutes with restriction**: the configuration of a pulled-back graph is the
restriction of the configuration. -/
theorem toRelationalConfiguration_comap (f : V → W) (G : SimpleGraph W) :
    (G.comap f).toRelationalConfiguration = G.toRelationalConfiguration.restrict f := by
  classical
  ext a
  induction a using Atom.induction_adjAtom with
  | h u v => simp

/-- Encoding commutes with restriction, as an identity of maps. -/
theorem toRelationalConfiguration_comp_comap (f : V → W) :
    toRelationalConfiguration ∘ SimpleGraph.comap f =
      restrict f ∘ (toRelationalConfiguration : SimpleGraph W → _) :=
  funext fun G => toRelationalConfiguration_comap f G

/-- For laws concentrated on simple graphs, pulling back to simple graphs commutes with
restriction. -/
theorem map_comap_comap_toRelationalConfiguration [Countable V] [Countable W] (f : V → W)
    {μ : Measure (RelationalConfiguration Language.graph W)} (hμ : ∀ᵐ c ∂μ, IsSimpleGraph c) :
    (μ.comap toRelationalConfiguration).map (SimpleGraph.comap f) =
      (μ.map (restrict f)).comap toRelationalConfiguration := by
  refine measurableEmbedding_toRelationalConfiguration.map_injective ?_
  rw [Measure.map_map measurable_toRelationalConfiguration (measurable_comap _),
    toRelationalConfiguration_comp_comap,
    ← Measure.map_map (measurable_restrict _) measurable_toRelationalConfiguration,
    map_comap_toRelationalConfiguration hμ,
    map_comap_toRelationalConfiguration (ae_isSimpleGraph_map_restrict f hμ)]

theorem relationalConfigurationEquiv_comap (f : V → W) (G : SimpleGraph W) :
    relationalConfigurationEquiv (G.comap f) =
      ⟨(relationalConfigurationEquiv G : RelationalConfiguration Language.graph W).restrict f,
        (relationalConfigurationEquiv G).2.restrict f⟩ :=
  Subtype.ext (toRelationalConfiguration_comap f G)

/-- Decoding commutes with restriction. -/
theorem relationalConfigurationEquiv_symm_restrict (f : V → W)
    (c : {c : RelationalConfiguration Language.graph W // IsSimpleGraph c}) :
    relationalConfigurationEquiv.symm ⟨c.1.restrict f, c.2.restrict f⟩ =
      (relationalConfigurationEquiv.symm c).comap f := by
  ext u v
  simp

end SimpleGraph
