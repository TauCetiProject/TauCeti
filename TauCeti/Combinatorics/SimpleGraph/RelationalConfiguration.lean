/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration
public import Mathlib.ModelTheory.Graph
public import Mathlib.MeasureTheory.Constructions.SimpleGraph
public import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Tactic.FinCases

/-!
# Simple graphs as relational configurations

The language of graphs, `FirstOrder.Language.graph`, has a single binary relation symbol `adj`. A
relational configuration of it is a truth value for every atom `adj(u, v)`, including the diagonal
atoms `adj(v, v)`. The configurations that are symmetric and false on the diagonal are exactly the
simple graphs: this file identifies `SimpleGraph V` with them as a measurable equivalence, and
shows that pulling a graph back along a vertex map corresponds to restricting its configuration.

## Main definitions

* `TauCeti.RelationalConfiguration.IsSimpleGraph` — a configuration of the language of graphs is
  symmetric and irreflexive;
* `SimpleGraph.toRelationalConfiguration` — the configuration of a simple graph;
* `SimpleGraph.relationalConfigurationEquiv` — the measurable equivalence between simple graphs and
  symmetric irreflexive configurations.

## Main results

* `SimpleGraph.toRelationalConfiguration_comap` — encoding a pulled-back graph is restricting its
  encoding;
* `TauCeti.RelationalConfiguration.IsSimpleGraph.restrict` — restriction preserves symmetry and
  irreflexivity, also along non-injective vertex maps;
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

/-! ### Compatibility with restriction -/

/-- **Encoding commutes with restriction**: the configuration of a pulled-back graph is the
restriction of the configuration. -/
theorem toRelationalConfiguration_comap (f : V → W) (G : SimpleGraph W) :
    (G.comap f).toRelationalConfiguration = G.toRelationalConfiguration.restrict f := by
  classical
  ext a
  induction a using Atom.induction_adjAtom with
  | h u v => simp

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
