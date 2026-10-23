/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.SimpleGraph.RelationalConfiguration
import TauCeti.Combinatorics.SimpleGraph.Maps
import TauCeti.Combinatorics.SimpleGraph.Measurable

/-!
# Regression examples: relational configurations and simple graphs

These examples exercise the public API of relational configurations and of the simple-graph
encoding from a downstream module, through public statements only. They pin down the edge cases
that a relational configuration must get right:

* the empty carrier: the language of graphs has no atom on `Fin 0`, whereas a nullary relation
  symbol has one (the empty tuple), so two distinct configurations exist there;
* repeated coordinates: diagonal atoms of a simple graph are false, so restricting along a constant
  map gives the empty graph;
* finite injections, as in the consistency of exchangeable graph laws, and windows of graphs on
  `ℕ` commute with encoding;
* measurability of encoding and restriction.
-/

open MeasureTheory TauCeti TauCeti.RelationalConfiguration

open _root_.FirstOrder (Language)

/-! ### The empty carrier -/

-- The language of graphs has only a binary symbol, so on `Fin 0` there is exactly one
-- configuration.
example (c d : RelationalConfiguration Language.graph (Fin 0)) : c = d :=
  ext fun a => by induction a using Atom.induction_adjAtom with | h u _ => exact u.elim0

-- A language with a single nullary relation symbol has an atom even on the empty carrier, the
-- symbol with the empty tuple, so two distinct configurations exist there.
example :
    ∃ c d : RelationalConfiguration
      (⟨fun _ => Empty, fun n => if n = 0 then Unit else Empty⟩ : Language) (Fin 0), c ≠ d := by
  refine ⟨mk fun _ => true, mk fun _ => false, fun h => ?_⟩
  have h' := congrArg (fun c => RelationalConfiguration.eval c
    (atom (L := ⟨fun _ => Empty, fun n => if n = 0 then Unit else Empty⟩) (n := 0)
      (cast (by simp) ()) Fin.elim0)) h
  simp only [eval_mk] at h'
  exact Bool.noConfusion h'

/-! ### Repeated coordinates -/

-- A diagonal atom of a simple graph is false.
example {V : Type*} (G : SimpleGraph V) (v : V) :
    G.toRelationalConfiguration.eval (adjAtom v v) = false :=
  (isSimpleGraph_iff.1 G.isSimpleGraph_toRelationalConfiguration).2 v

-- Restricting along a constant map reads only diagonal atoms, giving the empty graph.
example {V : Type*} (G : SimpleGraph V) (v : V) :
    SimpleGraph.relationalConfigurationEquiv.symm
        ⟨G.toRelationalConfiguration.restrict (fun _ : Fin 3 => v),
          G.isSimpleGraph_toRelationalConfiguration.restrict _⟩ = ⊥ := by
  ext i j
  simp [(isSimpleGraph_iff.1 G.isSimpleGraph_toRelationalConfiguration).2 v]

/-! ### Finite injections and windows on `ℕ` -/

-- The consistency maps of exchangeable graph laws: injections of finite label sets.
example {k l : ℕ} (f : Fin k ↪ Fin l) (G : SimpleGraph (Fin l)) :
    (G.comap f).toRelationalConfiguration = G.toRelationalConfiguration.restrict f :=
  SimpleGraph.toRelationalConfiguration_comap f G

-- Windows of graphs on `ℕ`.
example (G : SimpleGraph ℕ) (n : ℕ) :
    (G.restrictFin n).toRelationalConfiguration =
      G.toRelationalConfiguration.restrict (Fin.val : Fin n → ℕ) := by
  rw [← SimpleGraph.comap_val, SimpleGraph.toRelationalConfiguration_comap]

/-! ### Measurability -/

-- Window, then encode.
example (n : ℕ) :
    Measurable fun G : SimpleGraph ℕ =>
      SimpleGraph.relationalConfigurationEquiv (G.restrictFin n) :=
  SimpleGraph.relationalConfigurationEquiv.measurable.comp (SimpleGraph.measurable_restrictFin n)

-- Encode, then restrict.
example (n : ℕ) :
    Measurable fun G : SimpleGraph ℕ =>
      G.toRelationalConfiguration.restrict (Fin.val : Fin n → ℕ) :=
  (measurable_restrict _).comp SimpleGraph.measurable_toRelationalConfiguration
