/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.SimpleGraph.Measurable.Realize
import TauCeti.ModelTheory.BackAndForth.Graph

/-!
# Regression examples: joint measurability of graph-formula realization

* On `Fin 3`, the formula `Adj(x₀, x₁)` gives the measurable joint event of a graph and a pair of
  vertices that are adjacent in it.
* On `ℕ`, the formula `x₀ = x₁` gives the measurable joint event of a graph and a pair of equal
  vertices, which does not depend on the graph.
* Fixing the assignment recovers the measurable event of the graphs realizing a formula there, on
  `ℕ` and on `Fin n`.
-/

open FirstOrder FirstOrder.Language

-- `Adj(x₀, x₁)` on `Fin 3`: the graph and the pair vary together.
example :
    MeasurableSet {p : SimpleGraph (Fin 3) × (Fin 2 → Fin 3) × (Fin 0 → Fin 3) |
      p.1.Adj (p.2.1 0) (p.2.1 1)} := by
  simpa [BoundedFormula.realize_rel₂, SimpleGraph.relMap_adj] using
    SimpleGraph.measurableSet_realize_jointly (V := Fin 3)
      (Language.adj.boundedFormula₂ (Term.var (Sum.inl (0 : Fin 2))) (Term.var (Sum.inl 1)) :
        Language.graph.BoundedFormula (Fin 2) 0)

-- `x₀ = x₁` on `ℕ`.
example :
    MeasurableSet {p : SimpleGraph ℕ × (Fin 2 → ℕ) × (Fin 0 → ℕ) | p.2.1 0 = p.2.1 1} := by
  simpa [BoundedFormula.realize_bdEqual] using SimpleGraph.measurableSet_realize_jointly (V := ℕ)
    ((Term.var (Sum.inl 0)).bdEqual (Term.var (Sum.inl 1)) :
      Language.graph.BoundedFormula (Fin 2) 0)

-- Fixing the assignments recovers the fixed-assignment events, on `ℕ` and on `Fin n`.
example {α : Type*} {k : ℕ} (φ : Language.graph.BoundedFormula α k) (v : α → ℕ)
    (xs : Fin k → ℕ) :
    MeasurableSet {G : SimpleGraph ℕ | @BoundedFormula.Realize _ ℕ G.structure α k φ v xs} :=
  measurable_prodMk_right (y := (v, xs)) (SimpleGraph.measurableSet_realize_jointly φ)

example {n : ℕ} {α : Type*} {k : ℕ} (φ : Language.graph.BoundedFormula α k) (v : α → Fin n)
    (xs : Fin k → Fin n) :
    MeasurableSet {G : SimpleGraph (Fin n) | @BoundedFormula.Realize _ _ G.structure α k φ v xs} :=
  measurable_prodMk_right (y := (v, xs)) (SimpleGraph.measurableSet_realize_jointly φ)
