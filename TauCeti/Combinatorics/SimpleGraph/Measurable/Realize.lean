/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Graph
public import Mathlib.MeasureTheory.Constructions.SimpleGraph
import TauCeti.ModelTheory.Syntax

/-!
# Joint measurability of graph-formula realization

On a countable vertex type `V` with measurable singletons, for instance `ℕ` or `Fin n`, whether a
graph `G` realizes a finitary first-order formula of the language of graphs at an assignment of its
free and bound variables is a measurable condition on the graph and both assignments together. The
graph varies in Mathlib's adjacency σ-algebra on `SimpleGraph V`, and the assignments in the
product σ-algebras on `α → V` and `Fin n → V`. The type `α` of free variables is arbitrary: a
formula reads only finitely many coordinates, and the proof never enumerates the assignments.

The proof is an induction on the formula. Equality of two variables is measurable because the
diagonal of a countable type with measurable singletons is measurable. Adjacency of two variables
is the union, over the countably many vertex pairs, of an adjacency coordinate times a singleton.
A universal quantifier is a countable intersection over the vertices.

## Main results

* `SimpleGraph.measurableSet_realize_jointly`: on a countable vertex type with measurable
  singletons, realization of a graph formula is measurable on the product of the graph space with
  the assignment spaces.
-/

public section

open FirstOrder FirstOrder.Language MeasureTheory

namespace SimpleGraph

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

/-- **Joint measurability of realization.** On a countable vertex type with measurable singletons,
the graphs and assignments of free and bound variables at which a graph formula is realized form a
measurable set in the product of the graph space with the assignment spaces. -/
theorem measurableSet_realize_jointly {α : Type*} {n : ℕ}
    (φ : Language.graph.BoundedFormula α n) :
    MeasurableSet {p : SimpleGraph V × (α → V) × (Fin n → V) |
      @BoundedFormula.Realize _ V p.1.structure α n φ p.2.1 p.2.2} := by
  have hvar : ∀ {m : ℕ} (a : α ⊕ Fin m),
      Measurable fun p : SimpleGraph V × (α → V) × (Fin m → V) => Sum.elim p.2.1 p.2.2 a := by
    rintro m (a | a)
    · exact (measurable_pi_apply a).comp (measurable_fst.comp measurable_snd)
    · exact (measurable_pi_apply a).comp (measurable_snd.comp measurable_snd)
  induction φ with
  | falsum => exact MeasurableSet.empty
  | equal t₁ t₂ =>
    obtain ⟨a, rfl⟩ := t₁.exists_eq_var_of_isRelational
    obtain ⟨b, rfl⟩ := t₂.exists_eq_var_of_isRelational
    exact measurableSet_eq_fun (hvar a) (hvar b)
  | rel R ts =>
    choose a ha using fun i => (ts i).exists_eq_var_of_isRelational
    obtain rfl : ts = fun i => var (a i) := funext ha
    cases R
    -- `Realize` of the adjacency atom under `G.structure` is `G.Adj` on the two evaluated vertices.
    have hadj : MeasurableSet {q : SimpleGraph V × V × V | q.1.Adj q.2.1 q.2.2} :=
      measurableSet_setOfPred.2 <| measurable_from_prod_countable_left fun y =>
        (measurable_adj.eval.eval : Measurable fun G : SimpleGraph V => G.Adj y.1 y.2)
    exact hadj.preimage (measurable_fst.prodMk ((hvar (a 0)).prodMk (hvar (a 1))))
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormula.realize_imp]
    exact ihφ.imp ihψ
  | @all m φ ih =>
    simp only [BoundedFormula.realize_all, Set.ofPred_forall]
    refine .iInter fun y => ?_
    have hy : Measurable fun p : SimpleGraph V × (α → V) × (Fin m → V) =>
        (p.1, p.2.1, (Fin.snoc p.2.2 y : Fin (m + 1) → V)) := by
      fun_prop
    exact hy ih

end SimpleGraph
