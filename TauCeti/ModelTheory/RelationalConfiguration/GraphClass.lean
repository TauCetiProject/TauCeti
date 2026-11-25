/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Clique.Tag
public import TauCeti.Combinatorics.SimpleGraph.RelationalConfiguration
public import TauCeti.ModelTheory.RelationalConfiguration.BorelComplete
public import TauCeti.ModelTheory.RelationalConfiguration.IncidenceGraph

/-!
# Countable graphs are Borel complete

The class `graphClass` of codes of simple graphs on `ℕ`, the configurations of the language of
graphs whose adjacency is symmetric and false on the diagonal, is an isomorphism-invariant Borel
class, and it is Borel complete (`TauCeti.RelationalConfiguration.borelComplete_graphClass`):
isomorphism of countable structures in any countable relational language reduces to isomorphism
of countable graphs (Friedman–Stanley).

The reduction sends a configuration `c` to its incidence graph (`incidenceGraph`), coloured by an
injection of the relation symbols into `ℕ`, then to the clique-tagged graph (`cliqueTag`), which
makes the colours part of the uncoloured graph, and finally to the code of that graph after
relabelling its countably infinite vertex set by `ℕ`. Each adjacency of the result is constant in
`c` or one coordinate of `c`, so the map is continuous. It preserves and reflects isomorphism:
codes of graphs are isomorphic exactly when the graphs are
(`TauCeti.RelationalConfiguration.isoSetoid_toRelationalConfiguration_iff`), the tagged graphs of
the triangle-free incidence graphs are isomorphic exactly when the incidence graphs are by a
colour-preserving isomorphism (`SimpleGraph.nonempty_iso_cliqueTag_iff`), and that happens exactly
when the configurations are isomorphic
(`TauCeti.RelationalConfiguration.isoSetoid_iff_exists_iso_incidenceGraph`).

## Main definitions

* `TauCeti.RelationalConfiguration.graphClass`: the codes of simple graphs on `ℕ`.

## Main results

* `TauCeti.RelationalConfiguration.measurableSet_graphClass`,
  `TauCeti.RelationalConfiguration.isomorphismInvariant_graphClass`: `graphClass` is an
  isomorphism-invariant Borel class.
* `TauCeti.RelationalConfiguration.range_toRelationalConfiguration_eq_graphClass`: it is the range
  of the coding of simple graphs.
* `TauCeti.RelationalConfiguration.isoSetoid_toRelationalConfiguration_iff`: codes of simple
  graphs are isomorphic exactly when the graphs are.
* `TauCeti.RelationalConfiguration.continuous_incidenceGraph_adj`: each adjacency of the incidence
  graph depends continuously on the configuration.
* `TauCeti.RelationalConfiguration.borelComplete_graphClass`: countable graphs are Borel complete.

## References

* H. Friedman and L. Stanley, *A Borel reducibility theory for classes of countable structures*,
  J. Symbolic Logic 54 (1989), Theorem 1.
-/

public section

open FirstOrder FirstOrder.Language Set

namespace TauCeti.RelationalConfiguration

/-! ### Codes of simple graphs -/

section Codes

variable {V : Type*}

/-- **Codes of simple graphs are isomorphic exactly when the graphs are.** -/
theorem isoSetoid_toRelationalConfiguration_iff {G H : SimpleGraph V} :
    isoSetoid Language.graph V G.toRelationalConfiguration H.toRelationalConfiguration ↔
      Nonempty (G ≃g H) := by
  rw [isoSetoid_iff_exists_perm_smul_eq]
  refine ⟨fun ⟨σ, hσ⟩ => ⟨⟨σ, fun {a b} => ?_⟩⟩, fun ⟨e⟩ => ⟨e.toEquiv, ?_⟩⟩
  · rw [perm_smul_def, ← SimpleGraph.toRelationalConfiguration_comap] at hσ
    rw [← SimpleGraph.toRelationalConfiguration_injective hσ]
    simp
  · rw [perm_smul_def, ← SimpleGraph.toRelationalConfiguration_comap]
    congr 1
    ext u v
    exact e.symm.map_adj_iff

end Codes

/-- The class of **codes of simple graphs** on `ℕ`: the configurations of the language of graphs
whose adjacency is symmetric and false on the diagonal. -/
def graphClass : Set (RelationalConfiguration Language.graph ℕ) :=
  {c | IsSimpleGraph c}

theorem mem_graphClass_iff {c : RelationalConfiguration Language.graph ℕ} :
    c ∈ graphClass ↔ IsSimpleGraph c :=
  Iff.rfl

/-- The class of codes of simple graphs is Borel. -/
theorem measurableSet_graphClass : MeasurableSet graphClass :=
  measurableSet_setOf_isSimpleGraph

/-- The class of codes of simple graphs is isomorphism invariant. -/
theorem isomorphismInvariant_graphClass : IsomorphismInvariant graphClass := by
  refine isomorphismInvariant_iff.2 fun c d hcd hc => ?_
  obtain ⟨σ, rfl⟩ := isoSetoid_iff_exists_perm_smul_eq.1 hcd
  rw [mem_graphClass_iff, perm_smul_def]
  exact IsSimpleGraph.restrict hc _

/-- The codes of simple graphs on `ℕ` are exactly the codes of the members of `graphClass`. -/
theorem range_toRelationalConfiguration_eq_graphClass :
    range (SimpleGraph.toRelationalConfiguration : SimpleGraph ℕ → _) = graphClass :=
  SimpleGraph.range_toRelationalConfiguration

/-! ### Continuity of the incidence graph -/

section Continuity

universe u v w

variable {L : Language.{u, v}} {V : Type w}

open IncidenceVertex Classical in
/-- **Each adjacency of the incidence graph is continuous** in the configuration: it is constant,
except between a tuple vertex and the truth vertex of its atom, where it is the value of that
atom. -/
theorem continuous_incidenceGraph_adj (v w : IncidenceVertex L V) :
    Continuous fun c : RelationalConfiguration L V => decide ((incidenceGraph c).Adj v w) := by
  have key (q r : Atom L V) :
      Continuous fun c : RelationalConfiguration L V => decide (q = r ∧ c.eval q = true) := by
    by_cases h : q = r
    · simpa [h] using continuous_eval r
    · simpa [h] using continuous_const
  cases v <;> cases w <;>
    simp only [incidenceGraph_adj_tuple_position, incidenceGraph_adj_position_tuple,
      incidenceGraph_adj_position_point, incidenceGraph_adj_point_position,
      incidenceGraph_adj_tuple_truth, incidenceGraph_adj_truth_tuple,
      not_incidenceGraph_adj_point_point, not_incidenceGraph_adj_point_tuple,
      not_incidenceGraph_adj_tuple_point, not_incidenceGraph_adj_point_truth,
      not_incidenceGraph_adj_truth_point, not_incidenceGraph_adj_tuple_tuple,
      not_incidenceGraph_adj_position_position, not_incidenceGraph_adj_position_truth,
      not_incidenceGraph_adj_truth_position, not_incidenceGraph_adj_truth_truth,
      decide_false] <;>
    first
    | exact continuous_const
    | exact key _ _

end Continuity

/-! ### Borel completeness -/

section BorelComplete

variable {L : Language.{0, 0}} [L.IsRelational] [∀ n, Countable (L.Relations n)]

/-- The configurations of a countable relational language reduce to codes of graphs: the code of
the clique-tagged incidence graph, relabelled by `e`. -/
private theorem isoSetoid_borelReducible_classIso_graphClass :
    (isoSetoid L ℕ).BorelReducible (classIso graphClass) := by
  classical
  obtain ⟨ι, hι⟩ := Countable.exists_injective_nat (Σ n, L.Relations n)
  let κ : IncidenceVertex L ℕ → ℕ := IncidenceVertex.color ι
  let W := IncidenceVertex L ℕ ⊕ Σ x : IncidenceVertex L ℕ, Fin (κ x + 3)
  have : Infinite W := inferInstance
  have : Countable W := inferInstance
  obtain ⟨_⟩ := nonempty_denumerable W
  let e : W ≃ ℕ := Denumerable.eqv W
  let F : RelationalConfiguration L ℕ → RelationalConfiguration Language.graph ℕ := fun c =>
    (((incidenceGraph c).cliqueTag κ).comap e.symm).toRelationalConfiguration
  have hcode (c : RelationalConfiguration L ℕ) :
      Nonempty (((incidenceGraph c).cliqueTag κ).comap e.symm ≃g (incidenceGraph c).cliqueTag κ) :=
    ⟨⟨e.symm, Iff.rfl⟩⟩
  refine (Setoid.borelBireducible_iff.1 borelBireducible_classIso_univ).2.trans <|
    borelReducible_classIso_of_mapsTo (f := F) ?_ (fun c _ => ?_) fun c _ d _ => ?_
  · refine (Continuous.measurable ?_)
    refine continuous_iff.2 fun a => ?_
    induction a using Atom.induction_adjAtom with
    | h i j =>
      simp only [F, SimpleGraph.eval_toRelationalConfiguration_adjAtom, SimpleGraph.comap_adj]
      rcases e.symm i with v | p <;> rcases e.symm j with w | p' <;>
        simp only [SimpleGraph.cliqueTag_adj_inl_inl, SimpleGraph.cliqueTag_adj_inl_inr,
          SimpleGraph.cliqueTag_adj_inr_inl, SimpleGraph.cliqueTag_adj_inr_inr]
      · exact continuous_incidenceGraph_adj v w
      all_goals exact continuous_const
  · exact SimpleGraph.isSimpleGraph_toRelationalConfiguration _
  · obtain ⟨hc⟩ := hcode c
    obtain ⟨hd⟩ := hcode d
    rw [isoSetoid_toRelationalConfiguration_iff, isoSetoid_iff_exists_iso_incidenceGraph hι,
      ← SimpleGraph.nonempty_iso_cliqueTag_iff (cliqueFree_incidenceGraph c)
        (cliqueFree_incidenceGraph d)]
    exact ⟨fun ⟨f⟩ => ⟨(hc.trans f).trans hd.symm⟩, fun ⟨f⟩ => ⟨(hc.symm.trans f).trans hd⟩⟩

end BorelComplete

/-- **Countable graphs are Borel complete** (Friedman–Stanley 1989, Theorem 1): isomorphism of
countable structures in any countable relational language is Borel reducible to isomorphism of
countable graphs. -/
theorem borelComplete_graphClass : BorelComplete graphClass :=
  borelComplete_iff_forall_isoSetoid.2 fun _ _ _ => isoSetoid_borelReducible_classIso_graphClass

end TauCeti.RelationalConfiguration
