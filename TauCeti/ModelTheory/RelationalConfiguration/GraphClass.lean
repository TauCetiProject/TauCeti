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
* `TauCeti.RelationalConfiguration.isoSetoid_toRelationalConfiguration_iff`: codes of simple
  graphs are isomorphic exactly when the graphs are.
* `TauCeti.RelationalConfiguration.borelComplete_graphClass`: countable graphs are Borel complete.

## References

* H. Friedman and L. Stanley, *A Borel reducibility theory for classes of countable structures*,
  J. Symbolic Logic 54 (1989), Theorem 1.
-/

public section

open FirstOrder FirstOrder.Language

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

/-- Unfolding lemma for `graphClass`. -/
@[simp]
theorem mem_graphClass {c : RelationalConfiguration Language.graph ℕ} :
    c ∈ graphClass ↔ IsSimpleGraph c :=
  Iff.rfl

/-- The code of a simple graph on `ℕ` lies in `graphClass`. -/
theorem toRelationalConfiguration_mem_graphClass (G : SimpleGraph ℕ) :
    G.toRelationalConfiguration ∈ graphClass :=
  SimpleGraph.isSimpleGraph_toRelationalConfiguration G

/-- The class of codes of simple graphs is Borel. -/
theorem measurableSet_graphClass : MeasurableSet graphClass :=
  measurableSet_setOf_isSimpleGraph

/-- The class of codes of simple graphs is isomorphism invariant. -/
theorem isomorphismInvariant_graphClass : IsomorphismInvariant graphClass := by
  refine isomorphismInvariant_iff.2 fun c d hcd hc => ?_
  obtain ⟨σ, rfl⟩ := isoSetoid_iff_exists_perm_smul_eq.1 hcd
  rw [mem_graphClass, perm_smul_def]
  exact IsSimpleGraph.restrict hc _

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
  refine (Setoid.borelBireducible_iff.1 borelBireducible_classIso_univ).2.trans <|
    borelReducible_classIso_of_mapsTo (f := F) ?_ (fun c _ => ?_) fun c _ d _ => ?_
  · refine (Continuous.measurable ?_)
    refine continuous_iff.2 fun a => ?_
    induction a using Atom.induction_adjAtom with
    | h i j =>
      simp only [F, SimpleGraph.eval_toRelationalConfiguration_adjAtom, SimpleGraph.comap_adj]
      rcases e.symm i with v | p <;> rcases e.symm j with w | p' <;>
        simp [continuous_incidenceGraph_adj, continuous_const]
  · exact toRelationalConfiguration_mem_graphClass _
  · let hc := SimpleGraph.Iso.comap e.symm ((incidenceGraph c).cliqueTag κ)
    let hd := SimpleGraph.Iso.comap e.symm ((incidenceGraph d).cliqueTag κ)
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
