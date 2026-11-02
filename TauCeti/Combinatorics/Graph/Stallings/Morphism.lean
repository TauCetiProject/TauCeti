/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Folded

/-!
# Morphisms into folded labelled graphs

A based label-preserving morphism from a graph reachable from its base vertex into a folded
graph is unique. Starting at the base point, the target dart is determined by its source and
label; following a path then determines the target of each source vertex. This is the
uniqueness part of the Stallings subgroup-graph correspondence. Morphisms out of folded
graphs also preserve reduced paths; this lets them restrict to based cores.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 4, Lemma 4.2.
-/

public section

namespace TauCeti.StallingsGraph

variable {α : Type*} {S T : StallingsGraph α}

/-- Two based label-preserving morphisms to a folded graph agree if every source vertex is
reachable from the base vertex. -/
theorem Hom.eq_of_isFolded_of_reachable (hT : T.IsFolded)
    (hS : ∀ a : S.graph.V, Nonempty (S.graph.Path S.base a))
    (f g : S.Hom T) : f = g := by
  have hV : ∀ a : S.graph.V, f.graphHom.mapV a = g.graphHom.mapV a := by
    intro a
    obtain ⟨p⟩ := hS a
    induction p with
    | nil => exact f.map_base.trans g.map_base.symm
    | cons p e ih =>
      have he : f.graphHom.mapE e.1 = g.graphHom.mapE e.1 := by
        apply (T.isFolded_def.mp hT) _ _
        · simpa only [f.graphHom.map_src, g.graphHom.map_src, e.2.1] using ih
        · exact (f.map_label e.1).trans (g.map_label e.1).symm
      have ht := congrArg T.graph.tgt he
      simpa only [f.graphHom.map_tgt, g.graphHom.map_tgt, e.2.2] using ht
  apply Hom.ext
  apply SerreGraph.Hom.ext
  · funext a
    exact hV a
  · funext e
    apply (T.isFolded_def.mp hT) _ _
    · simpa only [f.graphHom.map_src, g.graphHom.map_src] using hV (S.graph.src e)
    · exact (f.map_label e).trans (g.map_label e).symm

/-- A label-preserving morphism out of a folded graph preserves reduced paths, even when
it identifies vertices or darts globally. -/
theorem Hom.isReduced_mapPath (f : S.Hom T) (hS : S.IsFolded)
    {a b : S.graph.V} (p : S.graph.Path a b)
    (hp : SerreGraph.Path.IsReduced S.graph p) :
    SerreGraph.Path.IsReduced T.graph (f.graphHom.toPrefunctor.mapPath p) := by
  induction p with
  | nil => exact SerreGraph.Path.isReduced_nil T.graph _
  | cons p e ih =>
    cases p with
    | nil => exact SerreGraph.Path.isReduced_toPath T.graph _
    | cons p d =>
      obtain ⟨hprev, hne⟩ := (SerreGraph.Path.isReduced_cons_cons S.graph p d e).mp hp
      apply (SerreGraph.Path.isReduced_cons_cons T.graph _ _ _).mpr
      refine ⟨ih hprev, ?_⟩
      intro he
      apply hS.labels_not_inverse S (e.2.1.trans d.2.2.symm) hne
      have hl := congrArg T.label he
      simpa only [f.graphHom.toPrefunctor_map_val, T.label_rev, f.map_label] using hl

/-- A label-preserving morphism from a folded graph that is injective on vertices is also
injective on darts. -/
theorem Hom.injective_mapE_of_injective_mapV (f : S.Hom T) (hS : S.IsFolded)
    (hf : Function.Injective f.graphHom.mapV) : Function.Injective f.graphHom.mapE := by
  intro e d h
  apply (S.isFolded_def.mp hS) e d
  · apply hf
    exact (f.graphHom.map_src e).symm.trans
      ((congrArg T.graph.src h).trans (f.graphHom.map_src d))
  · exact (f.map_label e).symm.trans ((congrArg T.label h).trans (f.map_label d))

end TauCeti.StallingsGraph
