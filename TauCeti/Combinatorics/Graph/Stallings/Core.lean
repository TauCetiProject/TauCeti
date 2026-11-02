/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Core
public import TauCeti.Combinatorics.Graph.Stallings.Morphism

/-!
# Based cores preserve accepted subgroups

Restricting a labelled graph to the union of its reduced based loops preserves its accepted
subgroup. The resulting graph is connected, is a core at its base vertex, and inherits
foldedness and finiteness. The construction retains the stem from the base to a circuit;
only vertices away from the base are forbidden to have degree one. A label-preserving
morphism out of a folded graph restricts to a morphism of based cores.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 3, Definition 3.5 and Lemma 3.7.
-/

public section

namespace TauCeti.StallingsGraph

variable {α : Type*} (S : StallingsGraph α)

/-- The based core, with labels inherited from the ambient graph. Its carrier computes to
the Serre core so paths and finite-type instances can be used directly. -/
@[expose] def core : StallingsGraph α where
  graph := S.graph.core S.base
  base := S.graph.coreBase S.base
  label := fun e => S.label e.1
  label_rev := fun e => S.label_rev e.1

@[simp] theorem core_graph : S.core.graph = S.graph.core S.base := (rfl)

@[simp] theorem core_base : S.core.base = S.graph.coreBase S.base := (rfl)

@[simp] theorem core_label (e : S.core.graph.E) : S.core.label e = S.label e.1 := (rfl)

instance [Finite S.graph.V] : Finite S.core.graph.V :=
  inferInstanceAs (Finite (S.graph.core S.base).V)

instance [Finite S.graph.E] : Finite S.core.graph.E :=
  inferInstanceAs (Finite (S.graph.core S.base).E)

/-- Inclusion of the core preserves the base vertex and every label. Its vertex map computes
so that mapped paths have their original ambient endpoints. -/
@[expose] def coreInclusion : S.core.Hom S where
  graphHom := S.graph.coreInclusion S.base
  map_base := by simp
  map_label := fun _ => rfl

@[simp] theorem coreInclusion_graphHom :
    S.coreInclusion.graphHom = S.graph.coreInclusion S.base := (rfl)

/-- The core is a core at its distinguished vertex; in particular all its vertices are
reachable from that vertex. -/
theorem core_isCore : S.core.graph.IsCore S.core.base :=
  S.graph.core_isCore S.base

/-- Taking the based core preserves foldedness. -/
theorem IsFolded.core (hS : S.IsFolded) : S.core.IsFolded := by
  apply S.core.isFolded_def.mpr
  intro e f hs hl
  apply Subtype.ext
  exact (S.isFolded_def.mp hS) e.1 f.1 (congrArg Subtype.val hs) hl

/-- The based core accepts exactly the same subgroup as the original labelled graph. -/
@[simp] theorem core_subgroup :
    S.core.subgroup (S.graph.coreBase S.base) = S.subgroup S.base := by
  apply le_antisymm S.coreInclusion.subgroup_le
  intro g hg
  obtain ⟨p, hp, rfl⟩ := S.mem_subgroup_iff_exists_reduced_path.mp hg
  obtain ⟨q, hq⟩ := S.graph.exists_core_loop S.base p hp
  apply S.core.mem_subgroup_iff.mpr
  refine ⟨q, ?_⟩
  exact (S.coreInclusion.read_mapPath q).symm.trans (congrArg S.read hq)

variable {S} {T : StallingsGraph α}

/-- A morphism out of a folded graph sends core darts to core darts. -/
theorem Hom.map_mem_coreDarts (f : S.Hom T) (hS : S.IsFolded)
    {e : S.graph.E} (he : e ∈ S.graph.coreDarts S.base) :
    f.graphHom.mapE e ∈ T.graph.coreDarts T.base := by
  obtain ⟨p, hp, he⟩ := (S.graph.mem_coreDarts_iff S.base e).mp he
  have h : ∃ q : T.graph.Path (f.graphHom.toPrefunctor.obj S.base)
      (f.graphHom.toPrefunctor.obj S.base),
      SerreGraph.Path.IsReduced T.graph q ∧
        f.graphHom.mapE e ∈ SerreGraph.Path.darts T.graph q := by
    refine ⟨f.graphHom.toPrefunctor.mapPath p, f.isReduced_mapPath hS p hp, ?_⟩
    rw [SerreGraph.Hom.darts_mapPath S.graph f.graphHom p]
    exact List.mem_map_of_mem he
  apply (T.graph.mem_coreDarts_iff T.base _).mpr
  simp only [SerreGraph.Hom.toPrefunctor_obj] at h
  rw [f.map_base] at h
  exact h

/-- A morphism out of a folded graph sends core vertices to core vertices, including the
isolated base vertex when the accepted subgroup is trivial. -/
theorem Hom.map_mem_coreVertices (f : S.Hom T) (hS : S.IsFolded)
    {a : S.graph.V} (ha : a ∈ S.graph.coreVertices S.base) :
    f.graphHom.mapV a ∈ T.graph.coreVertices T.base := by
  rcases (S.graph.mem_coreVertices_iff S.base a).mp ha with rfl | ⟨e, he, rfl⟩
  · exact (T.graph.mem_coreVertices_iff T.base _).mpr (Or.inl f.map_base)
  · rw [← f.graphHom.map_src]
    exact T.graph.src_mem_coreVertices T.base (f.map_mem_coreDarts hS he)

/-- Restriction of a labelled morphism to based cores. Foldedness of the source prevents
cancellation of the reduced loops that witness core membership. -/
def Hom.core (f : S.Hom T) (hS : S.IsFolded) : S.core.Hom T.core where
  graphHom := {
    mapV := fun a => ⟨f.graphHom.mapV a.1, f.map_mem_coreVertices hS a.2⟩
    mapE := fun e => ⟨f.graphHom.mapE e.1, f.map_mem_coreDarts hS e.2⟩
    map_src := fun e => Subtype.ext (f.graphHom.map_src e.1)
    map_rev := fun e => Subtype.ext (f.graphHom.map_rev e.1) }
  map_base := Subtype.ext f.map_base
  map_label := fun e => f.map_label e.1

@[simp] theorem Hom.core_mapV_val (f : S.Hom T) (hS : S.IsFolded)
    (a : S.core.graph.V) :
    ((f.core hS).graphHom.mapV a).1 = f.graphHom.mapV a.1 := (rfl)

@[simp] theorem Hom.core_mapE_val (f : S.Hom T) (hS : S.IsFolded)
    (e : S.core.graph.E) :
    ((f.core hS).graphHom.mapE e).1 = f.graphHom.mapE e.1 := (rfl)

end TauCeti.StallingsGraph
