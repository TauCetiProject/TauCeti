/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Core
public import TauCeti.Combinatorics.Graph.Stallings.Folded

/-!
# Based cores preserve accepted subgroups

Restricting a labelled graph to the union of its reduced based loops preserves its accepted
subgroup. The resulting graph is connected, is a core at its base vertex, and inherits
foldedness and finiteness. The construction retains the stem from the base to a circuit;
only vertices away from the base are forbidden to have degree one.

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

end TauCeti.StallingsGraph
