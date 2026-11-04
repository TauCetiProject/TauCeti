/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Coset.Embedding

/-!
# Subgroup containment as a morphism of subgroup graphs

For arbitrary subgroups of a free group, containment is equivalent to the existence of a
based label-preserving morphism between their canonical subgroup graphs. Such a morphism is
unique. Thus subgroup inclusion can be read directly from based folded cores, without finite
generation or a finite alphabet.

The inclusion morphisms preserve identities and composition. They need not be injective on
vertices: inclusion of a proper finite-index subgroup into the whole free group maps its
multi-vertex graph to the one-vertex rose.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 4, Lemmas 4.1–4.2 and Proposition 4.3; Section 5, Theorem 5.1.
-/

public section

namespace Subgroup

open TauCeti

variable {α : Type*} (H K L : Subgroup (FreeGroup α))

/-- Subgroup containment is precisely the existence of a based labelled morphism between
the canonical subgroup graphs. -/
@[simp] theorem nonempty_hom_subgroupGraph_iff :
    Nonempty (H.subgroupGraph.Hom K.subgroupGraph) ↔ H ≤ K := by
  constructor
  · rintro ⟨f⟩
    simpa only [subgroupGraph_subgroup] using f.subgroup_le
  · intro h
    obtain ⟨f⟩ := (StallingsGraph.nonempty_hom_cosetGraph_iff
      (S := H.cosetGraph) (H := K) H.cosetGraph_base_reachable).mpr
        (H.cosetGraph_subgroup.le.trans h)
    rw [H.subgroupGraph_def, K.subgroupGraph_def]
    exact ⟨f.core H.cosetGraph_isFolded⟩

/-- Between two canonical subgroup graphs there is at most one based labelled morphism. -/
instance : Subsingleton (H.subgroupGraph.Hom K.subgroupGraph) where
  allEq := StallingsGraph.Hom.eq_of_isFolded_of_reachable K.subgroupGraph_isFolded
    ((H.subgroupGraph.graph.isCore_iff H.subgroupGraph.base).mp H.subgroupGraph_isCore).1

/-- The unique morphism of canonical subgroup graphs induced by a subgroup inclusion. -/
noncomputable def subgroupGraphHom (h : H ≤ K) : H.subgroupGraph.Hom K.subgroupGraph :=
  ((H.nonempty_hom_subgroupGraph_iff K).mpr h).some

/-- Reflexive subgroup inclusion induces the identity morphism. -/
@[simp] theorem subgroupGraphHom_refl :
    H.subgroupGraphHom H le_rfl = StallingsGraph.Hom.id H.subgroupGraph :=
  Subsingleton.elim _ _

/-- Composing subgroup inclusions composes their based graph morphisms. -/
@[simp] theorem subgroupGraphHom_comp (hHK : H ≤ K) (hKL : K ≤ L) :
    (K.subgroupGraphHom L hKL).comp (H.subgroupGraphHom K hHK) =
      H.subgroupGraphHom L (hHK.trans hKL) :=
  Subsingleton.elim _ _

end Subgroup
