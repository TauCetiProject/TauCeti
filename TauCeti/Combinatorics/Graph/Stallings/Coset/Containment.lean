/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Coset.Embedding
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Subgroup containment as a morphism of subgroup graphs

For arbitrary subgroups of a free group, containment is equivalent to the existence of a
based label-preserving morphism between their canonical subgroup graphs. Such a morphism is
unique. Thus subgroup inclusion can be read directly from based folded cores, without finite
generation or a finite alphabet.

The inclusion morphisms make the subgroup graph a functor from the poset of subgroups to based
labelled graphs (`TauCeti.subgroupGraphFunctor`), and it is fully faithful
(`TauCeti.subgroupGraphFunctorFullyFaithful`): subgroups embed in based labelled graphs as a
full subcategory. The inclusion morphisms need not be injective on vertices: inclusion of a
proper finite-index subgroup into the whole free group maps its multi-vertex graph to the
one-vertex rose.

## Main declarations

* `Subgroup.nonempty_hom_subgroupGraph_iff`: containment of subgroups is the existence of a based
  labelled morphism of their subgroup graphs.
* `TauCeti.subgroupGraphFunctor`: the subgroup graph, as a functor out of the poset of subgroups.
* `TauCeti.subgroupGraphFunctorFullyFaithful`: **that functor is fully faithful.**

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 4, Lemmas 4.1–4.2 and Proposition 4.3; Section 5, Theorem 5.1.
-/

public section

namespace Subgroup

open CategoryTheory TauCeti

variable {α : Type*} (H K : Subgroup (FreeGroup α))

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
instance : Subsingleton (H.subgroupGraph ⟶ K.subgroupGraph) where
  allEq := StallingsGraph.Hom.eq_of_isFolded_of_reachable K.subgroupGraph_isFolded
    ((H.subgroupGraph.graph.isCore_iff H.subgroupGraph.base).mp H.subgroupGraph_isCore).1

end Subgroup

namespace TauCeti

open CategoryTheory

variable {α : Type*} (H K : Subgroup (FreeGroup α))

variable (α) in
/-- **The subgroup graph as a functor**: a subgroup inclusion `H ≤ K` goes to the unique based
labelled morphism `Γ(H) → Γ(K)`. -/
noncomputable def subgroupGraphFunctor : Subgroup (FreeGroup α) ⥤ StallingsGraph α where
  obj H := H.subgroupGraph
  map {H K} f := ((H.nonempty_hom_subgroupGraph_iff K).mpr f.le).some
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp]
theorem subgroupGraphFunctor_obj : (subgroupGraphFunctor α).obj H = H.subgroupGraph :=
  (rfl)

/-- Between two graphs in the image of `subgroupGraphFunctor` there is at most one morphism, so
every morphism between them is the image of the subgroup inclusion. -/
instance : Subsingleton ((subgroupGraphFunctor α).obj H ⟶ (subgroupGraphFunctor α).obj K) := by
  rw [subgroupGraphFunctor_obj, subgroupGraphFunctor_obj]
  infer_instance

variable (α) in
/-- **Subgroups of a free group are a full subcategory of based labelled graphs**: every based
labelled morphism `Γ(H) → Γ(K)` comes from the inclusion `H ≤ K`. -/
noncomputable def subgroupGraphFunctorFullyFaithful : (subgroupGraphFunctor α).FullyFaithful where
  preimage {H K} f := homOfLE ((H.nonempty_hom_subgroupGraph_iff K).mp ⟨f⟩)
  map_preimage _ := Subsingleton.elim _ _
  preimage_map _ := Subsingleton.elim _ _

instance : (subgroupGraphFunctor α).Full :=
  (subgroupGraphFunctorFullyFaithful α).full

instance : (subgroupGraphFunctor α).Faithful :=
  (subgroupGraphFunctorFullyFaithful α).faithful

end TauCeti
