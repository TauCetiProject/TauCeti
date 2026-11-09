/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Construction
public import TauCeti.Combinatorics.Graph.Stallings.Product
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

/-!
# The Howson property of free groups

The intersection of two finitely generated subgroups of a free group is finitely generated.
Each finitely generated subgroup is accepted at the base vertex of its Stallings graph, a finite
folded labelled graph. The product of two folded graphs accepts the intersection of their
subgroups at the pair of base vertices, and the product of finite graphs has finitely many
darts. A graph with finitely many darts accepts a finitely generated subgroup.

## Main results

* `Subgroup.FG.inf_of_isFreeGroup`: Howson's theorem.

## References

* A. G. Howson, *On the intersection of finitely generated free groups*, J. London Math. Soc. 29
  (1954), 428–434.
* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 9, Proposition 9.4 and Corollary 9.5.
-/

public section

open TauCeti

/-- **Howson's theorem**: in a free group, the intersection of two finitely generated subgroups
is finitely generated. -/
theorem Subgroup.FG.inf_of_isFreeGroup {G : Type*} [Group G] [IsFreeGroup G]
    {H K : Subgroup G} (hH : H.FG) (hK : K.FG) : (H ⊓ K).FG := by
  let e := IsFreeGroup.toFreeGroup G
  -- Transport both subgroups to the free group on the generators, where Stallings graphs exist.
  obtain ⟨ws, hws⟩ :=
    StallingsGraph.exists_subgroup_stallingsGraph_eq (H := H.map e.toMonoidHom) inferInstance
  obtain ⟨vs, hvs⟩ :=
    StallingsGraph.exists_subgroup_stallingsGraph_eq (H := K.map e.toMonoidHom) inferInstance
  have hfg : ((H ⊓ K).map e.toMonoidHom).FG := by
    rw [Subgroup.map_inf_eq H K e.toMonoidHom e.injective, ← hws, ← hvs,
      ← StallingsGraph.prod_subgroup (StallingsGraph.stallingsGraph_isFolded ws)
        (StallingsGraph.stallingsGraph_isFolded vs)]
    exact StallingsGraph.subgroup_fg _ _
  exact (isMulFG_congr ((H ⊓ K).equivMapOfInjective e.toMonoidHom e.injective)).mpr hfg
