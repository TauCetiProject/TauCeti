/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.RibbonGraph.Action
public import TauCeti.Combinatorics.RibbonGraph.Classification

/-!
# The classification of ribbon graphs read off the edge equivalence

The edge functor `TauCeti.BipartiteRibbonGraph.edgeFunctor` is an equivalence from finite
bipartite ribbon graphs to finite `FreeGroup (Fin 2)`-sets. This file reads the classification of
ribbon graphs off it.

* The isomorphisms `TauCeti.BipartiteRibbonGraph.Iso` of ribbon graphs are the isomorphisms of the
  category (`TauCeti.BipartiteRibbonGraph.isoEquivIso`), so the equivalence is also one of the
  groupoids of isomorphisms: two graphs are isomorphic exactly when their edge sets are
  isomorphic `FreeGroup (Fin 2)`-sets (`TauCeti.BipartiteRibbonGraph.nonempty_iso_iff_edges`).
* The bijection `TauCeti.BipartiteRibbonGraph.isoClassEquiv` between isomorphism classes of graphs
  with `n` edges and isomorphism classes of degree-`n` permutation triples identifies two graphs
  exactly when their edge actions are isomorphic
  (`TauCeti.BipartiteRibbonGraph.isoClassEquiv_eq_iff`): it is the bijection the equivalence
  induces on isomorphism classes.
* The automorphisms of a graph are the automorphisms of its edge action
  (`TauCeti.BipartiteRibbonGraph.autEquivIsoEdges`), compatibly with products
  (`TauCeti.BipartiteRibbonGraph.autEquivIsoEdges_mul`) and with the edge permutations, which is
  how `TauCeti.BipartiteRibbonGraph.autEquivAutomorphismGroup` reads them through a numbering.
* A graph is connected exactly when its edge action is nonempty and transitive
  (`TauCeti.BipartiteRibbonGraph.isConnected_iff_isPretransitive`), since the image of the edge
  action is the rotation group (`TauCeti.BipartiteRibbonGraph.range_edgeAction`).

## Main results

* `TauCeti.BipartiteRibbonGraph.isoEquivIso`: isomorphisms of ribbon graphs are categorical
  isomorphisms.
* `TauCeti.BipartiteRibbonGraph.nonempty_iso_iff_edges`: **two ribbon graphs are isomorphic
  exactly when their edge actions are.**
* `TauCeti.BipartiteRibbonGraph.isoClassEquiv_eq_iff`: `isoClassEquiv` is the bijection induced
  on isomorphism classes.
* `TauCeti.BipartiteRibbonGraph.autEquivIsoEdges`: **automorphisms of a ribbon graph are
  automorphisms of its edge action.**
* `TauCeti.BipartiteRibbonGraph.isConnected_iff_isPretransitive`: **connected ribbon graphs are
  the nonempty transitive `FreeGroup (Fin 2)`-sets.**

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.3 and §1.5.
-/

public section

noncomputable section

universe u

open CategoryTheory

namespace TauCeti

namespace BipartiteRibbonGraph

variable {Γ Δ : BipartiteRibbonGraph.{u}}

/-! ### Isomorphisms -/

/-- An isomorphism of ribbon graphs is an isomorphism of the category. -/
def Iso.toCatIso (f : Γ.Iso Δ) : Γ ≅ Δ where
  hom := f.toHom
  inv := f.symm.toHom
  hom_inv_id := hom_ext (funext fun e ↦ by simp)
  inv_hom_id := hom_ext (funext fun e ↦ by simp)

@[simp]
theorem Iso.toCatIso_hom_edge (f : Γ.Iso Δ) : f.toCatIso.hom.edge = f.edge :=
  funext f.toHom_edge_apply

/-- The edge map of a categorical isomorphism of ribbon graphs, as an equivalence. -/
def edgeEquivOfIso (i : Γ ≅ Δ) : Γ.E ≃ Δ.E where
  toFun := i.hom.edge
  invFun := i.inv.edge
  left_inv e := by
    rw [← Hom.comp_edge_apply, ← comp_eq_comp, i.hom_inv_id, id_eq_id, Hom.id_edge_apply]
  right_inv e := by
    rw [← Hom.comp_edge_apply, ← comp_eq_comp, i.inv_hom_id, id_eq_id, Hom.id_edge_apply]

@[simp]
theorem edgeEquivOfIso_apply (i : Γ ≅ Δ) (e : Γ.E) : edgeEquivOfIso i e = i.hom.edge e :=
  (rfl)

/-- **Isomorphisms of ribbon graphs are the isomorphisms of the category.** -/
def isoEquivIso : Γ.Iso Δ ≃ (Γ ≅ Δ) where
  toFun := Iso.toCatIso
  invFun i := Iso.ofEdge (edgeEquivOfIso i)
    (fun e ↦ i.hom.map_rotB e : Function.Semiconj (edgeEquivOfIso i) Γ.rotB Δ.rotB)
    (fun e ↦ i.hom.map_rotW e : Function.Semiconj (edgeEquivOfIso i) Γ.rotW Δ.rotW)
  left_inv f := Iso.ext (Equiv.ext fun e ↦
    (DFunLike.congr_fun (Iso.ofEdge_edge _ _ _) e).trans (congrFun (Iso.toCatIso_hom_edge f) e))
  right_inv _ := CategoryTheory.Iso.ext (hom_ext (funext fun e ↦
    (congrFun (Iso.toCatIso_hom_edge _) e).trans (DFunLike.congr_fun (Iso.ofEdge_edge _ _ _) e)))

@[simp]
theorem isoEquivIso_apply_hom_edge (f : Γ.Iso Δ) : (isoEquivIso f).hom.edge = f.edge := by
  simp [isoEquivIso, Iso.toCatIso_hom_edge]

/-- **Two ribbon graphs are isomorphic exactly when their edge actions are.** -/
theorem nonempty_iso_iff_edges : Nonempty (Γ.Iso Δ) ↔ Nonempty (Γ.edges ≅ Δ.edges) :=
  ⟨fun ⟨f⟩ ↦ ⟨edgeFunctor.mapIso (isoEquivIso f)⟩,
    fun ⟨i⟩ ↦ ⟨isoEquivIso.symm (edgeFunctorFullyFaithful.preimageIso i)⟩⟩

/-- **The classification bijection is induced by the edge equivalence**: two ribbon graphs with
`n` edges go to the same class of permutation triples exactly when their edge actions are
isomorphic. -/
theorem isoClassEquiv_eq_iff {n : ℕ}
    {Γ Δ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n}} :
    isoClassEquiv n ⟦Γ⟧ = isoClassEquiv n ⟦Δ⟧ ↔ Nonempty (Γ.val.edges ≅ Δ.val.edges) := by
  rw [(isoClassEquiv n).apply_eq_iff_eq, Quotient.eq, isoSetoid_r, nonempty_iso_iff_edges]

/-! ### Automorphisms -/

variable (Γ) in
/-- **Automorphisms of a ribbon graph are automorphisms of its edge action**: an automorphism goes
to the automorphism of `Γ.edges` given by its edge permutation. -/
def autEquivIsoEdges : Γ.Aut ≃ (edgeFunctor.obj Γ ≅ edgeFunctor.obj Γ) :=
  isoEquivIso.trans edgeFunctorFullyFaithful.isoEquiv

/-- An automorphism acts on the edge action by its edge permutation. -/
@[simp]
theorem autEquivIsoEdges_hom_hom_apply (f : Γ.Aut) (e : (edgeFunctor.obj Γ).V) :
    ConcreteCategory.hom (autEquivIsoEdges Γ f).hom.hom e = f.edge e := by
  rw [autEquivIsoEdges, Equiv.trans_apply, Functor.FullyFaithful.isoEquiv_apply,
    Functor.mapIso_hom]
  -- `edgeFunctor.map` is `edgesMap` (`edgeFunctor_map`), whose carrier `edgeFunctor.obj Γ` is
  -- `Γ.edges` only up to unfolding, so the last two steps are applied as terms.
  exact (edgesMap_hom_apply _ e).trans (congrFun (isoEquivIso_apply_hom_edge f) e)

/-- The correspondence of automorphisms turns the product of automorphisms, `f * g = g.trans f`,
into composition of isomorphisms. -/
theorem autEquivIsoEdges_mul (f g : Γ.Aut) :
    autEquivIsoEdges Γ (f * g) = autEquivIsoEdges Γ g ≪≫ autEquivIsoEdges Γ f :=
  CategoryTheory.Iso.ext (Action.Hom.ext (FintypeCat.hom_ext _ _ fun e ↦ by
    rw [autEquivIsoEdges_hom_hom_apply, Aut.mul_edge]
    -- Both sides evaluate as composites of the underlying maps: the product of permutations by
    -- `Equiv.Perm.mul_apply`, and the composite of isomorphisms by definition of composition in
    -- `Action FintypeCat`. Neither can be rewritten here, since the carrier of `edgeFunctor.obj Γ`
    -- is `Γ.E` only up to unfolding.
    exact (congrArg f.edge (autEquivIsoEdges_hom_hom_apply g e).symm).trans
      (autEquivIsoEdges_hom_hom_apply f _).symm))

/-! ### Connectedness -/

variable (Γ) in
/-- The image of the edge action is the rotation group. -/
theorem range_edgeAction : Γ.edgeAction.range = Γ.rotationGroup := by
  rw [MonoidHom.range_eq_map, ← FreeGroup.closure_range_of, MonoidHom.map_closure,
    ← closure_pair_eq_rotationGroup]
  congr 1
  ext σ
  simp [Fin.exists_fin_two, eq_comm]

variable (Γ) in
/-- **Connected ribbon graphs are the nonempty transitive `FreeGroup (Fin 2)`-sets**: a graph is
connected exactly when it has an edge and its edge action is transitive. -/
theorem isConnected_iff_isPretransitive :
    Γ.IsConnected ↔ Nonempty Γ.E ∧ MulAction.IsPretransitive (FreeGroup (Fin 2)) Γ.edges.V := by
  rw [isConnected_def]
  refine and_congr Iff.rfl ⟨fun ⟨h⟩ ↦ ⟨fun e e' ↦ ?_⟩, fun ⟨h⟩ ↦ ⟨fun e e' ↦ ?_⟩⟩
  · obtain ⟨⟨σ, hσ⟩, hσe⟩ := h e e'
    rw [← range_edgeAction] at hσ
    obtain ⟨w, rfl⟩ := hσ
    exact ⟨w, hσe⟩
  · obtain ⟨w, hw⟩ := h e e'
    exact ⟨⟨Γ.edgeAction w, range_edgeAction Γ ▸ ⟨w, rfl⟩⟩, hw⟩

end BipartiteRibbonGraph

end TauCeti
