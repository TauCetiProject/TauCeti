/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Iso
public import TauCeti.Combinatorics.RibbonGraph.Basic

/-!
# The category of bipartite ribbon graphs

Finite bipartite ribbon graphs form a category with the incidence- and rotation-preserving
morphisms `TauCeti.BipartiteRibbonGraph.Hom`. Identity and composition act on edges by the
identity and composition of edge maps, and a morphism is determined by its edge map.
`TauCeti.BipartiteRibbonGraph.isoEquiv` identifies the categorical isomorphisms with
`TauCeti.BipartiteRibbonGraph.Iso`.
-/

public section

open CategoryTheory

namespace TauCeti.BipartiteRibbonGraph

universe u

/-- Finite bipartite ribbon graphs form a category, with the morphisms `Hom`. -/
instance instCategory : Category BipartiteRibbonGraph.{u} where
  Hom := Hom
  id := Hom.id
  comp f g := g.comp f
  id_comp := Hom.comp_id
  comp_id := Hom.id_comp
  assoc f g h := Hom.comp_assoc h g f

/-- The categorical identity of a ribbon graph is `BipartiteRibbonGraph.Hom.id`. -/
@[simp]
theorem id_eq_id (Γ : BipartiteRibbonGraph.{u}) : 𝟙 Γ = Hom.id Γ :=
  (rfl)

/-- Categorical composition of ribbon-graph morphisms is `BipartiteRibbonGraph.Hom.comp`, in the
opposite order. -/
@[simp]
theorem comp_eq_comp {Γ Δ Θ : BipartiteRibbonGraph.{u}} (f : Γ ⟶ Δ) (g : Δ ⟶ Θ) :
    f ≫ g = g.comp f :=
  (rfl)

/-- Morphisms of ribbon graphs in the category are equal when their edge maps are. -/
@[ext]
theorem hom_ext {Γ Δ : BipartiteRibbonGraph.{u}} {f g : Γ ⟶ Δ} (h : f.edge = g.edge) : f = g :=
  Hom.ext h

variable {Γ Δ Θ : BipartiteRibbonGraph.{u}}

/-- The categorical identity fixes each edge. -/
theorem id_edge_apply (x : Γ.E) : (𝟙 Γ : Γ ⟶ Γ).edge x = x :=
  Hom.id_edge_apply x

/-- Categorical composition composes the underlying edge maps. -/
theorem comp_edge_apply (f : Γ ⟶ Δ) (g : Δ ⟶ Θ) (x : Γ.E) :
    (f ≫ g).edge x = g.edge (f.edge x) := Hom.comp_edge_apply g f x

/-- The categorical identity fixes each black vertex. -/
theorem id_black_apply (b : Γ.B) : (𝟙 Γ : Γ ⟶ Γ).black b = b :=
  Hom.id_black_apply b

/-- The categorical identity fixes each white vertex. -/
theorem id_white_apply (w : Γ.W) : (𝟙 Γ : Γ ⟶ Γ).white w = w :=
  Hom.id_white_apply w

/-- Categorical composition composes the maps on black vertices. -/
theorem comp_black_apply (f : Γ ⟶ Δ) (g : Δ ⟶ Θ) (b : Γ.B) :
    (f ≫ g).black b = g.black (f.black b) := Hom.comp_black_apply g f b

/-- Categorical composition composes the maps on white vertices. -/
theorem comp_white_apply (f : Γ ⟶ Δ) (g : Δ ⟶ Θ) (w : Γ.W) :
    (f ≫ g).white w = g.white (f.white w) := Hom.comp_white_apply g f w

/-- An isomorphism of ribbon graphs is the same as an isomorphism in their category. -/
def isoEquiv : Γ.Iso Δ ≃ (Γ ≅ Δ) where
  toFun f :=
    { hom := f.toHom
      inv := f.symm.toHom
      hom_inv_id := hom_ext (funext fun x ↦ by simp)
      inv_hom_id := hom_ext (funext fun x ↦ by simp) }
  invFun f :=
    { edge :=
        { toFun := f.hom.edge
          invFun := f.inv.edge
          left_inv := fun x ↦ by
            simpa only [comp_edge_apply, id_edge_apply] using
              congrArg (fun k : Γ ⟶ Γ ↦ k.edge x) f.hom_inv_id
          right_inv := fun x ↦ by
            simpa only [comp_edge_apply, id_edge_apply] using
              congrArg (fun k : Δ ⟶ Δ ↦ k.edge x) f.inv_hom_id }
      black :=
        { toFun := f.hom.black
          invFun := f.inv.black
          left_inv := fun b ↦ by
            simpa only [comp_black_apply, id_black_apply] using
              congrArg (fun k : Γ ⟶ Γ ↦ k.black b) f.hom_inv_id
          right_inv := fun b ↦ by
            simpa only [comp_black_apply, id_black_apply] using
              congrArg (fun k : Δ ⟶ Δ ↦ k.black b) f.inv_hom_id }
      white :=
        { toFun := f.hom.white
          invFun := f.inv.white
          left_inv := fun w ↦ by
            simpa only [comp_white_apply, id_white_apply] using
              congrArg (fun k : Γ ⟶ Γ ↦ k.white w) f.hom_inv_id
          right_inv := fun w ↦ by
            simpa only [comp_white_apply, id_white_apply] using
              congrArg (fun k : Δ ⟶ Δ ↦ k.white w) f.inv_hom_id }
      map_blackEnd := f.hom.map_blackEnd
      map_whiteEnd := f.hom.map_whiteEnd
      map_rotB := f.hom.map_rotB
      map_rotW := f.hom.map_rotW }
  left_inv f := Iso.ext (Equiv.ext fun x ↦ Iso.toHom_edge_apply f x)
  right_inv f := by
    apply CategoryTheory.Iso.ext
    refine hom_ext (funext fun x ↦ ?_)
    exact Iso.toHom_edge_apply _ x

/-- The forward categorical morphism is the morphism of the graph isomorphism. -/
@[simp] theorem isoEquiv_hom (f : Γ.Iso Δ) : (isoEquiv f).hom = f.toHom := by
  rw [isoEquiv]
  rfl

/-- The inverse categorical morphism comes from the inverse graph isomorphism. -/
@[simp] theorem isoEquiv_inv (f : Γ.Iso Δ) : (isoEquiv f).inv = f.symm.toHom := by
  rw [isoEquiv]
  rfl

/-- Converting back to a graph isomorphism preserves the forward morphism. -/
@[simp] theorem isoEquiv_symm_toHom (f : Γ ≅ Δ) : (isoEquiv.symm f).toHom = f.hom := by
  apply hom_ext
  funext x
  rw [Iso.toHom_edge_apply, isoEquiv]
  rfl

/-- The correspondence between isomorphisms preserves composition. -/
@[simp] theorem isoEquiv_trans (f : Γ.Iso Δ) (g : Δ.Iso Θ) :
    isoEquiv (f.trans g) = isoEquiv f ≪≫ isoEquiv g := by
  apply CategoryTheory.Iso.ext
  refine hom_ext (funext fun x ↦ ?_)
  simp only [CategoryTheory.Iso.trans_hom, isoEquiv_hom, comp_edge_apply, Iso.toHom_edge_apply,
    Iso.trans_edge_apply]

end TauCeti.BipartiteRibbonGraph
