/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Basic
public import TauCeti.Combinatorics.RibbonGraph.Basic

/-!
# The category of bipartite ribbon graphs

Finite bipartite ribbon graphs form a category with the incidence- and rotation-preserving
morphisms `TauCeti.BipartiteRibbonGraph.Hom`. Identity and composition act on edges by the
identity and composition of edge maps, and a morphism is determined by its edge map.
-/

public section

open CategoryTheory

namespace TauCeti.BipartiteRibbonGraph

universe u

/-- The category of bipartite ribbon graphs and maps preserving incidences and rotations. -/
instance : Category BipartiteRibbonGraph.{u} where
  Hom := Hom
  id := Hom.id
  comp f g := g.comp f
  id_comp := Hom.comp_id
  comp_id := Hom.id_comp
  assoc f g h := Hom.comp_assoc h g f

variable {Γ Δ Θ : BipartiteRibbonGraph.{u}}

/-- The categorical identity fixes each edge. -/
@[simp] theorem id_edge_apply (x : Γ.E) : (𝟙 Γ : Γ ⟶ Γ).edge x = x :=
  Hom.id_edge_apply x

/-- Categorical composition composes the underlying edge maps. -/
@[simp] theorem comp_edge_apply (f : Γ ⟶ Δ) (g : Δ ⟶ Θ) (x : Γ.E) :
    (f ≫ g).edge x = g.edge (f.edge x) := Hom.comp_edge_apply g f x

/-- A categorical morphism of bipartite ribbon graphs is determined by its edge map. -/
@[ext] theorem hom_ext {f g : Γ ⟶ Δ} (h : f.edge = g.edge) : f = g := Hom.ext h

end TauCeti.BipartiteRibbonGraph
