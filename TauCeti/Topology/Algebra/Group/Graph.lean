/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Graph
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Graphs of continuous group homomorphisms

This file equips the graph of a continuous group homomorphism with the topology needed to use it
as a subgroup of a product. The source is continuously multiplicatively equivalent to the graph,
and the graph is closed when the codomain is Hausdorff.
-/

public section

variable {G H F : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [FunLike F G H] [MonoidHomClass F G H] [ContinuousMapClass F G H]

/-- A group is continuously multiplicatively equivalent to the graph of a continuous
homomorphism out of it. -/
@[to_additive
  /-- An additive group is continuously additively equivalent to the graph of a continuous
  homomorphism out of it. -/]
def MonoidHomClass.graphEquiv (f : F) :
    G ≃ₜ* (MonoidHomClass.toMonoidHom f).graph where
  toFun g := ⟨(g, f g), rfl⟩
  invFun x := x.1.1
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact x.property
  map_mul' x y := by
    ext <;> simp
  continuous_toFun := (continuous_id.prodMk (map_continuous f)).subtype_mk _
  continuous_invFun := continuous_fst.comp continuous_subtype_val

/-- The graph equivalence sends an element to the corresponding point of the graph. -/
@[to_additive (attr := simp)
  /-- The additive graph equivalence sends an element to the corresponding point of the graph. -/]
theorem MonoidHomClass.coe_graphEquiv_apply (f : F) (g : G) :
    (MonoidHomClass.graphEquiv f g : G × H) = (g, f g) := (rfl)

/-- The inverse graph equivalence is the first projection. -/
@[to_additive (attr := simp)
  /-- The inverse additive graph equivalence is the first projection. -/]
theorem MonoidHomClass.graphEquiv_symm_apply (f : F)
    (x : (MonoidHomClass.toMonoidHom f).graph) :
    (MonoidHomClass.graphEquiv f).symm x = x.1.1 := (rfl)

/-- The graph of a continuous homomorphism into a Hausdorff group is closed. -/
@[to_additive
  /-- The graph of a continuous additive homomorphism into a Hausdorff additive group is closed. -/]
theorem MonoidHomClass.isClosed_graph [T2Space H] (f : F) :
    IsClosed ((MonoidHomClass.toMonoidHom f).graph : Set (G × H)) := by
  exact isClosed_eq ((map_continuous f).comp continuous_fst) continuous_snd
