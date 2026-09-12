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

@[expose] public section

namespace TauCeti

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

namespace ContinuousMonoidHom

/-- A group is continuously multiplicatively equivalent to the graph of a continuous
homomorphism out of it. -/
@[to_additive ContinuousAddMonoidHom.graphEquiv
  /-- An additive group is continuously additively equivalent to the graph of a continuous
  homomorphism out of it. -/]
def graphEquiv (f : G →ₜ* H) : G ≃ₜ* (f : G →* H).graph where
  toFun g := ⟨(g, f g), rfl⟩
  invFun x := x.1.1
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact x.property
  map_mul' x y := by
    apply Subtype.ext
    change (x * y, f (x * y)) = (x * y, f x * f y)
    simp
  continuous_toFun := (continuous_id.prodMk f.continuous).subtype_mk _
  continuous_invFun := continuous_fst.comp continuous_subtype_val

/-- The graph equivalence sends an element to the corresponding point of the graph. -/
@[to_additive (attr := simp) ContinuousAddMonoidHom.coe_graphEquiv_apply
  /-- The additive graph equivalence sends an element to the corresponding point of the graph. -/]
theorem coe_graphEquiv_apply (f : G →ₜ* H) (g : G) :
    (graphEquiv f g : G × H) = (g, f g) :=
  rfl

/-- The inverse graph equivalence is the first projection. -/
@[to_additive (attr := simp) ContinuousAddMonoidHom.graphEquiv_symm_apply
  /-- The inverse additive graph equivalence is the first projection. -/]
theorem graphEquiv_symm_apply (f : G →ₜ* H) (x : (f : G →* H).graph) :
    (graphEquiv f).symm x = x.1.1 :=
  rfl

/-- The graph of a continuous homomorphism into a Hausdorff group is closed. -/
@[to_additive ContinuousAddMonoidHom.isClosed_graph
  /-- The graph of a continuous additive homomorphism into a Hausdorff additive group is closed. -/]
theorem isClosed_graph [T2Space H] (f : G →ₜ* H) :
    IsClosed ((f : G →* H).graph : Set (G × H)) := by
  exact isClosed_eq (f.continuous.comp continuous_fst) continuous_snd

end ContinuousMonoidHom

end TauCeti
