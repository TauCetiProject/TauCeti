/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions

/-!
# A subtype of a subtype as a subtype

If `q x` implies `p x`, then the subtype of `Subtype p` cut out by `q` is homeomorphic to
`Subtype q`. For sets `S ⊆ S'` this reads `S`, as a subset of `S'`, as the subset `S` itself.

## Main results

* `Homeomorph.subtypeSubtypeEquivSubtype`: the homeomorphism version of Mathlib's
  `Equiv.subtypeSubtypeEquivSubtype`.
* `Homeomorph.subtypeSubtypeEquivSubtype_apply_coe` and
  `Homeomorph.subtypeSubtypeEquivSubtype_symm_apply_coe_coe`: both directions fix the underlying
  point.
-/

public section

namespace Homeomorph

variable {X : Type*} [TopologicalSpace X] {p q : X → Prop}

/-- If `q x` implies `p x`, then the subtype of `Subtype p` cut out by `q` is homeomorphic to
`Subtype q`. This is the homeomorphism version of Mathlib's `Equiv.subtypeSubtypeEquivSubtype`. -/
@[expose] def subtypeSubtypeEquivSubtype (h : ∀ {x}, q x → p x) :
    { x : Subtype p // q x.1 } ≃ₜ Subtype q where
  toEquiv := Equiv.subtypeSubtypeEquivSubtype h
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- `Homeomorph.subtypeSubtypeEquivSubtype` fixes the underlying point. -/
@[simp]
theorem subtypeSubtypeEquivSubtype_apply_coe (h : ∀ {x}, q x → p x)
    (x : { x : Subtype p // q x.1 }) : (subtypeSubtypeEquivSubtype h x : X) = x :=
  rfl

/-- The inverse of `Homeomorph.subtypeSubtypeEquivSubtype` fixes the underlying point. -/
@[simp]
theorem subtypeSubtypeEquivSubtype_symm_apply_coe_coe (h : ∀ {x}, q x → p x) (x : Subtype q) :
    (((subtypeSubtypeEquivSubtype h).symm x : Subtype p) : X) = x :=
  rfl

end Homeomorph
