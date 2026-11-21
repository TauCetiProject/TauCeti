/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Constructions

/-!
# The preimage of a set under the second projection

For `t : Set Y`, the subspace `Prod.snd ⁻¹' t` of `X × Y` is homeomorphic to the product `X × t`
(`Homeomorph.Set.preimageSnd`). Mathlib's `Homeomorph.Set.prod` treats the product set `s ×ˢ t`,
which is not syntactically a preimage.
-/

@[expose] public section

namespace Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The subspace `Prod.snd ⁻¹' t` of `X × Y` is homeomorphic to `X × t`. -/
@[simps]
def Set.preimageSnd (t : Set Y) : ↥(Prod.snd ⁻¹' t : Set (X × Y)) ≃ₜ X × t where
  toFun z := (z.val.1, ⟨z.val.2, z.property⟩)
  invFun z := ⟨(z.1, z.2.val), z.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end Homeomorph
