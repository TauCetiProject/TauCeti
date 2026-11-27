/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Blocks

/-!
# Invariance and saturation under a group action

An invariant block is exactly a set that equals its saturation under the orbit quotient.
This identifies invariance under the action with invariance for the associated setoid.
-/

public section

open Set
open scoped Pointwise

namespace TauCeti

/-- A set is invariant under a group action exactly when it equals the pullback of its image in
the orbit quotient. -/
theorem isInvariantBlock_iff_preimage_image_quotientMk {G X : Type*} [Group G] [MulAction G X]
    {A : Set X} :
    MulAction.IsInvariantBlock G A ↔
      Quotient.mk (MulAction.orbitRel G X) ⁻¹' (Quotient.mk (MulAction.orbitRel G X) '' A) = A := by
  refine ⟨fun hA => (subset_preimage_image _ _).antisymm' ?_, fun hA g => ?_⟩
  · rintro x ⟨a, ha, hax⟩
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1
      (Quotient.exact hax.symm))
    exact hA g (smul_mem_smul_set ha)
  · rintro _ ⟨a, ha, rfl⟩
    rw [← hA]
    exact ⟨a, ha, (Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit a g))).symm⟩

end TauCeti
