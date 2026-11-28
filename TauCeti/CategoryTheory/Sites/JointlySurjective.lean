/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.JointlySurjective

/-!
# Joint surjectivity under isomorphic functors to types

Mathlib's `Types.jointlySurjectivePrecoverage.comap F` declares a family of maps covering when
it is jointly surjective after applying a functor `F : C ⥤ Type u`
(`Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff`). This file shows that joint
surjectivity of a family under `F` depends on `F` only up to natural isomorphism
(`CategoryTheory.Iso.forall_exists_mem_range_map_iff`).
-/

public section

universe u

namespace CategoryTheory.Iso

/-- Joint surjectivity of a family of maps under a functor to types is invariant under natural
isomorphism of the functor. -/
theorem forall_exists_mem_range_map_iff {C : Type*} [Category* C] {F F' : C ⥤ Type u}
    (e : F ≅ F') {X : C} {ι : Type*} {Y : ι → C} (f : ∀ i, Y i ⟶ X) :
    (∀ s : F.obj X, ∃ i, s ∈ Set.range (F.map (f i))) ↔
      ∀ s : F'.obj X, ∃ i, s ∈ Set.range (F'.map (f i)) := by
  suffices H : ∀ {F F' : C ⥤ Type u}, (F ≅ F') →
      (∀ s : F.obj X, ∃ i, s ∈ Set.range (F.map (f i))) →
        ∀ s : F'.obj X, ∃ i, s ∈ Set.range (F'.map (f i)) from ⟨H e, H e.symm⟩
  intro F F' e h s
  obtain ⟨i, t, ht⟩ := h (e.inv.app X s)
  refine ⟨i, e.hom.app _ t, ?_⟩
  rw [← NatTrans.naturality_apply, ht, Iso.inv_hom_id_app_apply]

end CategoryTheory.Iso
