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
(`CategoryTheory.Iso.forall_exists_mem_range_map_iff`), and proves that refining a family of maps
by jointly surjective families preserves the union of ranges (`Set.iUnion_range_comp_sigma`).
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

/-- Refining a family of functions `u : ∀ i, U i → S` by families `v i : ∀ k, V i k → U i` whose
ranges cover each `U i` preserves the union of ranges. -/
theorem _root_.Set.iUnion_range_comp_sigma {S : Type*} {ι : Type*} {U : ι → Type*}
    (u : ∀ i, U i → S) {κ : ι → Type*} {V : ∀ i, κ i → Type*}
    {v : ∀ i, ∀ k : κ i, V i k → U i} (hv : ∀ i, ⋃ k, Set.range (v i k) = .univ) :
    (⋃ p : Σ i, κ i, Set.range (u p.1 ∘ v p.1 p.2)) = ⋃ i, Set.range (u i) := by
  ext s
  simp only [Set.mem_iUnion, Set.mem_range, Function.comp_apply, Sigma.exists]
  refine ⟨fun ⟨i, k, z, hz⟩ ↦ ⟨i, v i k z, hz⟩, fun ⟨i, x, hx⟩ ↦ ?_⟩
  obtain ⟨k, z, rfl⟩ := Set.mem_iUnion.mp (hv i ▸ Set.mem_univ x)
  exact ⟨i, k, z, hx⟩
