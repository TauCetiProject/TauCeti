/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Stabilizers and pointwise fixing subgroups

This file records small generic additions to Mathlib's stabilizer and `fixingSubgroup` APIs.
-/

public section

namespace TauCeti

open Equiv

/-- For a faithful action, the subgroup fixing the whole space pointwise is trivial. -/
@[simp]
theorem fixingSubgroup_univ {G α : Type*} [Group G] [MulAction G α] [FaithfulSMul G α] :
    _root_.fixingSubgroup G (Set.univ : Set α) = ⊥ := by
  ext g
  rw [_root_.mem_fixingSubgroup_iff, Subgroup.mem_bot]
  refine ⟨fun hg => ?_, fun hg x _ => by rw [hg, one_smul]⟩
  exact FaithfulSMul.eq_of_smul_eq_smul fun x =>
    (hg x (Set.mem_univ x)).trans (one_smul G x).symm

/-- If a point has trivial stabilizer under the image of a permutation representation, then its
stabilizer in the source is the kernel of the representation. -/
theorem comap_stabilizer_eq_ker {G α : Type*} [Group G] (ρ : G →* Perm α) (i : α)
    (hi : MulAction.stabilizer ρ.range i = ⊥) :
    (MulAction.stabilizer (Perm α) i).comap ρ = ρ.ker := by
  ext g
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MonoidHom.mem_ker]
  refine ⟨fun hg => ?_, fun hg => by rw [hg, one_smul]⟩
  let h : ρ.range := ⟨ρ g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩
  have hh : h = 1 := by
    rw [← Subgroup.mem_bot, ← hi, MulAction.mem_stabilizer_iff]
    exact hg
  exact congrArg Subtype.val hh

/-- For a transitive permutation representation, a point stabilizer is normal in the source
exactly when the image acts freely. -/
theorem normal_comap_stabilizer_iff_isCancelSMul {G α : Type*} [Group G]
    (ρ : G →* Perm α) (hρ : MulAction.IsPretransitive ρ.range α) (i : α) :
    ((MulAction.stabilizer (Perm α) i).comap ρ).Normal ↔ IsCancelSMul ρ.range α := by
  refine ⟨fun hN => ?_, fun hfree => ?_⟩
  · set K := (MulAction.stabilizer (Perm α) i).comap ρ
    have hK : ∀ (g : G) (j : α), ρ g j = j ↔ g ∈ K := by
      intro g j
      obtain ⟨h, hh⟩ := hρ.exists_smul_eq i j
      obtain ⟨k, hk⟩ : (h : Perm α) ∈ ρ.range := h.2
      have hki : ρ k i = j := hk ▸ hh
      have hconj : k⁻¹ * g * k ∈ K ↔ ρ g j = j := by
        rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
        simp only [map_mul, map_inv, Perm.smul_def, Perm.mul_apply]
        calc
          (ρ k)⁻¹ (ρ g (ρ k i)) = i ↔ ρ g (ρ k i) = ρ k i := by
            rw [Perm.inv_eq_iff_eq]
          _ ↔ ρ g j = j := by rw [hki]
      rw [← hconj]
      exact ⟨fun hg => by simpa [mul_assoc] using hN.conj_mem _ hg k,
        fun hg => by simpa using hN.conj_mem _ hg k⁻¹⟩
    refine isCancelSMul_iff_stabilizer_eq_bot.mpr fun j => ?_
    refine (Subgroup.eq_bot_iff_forall _).mpr fun h hh => ?_
    obtain ⟨g, hg⟩ : (h : Perm α) ∈ ρ.range := h.2
    have hgj : ρ g j = j := hg ▸ hh
    refine Subtype.ext <| hg ▸ Equiv.ext fun k => ?_
    exact (hK g k).mpr ((hK g j).mp hgj)
  · rw [comap_stabilizer_eq_ker ρ i (IsCancelSMul.stabilizer_eq_bot i)]
    infer_instance

end TauCeti
