/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement

/-!
# Transport of subgroup complements

A complement of the image of a subgroup pulls back along a homomorphism whose kernel
meets that subgroup trivially.
-/

public section

namespace Subgroup

variable {G G' : Type*} [Group G] [Group G'] {N : Subgroup G}

/-- A complement of the image of a subgroup pulls back along a homomorphism whose kernel
is disjoint from that subgroup. -/
theorem IsComplement'.comap_of_disjoint_ker {f : G →* G'} {D : Subgroup G'}
    (h : (N.map f).IsComplement' D) (hker : Disjoint N f.ker) :
    N.IsComplement' (D.comap f) := by
  apply isComplement'_of_disjoint_and_mul_eq_univ
  · rw [disjoint_iff_inf_le]
    intro x hx
    have hfx : f x = 1 := mem_bot.mp (disjoint_iff_inf_le.mp h.disjoint
      ⟨mem_map.mpr ⟨x, hx.1, rfl⟩, hx.2⟩)
    exact disjoint_iff_inf_le.mp hker ⟨hx.1, MonoidHom.mem_ker.mpr hfx⟩
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    obtain ⟨⟨n, d⟩, hd⟩ := h.surjective (f x)
    obtain ⟨n, hn, he⟩ := n.property
    have hfd : f (n⁻¹ * x) = d := by
      rw [map_mul, map_inv, he, ← hd, inv_mul_cancel_left]
    refine ⟨n, hn, n⁻¹ * x, ?_, by simp⟩
    exact mem_comap.mpr (hfd.symm ▸ d.property)

end Subgroup
