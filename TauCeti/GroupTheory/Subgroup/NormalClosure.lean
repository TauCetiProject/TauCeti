/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Normal generators inside a subgroup

Suppose the normal closure of `R` in `G` lies in a subgroup `H`. To normally generate that
kernel inside `H`, it suffices to conjugate `R` by representatives `t` with `G = H T`.
The representatives need not be unique. In particular, a right transversal supplies a
complete family of subgroup relators, not merely relations valid in a quotient image.

This is the normal-generation step in the Reidemeister–Schreier theorem. It is independent
of freeness, finiteness and the choice of generators for `H`.

## References

* D. L. Johnson, *Presentations of Groups*, second edition, Chapter 9.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- If `normalClosure R ≤ H` and every element of `G` is `h * t` with `h ∈ H` and `t ∈ T`,
then the conjugates `t * r * t⁻¹` normally generate `normalClosure R` inside `H`.
Neither distinct cosets nor a normal subgroup `H` are required. -/
theorem normalClosure_conjugates_eq_subgroupOf (H : Subgroup G) (R T : Set G)
    (hR : normalClosure R ≤ H) (hT : ∀ g : G, ∃ h : H, ∃ t ∈ T, (h : G) * t = g) :
    normalClosure {x : H | ∃ t ∈ T, ∃ r ∈ R, t * r * t⁻¹ = (x : G)} =
      (normalClosure R).subgroupOf H := by
  let S : Set H := {x : H | ∃ t ∈ T, ∃ r ∈ R, t * r * t⁻¹ = (x : G)}
  have hle : normalClosure S ≤ (normalClosure R).subgroupOf H := by
    refine normalClosure_le_normal ?_
    rintro x ⟨t, _, r, hr, hx⟩
    apply mem_subgroupOf.mpr
    rw [← hx]
    exact normalClosure_normal.conj_mem r (subset_normalClosure hr) t
  have hmap : normalClosure R ≤ (normalClosure S).map H.subtype := by
    rw [normalClosure, closure_le]
    intro x hx
    obtain ⟨r, hr, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
    obtain ⟨h, t, ht, rfl⟩ := hT g
    let y : H := ⟨t * r * t⁻¹, hR (normalClosure_normal.conj_mem r
      (subset_normalClosure hr) t)⟩
    have hy : y ∈ normalClosure S := subset_normalClosure ⟨t, ht, r, hr, rfl⟩
    refine ⟨h * y * h⁻¹, normalClosure_normal.conj_mem y hy h, ?_⟩
    simp [y, mul_assoc]
  refine le_antisymm hle ?_
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hmap (mem_subgroupOf.mp hx)
  exact (Subtype.ext hxy : y = x) ▸ hy

end Subgroup
