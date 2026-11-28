/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PGroup

/-!
# Quotient `p`-group constraints on group homomorphisms

When `G ⧸ H` is a `p`-group, any two monoid homomorphisms from `G` that agree on `H` have equal
`p^k`-th powers at every element of `G` for some `k : ℕ`.
-/

public section

namespace IsPGroup

/-- When `G ⧸ H` is a `p`-group, any two monoid homomorphisms from `G` with the same restriction
to `H` have equal `p^k`-th powers at every element `g ∈ G` for some `k : ℕ`. -/
theorem exists_pow_pow_eq_of_comp_eq {G M : Type*} [Group G] [Monoid M]
    {H : Subgroup G} [H.Normal] {p : ℕ} (hGH : IsPGroup p (G ⧸ H))
    {ψ₁ ψ₂ : G →* M} (hH : ψ₁.comp H.subtype = ψ₂.comp H.subtype) (g : G) :
    ∃ k : ℕ, ψ₁ g ^ p ^ k = ψ₂ g ^ p ^ k := by
  obtain ⟨k, hk⟩ := hGH.exists_pow_pow_eq_one (QuotientGroup.mk g)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
  refine ⟨k, ?_⟩
  simpa only [map_pow, MonoidHom.comp_apply, Subgroup.coe_subtype] using
    DFunLike.congr_fun hH ⟨g ^ p ^ k, hk⟩

end IsPGroup
