/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Logic.Equiv.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Splitting a subgroup along a complement

Let `i : M →* G` meet the subgroup `N` only in `i(1)`, and let `δ : D → M` be injective. If a
subgroup `Γ` contains every `i(δ d)` and every element of `Γ` lies in some `N i(δ d)⁻¹`, then
`(d, γ) ↦ i(δ d) γ` is a bijection `D × (Γ ∩ N) ≃ Γ`, where `Γ ∩ N` is `Γ.subgroupOf N`
(`Subgroup.exists_equiv_prod_subgroupOf`).

## References

The statement and proof are adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache
2.0, Copyright 2026 Anthropic PBC), `src/Lib/Adelic/QuotientMeasure/IwasawaUnfolding.lean`
(`New.exists_equiv_prod_subgroupOf`).
-/

public section

/-- **Splitting a subgroup along a complement.** Let `i : M →* G` meet the subgroup `N` only in
`i(1)`, and let `δ : D → M` be injective. If the subgroup `Γ` contains every `i(δ d)` and every
`g ∈ Γ` has some `g i(δ d) ∈ N`, then `(d, γ) ↦ i(δ d) γ` is a bijection
`D × (Γ ∩ N) ≃ Γ`. -/
theorem Subgroup.exists_equiv_prod_subgroupOf {G M D : Type*} [Group G] [Group M]
    {N Γ : Subgroup G} {i : M →* G}
    (h_triv : ∀ a : M, i a ∈ N → a = 1) {δ : D → M} (hδ : δ.Injective)
    (hδ_mem : ∀ d, i (δ d) ∈ Γ) (hΓ : ∀ g ∈ Γ, ∃ d, g * i (δ d) ∈ N) :
    ∃ e : D × Γ.subgroupOf N ≃ Γ, ∀ d (γ : Γ.subgroupOf N), (e (d, γ) : G) = i (δ d) * (γ : N) := by
  let φ (p : D × Γ.subgroupOf N) : Γ :=
    ⟨i (δ p.1) * (p.2 : N), mul_mem (hδ_mem p.1) (Subgroup.mem_subgroupOf.1 p.2.property)⟩
  refine ⟨.ofBijective φ ⟨?_, fun g ↦ ?_⟩, fun d γ ↦ rfl⟩
  · rintro ⟨d, γ⟩ ⟨d', γ'⟩ h
    have h_eq : i (δ d) * (γ : N) = i (δ d') * (γ' : N) := congrArg Subtype.val h
    have h_mem : i ((δ d)⁻¹ * δ d') ∈ N := by
      simpa [QuotientGroup.eq] using congrArg (QuotientGroup.mk : G → G ⧸ N) h_eq
    obtain rfl : d = d' := hδ (inv_mul_eq_one.1 (h_triv _ h_mem))
    simpa using h_eq
  · obtain ⟨d, h_mem⟩ : ∃ d, (g : G)⁻¹ * i (δ d) ∈ N := hΓ _ (inv_mem g.property)
    let γ : Γ.subgroupOf N :=
      ⟨⟨(g : G)⁻¹ * i (δ d), h_mem⟩, mul_mem (inv_mem g.property) (hδ_mem d)⟩
    exact ⟨(d, γ⁻¹), by simp [φ, γ]⟩
