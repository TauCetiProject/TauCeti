/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import TauCeti.GroupTheory.Amenable.DiscreteFoelner

/-!
# Følner sets on homogeneous coset spaces

Let `G` be a group and `H : Subgroup G` a subgroup (not necessarily normal), with `G` acting on the
left coset space `G ⧸ H` by left translation. This file establishes the two representation-free
transfers of finite Følner sets between `G` and `G ⧸ H`:

* **Mackey–Eymard coset Følner lift** (`TauCeti.exists_finset_card_smul_symmDiff_lt_of_quotient`):
  when `H` has Følner sets, any finite nonempty `F₁ ⊆ G ⧸ H` with `|g • F₁ ∆ F₁| < (ε / 2) |F₁|`
  on `K` lifts to a finite nonempty `E ⊆ G` with `|g • E ∆ E| < ε |E|` on `K` by multiplying
  chosen coset representatives of `F₁` on the right by a Følner set of `H` adapted to the section
  1-cocycle `c(g, q) = s(q)⁻¹ g s(g⁻¹ • q) ∈ H`.
* **Reiter coset pushforward** (`TauCeti.exists_finset_quotient_card_smul_symmDiff_lt`): when `G`
  has Følner sets, pushing a finitely supported Reiter probability density on `G` forward along
  `G → G ⧸ H` (`TauCeti.exists_finset_card_smul_symmDiff_lt_of_equivariant`) produces finite
  nonempty Følner sets in `G ⧸ H` for every finite `K ⊆ G` and `ε > 0`.

Together these imply `TauCeti.hasFoelnerSets_iff_exists_finset_quotient`: when `H` has Følner sets,
`G` has Følner sets if and only if `G ⧸ H` admits finite nonempty Følner sets for the `G`-action.

## Main results

* `TauCeti.exists_finset_card_smul_symmDiff_lt_of_quotient`: Mackey–Eymard coset Følner lift from
  `G ⧸ H` to `G` when `HasFoelnerSets H`.
* `TauCeti.exists_finset_quotient_card_smul_symmDiff_lt`: Reiter pushforward of Følner sets from `G`
  to `G ⧸ H`.
* `TauCeti.hasFoelnerSets_iff_exists_finset_quotient`: equivalence between `HasFoelnerSets G` and
  finite Følner sets in `G ⧸ H` when `HasFoelnerSets H`.

## References

* P. Eymard, *Moyennes invariantes et représentations unitaires*, Lecture Notes in Mathematics 300.
* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Lemma 15.1.9.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.5.
-/

public section

open Finset
open scoped Pointwise symmDiff

namespace TauCeti

variable {G : Type*} [Group G]

/-- **Mackey–Eymard coset Følner lift.** Given a subgroup `H` with Følner sets and a finite nonempty
`F₁ : Finset (G ⧸ H)` with `|g • F₁ ∆ F₁| < (ε / 2) |F₁|` for all `g ∈ K`, multiplying coset
representatives of `F₁` on the right by a suitable Følner set of `H` produces a finite nonempty
`E : Finset G` with `|g • E ∆ E| < ε |E|` for all `g ∈ K`. -/
theorem exists_finset_card_smul_symmDiff_lt_of_quotient [DecidableEq G] {H : Subgroup G}
    [DecidableEq (G ⧸ H)] (hH : HasFoelnerSets H) (K : Finset G) {ε : ℝ} (hε : 0 < ε)
    {F₁ : Finset (G ⧸ H)} (hF₁_ne : F₁.Nonempty)
    (hF₁ : ∀ g ∈ K, (#((g • F₁) ∆ F₁) : ℝ) < (ε / 2) * #F₁) :
    ∃ E : Finset G, E.Nonempty ∧ ∀ g ∈ K, (#((g • E) ∆ E) : ℝ) < ε * #E := by
  classical
  -- Step 1: Identify `(G ⧸ H) × H` injectively with `G` via `Quotient.out` and form the 1-cocycle.
  let s : G ⧸ H → G := Quotient.out
  have hs (q : G ⧸ H) : (s q : G ⧸ H) = q := QuotientGroup.out_eq' q
  let φ : (G ⧸ H) × H → G := fun p ↦ s p.1 * (p.2 : G)
  have hquot (p : (G ⧸ H) × H) : (φ p : G ⧸ H) = p.1 := by
    have hmem : (s p.1)⁻¹ * φ p ∈ H := by
      simp [φ]
    rw [← hs p.1]
    exact (QuotientGroup.eq.mpr hmem).symm
  have hφ_inj : Function.Injective φ := by
    intro p₁ p₂ hp
    have h1 : p₁.1 = p₂.1 := by rw [← hquot p₁, ← hquot p₂, hp]
    rcases p₁ with ⟨q₁, h₁⟩
    rcases p₂ with ⟨q₂, h₂⟩
    dsimp only at h1
    subst h1
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel hp))
  have hc_mem (g : G) (q : G ⧸ H) : (s q)⁻¹ * (g * s (g⁻¹ • q)) ∈ H := by
    apply QuotientGroup.eq.mp
    rw [hs q, ← smul_eq_mul, MulAction.Quotient.mk_smul_out, smul_inv_smul]
  let c (g : G) (q : G ⧸ H) : H := ⟨(s q)⁻¹ * (g * s (g⁻¹ • q)), hc_mem g q⟩
  have hgφ (g : G) (q : G ⧸ H) (h : H) : g * φ (g⁻¹ • q, h) = φ (q, c g q * h) := by
    simp only [φ, c, Subgroup.coe_mul]
    group
  -- Step 2: Choose a Følner set `F₂ ⊆ H` for the finite set of cocycle values `c(K × F₁)`.
  let K_H : Finset H := (K ×ˢ F₁).image fun p ↦ c p.1 p.2
  obtain ⟨F₂, hF₂_ne, hF₂⟩ := hasFoelnerSets_iff.mp hH K_H (ε / 4) (by positivity)
  let E : Finset G := (F₁ ×ˢ F₂).map ⟨φ, hφ_inj⟩
  have hE_ne : E.Nonempty := (hF₁_ne.product hF₂_ne).map
  have hE_card : #E = #F₁ * #F₂ := by simp [E]
  refine ⟨E, hE_ne, fun g hg ↦ ?_⟩
  -- Step 3: Decompose `E \ g • E` into cosets outside `g • F₁` and fiberwise cocycle boundaries.
  have hE_symm : #((g • E) ∆ E) = 2 * #(E \ g • E) := by
    rw [card_smul_finset_symmDiff, card_sdiff_comm (card_smul_finset g E)]
  have hF₁_symm : #((g • F₁) ∆ F₁) = 2 * #(F₁ \ g • F₁) := by
    rw [card_smul_finset_symmDiff, card_sdiff_comm (card_smul_finset g F₁)]
  let cover : Finset ((G ⧸ H) × H) :=
    (F₁ \ g • F₁) ×ˢ F₂ ∪ F₁.biUnion fun q ↦ {q} ×ˢ ((c g q • F₂) ∆ F₂)
  have hsub : E \ g • E ⊆ cover.map ⟨φ, hφ_inj⟩ := by
    intro x hx
    rw [mem_sdiff] at hx
    rcases mem_map.mp hx.1 with ⟨⟨q, h⟩, hqh, rfl⟩
    rw [mem_product] at hqh
    refine mem_map.mpr ⟨⟨q, h⟩, ?_, rfl⟩
    rw [mem_union]
    by_cases hqg : q ∈ g • F₁
    · right
      rw [mem_biUnion]
      refine ⟨q, hqh.1, mem_product.mpr ⟨mem_singleton_self q, ?_⟩⟩
      rw [mem_symmDiff]
      right
      refine ⟨hqh.2, fun hh' ↦ ?_⟩
      rcases mem_smul_finset.mp hh' with ⟨h', hh'_mem, rfl⟩
      apply hx.2
      rw [Function.Embedding.coeFn_mk, smul_eq_mul, ← hgφ]
      refine mem_smul_finset.mpr ⟨φ (g⁻¹ • q, h'), ?_, rfl⟩
      refine mem_map.mpr ⟨(g⁻¹ • q, h'), mem_product.mpr ⟨?_, hh'_mem⟩, rfl⟩
      rcases mem_smul_finset.mp hqg with ⟨q₀, hq₀, rfl⟩
      simpa using hq₀
    · left
      exact mem_product.mpr ⟨mem_sdiff.mpr ⟨hqh.1, hqg⟩, hqh.2⟩
  have hcard_le : #(E \ g • E) ≤ #(F₁ \ g • F₁) * #F₂ +
      ∑ q ∈ F₁, #((c g q • F₂) ∆ F₂) := by
    calc #(E \ g • E)
        ≤ #(cover.map ⟨φ, hφ_inj⟩) := card_le_card hsub
      _ = #cover := card_map _
      _ ≤ #((F₁ \ g • F₁) ×ˢ F₂) + #(F₁.biUnion fun q ↦ {q} ×ˢ ((c g q • F₂) ∆ F₂)) :=
          card_union_le _ _
      _ ≤ #(F₁ \ g • F₁) * #F₂ + ∑ q ∈ F₁, #({q} ×ˢ ((c g q • F₂) ∆ F₂)) := by
          rw [card_product]
          exact Nat.add_le_add_left card_biUnion_le _
      _ = #(F₁ \ g • F₁) * #F₂ + ∑ q ∈ F₁, #((c g q • F₂) ∆ F₂) := by
          simp
  -- Step 4: Combine the `(ε / 2)` coset boundary bound and the `(ε / 4)` fiber boundary bounds.
  have hterm1 : 2 * ((#(F₁ \ g • F₁) : ℝ) * #F₂) < (ε / 2) * (#F₁ * #F₂) := by
    have hpos2 : (0 : ℝ) < #F₂ := Nat.cast_pos.mpr hF₂_ne.card_pos
    have h1 : 2 * (#(F₁ \ g • F₁) : ℝ) < (ε / 2) * #F₁ := by
      have := hF₁ g hg
      rwa [hF₁_symm, Nat.cast_mul, Nat.cast_ofNat] at this
    nlinarith
  have hterm2 : (2 * ∑ q ∈ F₁, (#((c g q • F₂) ∆ F₂) : ℝ)) < (ε / 2) * (#F₁ * #F₂) := by
    have hsum : ∑ q ∈ F₁, (#((c g q • F₂) ∆ F₂) : ℝ) < ∑ _q ∈ F₁, (ε / 4) * #F₂ :=
      sum_lt_sum_of_nonempty hF₁_ne fun q hq ↦
        hF₂ (c g q) (mem_image.mpr ⟨(g, q), mem_product.mpr ⟨hg, hq⟩, rfl⟩)
    simp only [sum_const, nsmul_eq_mul] at hsum
    linarith
  have hnat_bound : (#((g • E) ∆ E) : ℝ) ≤
      2 * ((#(F₁ \ g • F₁) : ℝ) * #F₂) + 2 * ∑ q ∈ F₁, (#((c g q • F₂) ∆ F₂) : ℝ) := by
    have hmul : #((g • E) ∆ E) ≤ 2 * (#(F₁ \ g • F₁) * #F₂ + ∑ q ∈ F₁, #((c g q • F₂) ∆ F₂)) := by
      rw [hE_symm]
      exact Nat.mul_le_mul_left 2 hcard_le
    have hreal : (#((g • E) ∆ E) : ℝ) ≤
        ((2 * (#(F₁ \ g • F₁) * #F₂ + ∑ q ∈ F₁, #((c g q • F₂) ∆ F₂)) : ℕ) : ℝ) := by
      exact_mod_cast hmul
    push_cast at hreal
    linarith
  rw [hE_card, Nat.cast_mul]
  linarith

/-- **Reiter pushforward to coset spaces.** If `G` has Følner sets, then for any subgroup `H`,
every finite `K ⊆ G`, and `ε > 0`, there is a finite nonempty `F₁ : Finset (G ⧸ H)` with
`|g • F₁ ∆ F₁| < ε |F₁|` for all `g ∈ K`. -/
theorem exists_finset_quotient_card_smul_symmDiff_lt (hG : HasFoelnerSets G) (H : Subgroup G)
    [DecidableEq (G ⧸ H)] (K : Finset G) {ε : ℝ} (hε : 0 < ε) :
    ∃ F₁ : Finset (G ⧸ H), F₁.Nonempty ∧ ∀ g ∈ K, (#((g • F₁) ∆ F₁) : ℝ) < ε * #F₁ := by
  let : TopologicalSpace G := ⊥
  have : DiscreteTopology G := ⟨rfl⟩
  have : IsTopologicalGroup G := {}
  have : Amenable G := .of_hasFoelnerSets hG
  obtain ⟨p, hp0, hp_fin, hp1, hp_lt⟩ := Amenable.exists_sum_tsum_abs_sub_lt K hε
  exact exists_finset_card_smul_symmDiff_lt_of_equivariant
    (π := (QuotientGroup.mk : G → G ⧸ H)) (fun g x ↦ (MulAction.Quotient.smul_mk H g x).symm)
    hp0 hp_fin (by simpa [hp1] using hp_lt)

/-- **Mackey–Eymard coset Følner equivalence.** When `H` has Følner sets, `G` has Følner sets if and
only if the left coset space `G ⧸ H` admits finite nonempty Følner sets for every finite `K ⊆ G` and
`ε > 0`. -/
theorem hasFoelnerSets_iff_exists_finset_quotient {H : Subgroup G} [DecidableEq (G ⧸ H)]
    (hH : HasFoelnerSets H) :
    HasFoelnerSets G ↔ ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
      ∃ F₁ : Finset (G ⧸ H), F₁.Nonempty ∧ ∀ g ∈ K, (#((g • F₁) ∆ F₁) : ℝ) < ε * #F₁ := by
  classical
  rw [hasFoelnerSets_iff]
  refine ⟨fun h K ε hε ↦ exists_finset_quotient_card_smul_symmDiff_lt
    (hasFoelnerSets_iff.mpr h) H K hε, fun h K ε hε ↦ ?_⟩
  obtain ⟨F₁, hF₁_ne, hF₁⟩ := h K (ε / 2) (half_pos hε)
  exact exists_finset_card_smul_symmDiff_lt_of_quotient hH K hε hF₁_ne hF₁

end TauCeti
