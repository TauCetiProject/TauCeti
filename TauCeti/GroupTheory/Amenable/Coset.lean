/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import TauCeti.GroupTheory.Amenable.DiscreteFoelner
import TauCeti.Algebra.Group.Action.Pointwise.Finset

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
  has Følner sets, summing a finitely supported Reiter probability density on `G` along the fibers
  of `G → G ⧸ H` produces an almost invariant probability density on `G ⧸ H`, hence finite
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
    have h2 : (h₁ : G) = h₂ := mul_left_cancel hp
    exact Prod.ext rfl (Subtype.ext h2)
  have hc_mem (g : G) (q : G ⧸ H) : (s q)⁻¹ * (g * s (g⁻¹ • q)) ∈ H := by
    apply QuotientGroup.eq.mp
    rw [hs q, ← smul_eq_mul, MulAction.Quotient.mk_smul_out, smul_inv_smul]
  let c (g : G) (q : G ⧸ H) : H := ⟨(s q)⁻¹ * (g * s (g⁻¹ • q)), hc_mem g q⟩
  have hgφ (g : G) (q : G ⧸ H) (h : H) : g * φ (g⁻¹ • q, h) = φ (q, c g q * h) := by
    simp only [φ, c, Subgroup.coe_mul]
    group
  let K_H : Finset H := (K ×ˢ F₁).image fun p ↦ c p.1 p.2
  obtain ⟨F₂, hF₂_ne, hF₂⟩ := hasFoelnerSets_iff.mp hH K_H (ε / 4) (by positivity)
  let E : Finset G := (F₁ ×ˢ F₂).map ⟨φ, hφ_inj⟩
  have hE_ne : E.Nonempty := (hF₁_ne.product hF₂_ne).map
  have hE_card : #E = #F₁ * #F₂ := by simp [E]
  refine ⟨E, hE_ne, fun g hg ↦ ?_⟩
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
  classical
  let : TopologicalSpace G := ⊥
  have : DiscreteTopology G := ⟨rfl⟩
  have : IsTopologicalGroup G := {}
  have : Amenable G := .of_hasFoelnerSets hG
  obtain ⟨p, hp0, hp_fin, hp1, hp_lt⟩ := Amenable.exists_sum_tsum_abs_sub_lt K hε
  let S : Finset G := hp_fin.toFinset
  have hp_out (x : G) (hx : x ∉ S) : p x = 0 := by
    by_contra hne
    exact hx (hp_fin.mem_toFinset.mpr hne)
  let π : G → G ⧸ H := QuotientGroup.mk
  have hπ_smul (a b : G) : π (a * b) = a • π b :=
    (MulAction.Quotient.smul_mk H a b).symm
  let q : G ⧸ H → ℝ := fun y ↦ ∑ x ∈ S with π x = y, p x
  have hq0 (y : G ⧸ H) : 0 ≤ q y := sum_nonneg fun x _ ↦ hp0 x
  have hq_out (y : G ⧸ H) (hy : y ∉ S.image π) : q y = 0 :=
    sum_eq_zero fun x hx ↦
      absurd ((mem_filter.mp hx).2 ▸ mem_image_of_mem π (mem_filter.mp hx).1) hy
  have hq_fin : q.HasFiniteSupport := (S.image π).finite_toSet.subset fun y hy ↦ by
    by_contra hnot
    exact hy (hq_out y hnot)
  have hq1 : ∑' y, q y = 1 := by
    have hp_sum_eq : ∑' x, p x = ∑ x ∈ S, p x := tsum_eq_sum (s := S) hp_out
    rw [tsum_eq_sum (s := S.image π) hq_out]
    have hfib : (∑ y ∈ S.image π, ∑ x ∈ S with π x = y, p x) = ∑ x ∈ S, p x :=
      sum_fiberwise_of_maps_to (fun _ ↦ mem_image_of_mem π) _
    rw [hfib, ← hp_sum_eq, hp1]
  have hq_var (g : G) : ∑' y, |q (g⁻¹ • y) - q y| ≤ ∑' x, |p (g⁻¹ * x) - p x| := by
    let T : Finset G := S ∪ g • S
    have hS_sub : S ⊆ T := subset_union_left
    have hp_T (x : G) (hx : x ∉ T) : p (g⁻¹ * x) - p x = 0 := by
      have hx1 : x ∉ S := fun h ↦ hx (subset_union_left h)
      have hx2 : g⁻¹ * x ∉ S := fun h ↦ hx (subset_union_right
        (mem_smul_finset.mpr ⟨g⁻¹ * x, h, mul_inv_cancel_left g x⟩))
      simp [hp_out x hx1, hp_out (g⁻¹ * x) hx2]
    have hq_T (y : G ⧸ H) : q y = ∑ x ∈ T with π x = y, p x := by
      refine sum_subset (filter_subset_filter _ hS_sub) fun x hxT hxS ↦ ?_
      rw [mem_filter] at hxT hxS
      exact hp_out x fun hs ↦ hxS ⟨hs, hxT.2⟩
    have hq_T_inv (y : G ⧸ H) : q (g⁻¹ • y) = ∑ x ∈ T with π x = y, p (g⁻¹ * x) := by
      have hsub : S ⊆ g⁻¹ • T := fun z hz ↦ mem_smul_finset.mpr
        ⟨g * z, subset_union_right (mem_smul_finset.mpr ⟨z, hz, rfl⟩), inv_mul_cancel_left g z⟩
      have h1 : q (g⁻¹ • y) = ∑ z ∈ g⁻¹ • T with π z = g⁻¹ • y, p z := by
        refine sum_subset (filter_subset_filter _ hsub) fun z hzT hzS ↦ ?_
        rw [mem_filter] at hzT hzS
        exact hp_out z fun hs ↦ hzS ⟨hs, hzT.2⟩
      rw [h1]
      refine sum_bij (fun z _ ↦ g * z) (fun z hz ↦ ?_) (fun _ _ _ _ h ↦ mul_left_cancel h)
        (fun x hx ↦ ?_) (fun z _ ↦ by simp)
      · rw [mem_filter] at hz ⊢
        rcases mem_smul_finset.mp hz.1 with ⟨x, hx, rfl⟩
        refine ⟨by simpa using hx, ?_⟩
        rw [hπ_smul, hz.2, smul_inv_smul]
      · rw [mem_filter] at hx
        refine ⟨g⁻¹ * x, mem_filter.mpr ⟨mem_smul_finset.mpr ⟨x, hx.1, rfl⟩, ?_⟩,
          mul_inv_cancel_left g x⟩
        rw [hπ_smul, hx.2]
    have hdiff_out (y : G ⧸ H) (hy : y ∉ T.image π) : |q (g⁻¹ • y) - q y| = 0 := by
      rw [hq_T y, hq_T_inv y]
      have hemp : {x ∈ T | π x = y} = ∅ := filter_eq_empty_iff.mpr fun x hx hxy ↦
        hy (hxy ▸ mem_image_of_mem π hx)
      simp [hemp]
    rw [tsum_eq_sum (s := T.image π) hdiff_out,
      tsum_eq_sum (s := T) fun x hx ↦ by simp [hp_T x hx]]
    calc ∑ y ∈ T.image π, |q (g⁻¹ • y) - q y|
        = ∑ y ∈ T.image π, |∑ x ∈ T with π x = y, (p (g⁻¹ * x) - p x)| := by
          refine sum_congr rfl fun y _ ↦ ?_
          rw [hq_T y, hq_T_inv y, ← sum_sub_distrib]
      _ ≤ ∑ y ∈ T.image π, ∑ x ∈ T with π x = y, |p (g⁻¹ * x) - p x| :=
          sum_le_sum fun y _ ↦ abs_sum_le_sum_abs _ _
      _ = ∑ x ∈ T, |p (g⁻¹ * x) - p x| :=
          sum_fiberwise_of_maps_to (fun _ ↦ mem_image_of_mem π) _
  have hsum_q : ∑ g ∈ K, ∑' y, |q (g⁻¹ • y) - q y| < ε * ∑' y, q y := by
    rw [hq1, mul_one]
    exact (sum_le_sum fun g _ ↦ hq_var g).trans_lt hp_lt
  exact exists_finset_card_smul_symmDiff_lt_of_sum_tsum_lt hq0 hq_fin hsum_q

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
