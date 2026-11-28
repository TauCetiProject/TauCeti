/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti Contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

/-!
# Conjugation-Equivariant Root Choices on Group Cosets

Given a group homomorphism `π : E →* Γ` and an element `σ : Γ`, a *coset root choice*
(`TauCeti.CosetRootChoice`) consists of an injective homomorphism `j : G →* E` and a map
`r : G → E` landing in the coset `π ⁻¹' {σ}` such that `r γ ^ orderOf σ = j γ`, `r` is
conjugation-equivariant for `G`, and any element of `ker π` conjugating `r δ` to `r γ` lies in
`j.range`.

We prove that `j` lands in `ker π`, that for finite `G` and `E` every element of `π ⁻¹' {σ}` is
`ker π`-conjugate to some `r γ`, and that the cardinality of the set of `ker π`-conjugators
between two elements is invariant under simultaneous conjugation by elements with equal `π`-image.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), `src/Lib/LocalGL/Shintani/CosetRootChoice.lean`
(`New.IsRootChoice`, `New.IsRootChoice.apply_emb_eq_one`,
`New.IsRootChoice.exists_conj_eq_of_map_eq`, and `New.conjCount_conj`).
-/

@[expose] public section

namespace TauCeti

/-- A conjugation-equivariant choice of `orderOf σ`-th roots over the coset `π ⁻¹' {σ}`: `j` is
injective, `r γ` lies over `σ` with `r γ ^ orderOf σ = j γ`, `r` intertwines conjugation by `G`,
and any element of `ker π` conjugating `r δ` to `r γ` lies in the range of `j`. -/
structure CosetRootChoice {G E Γ : Type*} [Group G] [Group E] [Group Γ]
    (π : E →* Γ) (σ : Γ) (j : G →* E) (r : G → E) : Prop where
  /-- The homomorphism `j` is injective. -/
  injective : Function.Injective j
  /-- Every `r γ` lies in the fiber over `σ`. -/
  map_apply (γ : G) : π (r γ) = σ
  /-- Raising `r γ` to `orderOf σ` recovers `j γ`. -/
  pow_orderOf (γ : G) : r γ ^ orderOf σ = j γ
  /-- The root map `r` is equivariant for conjugation by `G`. -/
  map_conj (v γ : G) : r (v * γ * v⁻¹) = j v * r γ * (j v)⁻¹
  /-- Any element of `ker π` conjugating one chosen root to another lies in `j.range`. -/
  mem_range_of_conj (x : E) (γ δ : G) : π x = 1 → x * r δ * x⁻¹ = r γ → x ∈ j.range

/-- For a coset root choice `R`, the embedding `j` lands in the kernel of `π`. -/
theorem CosetRootChoice.map_emb_eq_one {G E Γ : Type*} [Group G] [Group E] [Group Γ]
    {π : E →* Γ} {σ : Γ} {j : G →* E} {r : G → E} (R : CosetRootChoice π σ j r) (γ : G) :
    π (j γ) = 1 := by
  rw [← R.pow_orderOf γ, map_pow, R.map_apply, pow_orderOf_eq_one]

/-- For a coset root choice `R` between finite groups, every element `s : E` in the fiber over `σ`
is conjugate to some `r γ` by an element of `ker π`. -/
theorem CosetRootChoice.exists_conj_eq_of_map_eq {G E Γ : Type*} [Group G] [Group E] [Group Γ]
    [Finite E] [Finite G] {π : E →* Γ} {σ : Γ} {j : G →* E} {r : G → E}
    (R : CosetRootChoice π σ j r) {s : E} (hs : π s = σ) :
    ∃ (x : E) (γ : G), π x = 1 ∧ x * r γ * x⁻¹ = s := by
  let H : Subgroup π.ker := (j.codRestrict π.ker R.map_emb_eq_one).range
  let f : (π.ker ⧸ H) × G → π ⁻¹' {σ} := fun z ↦
    ⟨(z.fst.out : E) * r z.snd * (z.fst.out : E)⁻¹, by
      simp [π.mem_ker.mp z.fst.out.property, R.map_apply]⟩
  have h_inj : Function.Injective f := by
    rintro ⟨y, δ⟩ ⟨x, γ⟩ hc
    have h_val : (f (x, γ) : E) = f (y, δ) := congrArg Subtype.val hc.symm
    have h_conj : (y.out⁻¹ * x.out : π.ker) * r γ * ((y.out⁻¹ * x.out : π.ker) : E)⁻¹ = r δ := by
      simpa [f, mul_assoc] using congrArg (fun t : E ↦ (y.out : E)⁻¹ * t * y.out) h_val
    obtain ⟨a, ha⟩ : ∃ a : G, j a = (y.out⁻¹ * x.out : π.ker) :=
      R.mem_range_of_conj _ δ γ (π.mem_ker.mp (y.out⁻¹ * x.out).property) h_conj
    have h_coset : y.out⁻¹ * x.out ∈ H := ⟨a, Subtype.ext ha⟩
    obtain rfl : y = x := y.out_equiv_out.mp (QuotientGroup.leftRel_apply.mpr h_coset)
    have h_root : r δ = r γ := by simpa [f] using hc
    have h_j : j δ = j γ := by rw [← R.pow_orderOf δ, ← R.pow_orderOf γ, h_root]
    rw [R.injective h_j]
  have h_fiber : Nat.card (π ⁻¹' {σ}) = Nat.card π.ker := by
    rw [← R.map_apply 1]
    exact Nat.card_congr (π.fiberEquivKer _)
  have h_card_le : Nat.card (π ⁻¹' {σ}) ≤ Nat.card ((π.ker ⧸ H) × G) := by
    rw [h_fiber, ← H.index_mul_card, Nat.card_prod]
    exact mul_le_mul_right (Finite.card_range_le _) _
  obtain ⟨⟨x, γ⟩, hc⟩ := (h_inj.bijective_of_nat_card_le h_card_le).surjective ⟨s, hs⟩
  exact ⟨x.out, γ, π.mem_ker.mp x.out.property, congrArg Subtype.val hc⟩

/-- Conjugating `s` by `y` and `t` by `u`, where `π u = π y`, preserves the cardinality of the
set of elements in `ker π` conjugating `t` to `s`. -/
theorem natCard_ker_conj_eq_of_map_eq {E Γ : Type*} [Group E] [Group Γ] (π : E →* Γ)
    {u y : E} (h_eq : π u = π y) (s t : E) :
    Nat.card {x : E // π x = 1 ∧ x * (u * t * u⁻¹) * x⁻¹ = y * s * y⁻¹} =
      Nat.card {x : E // π x = 1 ∧ x * t * x⁻¹ = s} := by
  refine (Nat.card_congr <| Equiv.subtypeEquiv ((Equiv.mulRight u⁻¹).trans (Equiv.mulLeft y))
    fun x ↦ ?_).symm
  have h_ker : π (y * (x * u⁻¹)) = 1 ↔ π x = 1 := by simp [h_eq, ← mul_assoc]
  have h_conj : y * (x * u⁻¹) * (u * t * u⁻¹) * (y * (x * u⁻¹))⁻¹ = y * s * y⁻¹ ↔
      x * t * x⁻¹ = s := by
    rw [show y * (x * u⁻¹) * (u * t * u⁻¹) * (y * (x * u⁻¹))⁻¹ = y * (x * t * x⁻¹) * y⁻¹ by group,
      mul_left_inj, mul_right_inj]
  simp only [Equiv.trans_apply, Equiv.coe_mulLeft, Equiv.coe_mulRight, h_ker, h_conj]

end TauCeti
