/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

/-!
# Point stabilizers, Sylow `3`-subgroups, and complements of `kleinFour` in degree four

Let `α` be a finite type with `Nat.card α = 4`. The Klein four-subgroup
`alternatingGroup.kleinFour α` of `alternatingGroup α` consists of `1` together with the three
double transpositions of cycle type `{2, 2}`. Because every double transposition has support of
cardinality `4`, no nonidentity element of `kleinFour α` has a fixed point on `α`. Since
`Nat.card (kleinFour α) = 4 = Nat.card α`, orbit evaluation `v ↦ v • a` at any basepoint `a : α`
is an equivalence `kleinFour α ≃ α` (`alternatingGroup.kleinFourOrbitEquiv`); in particular,
`kleinFour α` acts freely and transitively on `α`.

Consequently, for each `a : α`, the point stabilizer `MulAction.stabilizer (alternatingGroup α) a`
is a complement of `kleinFour α` in `alternatingGroup α` of cardinality `3`. Conversely, every
subgroup of `alternatingGroup α` of cardinality `3` is a `3`-group acting on the `4`-element type
`α`, hence fixes a point by `IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card` and coincides
with that point's stabilizer. Distinct points have distinct stabilizers because an even permutation
fixing two distinct points of a `4`-element set has support of cardinality at most `2` and cannot
be a transposition. This identifies the four elements of `α`, the four point stabilizers, the four
Sylow `3`-subgroups of `alternatingGroup α`, and the four complements of `kleinFour α`.

Finally, conjugating the point stabilizer of `a` by `g` yields the point stabilizer of `g • a`, so
each point stabilizer is self-normalizing in `alternatingGroup α` and its image in `Equiv.Perm α`
has normalizer equal to `MulAction.stabilizer (Equiv.Perm α) a`.

## Main definitions

* `alternatingGroup.kleinFourOrbitEquiv`: the equivalence `kleinFour α ≃ α` sending `v` to `v • a`.
* `alternatingGroup.stabilizerThreeSylow`: the point stabilizer of `a : α` packaged as a
  `Sylow 3 (alternatingGroup α)`.
* `alternatingGroup.stabilizerThreeSylowEquiv`: the bijection `α ≃ Sylow 3 (alternatingGroup α)`.
* `alternatingGroup.kleinFourComplementEquiv`: the bijection
  `α ≃ {D : Subgroup (alternatingGroup α) // (kleinFour α).IsComplement' D}`.

## Main results

* `alternatingGroup.smul_eq_self_iff_of_mem_kleinFour`: an element of `kleinFour α` fixes a point
  if and only if it is `1`.
* `alternatingGroup.isPretransitive_kleinFour`, `alternatingGroup.smul_left_injective_kleinFour`:
  `kleinFour α` acts transitively and freely on `α`.
* `alternatingGroup.isComplement'_kleinFour_stabilizer`: every point stabilizer complements
  `kleinFour α` in `alternatingGroup α`.
* `alternatingGroup.isComplement'_kleinFour_iff_exists_stabilizer`: the complements of
  `kleinFour α` are precisely the point stabilizers `MulAction.stabilizer (alternatingGroup α) a`.
* `alternatingGroup.normalizer_map_subtype_stabilizer_of_card_eq_four`: in `Equiv.Perm α`, the
  normalizer of `(MulAction.stabilizer (alternatingGroup α) a).map (alternatingGroup α).subtype` is
  `MulAction.stabilizer (Equiv.Perm α) a`.
-/

public section

open scoped Pointwise

namespace alternatingGroup

open Equiv Equiv.Perm

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ### Unconditional normality and regular action of `kleinFour α` -/

/-- `kleinFour α` is normal in `alternatingGroup α` for every finite type `α` (without any
cardinality assumption), since conjugation preserves cycle type `{2, 2}`. -/
instance instNormalKleinFour : (kleinFour α).Normal where
  conj_mem n hn g := by
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      apply Subgroup.subset_closure
      simp only [Set.mem_ofPred_eq] at hx ⊢
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, cycleType_conj, hx]
    | one => simp
    | mul _ _ _ _ ih₁ ih₂ =>
      convert mul_mem ih₁ ih₂ using 1
      group
    | inv _ _ ih =>
      convert inv_mem ih using 1
      group

/-- Viewed in `Equiv.Perm α`, `kleinFour α` is normal in the full symmetric group for every finite
type `α`, since conjugation by any permutation preserves evenness and cycle type `{2, 2}`. -/
instance instNormalMapSubtypeKleinFour :
    ((kleinFour α).map (alternatingGroup α).subtype).Normal where
  conj_mem n hn σ := by
    rw [kleinFour, MonoidHom.map_closure] at hn ⊢
    induction hn using Subgroup.closure_induction with
    | mem _ hx =>
      rcases hx with ⟨x, hx, rfl⟩
      apply Subgroup.subset_closure
      refine ⟨⟨σ * (x : Perm α) * σ⁻¹, alternatingGroup.normal.conj_mem _ x.property σ⟩, ?_, rfl⟩
      simp only [Set.mem_ofPred_eq] at hx ⊢
      exact cycleType_conj.trans hx
    | one => simp
    | mul _ _ _ _ ih₁ ih₂ =>
      convert mul_mem ih₁ ih₂ using 1
      group
    | inv _ _ ih =>
      convert inv_mem ih using 1
      group

/-- When `Nat.card α = 4`, an element of `kleinFour α` fixes a point of `α` if and only if it is
the identity: every nonidentity element has cycle type `{2, 2}` and hence full support. -/
theorem smul_eq_self_iff_of_mem_kleinFour (hα4 : Nat.card α = 4) {g : alternatingGroup α}
    (hg : g ∈ kleinFour α) (a : α) : g • a = a ↔ g = 1 := by
  refine ⟨fun ha => ?_, fun h => by rw [h, one_smul]⟩
  rw [← SetLike.mem_coe, coe_kleinFour_of_card_eq_four hα4] at hg
  rcases hg with rfl | hct
  · rfl
  · exfalso
    have hcard : Fintype.card α = 4 := Nat.card_eq_fintype_card.symm.trans hα4
    have hsum : (g : Perm α).support.card = Fintype.card α := by
      rw [← sum_cycleType, hct, hcard]
      decide
    have huniv : (g : Perm α).support = Finset.univ := Finset.eq_univ_of_card _ hsum
    exact (mem_support.mp (huniv ▸ Finset.mem_univ a)) ha

/-- Every point stabilizer for the action of `kleinFour α` on a `4`-element type is trivial. -/
theorem stabilizer_kleinFour_eq_bot (hα4 : Nat.card α = 4) (a : α) :
    MulAction.stabilizer (kleinFour α) a = ⊥ := by
  ext v
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_bot, Subtype.ext_iff]
  exact smul_eq_self_iff_of_mem_kleinFour hα4 v.property a

/-- Orbit evaluation `v ↦ v • a` from `kleinFour α` to a `4`-element type `α` is injective. -/
theorem smul_left_injective_kleinFour (hα4 : Nat.card α = 4) (a : α) :
    Function.Injective (fun v : kleinFour α => v • a) := by
  intro v₁ v₂ (h : v₁ • a = v₂ • a)
  have hfix : ((v₁⁻¹ * v₂ : kleinFour α) : alternatingGroup α) • a = a := by
    rw [Subgroup.coe_mul, mul_smul, ← Subgroup.smul_def, ← Subgroup.smul_def, ← h, inv_smul_smul]
  have hone : ((v₁⁻¹ * v₂ : kleinFour α) : alternatingGroup α) = 1 :=
    (smul_eq_self_iff_of_mem_kleinFour hα4 (v₁⁻¹ * v₂).property a).mp hfix
  exact inv_mul_eq_one.mp (Subtype.ext hone)

/-- Orbit evaluation `v ↦ v • a` from `kleinFour α` to a `4`-element type `α` is bijective. -/
theorem bijective_kleinFour_smul (hα4 : Nat.card α = 4) (a : α) :
    Function.Bijective (fun v : kleinFour α => v • a) := by
  let _ := Fintype.ofFinite (kleinFour α)
  refine (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨smul_left_injective_kleinFour hα4 a, ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    kleinFour_card_of_card_eq_four hα4, hα4]

/-- For `Nat.card α = 4` and a basepoint `a : α`, orbit evaluation `v ↦ v • a` identifies
`kleinFour α` with `α`. -/
noncomputable def kleinFourOrbitEquiv (hα4 : Nat.card α = 4) (a : α) : kleinFour α ≃ α :=
  Equiv.ofBijective (fun v => v • a) (bijective_kleinFour_smul hα4 a)

@[simp]
theorem kleinFourOrbitEquiv_apply (hα4 : Nat.card α = 4) (a : α) (v : kleinFour α) :
    kleinFourOrbitEquiv hα4 a v = v • a := (rfl)

theorem kleinFourOrbitEquiv_one (hα4 : Nat.card α = 4) (a : α) :
    kleinFourOrbitEquiv hα4 a 1 = a := by
  rw [kleinFourOrbitEquiv_apply, one_smul]

@[simp]
theorem kleinFourOrbitEquiv_symm_self (hα4 : Nat.card α = 4) (a : α) :
    (kleinFourOrbitEquiv hα4 a).symm a = 1 :=
  (kleinFourOrbitEquiv hα4 a).symm_apply_eq.mpr (kleinFourOrbitEquiv_one hα4 a).symm

@[simp]
theorem kleinFourOrbitEquiv_symm_smul (hα4 : Nat.card α = 4) (a b : α) :
    (kleinFourOrbitEquiv hα4 a).symm b • a = b :=
  (kleinFourOrbitEquiv hα4 a).apply_symm_apply b

theorem kleinFourOrbitEquiv_symm_eq_iff (hα4 : Nat.card α = 4) (a b : α) (v : kleinFour α) :
    (kleinFourOrbitEquiv hα4 a).symm b = v ↔ v • a = b :=
  (kleinFourOrbitEquiv hα4 a).symm_apply_eq.trans eq_comm

/-- The action of `kleinFour α` on a `4`-element type is transitive. -/
theorem isPretransitive_kleinFour (hα4 : Nat.card α = 4) :
    MulAction.IsPretransitive (kleinFour α) α where
  exists_smul_eq x y := ⟨(kleinFourOrbitEquiv hα4 x).symm y, kleinFourOrbitEquiv_symm_smul hα4 x y⟩

/-- For any two points `a, b : α` of a `4`-element type, there is a unique `v : kleinFour α`
sending `a` to `b`. -/
theorem existsUnique_kleinFour_smul_eq (hα4 : Nat.card α = 4) (a b : α) :
    ∃! v : kleinFour α, v • a = b :=
  (kleinFourOrbitEquiv hα4 a).bijective.existsUnique b

/-! ### Point stabilizers, Sylow `3`-subgroups, and complements of `kleinFour α` -/

/-- `kleinFour α` meets every point stabilizer trivially when `Nat.card α = 4`. -/
theorem kleinFour_inf_stabilizer_eq_bot (hα4 : Nat.card α = 4) (a : α) :
    kleinFour α ⊓ MulAction.stabilizer (alternatingGroup α) a = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgK, hgS⟩
  exact Subgroup.mem_bot.mpr ((smul_eq_self_iff_of_mem_kleinFour hα4 hgK a).mp hgS)

/-- Every point stabilizer of `alternatingGroup α` is a complement of `kleinFour α` when
`Nat.card α = 4`. -/
theorem isComplement'_kleinFour_stabilizer (hα4 : Nat.card α = 4) (a : α) :
    (kleinFour α).IsComplement' (MulAction.stabilizer (alternatingGroup α) a) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    (disjoint_iff.mpr (kleinFour_inf_stabilizer_eq_bot hα4 a)) ?_
  rw [Set.eq_univ_iff_forall]
  intro g
  let v : kleinFour α := (kleinFourOrbitEquiv hα4 a).symm (g • a)
  refine ⟨v, v.property, (v : alternatingGroup α)⁻¹ * g, ?_, mul_inv_cancel_left _ _⟩
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]
  exact (kleinFourOrbitEquiv_symm_smul hα4 a (g • a)).symm

/-- Every point stabilizer of `alternatingGroup α` has cardinality `3` when `Nat.card α = 4`. -/
theorem card_stabilizer_of_card_eq_four (hα4 : Nat.card α = 4) (a : α) :
    Nat.card (MulAction.stabilizer (alternatingGroup α) a) = 3 := by
  have hmul : Nat.card (kleinFour α) * Nat.card (MulAction.stabilizer (alternatingGroup α) a) =
      Nat.card (alternatingGroup α) :=
    (Nat.card_prod _ _).symm.trans
      (Nat.card_congr (isComplement'_kleinFour_stabilizer hα4 a).equiv.symm)
  rw [kleinFour_card_of_card_eq_four hα4, card_of_card_eq_four hα4] at hmul
  omega

/-- An even permutation of a `4`-element type fixing two distinct points is the identity. -/
theorem eq_one_of_mem_stabilizer_of_mem_stabilizer (hα4 : Nat.card α = 4) {a b : α}
    (hab : a ≠ b) {g : alternatingGroup α}
    (ha : g ∈ MulAction.stabilizer (alternatingGroup α) a)
    (hb : g ∈ MulAction.stabilizer (alternatingGroup α) b) : g = 1 := by
  have hsub : (g : Perm α).support ⊆ ({a, b} : Finset α)ᶜ := by
    intro x hx
    rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl)
    · exact mem_support.mp hx ha
    · exact mem_support.mp hx hb
  have hcard : Fintype.card α = 4 := Nat.card_eq_fintype_card.symm.trans hα4
  have hle : (g : Perm α).support.card ≤ 2 := by
    refine (Finset.card_le_card hsub).trans ?_
    rw [Finset.card_compl, hcard, Finset.card_pair hab]
  have hne1 : (g : Perm α).support.card ≠ 1 := card_support_ne_one (g : Perm α)
  have hne2 : (g : Perm α).support.card ≠ 2 := by
    intro h2
    have hsign := (card_support_eq_two.mp h2).sign_eq
    have halt := mem_alternatingGroup.mp g.property
    rw [hsign] at halt
    exact absurd halt (by decide)
  have h0 : (g : Perm α).support.card = 0 := by omega
  exact Subtype.ext (support_eq_empty_iff.mp (Finset.card_eq_zero.mp h0))

/-- Distinct points of a `4`-element type have trivially intersecting stabilizers in
`alternatingGroup α`. -/
theorem stabilizer_inf_stabilizer_eq_bot (hα4 : Nat.card α = 4) {a b : α} (hab : a ≠ b) :
    MulAction.stabilizer (alternatingGroup α) a ⊓
      MulAction.stabilizer (alternatingGroup α) b = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨ha, hb⟩
  exact Subgroup.mem_bot.mpr (eq_one_of_mem_stabilizer_of_mem_stabilizer hα4 hab ha hb)

/-- Distinct points of a `4`-element type have distinct stabilizers in `alternatingGroup α`. -/
theorem stabilizer_injective_of_card_eq_four (hα4 : Nat.card α = 4) :
    Function.Injective (MulAction.stabilizer (alternatingGroup α) : α → _) := by
  intro a b h
  by_contra hab
  have hbot := stabilizer_inf_stabilizer_eq_bot hα4 hab
  rw [← h, inf_idem] at hbot
  have hcard := card_stabilizer_of_card_eq_four hα4 a
  rw [hbot, Subgroup.card_bot] at hcard
  omega

/-- Every subgroup of `alternatingGroup α` of cardinality `3` is the stabilizer of a point when
`Nat.card α = 4`. -/
theorem eq_stabilizer_of_card_eq_three (hα4 : Nat.card α = 4)
    {D : Subgroup (alternatingGroup α)} (hD : Nat.card D = 3) :
    ∃ a : α, D = MulAction.stabilizer (alternatingGroup α) a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 D := IsPGroup.of_card (n := 1) (by simpa using hD)
  obtain ⟨a, ha⟩ := hp.nonempty_fixed_point_of_prime_not_dvd_card α (by rw [hα4]; decide)
  refine ⟨a, Subgroup.eq_of_le_of_card_ge (fun g hg => ?_) ?_⟩
  · exact ha ⟨g, hg⟩
  · rw [hD, card_stabilizer_of_card_eq_four hα4 a]

/-- A subgroup of `alternatingGroup α` has cardinality `3` if and only if it is a point stabilizer
when `Nat.card α = 4`. -/
theorem card_eq_three_iff_exists_stabilizer (hα4 : Nat.card α = 4)
    (D : Subgroup (alternatingGroup α)) :
    Nat.card D = 3 ↔ ∃ a : α, D = MulAction.stabilizer (alternatingGroup α) a := by
  refine ⟨eq_stabilizer_of_card_eq_three hα4, ?_⟩
  rintro ⟨a, rfl⟩
  exact card_stabilizer_of_card_eq_four hα4 a

private theorem pow_three_factorization_twelve : 3 ^ (Nat.factorization 12) 3 = 3 := by
  have h12 : 12 = 2 ^ 2 * 3 := by decide
  rw [h12, Nat.factorization_mul_apply_of_coprime (by decide),
    Nat.factorization_eq_zero_of_not_dvd (by decide), Nat.prime_three.factorization_self]
  simp

/-- Every Sylow `3`-subgroup of `alternatingGroup α` has cardinality `3` when
`Nat.card α = 4`. -/
theorem card_three_sylow_of_card_eq_four (hα4 : Nat.card α = 4)
    (P : Sylow 3 (alternatingGroup α)) : Nat.card P = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Sylow.card_eq_multiplicity, card_of_card_eq_four hα4]
  exact pow_three_factorization_twelve

/-- The point stabilizer of `a : α` in `alternatingGroup α` packaged as a Sylow `3`-subgroup when
`Nat.card α = 4`. -/
noncomputable def stabilizerThreeSylow (hα4 : Nat.card α = 4) (a : α) :
    Sylow 3 (alternatingGroup α) :=
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  Sylow.ofCard (MulAction.stabilizer (alternatingGroup α) a)
    (by rw [card_stabilizer_of_card_eq_four hα4 a, card_of_card_eq_four hα4]
        exact pow_three_factorization_twelve.symm)

@[simp]
theorem coe_stabilizerThreeSylow (hα4 : Nat.card α = 4) (a : α) :
    (stabilizerThreeSylow hα4 a : Subgroup (alternatingGroup α)) =
      MulAction.stabilizer (alternatingGroup α) a := (rfl)

/-- For `Nat.card α = 4`, `a ↦ stabilizerThreeSylow hα4 a` is a bijection between `α` and the
Sylow `3`-subgroups of `alternatingGroup α`. -/
noncomputable def stabilizerThreeSylowEquiv (hα4 : Nat.card α = 4) :
    α ≃ Sylow 3 (alternatingGroup α) :=
  Equiv.ofBijective (stabilizerThreeSylow hα4)
    ⟨fun a b h => stabilizer_injective_of_card_eq_four hα4 (congrArg Sylow.toSubgroup h),
      fun P => by
        obtain ⟨a, ha⟩ := eq_stabilizer_of_card_eq_three hα4
          (card_three_sylow_of_card_eq_four hα4 P)
        exact ⟨a, Sylow.ext ha.symm⟩⟩

@[simp]
theorem stabilizerThreeSylowEquiv_apply (hα4 : Nat.card α = 4) (a : α) :
    stabilizerThreeSylowEquiv hα4 a = stabilizerThreeSylow hα4 a := (rfl)

/-- A subgroup of `alternatingGroup α` complements `kleinFour α` if and only if it has
cardinality `3`, when `Nat.card α = 4`. -/
theorem isComplement'_kleinFour_iff_card_eq_three (hα4 : Nat.card α = 4)
    (D : Subgroup (alternatingGroup α)) :
    (kleinFour α).IsComplement' D ↔ Nat.card D = 3 := by
  refine ⟨fun h => ?_, fun hD => ?_⟩
  · have hmul : Nat.card (kleinFour α) * Nat.card D = Nat.card (alternatingGroup α) :=
      (Nat.card_prod _ _).symm.trans (Nat.card_congr h.equiv.symm)
    rw [kleinFour_card_of_card_eq_four hα4, card_of_card_eq_four hα4] at hmul
    omega
  · obtain ⟨a, rfl⟩ := eq_stabilizer_of_card_eq_three hα4 hD
    exact isComplement'_kleinFour_stabilizer hα4 a

/-- A subgroup of `alternatingGroup α` complements `kleinFour α` if and only if it is the
point stabilizer of some `a : α`, when `Nat.card α = 4`. -/
theorem isComplement'_kleinFour_iff_exists_stabilizer (hα4 : Nat.card α = 4)
    (D : Subgroup (alternatingGroup α)) :
    (kleinFour α).IsComplement' D ↔
      ∃ a : α, D = MulAction.stabilizer (alternatingGroup α) a :=
  (isComplement'_kleinFour_iff_card_eq_three hα4 D).trans
    (card_eq_three_iff_exists_stabilizer hα4 D)

/-- A subgroup of `alternatingGroup α` complements `kleinFour α` if and only if it is a Sylow
`3`-subgroup of `alternatingGroup α`, when `Nat.card α = 4`. -/
theorem isComplement'_kleinFour_iff_exists_sylow (hα4 : Nat.card α = 4)
    (D : Subgroup (alternatingGroup α)) :
    (kleinFour α).IsComplement' D ↔ ∃ P : Sylow 3 (alternatingGroup α), D = P := by
  rw [isComplement'_kleinFour_iff_exists_stabilizer hα4]
  refine ⟨?_, ?_⟩
  · rintro ⟨a, rfl⟩
    exact ⟨stabilizerThreeSylow hα4 a, rfl⟩
  · rintro ⟨P, rfl⟩
    obtain ⟨a, rfl⟩ := (stabilizerThreeSylowEquiv hα4).surjective P
    exact ⟨a, rfl⟩

/-- Point stabilizers parameterize all complements of `kleinFour α` in `alternatingGroup α` when
`Nat.card α = 4`. -/
noncomputable def kleinFourComplementEquiv (hα4 : Nat.card α = 4) :
    α ≃ {D : Subgroup (alternatingGroup α) // (kleinFour α).IsComplement' D} :=
  Equiv.ofBijective
    (fun a => ⟨MulAction.stabilizer (alternatingGroup α) a,
      isComplement'_kleinFour_stabilizer hα4 a⟩)
    ⟨fun a b h => stabilizer_injective_of_card_eq_four hα4 (congrArg Subtype.val h),
      fun ⟨D, hD⟩ => by
        obtain ⟨a, rfl⟩ := (isComplement'_kleinFour_iff_exists_stabilizer hα4 D).mp hD
        exact ⟨a, rfl⟩⟩

@[simp]
theorem kleinFourComplementEquiv_apply_coe (hα4 : Nat.card α = 4) (a : α) :
    (kleinFourComplementEquiv hα4 a).val = MulAction.stabilizer (alternatingGroup α) a := (rfl)

/-- `kleinFour α` has exactly `4` complements in `alternatingGroup α` when `Nat.card α = 4`. -/
theorem card_isComplement'_kleinFour (hα4 : Nat.card α = 4) :
    Nat.card {D : Subgroup (alternatingGroup α) // (kleinFour α).IsComplement' D} = 4 :=
  (Nat.card_congr (kleinFourComplementEquiv hα4).symm).trans hα4

/-! ### Conjugation and normalizers of point stabilizers -/

/-- Conjugating a point stabilizer in `alternatingGroup α` shifts the basepoint. -/
theorem conj_smul_stabilizer (g : alternatingGroup α) (a : α) :
    MulAut.conj g • MulAction.stabilizer (alternatingGroup α) a =
      MulAction.stabilizer (alternatingGroup α) (g • a) := by
  ext x
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAction.mem_stabilizer_iff,
    MulAut.smul_def, MulAut.conj_inv_apply, mul_smul, inv_smul_eq_iff]

/-- Every point stabilizer of `alternatingGroup α` is self-normalizing when `Nat.card α = 4`. -/
theorem normalizer_stabilizer_of_card_eq_four (hα4 : Nat.card α = 4) (a : α) :
    Subgroup.normalizer (MulAction.stabilizer (alternatingGroup α) a) =
      MulAction.stabilizer (alternatingGroup α) a := by
  ext g
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe,
    ← MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    (stabilizer_injective_of_card_eq_four hα4).eq_iff, MulAction.mem_stabilizer_iff]

/-- Viewed in `Equiv.Perm α`, the point stabilizer of `a` in `alternatingGroup α` is the
intersection of `alternatingGroup α` with `MulAction.stabilizer (Equiv.Perm α) a`. -/
theorem map_subtype_stabilizer (a : α) :
    (MulAction.stabilizer (alternatingGroup α) a).map (alternatingGroup α).subtype =
      alternatingGroup α ⊓ MulAction.stabilizer (Perm α) a := by
  ext σ
  simp only [Subgroup.mem_map, MulAction.mem_stabilizer_iff, Subgroup.coe_subtype,
    Subgroup.mem_inf]
  exact ⟨fun ⟨g, hg, hσ⟩ => ⟨hσ ▸ g.property, hσ ▸ hg⟩, fun ⟨hσ, ha⟩ => ⟨⟨σ, hσ⟩, ha, rfl⟩⟩

/-- Conjugating the image of `MulAction.stabilizer (alternatingGroup α) a` in `Equiv.Perm α` by a
permutation `σ` shifts the basepoint to `σ a`. -/
theorem conj_smul_map_subtype_stabilizer (σ : Perm α) (a : α) :
    MulAut.conj σ •
        ((MulAction.stabilizer (alternatingGroup α) a).map (alternatingGroup α).subtype) =
      (MulAction.stabilizer (alternatingGroup α) (σ a)).map (alternatingGroup α).subtype := by
  rw [map_subtype_stabilizer, map_subtype_stabilizer, Subgroup.smul_inf,
    Subgroup.Normal.conj_smul_eq_self σ (alternatingGroup α)]
  congr 1
  ext τ
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAction.mem_stabilizer_iff,
    MulAut.smul_def, MulAut.conj_inv_apply, Perm.smul_def, Perm.mul_apply, Perm.inv_eq_iff_eq]

/-- In `Equiv.Perm α`, the normalizer of the image of `MulAction.stabilizer (alternatingGroup α) a`
is `MulAction.stabilizer (Equiv.Perm α) a` when `Nat.card α = 4`. -/
theorem normalizer_map_subtype_stabilizer_of_card_eq_four (hα4 : Nat.card α = 4) (a : α) :
    Subgroup.normalizer
      ((MulAction.stabilizer (alternatingGroup α) a).map (alternatingGroup α).subtype) =
      MulAction.stabilizer (Perm α) a := by
  ext σ
  have hsmul :
      ((MulAction.stabilizer (alternatingGroup α) a).map (alternatingGroup α).subtype).map
        (MulAut.conj σ : Perm α →* Perm α) =
      MulAut.conj σ •
        ((MulAction.stabilizer (alternatingGroup α) a).map (alternatingGroup α).subtype) := rfl
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, hsmul, conj_smul_map_subtype_stabilizer,
    (Subgroup.map_injective (alternatingGroup α).subtype_injective).eq_iff,
    (stabilizer_injective_of_card_eq_four hα4).eq_iff, MulAction.mem_stabilizer_iff]
  rfl

end alternatingGroup
