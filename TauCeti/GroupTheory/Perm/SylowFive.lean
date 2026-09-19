/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.Recognition
public import TauCeti.GroupTheory.Sylow

/-!
# Sylow `5`-subgroups of `S₅` and the orders of its transitive subgroups

Let `α` be a type with five elements, so that `Equiv.Perm α` is the symmetric group `S₅` of
order `120`. Its Sylow `5`-subgroups have order `5`; there are six of them, and each has a
normalizer of order `20`.

The main result is a dichotomy for a subgroup `G` of `S₅` whose order is divisible by `5`:
either `G` lies between a Sylow `5`-subgroup `P` of `S₅` and its normalizer, or `G` contains
the alternating group. The two cases are distinguished by whether `G` has one or six Sylow
`5`-subgroups.

Applied to a transitive subgroup, whose order is divisible by `5`, this shows that the order of a
transitive subgroup of `S₅` is one of `5`, `10`, `20`, `60`, `120`. This is the first half of the
classification of the transitive subgroups of `S₅`: the transitive subgroups of order `60` and
`120` are `A₅` and `S₅`, and those of order dividing `20` sit inside the normalizer of a Sylow
`5`-subgroup.

## Main results

* `TauCeti.card_sylow_five_perm`: `S₅` has six Sylow `5`-subgroups.
* `TauCeti.card_normalizer_sylow_five_perm`: each has a normalizer of order `20`.
* `TauCeti.card_sylow_five_eq_one_or_six`: a subgroup of `S₅` of order divisible by `5` has one
  or six Sylow `5`-subgroups.
* `TauCeti.exists_sylow_le_le_normalizer_of_card_sylow_five_eq_one`: if it has one, it lies
  between a Sylow `5`-subgroup of `S₅` and its normalizer.
* `TauCeti.thirty_dvd_natCard_of_card_sylow_five_eq_six`: if it has six, its order is divisible
  by `30`.
* `TauCeti.natCard_ne_thirty`: `S₅` has no subgroup of order `30`.
* `TauCeti.eq_alternatingGroup_or_eq_top_of_thirty_dvd_natCard`: a subgroup of `S₅` of order
  divisible by `30` is `A₅` or `S₅`.
* `TauCeti.exists_sylow_le_le_normalizer_or_alternatingGroup_le`: a subgroup of `S₅` of order
  divisible by `5` lies between a Sylow `5`-subgroup and its normalizer, or contains `A₅`.
* `TauCeti.natCard_mem_of_five_dvd_natCard`: a subgroup of `S₅` of order divisible by `5` has
  order `5`, `10`, `20`, `60` or `120`.
* `TauCeti.natCard_mem_of_natCard_eq_five_of_isPretransitive`: in particular so does a transitive
  subgroup of `S₅`.

## References

* J. D. Dixon and B. Mortimer, *Permutation Groups*, GTM 163, Springer, 1996, §2 and §5.2.
-/

public section

open Equiv Subgroup

namespace TauCeti

variable {α : Type*}

local instance sylowFiveFactPrimeFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private theorem natCard_perm_eq_120 [Finite α] (hα : Nat.card α = 5) : Nat.card (Perm α) = 120 := by
  rw [Nat.card_perm, hα]
  rfl

/-- The symmetric group on five points has exactly six Sylow `5`-subgroups. -/
@[simp]
theorem card_sylow_five_perm [Finite α] (hα : Nat.card α = 5) :
    Nat.card (Sylow 5 (Perm α)) = 6 := by
  classical
  have := Fintype.ofFinite α
  have h120 := natCard_perm_eq_120 hα
  obtain ⟨P⟩ : Nonempty (Sylow 5 (Perm α)) := inferInstance
  have hP : Nat.card P = 5 :=
    P.card_eq_of_dvd_of_not_sq_dvd (by rw [h120]; norm_num) (by rw [h120]; norm_num)
  have hindex : P.index = 24 := by
    have := P.1.index_mul_card
    rw [hP, h120] at this
    omega
  have hdvd : Nat.card (Sylow 5 (Perm α)) ∣ 24 := hindex ▸ P.card_dvd_index
  have hmod := card_sylow_modEq_one 5 (Perm α)
  have hne : Nat.card (Sylow 5 (Perm α)) ≠ 1 := by
    intro h1
    have : Subsingleton (Sylow 5 (Perm α)) := (Nat.card_eq_one_iff_unique.mp h1).1
    have := P.normal_of_subsingleton
    have hnt : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    have hle := card_le_of_le (Perm.alternatingGroup_le_of_normal (by omega) hnt)
    rw [nat_card_alternatingGroup, hα, hP] at hle
    norm_num [Nat.factorial] at hle
  generalize Nat.card (Sylow 5 (Perm α)) = n at hdvd hmod hne ⊢
  have hle : n ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
  unfold Nat.ModEq at hmod
  interval_cases n <;> omega

/-- The normalizer of a Sylow `5`-subgroup of the symmetric group on five points has order
`20`. -/
@[simp]
theorem card_normalizer_sylow_five_perm [Finite α] (hα : Nat.card α = 5) (P : Sylow 5 (Perm α)) :
    Nat.card (normalizer (P : Set (Perm α))) = 20 := by
  have h := (normalizer (P : Set (Perm α))).index_mul_card
  rw [← P.card_eq_index_normalizer, card_sylow_five_perm hα, natCard_perm_eq_120 hα] at h
  omega

/-- A subgroup of the symmetric group on five points whose order is divisible by `5` has one or
six Sylow `5`-subgroups. -/
theorem card_sylow_five_eq_one_or_six [Finite α] (hα : Nat.card α = 5)
    (G : Subgroup (Perm α)) (h5 : 5 ∣ Nat.card G) :
    Nat.card (Sylow 5 G) = 1 ∨ Nat.card (Sylow 5 G) = 6 := by
  have hG : Nat.card G ∣ 120 := natCard_perm_eq_120 hα ▸ G.card_subgroup_dvd_card
  obtain ⟨Q⟩ : Nonempty (Sylow 5 G) := inferInstance
  have hQ : Nat.card Q = 5 := Q.card_eq_of_dvd_of_not_sq_dvd h5 fun h => by
    have := h.trans hG
    norm_num at this
  have hQi : Q.index * 5 = Nat.card G := by
    rw [← (Q : Subgroup G).index_mul_card, hQ]
  have hQ24 : Q.index ∣ 24 :=
    Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 5) (by rw [hQi]; exact hG)
  have hdvd := Q.card_dvd_index.trans hQ24
  have hmod := card_sylow_modEq_one 5 G
  generalize Nat.card (Sylow 5 G) = n at hmod hdvd ⊢
  have hle : n ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
  unfold Nat.ModEq at hmod
  interval_cases n <;> omega

/-- A subgroup `G` of the symmetric group on five points whose order is divisible by `5` and which
has a unique Sylow `5`-subgroup lies between a Sylow `5`-subgroup of the symmetric group and its
normalizer. -/
theorem exists_sylow_le_le_normalizer_of_card_sylow_five_eq_one [Finite α] (hα : Nat.card α = 5)
    (G : Subgroup (Perm α)) (h5 : 5 ∣ Nat.card G) (h1 : Nat.card (Sylow 5 G) = 1) :
    ∃ P : Sylow 5 (Perm α), (P : Subgroup (Perm α)) ≤ G ∧ G ≤ normalizer (P : Set (Perm α)) := by
  have h120 := natCard_perm_eq_120 hα
  have hG : Nat.card G ∣ 120 := h120 ▸ G.card_subgroup_dvd_card
  obtain ⟨Q⟩ : Nonempty (Sylow 5 G) := inferInstance
  have hQ : Nat.card Q = 5 := Q.card_eq_of_dvd_of_not_sq_dvd h5 fun h => by
    have := h.trans hG
    norm_num at this
  have : Subsingleton (Sylow 5 G) := (Nat.card_eq_one_iff_unique.mp h1).1
  have := Q.normal_of_subsingleton
  obtain ⟨P, hP⟩ := (Q.isPGroup'.map G.subtype).exists_le_sylow
  have hPQ : (Q : Subgroup G).map G.subtype = P := by
    refine eq_of_le_of_card_ge hP ?_
    rw [card_map_of_injective G.subtype_injective, hQ,
      P.card_eq_of_dvd_of_not_sq_dvd (by rw [h120]; norm_num) (by rw [h120]; norm_num)]
  refine ⟨P, hPQ ▸ map_subtype_le _, ?_⟩
  have key : G ≤ normalizer ((Q : Subgroup G).map G.subtype : Set (Perm α)) :=
    calc G = (⊤ : Subgroup G).map G.subtype := by rw [← MonoidHom.range_eq_map, range_subtype]
      _ = (normalizer ((Q : Subgroup G) : Set G)).map G.subtype := by rw [normalizer_eq_top]
      _ ≤ _ := le_normalizer_map _
  rwa [hPQ] at key

/-- A subgroup of the symmetric group on five points whose order is divisible by `30` is the
alternating group or the whole symmetric group. -/
theorem eq_alternatingGroup_or_eq_top_of_thirty_dvd_natCard [Fintype α] [DecidableEq α]
    (hα : Nat.card α = 5) (G : Subgroup (Perm α)) (h30 : 30 ∣ Nat.card G) :
    G = alternatingGroup α ∨ G = ⊤ := by
  have h120 := natCard_perm_eq_120 hα
  have hGi := G.index_mul_card
  rw [h120] at hGi
  obtain ⟨k, hk⟩ := h30
  have h4 : G.index ∣ 4 := Dvd.intro k (by rw [hk] at hGi; linarith)
  have hle := Nat.le_of_dvd (by norm_num) h4
  have hA : alternatingGroup α ≤ G := alternatingGroup_le_of_index_lt (by omega) (by omega)
  have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hdvd := index_dvd_of_le hA
  rw [alternatingGroup.index_eq_two] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact Or.inr (index_eq_one.mp h)
  · refine Or.inl (eq_of_le_of_card_ge hA ?_).symm
    have hAi := (alternatingGroup α).index_mul_card
    rw [alternatingGroup.index_eq_two, h120] at hAi
    rw [h] at hGi
    omega

/-- The symmetric group on five points has no subgroup of order `30`. -/
theorem natCard_ne_thirty [Finite α] (hα : Nat.card α = 5) (G : Subgroup (Perm α)) :
    Nat.card G ≠ 30 := by
  classical
  have := Fintype.ofFinite α
  intro h
  have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  rcases eq_alternatingGroup_or_eq_top_of_thirty_dvd_natCard hα G (h ▸ dvd_rfl) with rfl | rfl
  · rw [nat_card_alternatingGroup, hα] at h
    norm_num [Nat.factorial] at h
  · rw [card_top, natCard_perm_eq_120 hα] at h
    norm_num at h

/-- A subgroup `G` of the symmetric group on five points whose order is divisible by `5` either
lies between a Sylow `5`-subgroup of the symmetric group and its normalizer, or contains the
alternating group. -/
theorem exists_sylow_le_le_normalizer_or_alternatingGroup_le [Fintype α] [DecidableEq α]
    (hα : Nat.card α = 5)
    (G : Subgroup (Perm α)) (h5 : 5 ∣ Nat.card G) :
    (∃ P : Sylow 5 (Perm α), (P : Subgroup (Perm α)) ≤ G ∧ G ≤ normalizer (P : Set (Perm α))) ∨
      alternatingGroup α ≤ G := by
  rcases card_sylow_five_eq_one_or_six hα G h5 with h1 | h6
  · exact Or.inl (exists_sylow_le_le_normalizer_of_card_sylow_five_eq_one hα G h5 h1)
  · right
    rcases eq_alternatingGroup_or_eq_top_of_thirty_dvd_natCard hα G
      (thirty_dvd_natCard_of_card_sylow_five_eq_six h5 h6) with rfl | rfl
    exacts [le_rfl, le_top]

/-- A subgroup of the symmetric group on five points whose order is divisible by `5` has order
`5`, `10`, `20`, `60` or `120`. -/
theorem natCard_mem_of_five_dvd_natCard [Finite α] (hα : Nat.card α = 5)
    (G : Subgroup (Perm α)) (h5 : 5 ∣ Nat.card G) :
    Nat.card G ∈ ({5, 10, 20, 60, 120} : Finset ℕ) := by
  classical
  have := Fintype.ofFinite α
  have hG : Nat.card G ∣ 120 := natCard_perm_eq_120 hα ▸ G.card_subgroup_dvd_card
  rcases exists_sylow_le_le_normalizer_or_alternatingGroup_le hα G h5 with ⟨P, -, hle⟩ | hA
  · have h20 := card_dvd_of_le hle
    rw [card_normalizer_sylow_five_perm hα] at h20
    generalize Nat.card G = g at h5 h20 ⊢
    have : g ≤ 20 := Nat.le_of_dvd (by norm_num) h20
    interval_cases g <;> first | decide | omega
  · have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    have h60 := card_dvd_of_le hA
    rw [nat_card_alternatingGroup, hα] at h60
    replace h60 : 60 ∣ Nat.card G := by simpa [Nat.factorial] using h60
    generalize Nat.card G = g at hG h60 ⊢
    obtain ⟨k, rfl⟩ := h60
    have : k ≤ 2 := by have := Nat.le_of_dvd (by norm_num) hG; omega
    interval_cases k <;> first | decide | omega

/-- A transitive subgroup of the symmetric group on five points has order `5`, `10`, `20`,
`60` or `120`. -/
theorem natCard_mem_of_natCard_eq_five_of_isPretransitive [Finite α] (hα : Nat.card α = 5)
    (G : Subgroup (Perm α)) [MulAction.IsPretransitive G α] :
    Nat.card G ∈ ({5, 10, 20, 60, 120} : Finset ℕ) := by
  have : Nonempty α := (Nat.card_pos_iff.mp (by omega)).1
  exact natCard_mem_of_five_dvd_natCard hα G (hα ▸ natCard_dvd_natCard_of_isPretransitive G)

end TauCeti
