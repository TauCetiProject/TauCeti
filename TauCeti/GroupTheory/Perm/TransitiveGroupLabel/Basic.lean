/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAction.FinRotate
public import TauCeti.GroupTheory.Perm.PermCongr
public import TauCeti.GroupTheory.Solvable
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

/-!
# Reference transitive permutation groups in degree at most five

This file defines the reference permutation groups underlying the standard `nTj` labels in
degrees at most five. A label records the ambient conjugacy class of a subgroup of the
symmetric group; it does not attach an abstract group name or classify arbitrary subgroups.

The chosen generators are the zero-based translations of the representatives in the LMFDB
transitive-groups table. The reference family is empty outside degrees one through five.

## Main definitions

* `numTransitiveGroups`: the number of reference groups in each supported degree.
* `TransitiveGroupIndex`: the type of valid zero-based label indices.
* `referenceSubgroup`: the subgroup represented by a valid index.
* `TransitiveGroupLabel`: conjugacy to a reference subgroup.

## Main results

* `TauCeti.isPretransitive_referenceSubgroup`: every reference subgroup is transitive.
* `Subgroup.transitiveGroupLabel_map_permCongrHom_iff`: the label of a permutation group on an
  arbitrary set of `n` points does not depend on the numbering by `Fin n` used to read it.
* `TauCeti.TransitiveGroupLabel.natCard_eq`, `TauCeti.TransitiveGroupLabel.le_alternatingGroup_iff`,
  `TauCeti.TransitiveGroupLabel.isPreprimitive_iff`, `TauCeti.TransitiveGroupLabel.isSolvable_iff`:
  a labelled subgroup has the order, parity, primitivity, and solvability of its reference.
* `TauCeti.transitiveGroupLabel_one`, `TauCeti.transitiveGroupLabel_two_iff`: in degrees one and
  two, a subgroup carries the unique label exactly when it is transitive.

## References

* LMFDB, *Transitive groups*, entries of degrees at most five.
* G. Butler and J. McKay, *The transitive groups of degree up to eleven*.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm MulAction

/-- The number of reference transitive permutation groups in a supported degree.

The supported values are `1, 1, 2, 5, 5` in degrees one through five, and zero in every other
degree. -/
def numTransitiveGroups : ℕ → ℕ
  | 1 | 2 => 1
  | 3 => 2
  | 4 | 5 => 5
  | _ => 0

@[simp] theorem numTransitiveGroups_zero : numTransitiveGroups 0 = 0 := by
  simp [numTransitiveGroups]

@[simp] theorem numTransitiveGroups_one : numTransitiveGroups 1 = 1 := by
  simp [numTransitiveGroups]

@[simp] theorem numTransitiveGroups_two : numTransitiveGroups 2 = 1 := by
  simp [numTransitiveGroups]

@[simp] theorem numTransitiveGroups_three : numTransitiveGroups 3 = 2 := by
  simp [numTransitiveGroups]

/-- There are five reference groups in degree four. -/
@[simp]
theorem numTransitiveGroups_four : numTransitiveGroups 4 = 5 :=
  (rfl)

@[simp] theorem numTransitiveGroups_five : numTransitiveGroups 5 = 5 := by
  simp [numTransitiveGroups]

/-- There are no reference groups in degree greater than five. -/
theorem numTransitiveGroups_eq_zero_of_five_lt {n : ℕ} (hn : 5 < n) :
    numTransitiveGroups n = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  simp [numTransitiveGroups]

/-- A zero-based index for a transitive-group label in degree `n`.

An index `j` is displayed externally as `nT(j + 1)`. -/
abbrev TransitiveGroupIndex (n : ℕ) := Fin (numTransitiveGroups n)

/-- There are no labels in degree zero, so a label index has a positive degree. -/
theorem pos_of_transitiveGroupIndex {n : ℕ} (j : TransitiveGroupIndex n) : 0 < n :=
  Nat.pos_of_ne_zero fun hn => by
    subst hn
    exact j.elim0

private def doubleSwap5 : Perm (Fin 5) :=
  swap 0 3 * swap 1 2

private def frobeniusComplement5 : Perm (Fin 5) :=
  [0, 1, 3, 2].formPerm

private def referenceSubgroup3 : Fin 2 → Subgroup (Perm (Fin 3))
  | 0 => Subgroup.closure {finRotate 3}
  | 1 => ⊤

private def referenceSubgroup4 : Fin 5 → Subgroup (Perm (Fin 4))
  | 0 => Subgroup.closure {finRotate 4}
  | 1 => (alternatingGroup.kleinFour (Fin 4)).map (alternatingGroup (Fin 4)).subtype
  | 2 => Subgroup.closure {finRotate 4, swap 0 2}
  | 3 => alternatingGroup (Fin 4)
  | 4 => ⊤

private def referenceSubgroup5 : Fin 5 → Subgroup (Perm (Fin 5))
  | 0 => Subgroup.closure {finRotate 5}
  | 1 => Subgroup.closure {finRotate 5, doubleSwap5}
  | 2 => Subgroup.closure {finRotate 5, frobeniusComplement5}
  | 3 => alternatingGroup (Fin 5)
  | 4 => ⊤

/-- The reference subgroup represented by a transitive-group label of degree at most five.

The entries use the standard ordering `1T1`, `2T1`, `3T1`--`3T2`, `4T1`--`4T5`, and
`5T1`--`5T5`. -/
def referenceSubgroup (n : ℕ) : TransitiveGroupIndex n → Subgroup (Perm (Fin n)) :=
  match n with
  | 0 => Fin.elim0
  | 1 => fun _ => ⊤
  | 2 => fun _ => ⊤
  | 3 => referenceSubgroup3
  | 4 => referenceSubgroup4
  | 5 => referenceSubgroup5
  | _ + 6 => Fin.elim0

/-- A subgroup has label `j` when it is conjugate in the ambient symmetric group to the
corresponding reference subgroup. -/
def TransitiveGroupLabel {n : ℕ} (j : TransitiveGroupIndex n)
    (G : Subgroup (Perm (Fin n))) : Prop :=
  ∃ τ : Perm (Fin n), Subgroup.map (MulAut.conj τ).toMonoidHom G = referenceSubgroup n j

/-- A transitive-group label is equivalent to the existence of a conjugating permutation. -/
theorem transitiveGroupLabel_iff {n : ℕ} (j : TransitiveGroupIndex n)
    (G : Subgroup (Perm (Fin n))) :
    TransitiveGroupLabel j G ↔
      ∃ τ : Perm (Fin n), Subgroup.map (MulAut.conj τ).toMonoidHom G = referenceSubgroup n j :=
  (Iff.rfl)

/-- The reference subgroup for `1T1` is the full symmetric group on one letter. -/
@[simp]
theorem referenceSubgroup_one (j : TransitiveGroupIndex 1) :
    referenceSubgroup 1 j = ⊤ := by simp [referenceSubgroup]

/-- The reference subgroup for `2T1` is the full symmetric group on two letters. -/
@[simp]
theorem referenceSubgroup_two (j : TransitiveGroupIndex 2) :
    referenceSubgroup 2 j = ⊤ := by simp [referenceSubgroup]

/-- The reference subgroup for `3T1` is generated by a rotation. -/
@[simp]
theorem referenceSubgroup_three_zero :
    referenceSubgroup 3 ⟨0, by simp [numTransitiveGroups]⟩ =
      Subgroup.closure {finRotate 3} := by
  simp [referenceSubgroup, referenceSubgroup3]

/-- The reference subgroup for `3T2` is the full symmetric group. -/
@[simp]
theorem referenceSubgroup_three_one :
    referenceSubgroup 3 ⟨1, by simp [numTransitiveGroups]⟩ = ⊤ := by
  simp [referenceSubgroup, referenceSubgroup3]

/-- The reference subgroup for `4T1` is generated by a rotation. -/
@[simp]
theorem referenceSubgroup_four_zero :
    referenceSubgroup 4 ⟨0, by simp [numTransitiveGroups]⟩ =
      Subgroup.closure {finRotate 4} := by
  simp [referenceSubgroup, referenceSubgroup4]

/-- The reference subgroup for `4T2` is the canonical Klein-four subgroup. -/
@[simp]
theorem referenceSubgroup_four_one :
    referenceSubgroup 4 ⟨1, by simp [numTransitiveGroups]⟩ =
      (alternatingGroup.kleinFour (Fin 4)).map (alternatingGroup (Fin 4)).subtype := by
  simp [referenceSubgroup, referenceSubgroup4]

/-- The reference subgroup for `4T3` is generated by a rotation and a diagonal swap. -/
@[simp]
theorem referenceSubgroup_four_two :
    referenceSubgroup 4 ⟨2, by simp [numTransitiveGroups]⟩ =
      Subgroup.closure {finRotate 4, swap 0 2} := by
  simp [referenceSubgroup, referenceSubgroup4]

/-- The reference subgroup for `4T3` is the dihedral group of the square `0, 1, 2, 3`: a
permutation lies in it exactly when it preserves the pairing `{{0, 2}, {1, 3}}` of opposite
vertices, that is, commutes with `i ↦ i + 2`. -/
theorem mem_referenceSubgroup_four_two_iff {σ : Perm (Fin 4)} :
    σ ∈ referenceSubgroup 4 ⟨2, by simp [numTransitiveGroups]⟩ ↔ ∀ i, σ (i + 2) = σ i + 2 := by
  rw [referenceSubgroup_four_two]
  constructor
  · intro h
    induction h using Subgroup.closure_induction with
    | mem τ hτ =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hτ
      rcases hτ with rfl | rfl <;> decide
    | one => simp
    | mul τ ρ _ _ hτ hρ => simp [hρ, hτ]
    | inv τ _ hτ =>
      intro i
      apply τ.injective
      simp [hτ]
  · intro h
    -- The eight permutations commuting with `i ↦ i + 2` are the eight words `rᵃ sᵇ` in the
    -- rotation `r` and the diagonal swap `s`.
    have hword : ∀ σ : Perm (Fin 4), (∀ i, σ (i + 2) = σ i + 2) →
        ∃ a : Fin 4, ∃ b : Fin 2, σ = finRotate 4 ^ (a : ℕ) * swap 0 2 ^ (b : ℕ) := by
      decide
    obtain ⟨a, b, rfl⟩ := hword σ h
    exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
      (pow_mem (Subgroup.subset_closure (by simp)) _)

/-- The reference subgroup for `4T4` is the alternating group. -/
@[simp]
theorem referenceSubgroup_four_three :
    referenceSubgroup 4 ⟨3, by simp [numTransitiveGroups]⟩ = alternatingGroup (Fin 4) := by
  simp [referenceSubgroup, referenceSubgroup4]

/-- The reference subgroup for `4T5` is the full symmetric group. -/
@[simp]
theorem referenceSubgroup_four_four :
    referenceSubgroup 4 ⟨4, by simp [numTransitiveGroups]⟩ = ⊤ := by
  simp [referenceSubgroup, referenceSubgroup4]

/-- The reference subgroup for `5T1` is generated by a rotation. -/
@[simp]
theorem referenceSubgroup_five_zero :
    referenceSubgroup 5 ⟨0, by simp [numTransitiveGroups]⟩ =
      Subgroup.closure {finRotate 5} := by
  simp [referenceSubgroup, referenceSubgroup5]

/-- The reference subgroup for `5T2` is generated by a rotation and a double swap. -/
@[simp]
theorem referenceSubgroup_five_one :
    referenceSubgroup 5 ⟨1, by simp [numTransitiveGroups]⟩ =
      Subgroup.closure {finRotate 5, swap 0 3 * swap 1 2} := by
  simp [referenceSubgroup, referenceSubgroup5, doubleSwap5]

/-- The reference subgroup for `5T3` is generated by a rotation and a Frobenius complement. -/
@[simp]
theorem referenceSubgroup_five_two :
    referenceSubgroup 5 ⟨2, by simp [numTransitiveGroups]⟩ =
      Subgroup.closure {finRotate 5, [0, 1, 3, 2].formPerm} := by
  simp [referenceSubgroup, referenceSubgroup5, frobeniusComplement5]

/-- The reference subgroup for `5T4` is the alternating group. -/
@[simp]
theorem referenceSubgroup_five_three :
    referenceSubgroup 5 ⟨3, by simp [numTransitiveGroups]⟩ = alternatingGroup (Fin 5) := by
  simp [referenceSubgroup, referenceSubgroup5]

/-- The reference subgroup for `5T5` is the full symmetric group. -/
@[simp]
theorem referenceSubgroup_five_four :
    referenceSubgroup 5 ⟨4, by simp [numTransitiveGroups]⟩ = ⊤ := by
  simp [referenceSubgroup, referenceSubgroup5]

private theorem isPretransitive_referenceSubgroup4_one :
    IsPretransitive (referenceSubgroup4 1) (Fin 4) := by
  let K := alternatingGroup.kleinFour (Fin 4)
  let e := K.equivMapOfInjective (alternatingGroup (Fin 4)).subtype
    (alternatingGroup (Fin 4)).subtype_injective
  let _ : K.Normal := alternatingGroup.normal_kleinFour (by simp)
  let _ : IsPreprimitive (alternatingGroup (Fin 4)) (Fin 4) :=
    alternatingGroup.isPreprimitive_of_three_le_card (Fin 4) (by simp)
  have hK : IsPretransitive K (Fin 4) := by
    apply IsQuasiPreprimitive.isPretransitive_of_normal
    rw [Set.ne_univ_iff_exists_notMem]
    have hKne : K ≠ ⊥ := by
      intro hKbot
      have hcard :=
        alternatingGroup.kleinFour_card_of_card_eq_four (α := Fin 4) (by simp)
      have hbotcard : Nat.card (⊥ : Subgroup (alternatingGroup (Fin 4))) = 4 := by
        rw [← hKbot]
        exact hcard
      simp at hbotcard
    obtain ⟨g, hg⟩ := K.ne_bot_iff_exists_ne_one.mp hKne
    have hg' : (g : Perm (Fin 4)) ≠ 1 := fun h ↦ hg (Subtype.ext (Subtype.ext h))
    obtain ⟨x, hx⟩ : ∃ x, (g : Perm (Fin 4)) x ≠ x := by
      by_contra! hfix
      exact hg' (Equiv.ext hfix)
    refine ⟨x, ?_⟩
    simpa only [mem_fixedPoints, Subgroup.smul_def, not_forall] using
      ⟨g, hx⟩
  constructor
  intro x y
  obtain ⟨g, hg⟩ := hK.exists_smul_eq x y
  refine ⟨e g, ?_⟩
  calc
    e g • x = g • x := by
      simpa only [e, Subgroup.smul_def, Equiv.Perm.smul_def, Subgroup.subtype_apply] using
        congrArg (fun p : Perm (Fin 4) ↦ p x)
        (Subgroup.coe_equivMapOfInjective_apply K (alternatingGroup (Fin 4)).subtype
          (alternatingGroup (Fin 4)).subtype_injective g)
    _ = y := hg

/-- Every reference subgroup acts transitively in its defining permutation representation. -/
theorem isPretransitive_referenceSubgroup :
    ∀ (n : ℕ) (j : TransitiveGroupIndex n),
      IsPretransitive (referenceSubgroup n j) (Fin n)
  | 0, j => j.elim0
  | 1, _ => inferInstance
  | 2, _ => by
      rw [referenceSubgroup_two]
      exact isPretransitive_of_finRotate_mem (n := 2) (G := ⊤) (by simp)
  | 3, j => by
      fin_cases j
      · exact isPretransitive_of_finRotate_mem (Subgroup.subset_closure (by simp))
      · rw [referenceSubgroup_three_one]
        exact isPretransitive_of_finRotate_mem (n := 3) (G := ⊤) (by simp)
  | 4, j => by
      fin_cases j
      · exact isPretransitive_of_finRotate_mem (Subgroup.subset_closure (by simp))
      · exact isPretransitive_referenceSubgroup4_one
      · exact isPretransitive_of_finRotate_mem (Subgroup.subset_closure (by simp))
      · exact alternatingGroup.isPretransitive_of_three_le_card (Fin 4) (by simp)
      · rw [referenceSubgroup_four_four]
        exact isPretransitive_of_finRotate_mem (n := 4) (G := ⊤) (by simp)
  | 5, j => by
      fin_cases j
      · exact isPretransitive_of_finRotate_mem (Subgroup.subset_closure (by simp))
      · exact isPretransitive_of_finRotate_mem (Subgroup.subset_closure (by simp))
      · exact isPretransitive_of_finRotate_mem (Subgroup.subset_closure (by simp))
      · exact alternatingGroup.isPretransitive_of_three_le_card (Fin 5) (by simp)
      · rw [referenceSubgroup_five_four]
        exact isPretransitive_of_finRotate_mem (n := 5) (G := ⊤) (by simp)
  | _ + 6, j => j.elim0

/-- A reference subgroup carries its defining transitive-group label. -/
@[simp]
theorem transitiveGroupLabel_referenceSubgroup (n : ℕ) (j : TransitiveGroupIndex n) :
    TransitiveGroupLabel j (referenceSubgroup n j) := by
  refine ⟨1, ?_⟩
  ext g
  simp [Subgroup.mem_map]

/-- Conjugating the permutation representation does not change its transitive-group label. -/
theorem TransitiveGroupLabel.map_conj {n : ℕ} {j : TransitiveGroupIndex n}
    {G : Subgroup (Perm (Fin n))} (h : TransitiveGroupLabel j G) (σ : Perm (Fin n)) :
    TransitiveGroupLabel j (Subgroup.map (MulAut.conj σ).toMonoidHom G) := by
  obtain ⟨τ, hτ⟩ := h
  refine ⟨τ * σ⁻¹, ?_⟩
  simp only [Subgroup.map_map, MulEquiv.toMonoidHom_eq_coe,
    ← MulEquiv.coe_monoidHom_trans, ← MulAut.mul_def, ← map_mul]
  simpa [mul_assoc] using hτ

/-- A subgroup and any conjugate subgroup have exactly the same transitive-group labels. -/
@[simp]
theorem transitiveGroupLabel_map_conj_iff {n : ℕ} {j : TransitiveGroupIndex n}
    (G : Subgroup (Perm (Fin n))) (σ : Perm (Fin n)) :
    TransitiveGroupLabel j (Subgroup.map (MulAut.conj σ) G) ↔
      TransitiveGroupLabel j G := by
  constructor
  · rintro ⟨τ, hτ⟩
    refine ⟨τ * σ, ?_⟩
    simp only [Subgroup.map_map, MulEquiv.toMonoidHom_eq_coe,
      ← MulEquiv.coe_monoidHom_trans, ← MulAut.mul_def, ← map_mul] at hτ
    exact hτ
  · exact fun h => h.map_conj σ

/-- A subgroup carrying a transitive-group label acts transitively on its permutation domain. -/
theorem TransitiveGroupLabel.isPretransitive {n : ℕ} {j : TransitiveGroupIndex n}
    {G : Subgroup (Perm (Fin n))} (h : TransitiveGroupLabel j G) :
    IsPretransitive G (Fin n) := by
  obtain ⟨τ, hτ⟩ := h
  constructor
  intro x y
  obtain ⟨r, hr⟩ :=
    (isPretransitive_referenceSubgroup n j).exists_smul_eq (τ x) (τ y)
  have hrmem : (r : Perm (Fin n)) ∈ Subgroup.map (MulAut.conj τ).toMonoidHom G := by
    rw [hτ]
    exact r.property
  obtain ⟨g, hg, hgr⟩ := hrmem
  refine ⟨⟨g, hg⟩, τ.injective ?_⟩
  rw [← hr]
  simp only [Subgroup.smul_def, Equiv.Perm.smul_def]
  rw [← hgr]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Equiv.Perm.mul_apply,
    Equiv.Perm.inv_def, Equiv.symm_apply_apply]

/-- A label is witnessed by a transport of the subgroup along a renumbering of `Fin n`. -/
theorem TransitiveGroupLabel.exists_map_permCongrHom_eq {n : ℕ} {j : TransitiveGroupIndex n}
    {G : Subgroup (Perm (Fin n))} (h : TransitiveGroupLabel j G) :
    ∃ τ : Perm (Fin n), G.map τ.permCongrHom.toMonoidHom = referenceSubgroup n j := by
  obtain ⟨τ, hτ⟩ := h
  refine ⟨τ, hτ ▸ congrArg (Subgroup.map · G) ?_⟩
  ext σ x
  simp [Equiv.permCongr_eq_mul]

/-- Reading a permutation group on `n` points through two numberings by `Fin n` gives the same
transitive-group labels. -/
theorem _root_.Subgroup.transitiveGroupLabel_map_permCongrHom_iff {α : Type*} {n : ℕ}
    {j : TransitiveGroupIndex n} (G : Subgroup (Perm α)) (e e' : α ≃ Fin n) :
    TransitiveGroupLabel j (G.map e.permCongrHom.toMonoidHom) ↔
      TransitiveGroupLabel j (G.map e'.permCongrHom.toMonoidHom) := by
  have h : G.map e'.permCongrHom.toMonoidHom =
      Subgroup.map (MulAut.conj (e.symm.trans e')) (G.map e.permCongrHom.toMonoidHom) := by
    rw [Subgroup.map_map]
    congr 1
    ext σ x
    simp [Equiv.permCongrHom_coe]
  rw [h, transitiveGroupLabel_map_conj_iff]

/-- A subgroup carrying a transitive-group label has the order of its reference subgroup. -/
theorem TransitiveGroupLabel.natCard_eq {n : ℕ} {j : TransitiveGroupIndex n}
    {G : Subgroup (Perm (Fin n))} (h : TransitiveGroupLabel j G) :
    Nat.card G = Nat.card (referenceSubgroup n j) := by
  obtain ⟨τ, hτ⟩ := h.exists_map_permCongrHom_eq
  rw [← hτ, Subgroup.card_map_of_injective τ.permCongrHom.injective]

/-- A subgroup carrying a transitive-group label consists of even permutations exactly when its
reference subgroup does. -/
theorem TransitiveGroupLabel.le_alternatingGroup_iff {n : ℕ} {j : TransitiveGroupIndex n}
    {G : Subgroup (Perm (Fin n))} (h : TransitiveGroupLabel j G) :
    G ≤ alternatingGroup (Fin n) ↔ referenceSubgroup n j ≤ alternatingGroup (Fin n) := by
  obtain ⟨τ, hτ⟩ := h.exists_map_permCongrHom_eq
  rw [← hτ, Equiv.map_permCongrHom_le_alternatingGroup_iff]

/-- A subgroup carrying a transitive-group label acts primitively exactly when its reference
subgroup does. -/
theorem TransitiveGroupLabel.isPreprimitive_iff {n : ℕ} {j : TransitiveGroupIndex n}
    {G : Subgroup (Perm (Fin n))} (h : TransitiveGroupLabel j G) :
    IsPreprimitive G (Fin n) ↔ IsPreprimitive (referenceSubgroup n j) (Fin n) := by
  obtain ⟨τ, hτ⟩ := h.exists_map_permCongrHom_eq
  rw [← hτ, Equiv.isPreprimitive_map_permCongrHom_iff]

/-- A subgroup carrying a transitive-group label is solvable exactly when its reference subgroup
is. -/
theorem TransitiveGroupLabel.isSolvable_iff {n : ℕ} {j : TransitiveGroupIndex n}
    {G : Subgroup (Perm (Fin n))} (h : TransitiveGroupLabel j G) :
    Group.IsSolvable G ↔ Group.IsSolvable (referenceSubgroup n j) := by
  obtain ⟨τ, hτ⟩ := h.exists_map_permCongrHom_eq
  rw [← hτ, MulEquiv.toMonoidHom_eq_coe]
  exact (τ.permCongrHom.subgroupMap G).isSolvable_congr

/-- In degree one every subgroup carries the label `1T1`. -/
@[simp]
theorem transitiveGroupLabel_one (j : TransitiveGroupIndex 1) (G : Subgroup (Perm (Fin 1))) :
    TransitiveGroupLabel j G :=
  ⟨1, Subsingleton.elim _ _⟩

/-- In degree two a subgroup carries the label `2T1` exactly when it is transitive: the only
transitive subgroup of the symmetric group on two letters is the whole group. -/
@[simp]
theorem transitiveGroupLabel_two_iff (j : TransitiveGroupIndex 2) (G : Subgroup (Perm (Fin 2))) :
    TransitiveGroupLabel j G ↔ IsPretransitive G (Fin 2) := by
  refine ⟨TransitiveGroupLabel.isPretransitive, fun hG => ⟨1, ?_⟩⟩
  obtain ⟨g, hg⟩ := hG.exists_smul_eq 0 1
  have hg1 : (g : Perm (Fin 2)) ≠ 1 := by
    rintro h
    simp [Subgroup.smul_def, h] at hg
  have hperm : ∀ σ τ : Perm (Fin 2), τ ≠ 1 → σ = 1 ∨ σ = τ := by decide
  have htop : G = ⊤ := by
    refine eq_top_iff.mpr fun σ _ => ?_
    rcases hperm σ g hg1 with rfl | rfl
    exacts [G.one_mem, g.2]
  rw [htop, referenceSubgroup_two]
  exact Subgroup.map_top_of_surjective _ (MulAut.conj 1).surjective

end TauCeti
