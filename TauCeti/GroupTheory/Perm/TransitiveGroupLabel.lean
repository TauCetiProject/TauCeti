/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.List

/-!
# Reference transitive permutation groups in degree at most five

This file defines the reference permutation groups underlying the standard `nTj` labels in
degrees at most five. A label records the simultaneous-conjugacy class of a subgroup of the
symmetric group; it does not attach an abstract group name or classify arbitrary subgroups.

The chosen generators are the zero-based translations of the representatives in the LMFDB
transitive-groups table. The reference family is empty outside degrees one through five.

## Main definitions

* `numTransitiveGroups`: the number of reference groups in each supported degree.
* `TransitiveGroupIndex`: the type of valid zero-based label indices.
* `referenceSubgroup`: the subgroup represented by a valid index.
* `TransitiveGroupLabel`: conjugacy to a reference subgroup.

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

/-- A zero-based index for a transitive-group label in degree `n`.

An index `j` is displayed externally as `nT(j + 1)`. -/
abbrev TransitiveGroupIndex (n : ℕ) := Fin (numTransitiveGroups n)

private def doubleSwap4A : Perm (Fin 4) :=
  swap 0 1 * swap 2 3

private def doubleSwap4B : Perm (Fin 4) :=
  swap 0 3 * swap 1 2

private def doubleSwap5 : Perm (Fin 5) :=
  swap 0 3 * swap 1 2

private def frobeniusComplement5 : Perm (Fin 5) :=
  [0, 1, 3, 2].formPerm

private def referenceSubgroup3 : Fin 2 → Subgroup (Perm (Fin 3))
  | 0 => Subgroup.closure {finRotate 3}
  | 1 => ⊤

private def referenceSubgroup4 : Fin 5 → Subgroup (Perm (Fin 4))
  | 0 => Subgroup.closure {finRotate 4}
  | 1 => Subgroup.closure {doubleSwap4A, doubleSwap4B}
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

private theorem isPretransitive_of_isCycle_mem_support_eq_univ
    {n : ℕ} {G : Subgroup (Perm (Fin n))} {g : Perm (Fin n)} (hcycle : g.IsCycle)
    (hsupport : g.support = Finset.univ) (hg : g ∈ G) : IsPretransitive G (Fin n) := by
  constructor
  intro x y
  have hx : g x ≠ x := by simpa [← mem_support] using congrArg (x ∈ ·) hsupport
  have hy : g y ≠ y := by simpa [← mem_support] using congrArg (y ∈ ·) hsupport
  obtain ⟨k, hk⟩ := hcycle.exists_zpow_eq hx hy
  exact ⟨⟨g ^ k, G.zpow_mem hg k⟩, hk⟩

private theorem isPretransitive_of_finRotate_mem {n : ℕ} (hn : 2 ≤ n)
    {G : Subgroup (Perm (Fin n))} (hg : finRotate n ∈ G) : IsPretransitive G (Fin n) :=
  isPretransitive_of_isCycle_mem_support_eq_univ
    (isCycle_finRotate_of_le hn) (support_finRotate_of_le hn) hg

private theorem isPretransitive_referenceSubgroup4_one :
    IsPretransitive (referenceSubgroup4 1) (Fin 4) := by
  let H := referenceSubgroup4 1
  have reaches : ∀ y : Fin 4, ∃ g : H, g • (0 : Fin 4) = y := by
    intro y
    fin_cases y
    · exact ⟨1, rfl⟩
    · exact ⟨⟨doubleSwap4A, Subgroup.subset_closure (by simp)⟩, by decide⟩
    · exact ⟨⟨doubleSwap4A * doubleSwap4B,
          Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp))⟩, by decide⟩
    · exact ⟨⟨doubleSwap4B, Subgroup.subset_closure (by simp)⟩, by decide⟩
  constructor
  intro x y
  obtain ⟨gx, hx⟩ := reaches x
  obtain ⟨gy, hy⟩ := reaches y
  refine ⟨gy * gx⁻¹, ?_⟩
  rw [← hx, mul_smul, inv_smul_smul, hy]

/-- Every reference subgroup acts transitively in its defining permutation representation. -/
theorem isPretransitive_referenceSubgroup :
    ∀ (n : ℕ) (j : TransitiveGroupIndex n),
      IsPretransitive (referenceSubgroup n j) (Fin n)
  | 0, j => j.elim0
  | 1, _ => inferInstance
  | 2, _ => by
      change IsPretransitive (⊤ : Subgroup (Perm (Fin 2))) (Fin 2)
      exact isPretransitive_of_finRotate_mem (by decide) (by simp)
  | 3, j => by
      fin_cases j
      · exact isPretransitive_of_finRotate_mem (by decide) (Subgroup.subset_closure (by simp))
      · change IsPretransitive (⊤ : Subgroup (Perm (Fin 3))) (Fin 3)
        exact isPretransitive_of_finRotate_mem (by decide) (by simp)
  | 4, j => by
      fin_cases j
      · exact isPretransitive_of_finRotate_mem (by decide) (Subgroup.subset_closure (by simp))
      · exact isPretransitive_referenceSubgroup4_one
      · exact isPretransitive_of_finRotate_mem (by decide) (Subgroup.subset_closure (by simp))
      · exact alternatingGroup.isPretransitive_of_three_le_card (Fin 4) (by simp)
      · change IsPretransitive (⊤ : Subgroup (Perm (Fin 4))) (Fin 4)
        exact isPretransitive_of_finRotate_mem (by decide) (by simp)
  | 5, j => by
      fin_cases j
      · exact isPretransitive_of_finRotate_mem (by decide) (Subgroup.subset_closure (by simp))
      · exact isPretransitive_of_finRotate_mem (by decide) (Subgroup.subset_closure (by simp))
      · exact isPretransitive_of_finRotate_mem (by decide) (Subgroup.subset_closure (by simp))
      · exact alternatingGroup.isPretransitive_of_three_le_card (Fin 5) (by simp)
      · change IsPretransitive (⊤ : Subgroup (Perm (Fin 5))) (Fin 5)
        exact isPretransitive_of_finRotate_mem (by decide) (by simp)
  | _ + 6, j => j.elim0

private theorem map_conj_map_conj {n : ℕ} (G : Subgroup (Perm (Fin n)))
    (σ τ : Perm (Fin n)) :
    Subgroup.map (MulAut.conj σ).toMonoidHom
        (Subgroup.map (MulAut.conj τ).toMonoidHom G) =
      Subgroup.map (MulAut.conj (σ * τ)).toMonoidHom G := by
  rw [Subgroup.map_map]
  congr 1

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
  rw [map_conj_map_conj]
  simpa [mul_assoc] using hτ

/-- A subgroup and any conjugate subgroup have exactly the same transitive-group labels. -/
theorem transitiveGroupLabel_map_conj_iff {n : ℕ} {j : TransitiveGroupIndex n}
    (G : Subgroup (Perm (Fin n))) (σ : Perm (Fin n)) :
    TransitiveGroupLabel j (Subgroup.map (MulAut.conj σ).toMonoidHom G) ↔
      TransitiveGroupLabel j G := by
  constructor
  · rintro ⟨τ, hτ⟩
    refine ⟨τ * σ, ?_⟩
    rw [← map_conj_map_conj]
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
  change τ (g x) = (r : Perm (Fin n)) (τ x)
  rw [← hgr]
  simp [MulAut.conj_apply]

end TauCeti
