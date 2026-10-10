/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.ArtinCoefficient
public import TauCeti.GroupTheory.Perm.FinThree.Subgroup
import Mathlib.Data.Finite.Perm

/-!
# Artin coefficients of the symmetric group on three points

The coefficient of the trivial subgroup is `-3`, those of the three point stabilizers
and the alternating subgroup are `1`, and that of the whole group is `0`.
These are integral coefficients: they can be used in induction identities in every
characteristic, including characteristics two and three.

The calculation uses the subgroup enumeration and the upper-sum identity
`TauCeti.sum_artinCoeff_of_mem`, rather than enumerating relative indices separately.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §9.2.
-/

public section

namespace TauCeti

/-- The Artin coefficient of the whole symmetric group `S₃` is zero. -/
@[simp]
theorem artinCoeff_top_perm_fin_three :
    (⊤ : Subgroup (Equiv.Perm (Fin 3))).artinCoeff = 0 := by
  apply Subgroup.artinCoeff_eq_zero_of_not_isCyclic
  simpa only [Subgroup.topEquiv.isCyclic, Equiv.Perm.isCyclic_iff_card_le_two,
    Nat.card_fin] using (by decide : ¬ 3 ≤ 2)

/-- Each point stabilizer of `S₃` has Artin coefficient one. -/
@[simp]
theorem artinCoeff_stabilizer_perm_fin_three (a : Fin 3) :
    (MulAction.stabilizer (Equiv.Perm (Fin 3)) a).artinCoeff = 1 := by
  have hmem : ∀ a b : Fin 3,
      Equiv.swap (a + 1) (a + 2) ∈ MulAction.stabilizer (Equiv.Perm (Fin 3)) b ↔ a = b := by
    simp only [mem_stabilizer_perm_fin_three_iff]
    decide
  have hbot : ∀ a : Fin 3,
      Equiv.swap (a + 1) (a + 2) ∉ (⊥ : Subgroup (Equiv.Perm (Fin 3))) := by
    simp only [Subgroup.mem_bot]
    decide
  have halt : ∀ a : Fin 3, Equiv.swap (a + 1) (a + 2) ∉ alternatingGroup (Fin 3) := by
    simp only [Equiv.Perm.mem_alternatingGroup]
    decide
  classical
  have h := sum_artinCoeff_of_mem (Equiv.swap (a + 1) (a + 2))
  simp only [finsum_eq_if, Subgroup.finsum_fin_three, artinCoeff_top_perm_fin_three,
    hmem, hbot, halt, ite_false, zero_add, add_zero, ite_self] at h
  fin_cases a <;> simpa using h

/-- The alternating subgroup of `S₃` has Artin coefficient one. -/
@[simp]
theorem artinCoeff_alternatingGroup_fin_three : (alternatingGroup (Fin 3)).artinCoeff = 1 := by
  have hbot : finRotate 3 ∉ (⊥ : Subgroup (Equiv.Perm (Fin 3))) := by
    simp only [Subgroup.mem_bot]
    decide
  have hstab : ∀ a : Fin 3,
      finRotate 3 ∉ MulAction.stabilizer (Equiv.Perm (Fin 3)) a := by
    simp only [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
    decide
  have halt : finRotate 3 ∈ alternatingGroup (Fin 3) := by
    simp only [Equiv.Perm.mem_alternatingGroup]
    decide
  classical
  have h := sum_artinCoeff_of_mem (finRotate 3)
  simpa only [finsum_eq_if, Subgroup.finsum_fin_three, artinCoeff_top_perm_fin_three,
    hbot, hstab, halt, ite_true, ite_false, zero_add, add_zero, ite_self] using h

/-- The trivial subgroup of `S₃` has Artin coefficient minus three. -/
@[simp]
theorem artinCoeff_bot_perm_fin_three :
    (⊥ : Subgroup (Equiv.Perm (Fin 3))).artinCoeff = -3 := by
  classical
  have h := sum_artinCoeff_of_mem (1 : Equiv.Perm (Fin 3))
  simp only [Subgroup.one_mem, finsum_eq_if, ite_true, Subgroup.finsum_fin_three,
    artinCoeff_stabilizer_perm_fin_three, artinCoeff_alternatingGroup_fin_three,
    artinCoeff_top_perm_fin_three] at h
  omega

/-- Artin's fixed-point identity for `S₃`, with all subgroup coefficients evaluated. -/
theorem artin_fixedPoint_identity_perm_fin_three (g : Equiv.Perm (Fin 3)) :
    -3 * (Nat.card (MulAction.fixedBy
        (Equiv.Perm (Fin 3) ⧸ (⊥ : Subgroup (Equiv.Perm (Fin 3)))) g) : ℤ) +
      2 * (∑ a : Fin 3, (Nat.card (MulAction.fixedBy
        (Equiv.Perm (Fin 3) ⧸ MulAction.stabilizer (Equiv.Perm (Fin 3)) a) g) : ℤ)) +
      3 * (Nat.card (MulAction.fixedBy
        (Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) g) : ℤ) = 6 := by
  have h := sum_artinCoeff_mul_card_fixedBy g
  simp only [Subgroup.finsum_fin_three, artinCoeff_bot_perm_fin_three,
    artinCoeff_stabilizer_perm_fin_three, artinCoeff_alternatingGroup_fin_three,
    artinCoeff_top_perm_fin_three, card_stabilizer_perm_fin_three,
    card_alternatingGroup_fin_three, Subgroup.card_bot, Nat.cast_one, mul_one,
    one_mul, zero_mul] at h
  have hg : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rw [hg] at h
  simpa [Fin.sum_univ_three, mul_add, add_assoc] using h

end TauCeti
