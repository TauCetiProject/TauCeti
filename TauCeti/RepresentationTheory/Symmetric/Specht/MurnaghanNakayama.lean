/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Symmetric.FrobeniusCharacteristic
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.MurnaghanNakayama

/-!
# The Murnaghan–Nakayama rule for Specht characters

Removing a part `r` from a cycle type computes a Specht character value by removing all
rim hooks of size `r` from its shape, with sign `(-1)` to the height of each hook. The
rule is stated over the integers, for the characters of the actual Specht modules.

`spechtCharValue_eq_sum_rimHook` accepts the smaller cycle type through its multiset of
parts. `spechtCharValue_eq_sum_rimHook_removePart` uses Mathlib's
`Nat.Partition.partitionWithPartEquiv` to remove a chosen occurrence. These formulas
reduce the size of the symmetric group at every step and so compute character values
from the empty partition.

The Frobenius characteristic identifies Specht characters with Schur polynomials.
The power-sum identities `psumPart_eq_sum_spechtCharValue_smul_schurPoly` and
`psum_mul_schurPoly` express this character recursion in symmetric polynomials.

## References

* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, second edition,
  Chapter I, Section 7.
* B. E. Sagan, *The Symmetric Group*, second edition, Chapter 4.
-/

public section

namespace TauCeti

open Finset MvPolynomial

open scoped Classical in
/-- **The Murnaghan–Nakayama character rule.** If the cycle type `ρ` is obtained from
`ν` by adding a positive part `r`, its value in the Specht module of shape `μ` is the
signed sum over the shapes obtained by removing a rim hook of size `r` from `μ`. -/
theorem spechtCharValue_eq_sum_rimHook {n m r : ℕ} (μ ρ : n.Partition)
    (ν : m.Partition) (hρ : ρ.parts = r ::ₘ ν.parts) :
    spechtCharValue μ ρ =
      ∑ τ : m.Partition with (diagramOf μ).IsRimHook (diagramOf τ),
        (-1) ^ (diagramOf μ).rimHookHeight (diagramOf τ) * spechtCharValue τ ν := by
  classical
  have hr : 0 < r := ρ.parts_pos (by simp [hρ])
  have hn : n = m + r := by
    have hs := congrArg Multiset.sum hρ
    simpa [ρ.parts_sum, ν.parts_sum, Nat.add_comm] using hs
  subst n
  have hp : psumPart (Fin (m + r)) ℤ ρ =
      psum (Fin (m + r)) ℤ r * psumPart (Fin (m + r)) ℤ ν := by
    simp only [psumPart, hρ, Multiset.map_cons, Multiset.prod_cons]
  have hexp :
      (∑ η : (m + r).Partition,
        spechtCharValue η ρ • schurPoly (Fin (m + r)) ℤ η) =
      ∑ η : (m + r).Partition,
        (∑ τ : m.Partition with (diagramOf η).IsRimHook (diagramOf τ),
          (-1) ^ (diagramOf η).rimHookHeight (diagramOf τ) * spechtCharValue τ ν) •
            schurPoly (Fin (m + r)) ℤ η := by
    rw [← psumPart_eq_sum_spechtCharValue_smul_schurPoly, hp,
      psumPart_eq_sum_spechtCharValue_smul_schurPoly, mul_sum]
    simp_rw [mul_smul_comm, psum_mul_schurPoly (R := ℤ) _ hr, sum_filter,
      Finset.smul_sum]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun η _ ↦ ?_
    rw [sum_smul]
    refine sum_congr rfl fun τ _ ↦ ?_
    split_ifs with h
    · simp [zsmul_eq_mul, mul_comm, mul_left_comm]
    · simp
  exact (linearIndependent_schurPoly (σ := Fin (m + r)) (R := ℤ)
    (by simp)).eq_coords_of_eq hexp μ

open scoped Classical in
/-- Remove a chosen part of the cycle type with Mathlib's partition equivalence, then
compute the character by signed rim-hook removal. Repeated parts are removed one at a time. -/
theorem spechtCharValue_eq_sum_rimHook_removePart {n r : ℕ} (μ ρ : n.Partition)
    (hρ : r ∈ ρ.parts) :
    spechtCharValue μ ρ =
      ∑ τ : (n - r).Partition with (diagramOf μ).IsRimHook (diagramOf τ),
        (-1) ^ (diagramOf μ).rimHookHeight (diagramOf τ) *
          spechtCharValue τ (Nat.Partition.partitionWithPartEquiv
            (Nat.succ_le_of_lt (ρ.parts_pos hρ)) (Nat.Partition.le_of_mem_parts hρ) ⟨ρ, hρ⟩) := by
  apply spechtCharValue_eq_sum_rimHook (r := r) μ ρ _
  simp only [Nat.Partition.partitionWithPartEquiv_apply_parts, Multiset.cons_erase hρ]

open scoped Classical in
/-- The Murnaghan–Nakayama rule at actual permutations. The smaller permutation `π'`
has the cycle type obtained by deleting one part `r` from that of `π`, including fixed
points as parts of size one. -/
theorem spechtChar_eq_sum_rimHook {n m r : ℕ} (μ : n.Partition)
    (π : Equiv.Perm (Fin n)) (π' : Equiv.Perm (Fin m))
    (hπ : π.partition.parts = r ::ₘ π'.partition.parts) :
    spechtChar μ π =
      ∑ τ : m.Partition with (diagramOf μ).IsRimHook (diagramOf τ),
        (-1) ^ (diagramOf μ).rimHookHeight (diagramOf τ) * spechtChar τ π' := by
  simp_rw [spechtChar_eq_value]
  apply spechtCharValue_eq_sum_rimHook (r := r) _ _ _
  simpa only [parts_partitionEquivConjClasses_symm_mk] using hπ

end TauCeti
