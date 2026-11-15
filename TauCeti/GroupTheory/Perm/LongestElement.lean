/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.LongestElement
public import TauCeti.GroupTheory.Perm.Coxeter

/-!
# Order reversal as the longest element of the symmetric group

Reversing the order of `Fin n` by `Fin.revPerm : i ↦ n - 1 - i` inverts every pair of letters, so
its Coxeter length in `TauCeti.permCoxeterSystem n` is `n.choose 2`. Right multiplication by
`Fin.revPerm` complements the inversion set of any permutation `σ`: a pair `a < b` is inverted by
`σ * Fin.revPerm` precisely when the reversed pair `b.rev < a.rev` is not inverted by `σ`. Hence
`ℓ (σ * Fin.revPerm) + ℓ σ = ℓ Fin.revPerm`, making `Fin.revPerm` the unique longest element of
`TauCeti.permCoxeterSystem n`.

Conjugation by `Fin.revPerm` reverses the simple reflections, sending the adjacent transposition
`transposition i` to `transposition i.rev`.

## Main results

* `TauCeti.BraidGroup.strand_rev` and `TauCeti.BraidGroup.strandSucc_rev`: reversing generator
  indices exchanges and reverses the two crossed strands.
* `TauCeti.BraidGroup.revPerm_mul_transposition_mul_revPerm` and
  `TauCeti.BraidGroup.revPerm_mul_transposition`: conjugation by `Fin.revPerm` reverses the
  adjacent transpositions.
* `TauCeti.permCoxeterSystem_length_revPerm`: the Coxeter length of `Fin.revPerm` is `n.choose 2`.
* `TauCeti.isLongest_permCoxeterSystem_revPerm`: `Fin.revPerm` is the longest element of
  `TauCeti.permCoxeterSystem n`.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 1.5 and 2.3.
-/

public section

namespace TauCeti.BraidGroup

variable {n : ℕ}

/-- Reversing the crossing index sends the lower crossed strand to the reversal of the upper
crossed strand. -/
@[simp]
theorem strand_rev (i : Fin (n - 1)) : strand i.rev = (strandSucc i).rev := by
  ext
  simp only [val_strand, val_strandSucc, Fin.val_rev]
  omega

/-- Reversing the crossing index sends the upper crossed strand to the reversal of the lower
crossed strand. -/
@[simp]
theorem strandSucc_rev (i : Fin (n - 1)) : strandSucc i.rev = (strand i).rev := by
  ext
  simp only [val_strand, val_strandSucc, Fin.val_rev]
  omega

/-- `Fin.revPerm` intertwines each adjacent transposition with the reversed one. -/
theorem revPerm_mul_transposition (i : Fin (n - 1)) :
    Fin.revPerm * transposition i = transposition i.rev * Fin.revPerm := by
  rw [transposition_eq_swap, Equiv.mul_swap_eq_swap_mul, Fin.revPerm_apply, Fin.revPerm_apply,
    Equiv.swap_comm, ← strand_rev, ← strandSucc_rev, ← transposition_eq_swap]

/-- Conjugation by `Fin.revPerm` reverses the index of an adjacent transposition. -/
@[simp]
theorem revPerm_mul_transposition_mul_revPerm (i : Fin (n - 1)) :
    Fin.revPerm * transposition i * Fin.revPerm = transposition i.rev := by
  have hself : (Fin.revPerm : Equiv.Perm (Fin n)) * Fin.revPerm = 1 := by
    ext x
    simp
  rw [revPerm_mul_transposition, mul_assoc, hself, mul_one]

end TauCeti.BraidGroup

namespace TauCeti

/-- The Coxeter length of the order-reversing permutation `Fin.revPerm` is `n.choose 2`. -/
@[simp]
theorem permCoxeterSystem_length_revPerm (n : ℕ) :
    (permCoxeterSystem n).length (Fin.revPerm : Equiv.Perm (Fin n)) = n.choose 2 := by
  have h : (Finset.univ.filter fun p : Fin n × Fin n ↦
      p.1 < p.2 ∧ Fin.revPerm p.2 < Fin.revPerm p.1) =
      Finset.univ.filter fun p : Fin n × Fin n ↦ p.1 < p.2 :=
    Finset.filter_congr fun p _ ↦ by simp
  rw [permCoxeterSystem_length_eq_card_inversion, h, Fintype.card_product_filter_lt,
    Fintype.card_fin]

/-- **Order reversal is the longest element of the symmetric group.** In the type-`A` Coxeter
system `TauCeti.permCoxeterSystem n`, right multiplication by `Fin.revPerm` complements Coxeter
lengths in `n.choose 2`. -/
theorem isLongest_permCoxeterSystem_revPerm (n : ℕ) :
    (permCoxeterSystem n).IsLongest (Fin.revPerm : Equiv.Perm (Fin n)) := by
  rw [CoxeterSystem.isLongest_iff]
  intro σ
  rw [permCoxeterSystem_length_eq_card_inversion, permCoxeterSystem_length_eq_card_inversion,
    permCoxeterSystem_length_revPerm]
  set U := Finset.univ.filter fun p : Fin n × Fin n ↦ p.1 < p.2
  let e : Fin n × Fin n ≃ Fin n × Fin n :=
    { toFun p := (p.2.rev, p.1.rev)
      invFun p := (p.2.rev, p.1.rev)
      left_inv p := by simp
      right_inv p := by simp }
  have hmap : (Finset.univ.filter fun p : Fin n × Fin n ↦
      p.1 < p.2 ∧ (σ * Fin.revPerm : Equiv.Perm (Fin n)) p.2 <
        (σ * Fin.revPerm : Equiv.Perm (Fin n)) p.1).map e.toEmbedding =
      U.filter fun q ↦ ¬ σ q.2 < σ q.1 := by
    ext ⟨a, b⟩
    simp only [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and, U, e,
      Equiv.coe_fn_symm_mk, Fin.rev_lt_rev, Equiv.Perm.mul_apply, Fin.revPerm_apply, Fin.rev_rev]
    exact and_congr_right fun hab ↦
      ⟨not_lt_of_gt, fun h ↦ lt_of_le_of_ne (not_lt.mp h) (σ.injective.ne hab.ne)⟩
  have hcard : (Finset.univ.filter fun p : Fin n × Fin n ↦
      p.1 < p.2 ∧ (σ * Fin.revPerm : Equiv.Perm (Fin n)) p.2 <
        (σ * Fin.revPerm : Equiv.Perm (Fin n)) p.1).card =
      (U.filter fun q ↦ ¬ σ q.2 < σ q.1).card := by
    rw [← hmap, Finset.card_map]
  have hfilter : (Finset.univ.filter fun p : Fin n × Fin n ↦ p.1 < p.2 ∧ σ p.2 < σ p.1) =
      U.filter fun q ↦ σ q.2 < σ q.1 := by
    rw [Finset.filter_filter]
  rw [hcard, hfilter, add_comm, Finset.card_filter_add_card_filter_not,
    Fintype.card_product_filter_lt, Fintype.card_fin]

/-- Every permutation of `Fin n` lies below `Fin.revPerm` in the Bruhat order of
`TauCeti.permCoxeterSystem n`. -/
theorem permCoxeterSystem_bruhatLE_revPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (permCoxeterSystem n).BruhatLE σ Fin.revPerm :=
  (isLongest_permCoxeterSystem_revPerm n).bruhatLE σ

end TauCeti
