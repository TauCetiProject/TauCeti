/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Fin.Basic

/-!
# Ordered pairs of distinct elements of `Fin n`, by their difference

An ordered pair `(a, b)` of distinct elements of `Fin n` is determined by its source `a` and its
nonzero cyclic difference `b - a`. Shifting the difference down by one gives an equivalence
`{p : Fin n × Fin n // p.1 ≠ p.2} ≃ Fin (n - 1) × Fin n`. Composed with `finProdFinEquiv`, it lists
the pairs of difference `1` first, then those of difference `2`, and so on, each group by its
source. The root systems of types `Aₙ` and `Dₙ` enumerate their roots this way, so that the pairs
`(a, a + 1)` behind the simple roots come first.

## Main definitions

* `TauCeti.finDistinctPairsEquiv`: the equivalence, with the evaluation lemmas
  `TauCeti.finDistinctPairsEquiv_apply_fst_val`, `TauCeti.finDistinctPairsEquiv_apply_snd` and
  `TauCeti.finDistinctPairsEquiv_symm_apply_coe`.
* `TauCeti.finDistinctPairsRevSwap`: the involution `(a, b) ↦ (rev b, rev a)` of the pairs, the
  diagram automorphism of type `A` read on root indices. It is its own inverse
  (`finDistinctPairsRevSwap_symm`, `finDistinctPairsRevSwap_finDistinctPairsRevSwap`),
  `finDistinctPairsRevSwap_eq_self_iff` describes its fixed pairs, and
  `finDistinctPairsRevSwap_val_fst_add_val_snd` and `finDistinctPairsRevSwap_val_fst_add_val_snd_lt`
  relate the index sums of a pair and its image.
-/

public section

namespace TauCeti

/-- The ordered pairs of distinct elements of `Fin n`, by their nonzero cyclic difference `b - a`
shifted down to `Fin (n - 1)`, and their source `a`. -/
def finDistinctPairsEquiv (n : ℕ) : {p : Fin n × Fin n // p.1 ≠ p.2} ≃ Fin (n - 1) × Fin n where
  toFun p := (⟨((p.1.2 - p.1.1 : Fin n) : ℕ) - 1, by
      have h₁ := (p.1.2 - p.1.1 : Fin n).isLt
      have h₂ : (p.1.1 : ℕ) ≠ p.1.2 := fun h => p.2 (Fin.ext h)
      have := p.1.1.isLt
      have := p.1.2.isLt
      omega⟩, p.1.1)
  invFun q := ⟨(q.2, q.2 + (⟨(q.1 : ℕ) + 1, by omega⟩ : Fin n)), by
    have : NeZero n := ⟨by have := q.1.isLt; omega⟩
    intro h
    simp at h⟩
  left_inv p := by
    have : NeZero n := ⟨by have := p.1.1.isLt; omega⟩
    have h₁ : 1 ≤ ((p.1.2 - p.1.1 : Fin n) : ℕ) := by
      have h : (p.1.2 - p.1.1 : Fin n) ≠ 0 := fun h => p.2 (sub_eq_zero.mp h).symm
      have : ((p.1.2 - p.1.1 : Fin n) : ℕ) ≠ 0 := by simpa [Fin.val_eq_zero_iff] using h
      omega
    refine Subtype.ext (Prod.ext rfl ?_)
    have hx : (⟨((p.1.2 - p.1.1 : Fin n) : ℕ) - 1 + 1, by omega⟩ : Fin n) = p.1.2 - p.1.1 :=
      Fin.ext (by simp only; omega)
    dsimp only
    rw [hx, add_sub_cancel]
  right_inv q := by
    have : NeZero n := ⟨by have := q.1.isLt; omega⟩
    refine Prod.ext (Fin.ext ?_) rfl
    dsimp only
    rw [add_sub_cancel_left]
    simp

/-- The first coordinate of `finDistinctPairsEquiv` is the cyclic difference minus one. -/
@[simp]
theorem finDistinctPairsEquiv_apply_fst_val {n : ℕ} (p : {p : Fin n × Fin n // p.1 ≠ p.2}) :
    ((finDistinctPairsEquiv n p).1 : ℕ) = ((p.1.2 - p.1.1 : Fin n) : ℕ) - 1 :=
  (rfl)

/-- The second coordinate of `finDistinctPairsEquiv` is the source. -/
@[simp]
theorem finDistinctPairsEquiv_apply_snd {n : ℕ} (p : {p : Fin n × Fin n // p.1 ≠ p.2}) :
    (finDistinctPairsEquiv n p).2 = p.1.1 :=
  (rfl)

/-- The inverse of `finDistinctPairsEquiv` sends a difference index `i` and a source `a` to the
pair `(a, a + (i + 1))`. -/
@[simp]
theorem finDistinctPairsEquiv_symm_apply_coe {n : ℕ} (q : Fin (n - 1) × Fin n) :
    ((finDistinctPairsEquiv n).symm q : Fin n × Fin n) =
      (q.2, q.2 + (⟨(q.1 : ℕ) + 1, by omega⟩ : Fin n)) :=
  (rfl)

/-- Reversing both entries of a pair of distinct elements of `Fin n` and exchanging them,
`(a, b) ↦ (rev b, rev a)`. On the index pairs of the type `A` root system this is the diagram
automorphism, the effect of `e_a ↦ -e_{rev a}` on the root `e_a - e_b`. -/
def finDistinctPairsRevSwap (n : ℕ) : Equiv.Perm {p : Fin n × Fin n // p.1 ≠ p.2} :=
  Function.Involutive.toPerm
    (fun p ↦ ⟨(p.val.2.rev, p.val.1.rev), Fin.rev_injective.ne p.property.symm⟩)
    fun p ↦ by apply Subtype.ext; simp

/-- The underlying pair of the reversed exchange. -/
@[simp]
theorem finDistinctPairsRevSwap_apply_val {n : ℕ} (p : {p : Fin n × Fin n // p.1 ≠ p.2}) :
    (finDistinctPairsRevSwap n p).val = (p.val.2.rev, p.val.1.rev) :=
  (rfl)

/-- The reversed exchange is its own inverse. -/
@[simp]
theorem finDistinctPairsRevSwap_symm (n : ℕ) :
    (finDistinctPairsRevSwap n).symm = finDistinctPairsRevSwap n :=
  Function.Involutive.toPerm_symm _

/-- The reversed exchange is an involution. -/
@[simp]
theorem finDistinctPairsRevSwap_finDistinctPairsRevSwap {n : ℕ}
    (p : {p : Fin n × Fin n // p.1 ≠ p.2}) :
    finDistinctPairsRevSwap n (finDistinctPairsRevSwap n p) = p :=
  Function.Involutive.toPerm_involutive _ p

/-- The reversed exchange fixes exactly the pairs whose entries sum to `n - 1`. -/
theorem finDistinctPairsRevSwap_eq_self_iff {n : ℕ} (p : {p : Fin n × Fin n // p.1 ≠ p.2}) :
    finDistinctPairsRevSwap n p = p ↔ p.val.1.val + p.val.2.val + 1 = n := by
  rw [Subtype.ext_iff, finDistinctPairsRevSwap_apply_val, Prod.ext_iff]
  simp only [Fin.ext_iff, Fin.val_rev]
  have hi := p.val.1.isLt
  have hj := p.val.2.isLt
  omega

/-- The index sums of a pair and of its reversed exchange add up to `2 * (n - 1)`. -/
theorem finDistinctPairsRevSwap_val_fst_add_val_snd {n : ℕ}
    (p : {p : Fin n × Fin n // p.1 ≠ p.2}) :
    (finDistinctPairsRevSwap n p).val.1.val + (finDistinctPairsRevSwap n p).val.2.val +
      (p.val.1.val + p.val.2.val) = 2 * (n - 1) := by
  simp only [finDistinctPairsRevSwap_apply_val, Fin.val_rev]
  have hi := p.val.1.isLt
  have hj := p.val.2.isLt
  omega

/-- A pair whose index sum exceeds `n - 1` is exchanged with a pair whose index sum is below
`n - 1`. -/
theorem finDistinctPairsRevSwap_val_fst_add_val_snd_lt {n : ℕ}
    (p : {p : Fin n × Fin n // p.1 ≠ p.2}) (h : n - 1 < p.val.1.val + p.val.2.val) :
    (finDistinctPairsRevSwap n p).val.1.val + (finDistinctPairsRevSwap n p).val.2.val <
      n - 1 := by
  have := finDistinctPairsRevSwap_val_fst_add_val_snd p
  omega

end TauCeti
