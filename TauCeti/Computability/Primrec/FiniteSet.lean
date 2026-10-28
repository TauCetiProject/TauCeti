/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Primrec.Bitwise
public import Mathlib.Combinatorics.Colex

/-!
# Effective operations on binary finite-set codes

The canonical code of a finite set `D : Finset ℕ` is `∑ x ∈ D, 2 ^ x`. We use Mathlib's
`Finset.equivBitIndices` for this equivalence, including its round-trip equations, rather
than introducing another encoding or a `Primcodable` instance for finite sets.

Bit inspection, bitwise union, intersection and difference implement the corresponding
finite-set operations. Bounded filtering and least-element search have primitive recursive
certificates uniform in their numerical inputs, so they can be used in computable finite-stage
constructions. Search returns `none` precisely for the empty code.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter II.2.
* Mathlib's `Finset.equivBitIndices` supplies the binary finite-set equivalence.
-/

public section

namespace Finset

/-- Binary union decodes to finite-set union. -/
theorem equivBitIndices_lor (m n : ℕ) :
    equivBitIndices (m ||| n) = equivBitIndices m ∪ equivBitIndices n := by
  ext x
  simp [equivBitIndices]

/-- Binary intersection decodes to finite-set intersection. -/
theorem equivBitIndices_land (m n : ℕ) :
    equivBitIndices (m &&& n) = equivBitIndices m ∩ equivBitIndices n := by
  ext x
  simp [equivBitIndices]

/-- Binary difference decodes to finite-set difference. -/
theorem equivBitIndices_ldiff (m n : ℕ) :
    equivBitIndices (Nat.ldiff m n) = equivBitIndices m \ equivBitIndices n := by
  ext x
  simp [equivBitIndices, Nat.testBit_ldiff]

end Finset

namespace Nat

/-- Keep the members of the binary-coded finite set `n` that lie below `b` and satisfy `p`. -/
def filterBitIndices (n b : ℕ) (p : ℕ → Bool) : ℕ :=
  Finset.equivBitIndices.symm ((Finset.equivBitIndices n).filter (fun x => x < b ∧ p x))

/-- Decoding bounded filtering gives the corresponding filtered finite set. -/
theorem equivBitIndices_filterBitIndices (n b : ℕ) (p : ℕ → Bool) :
    Finset.equivBitIndices (filterBitIndices n b p) =
      (Finset.equivBitIndices n).filter (fun x => x < b ∧ p x) :=
  Finset.equivBitIndices.apply_symm_apply _

/-- The result of bounded filtering contains exactly the requested members. -/
@[simp]
theorem testBit_filterBitIndices (n b x : ℕ) (p : ℕ → Bool) :
    (filterBitIndices n b p).testBit x = (n.testBit x && decide (x < b) && p x) := by
  apply Bool.eq_iff_iff.mpr
  have h := congrArg (fun s : Finset ℕ => x ∈ s)
    (equivBitIndices_filterBitIndices n b p)
  simpa [Finset.equivBitIndices, and_assoc] using Iff.of_eq h

/-- The least member of a binary-coded finite set, or `none` for the empty set. -/
def leastBitIndex (n : ℕ) : Option ℕ := n.bitIndices.head?

/-- Least-element search succeeds precisely at a member below every other member. -/
@[simp]
theorem leastBitIndex_eq_some_iff (n k : ℕ) :
    leastBitIndex n = some k ↔ k ∈ Finset.equivBitIndices n ∧
      ∀ x ∈ Finset.equivBitIndices n, k ≤ x := by
  have hs := n.bitIndices_sorted.pairwise
  cases h : n.bitIndices with
  | nil => simp [leastBitIndex, Finset.equivBitIndices, h]
  | cons a l =>
    rw [h, List.pairwise_cons] at hs
    simp only [leastBitIndex, List.head?_cons, Option.some.injEq,
      Finset.equivBitIndices_apply, h, List.mem_toFinset, List.mem_cons]
    constructor
    · rintro rfl
      exact ⟨Or.inl rfl, fun x hx => hx.elim (fun h => h.ge) (fun h => (hs.1 x h).le)⟩
    · rintro ⟨hk, hmin⟩
      exact le_antisymm (hk.elim (fun h => h.ge) (fun h => (hs.1 k h).le))
        (hmin a (Or.inl rfl))

/-- Least-element search returns `none` exactly for the zero code. -/
@[simp]
theorem leastBitIndex_eq_none_iff (n : ℕ) : leastBitIndex n = none ↔ n = 0 := by
  simp only [leastBitIndex, List.head?_eq_none_iff]
  constructor
  · intro h
    simpa [h] using (sum_map_two_pow_bitIndices n).symm
  · rintro rfl
    exact bitIndices_zero

end Nat

namespace Primrec

/-- Membership in the decoded binary finite set is primitive recursive. -/
theorem mem_equivBitIndices : PrimrecRel fun n x => x ∈ Finset.equivBitIndices n :=
  PrimrecRel.of_eq (Primrec.eq.comp nat_testBit (const true)).primrecRel
    fun n x => by simp [Finset.equivBitIndices]

/-- Bounded filtering of binary codes is primitive recursive, uniformly in a primitive
recursive predicate and the code and bound supplied by the caller. -/
theorem nat_filterBitIndices {α : Type*} [Primcodable α]
    {n b : α → ℕ} {p : α → ℕ → Bool}
    (hn : Primrec n) (hb : Primrec b) (hp : Primrec₂ p) :
    Primrec fun a => Nat.filterBitIndices (n a) (b a) (p a) := by
  have hfilter := ((nat_lt.comp fst (hb.comp snd)).and
    (Primrec.eq.comp (hp.comp snd fst) (const true))).primrecRel.listFilter.comp
      (nat_bitIndices.comp hn) Primrec.id
  have hmap := list_map hfilter (nat_pow.comp (const 2) snd).to₂
  have hsum := list_foldr hmap (const 0) (nat_add.comp (fst.comp snd) (snd.comp snd)).to₂
  refine hsum.of_eq fun a => ?_
  simp only [Nat.filterBitIndices, Finset.equivBitIndices_symm_apply]
  rw [← List.sum_eq_foldr]
  rw [← List.sum_toFinset _ (Nat.bitIndices_nodup.filter _), List.toFinset_filter]
  congr 1

/-- Least-element search on binary finite-set codes is primitive recursive. -/
theorem nat_leastBitIndex : Primrec Nat.leastBitIndex :=
  list_head?.comp nat_bitIndices

end Primrec
