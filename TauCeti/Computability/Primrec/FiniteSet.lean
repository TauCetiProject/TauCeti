/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Primrec.Bitwise

/-!
# Primitive recursive operations on binary finite-set codes

Primitive recursion certificates for membership, bounded filtering and least-element search on
binary finite-set codes. The code operations and their finite-set interpretations are defined
in `TauCeti.Data.Nat.BitIndices`, using Mathlib's `Finset.equivBitIndices` rather than another
encoding or a `Primcodable` instance for finite sets.

The certificates are uniform in their numerical inputs and, for bounded filtering, in the
primitive recursive predicate, so they can be used in computable finite-stage constructions.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter II.2.
* Mathlib's `Finset.equivBitIndices` supplies the binary finite-set equivalence.
-/

public section

namespace Primrec

/-- Membership in the decoded binary finite set is primitive recursive. -/
theorem mem_equivBitIndices : PrimrecRel fun n x => x ∈ Finset.equivBitIndices n :=
  PrimrecRel.of_eq (Primrec.eq.comp nat_testBit (const true)).primrecRel
    fun n x => by simp

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
  rw [← Finset.equivBitIndices.symm_apply_apply
    (Nat.filterBitIndices (n a) (b a) (p a)), Nat.equivBitIndices_filterBitIndices]
  simp [Finset.equivBitIndices_symm_apply, ← List.sum_eq_foldr,
    ← List.sum_toFinset _ (Nat.bitIndices_nodup.filter _), List.toFinset_filter,
    Finset.equivBitIndices_apply]

/-- Least-element search on binary finite-set codes is primitive recursive. -/
theorem nat_leastBitIndex : Primrec Nat.leastBitIndex :=
  (list_head?.comp nat_bitIndices).of_eq fun n => (Nat.leastBitIndex_def n).symm

end Primrec
