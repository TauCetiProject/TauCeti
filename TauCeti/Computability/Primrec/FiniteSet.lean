/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Primrec.Bitwise
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Sum
import TauCeti.Computability.Primrec.List

/-!
# Primitive recursive operations on binary finite-set codes

Primitive recursion certificates for membership, cardinality, the characteristic function,
bounded filtering, and least-element search on binary finite-set codes. This file also
certifies codes for list entries, ranges, images, finite products, and tagged sums.
The certificates use Mathlib's `Finset.equivBitIndices` and the code operations in
`TauCeti.Data.Nat.BitIndices`.

The certificates are uniform in their numerical inputs and, for bounded filtering, in the
primitive recursive predicate, so they can be used in computable finite-stage constructions.
For finite sets over any primitive-codable type, membership is a primitive recursive predicate
(`Set.Finite.primrecPred`).

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

/-- The cardinality of the finite set represented by a binary code is primitive recursive. -/
theorem card_equivBitIndices : Primrec fun n => (Finset.equivBitIndices n).card :=
  (list_length.comp nat_bitIndices).of_eq fun n => by
    simp [Finset.equivBitIndices_apply, List.toFinset_card_of_nodup (Nat.bitIndices_nodup (n := n))]

/-- The characteristic function of the decoded binary finite set is primitive recursive in the
code and the argument. -/
theorem indicator_equivBitIndices :
    Primrec₂ fun n x => (Finset.equivBitIndices n : Set ℕ).indicator (1 : ℕ → ℕ) x :=
  (Primrec.ite mem_equivBitIndices (const 1) (const 0)).of_eq fun p => by
    simp [Set.indicator_apply]

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

/-- The code of the set of entries of a list is primitive recursive. -/
theorem equivBitIndices_symm_toFinset :
    Primrec fun l : List ℕ => Finset.equivBitIndices.symm l.toFinset := by
  -- add `2 ^ x` for each entry `x` whose bit is not yet set
  refine (list_foldr (h := fun _ (p : ℕ × ℕ) => bif p.2.testBit p.1 then p.2 else p.2 + 2 ^ p.1)
    .id (const 0) (cond (nat_testBit.comp (snd.comp snd) (fst.comp snd)) (snd.comp snd)
      (nat_add.comp (snd.comp snd) (nat_pow.comp (const 2) (fst.comp snd))))).of_eq fun l => ?_
  simp only [id]
  induction l with
  | nil => simp [Finset.equivBitIndices_symm_apply]
  | cons x l ih =>
    rw [List.foldr_cons, ih, List.toFinset_cons]
    by_cases hx : x ∈ l.toFinset <;>
      simp [hx, Finset.equivBitIndices_symm_apply, Finset.sum_insert, add_comm]

/-- The code `2 ^ n - 1` of `Finset.range n` is primitive recursive in `n`. -/
theorem equivBitIndices_symm_range :
    Primrec fun n => Finset.equivBitIndices.symm (Finset.range n) :=
  (equivBitIndices_symm_toFinset.comp list_range).of_eq fun n => by rw [List.toFinset_range]

/-- Binary codes of filtered initial intervals `(Finset.range (b a)).filter (p a)` are primitive
recursive, uniformly in the bound and predicate. -/
theorem equivBitIndices_symm_filter_range {α : Type*} [Primcodable α]
    {b : α → ℕ} {p : α → ℕ → Bool} (hb : Primrec b) (hp : Primrec₂ p) :
    Primrec fun a => Finset.equivBitIndices.symm ((Finset.range (b a)).filter fun x => p a x) := by
  refine (nat_filterBitIndices (equivBitIndices_symm_range.comp hb) hb hp).of_eq fun a => ?_
  apply Finset.equivBitIndices.injective
  rw [Nat.equivBitIndices_filterBitIndices, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact Finset.filter_congr fun x hx => by simp [Finset.mem_range.1 hx]

/-- Least-element search on binary finite-set codes is primitive recursive. -/
theorem nat_leastBitIndex : Primrec Nat.leastBitIndex :=
  (list_head?.comp nat_bitIndices).of_eq fun n => (Nat.leastBitIndex_def n).symm

/-- Binary coding of the values of a primitive recursive function on a coded finite set
is primitive recursive. -/
theorem equivBitIndices_symm_image {α : Type*} [Primcodable α]
    {f : α → ℕ → ℕ} {c : α → ℕ} (hf : Primrec₂ f) (hc : Primrec c) :
    Primrec fun a => Finset.equivBitIndices.symm ((Finset.equivBitIndices (c a)).image (f a)) := by
  refine (equivBitIndices_symm_toFinset.comp
    (list_map (nat_bitIndices.comp hc) hf)).of_eq fun a => ?_
  rw [Finset.equivBitIndices_apply, List.toFinset_map]

/-- A finite Cartesian product of two binary-coded sets has a primitive recursive
binary code using the canonical pairing of its entries. -/
theorem equivBitIndices_symm_product :
    Primrec₂ fun a b =>
      Finset.equivBitIndices.symm
        ((Finset.equivBitIndices a ×ˢ Finset.equivBitIndices b).map
          (Encodable.encode' (ℕ × ℕ))) := by
  have hlists := list_product.comp (nat_bitIndices.comp fst) (nat_bitIndices.comp snd)
  have hmap := list_map hlists ((Primrec.encode (α := ℕ × ℕ)).comp snd).to₂
  refine (equivBitIndices_symm_toFinset.comp hmap).to₂.of_eq fun a b => ?_
  congr 1
  ext n
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_map,
    Finset.equivBitIndices_apply, Encodable.encode']
  simp

/-- A disjoint sum of two binary-coded sets has a primitive recursive binary code
using even positions for the left side and odd positions for the right side. -/
theorem equivBitIndices_symm_disjSum :
    Primrec₂ fun a b =>
      Finset.equivBitIndices.symm
        (((Finset.equivBitIndices a).disjSum (Finset.equivBitIndices b)).map
          (Encodable.encode' (ℕ ⊕ ℕ))) := by
  have hleft := equivBitIndices_symm_image (α := ℕ × ℕ)
    (nat_mul.comp (const 2) snd).to₂ fst
  have hright := equivBitIndices_symm_image (α := ℕ × ℕ)
    (succ.comp (nat_mul.comp (const 2) snd)).to₂ snd
  refine (nat_lor.comp hleft hright).to₂.of_eq fun a b => ?_
  apply Finset.equivBitIndices.injective
  -- The primitive-recursion certificate uses `Nat.lor`, while the decoder uses the operator.
  rw [show Nat.lor = (· ||| ·) from rfl, Finset.equivBitIndices_lor]
  simp only [Equiv.apply_symm_apply]
  ext n
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_map, Finset.mem_disjSum,
    Encodable.encode']
  constructor
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨Sum.inl x, Or.inl ⟨x, hx, rfl⟩, rfl⟩
    · exact ⟨Sum.inr x, Or.inr ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩), rfl⟩
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩

end Primrec

namespace Set

/-- Membership in a finite subset of a primitive-codable type is primitive recursive. -/
theorem Finite.primrecPred {α : Type*} [Primcodable α] {A : Set α} (hA : A.Finite) :
    PrimrecPred (· ∈ A) := by
  classical
  exact (Primrec.eq.exists_mem_list.comp (Primrec.const (Set.Finite.toFinset hA).toList)
    Primrec.id).of_eq fun x => by simp

end Set
