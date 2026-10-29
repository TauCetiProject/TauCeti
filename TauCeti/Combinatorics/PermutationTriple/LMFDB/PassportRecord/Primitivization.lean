/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.BlockQuotient
public import TauCeti.Combinatorics.PermutationTriple.LMFDB.BelyiRecord
public import TauCeti.Combinatorics.PermutationTriple.LMFDB.PassportRecord.Basic

/-!
# The primitivization of a passport record

The stored primitivization of a row of the LMFDB table of Belyi passports is the label of a row of
the table of Belyi maps. Here that row is read as sharing the passport of the block quotient of the
chosen reference triple; this does not identify a particular quotient map, and it does not assert
that every map of the passport factors through a map of that row.
A valid passport row carries a block of sheets of its reference triple `t`, and a maximal proper
one (`TauCeti.PermutationTriple.LMFDB.PassportRecord.IsValidAt`). This file ties the stored label
to the mathematics through that block rather than through a label lookup:
`TauCeti.PermutationTriple.LMFDB.BelyiRecord.IsPrimitivizationOf q r t` says that the map row `q`
carries the stored primitivization label of `r`, and that it is a valid row for the passport of
the quotient of `t` by the translates of the stored block
(`TauCeti.PermutationTriple.blockQuotient`).
Geometrically, the cover described by `t` factors through the cover described by the quotient, and
the fibres of the intermediate map are the translates of the block.

A primitivization is not canonical: a triple can have several maximal block systems. The row `q`
certifies the one chosen by the stored block, and nothing here asserts that another choice gives
the same passport.

The consequences read the stored fields of the two rows against each other: the stored triples of
`q` are primitive, because the stored block is maximal; the degree of `r` is the size of the block
times the degree of `q`; the stored genus of `q` is at most that of `r`; and the stored primitivity
flag of `r` is set exactly when `q` has the same degree as `r`, so that a primitive passport is
its own primitivization in degree.

## Main definitions

* `TauCeti.PermutationTriple.LMFDB.BelyiRecord.IsPrimitivizationOf`: a map row certifies the
  stored primitivization of a passport row.

## Main results

* `TauCeti.PermutationTriple.LMFDB.BelyiRecord.IsPrimitivizationOf.isPrimitive_toTriple`: the
  stored triples of the primitivization are primitive.
* `TauCeti.PermutationTriple.LMFDB.BelyiRecord.IsPrimitivizationOf.card_mul_deg`: the degree of a
  passport row is the size of its primitivization block times the degree of its primitivization.
* `TauCeti.PermutationTriple.LMFDB.BelyiRecord.IsPrimitivizationOf.g_le`: the primitivization has
  genus at most that of the passport.
* `TauCeti.PermutationTriple.LMFDB.BelyiRecord.IsPrimitivizationOf.isPrimitive_eq_true_iff`: the
  stored primitivity flag is set exactly when the primitivization has the same degree.

## References

* M. Musty, S. Schiavone, J. Sijsling, J. Voight, *A database of Belyi maps*.
* LMFDB, [Belyi maps](https://www.lmfdb.org/Belyi/).
-/

open Equiv MulAction
open scoped Pointwise

public section

namespace TauCeti
namespace PermutationTriple
namespace LMFDB

namespace BelyiRecord

variable {n m : ℕ}

/-- The map row `q` certifies the stored primitivization of the passport row `r` at the connected
triple `t`: the label of `q` is the stored primitivization label of `r`, and, for some numbering of
the translates of the primitivization block of `r` by the sheets of `q`, the row `q` is valid for
the passport of the quotient of `t` by those translates. -/
structure IsPrimitivizationOf (q : BelyiRecord m) (r : PassportRecord n) (t : ConnectedTriple n) :
    Prop where
  /-- The label of the map row is the stored primitivization label. -/
  label_eq : q.label = r.primitivization
  /-- The map row is valid for the passport of the quotient by the primitivization block. -/
  exists_isValidFor :
    ∃ e : orbit t.1.monodromyGroup (r.primitivizationBlock : Set (Fin n)) ≃ Fin m,
      q.IsValidFor
        (ConnectedTriple.passportOf ⟨t.1.blockQuotient _ e, t.1.isConnected_blockQuotient _ e⟩)

namespace IsPrimitivizationOf

variable {q : BelyiRecord m} {r : PassportRecord n} {t : ConnectedTriple n}

/-- The stored triples of the primitivization of a valid passport row denote primitive triples:
the quotient by a maximal proper block is primitive. -/
theorem isPrimitive_toTriple (hr : r.IsValidAt t) (h : q.IsPrimitivizationOf r t)
    {s : StoredTriple m} (hs : s ∈ q.triples) : s.toTriple.IsPrimitive := by
  obtain ⟨e, hq⟩ := h.exists_isValidFor
  obtain ⟨hsc, hsP⟩ := hq.hasPassport s hs
  refine (PassportSpec.isPrimitive_iff_of_hasPassport (ConnectedTriple.hasPassport_passportOf _)
    hsP).mp ?_
  exact (isPrimitive_blockQuotient_iff e t.2.isPretransitive hr.isBlock_primitivizationBlock
    (Finset.coe_nonempty.mpr hr.primitivizationBlock_nonempty)).mpr
    hr.eq_or_eq_univ_of_primitivizationBlock_subset

/-- The degree of a valid passport row is the size of its primitivization block times the degree
of its primitivization. -/
theorem card_mul_deg (hr : r.IsValidAt t) (h : q.IsPrimitivizationOf r t) :
    r.primitivizationBlock.card * q.deg = r.deg := by
  obtain ⟨e, hq⟩ := h.exists_isValidFor
  rw [hq.deg_eq, hr.deg_eq, ← Set.ncard_coe_finset]
  exact ncard_mul_eq_of_isBlock t.2.isPretransitive hr.isBlock_primitivizationBlock
    (Finset.coe_nonempty.mpr hr.primitivizationBlock_nonempty) e

/-- The stored genus of the primitivization of a valid passport row is at most the stored genus of
the passport row: passing to a block quotient does not increase the genus. -/
theorem g_le (hr : r.IsValidAt t) (h : q.IsPrimitivizationOf r t) : q.g ≤ r.g := by
  obtain ⟨e, hq⟩ := h.exists_isValidFor
  rw [hq.g_eq_genus (ConnectedTriple.hasPassport_passportOf _), hr.g_eq]
  exact genus_blockQuotient_le e hr.isBlock_primitivizationBlock
    (Finset.coe_nonempty.mpr hr.primitivizationBlock_nonempty) t.2

/-- The stored primitivity flag of a valid passport row is set exactly when its primitivization
has the same degree, that is, when the primitivization block is a single sheet. -/
theorem isPrimitive_eq_true_iff (hr : r.IsValidAt t) (h : q.IsPrimitivizationOf r t) :
    r.isPrimitive = true ↔ q.deg = r.deg := by
  have := t.2.isPretransitive
  have hmul := h.card_mul_deg hr
  have hn : r.deg ≠ 0 := by
    rw [hr.deg_eq]
    exact t.2.ne_zero
  have hB := hr.isBlock_primitivizationBlock
  have hmax := hr.eq_or_eq_univ_of_primitivizationBlock_subset
  rw [hr.isPrimitive_eq_true_iff, isPrimitive_iff]
  constructor
  · -- A maximal proper block of a primitive action is a single sheet, unless there is only one.
    intro hprim
    suffices r.primitivizationBlock.card = 1 by rwa [this, one_mul] at hmul
    rcases hprim.isTrivialBlock_of_isBlock hB with hsub | huniv
    · obtain ⟨x, hx⟩ := hr.primitivizationBlock_nonempty
      rw [Finset.card_eq_one]
      exact ⟨x, Finset.coe_injective (by simpa using hsub.eq_singleton_of_mem hx)⟩
    · have huniv : r.primitivizationBlock = Finset.univ := Finset.coe_eq_univ.mp huniv
      rw [huniv, Finset.card_univ, Fintype.card_fin]
      exact hr.deg_eq_one_of_primitivizationBlock_eq_univ huniv
  · -- A single sheet that is a maximal block shows that every block through it is trivial.
    intro hdeg
    rw [hdeg, Nat.mul_eq_right hn, Finset.card_eq_one] at hmul
    obtain ⟨x, hx⟩ := hmul
    refine IsPreprimitive.of_isTrivialBlock_base x fun {C} hxC hC ↦ ?_
    rcases hmax C hC (by simpa [hx] using hxC) with h | h
    · exact Or.inl (h ▸ by simp [hx])
    · exact Or.inr h

end IsPrimitivizationOf

end BelyiRecord

end LMFDB
end PermutationTriple
end TauCeti
