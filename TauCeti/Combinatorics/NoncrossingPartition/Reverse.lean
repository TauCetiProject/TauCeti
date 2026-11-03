/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Rev
public import TauCeti.Combinatorics.NoncrossingPartition.Basic

/-!
# Reversal of noncrossing partitions

The permutation `Fin.rev` of `Fin n` sends each position `i` to `n - 1 - i`, so it reverses the
order of the positions. A crossing `a < b < c < d` between two parts becomes the crossing
`rev d < rev c < rev b < rev a` between the same two parts, so moving every part of a noncrossing
partition of `Fin n` along `Fin.rev` gives a noncrossing partition. This is an involutive order
automorphism of the lattice `NC(n)`: the reversal of `NC(n)`.

Reversal is the combinatorial side of taking adjoints of words: the adjoint of a product
`a₁ * ⋯ * aₙ` is the product `star aₙ * ⋯ * star a₁` of the adjoints in reversed order.

## Main definitions

* `TauCeti.NoncrossingPartition.reverse n` — the order automorphism of `NC(n)` whose value on `π`
  has the parts `Fin.rev '' B` for the parts `B` of `π`.

## Main results

* `TauCeti.NoncrossingPartition.parts_reverse` — the parts of `reverse n π` are the images of the
  parts of `π` under `Fin.rev`.
* `TauCeti.NoncrossingPartition.reverse_reverse` and `TauCeti.NoncrossingPartition.reverse_symm`
  — the reversal is an involution.
* `TauCeti.NoncrossingPartition.prod_parts_reverse` — a product over the parts of `reverse n π` is
  the product over the parts `B` of `π` evaluated at the reversed parts.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 9.
-/

public section

open Finset

namespace TauCeti.NoncrossingPartition

variable {n : ℕ}

/-- Pulling a noncrossing partition of `Fin n` back along the order-reversing permutation
`Fin.revPerm` gives a noncrossing partition. -/
private theorem isNoncrossing_comap_copy_revPerm {P : Finpartition (univ : Finset (Fin n))}
    (hP : P.IsNoncrossing) :
    ((P.copy (image_univ_equiv Fin.revPerm).symm).comap Fin.revPerm).IsNoncrossing := by
  rw [Finpartition.isNoncrossing_iff, Finpartition.parts_comap]
  intro X hX Y hY a ha b hb c hc d hd hab hbc hcd
  obtain ⟨C, hC, rfl⟩ := mem_image.1 hX
  obtain ⟨D, hD, rfl⟩ := mem_image.1 hY
  simp only [mem_filter, mem_univ, true_and, Fin.revPerm_apply] at ha hb hc hd
  rw [Finpartition.copy_parts] at hC hD
  -- The crossing `a < b < c < d` becomes the crossing `rev d < rev c < rev b < rev a`.
  rw [(Finpartition.isNoncrossing_iff.1 hP D hD C hC _ hd _ hc _ hb _ ha (Fin.rev_lt_rev.2 hcd)
    (Fin.rev_lt_rev.2 hbc) (Fin.rev_lt_rev.2 hab))]

/-- The *reversal* of noncrossing partitions of `Fin n`: each part `B` of `π` is moved along
`Fin.rev`, which sends `i` to `n - 1 - i`, to the part `Fin.rev '' B` of `reverse n π`. -/
def reverse (n : ℕ) :
    NoncrossingPartition (univ : Finset (Fin n)) ≃o NoncrossingPartition (univ : Finset (Fin n))
    where
  toFun π := ⟨(π.1.copy (image_univ_equiv Fin.revPerm).symm).comap Fin.revPerm,
    isNoncrossing_comap_copy_revPerm π.2⟩
  invFun π := ⟨(π.1.copy (image_univ_equiv Fin.revPerm).symm).comap Fin.revPerm,
    isNoncrossing_comap_copy_revPerm π.2⟩
  left_inv π := Subtype.ext <| Finpartition.ext <| by
    simp [Finpartition.parts_comap_copy_equiv, image_image, map_eq_image, Function.comp_def]
  right_inv π := Subtype.ext <| Finpartition.ext <| by
    simp [Finpartition.parts_comap_copy_equiv, image_image, map_eq_image, Function.comp_def]
  map_rel_iff' := Finpartition.comap_le_comap_iff

/-- The parts of the reversal `reverse n π` are the images of the parts of `π` under
`Fin.rev`. -/
@[simp]
theorem parts_reverse (π : NoncrossingPartition (univ : Finset (Fin n))) :
    (reverse n π).1.parts = π.1.parts.image fun B => B.map Fin.revPerm.toEmbedding :=
  Finpartition.parts_comap_copy_equiv π.1 Fin.revPerm

/-- The reversal of noncrossing partitions is its own inverse. -/
@[simp]
theorem reverse_symm : (reverse n).symm = reverse n :=
  -- The inverse of `reverse n` is defined by the same formula as `reverse n`.
  OrderIso.ext rfl

/-- The reversal of noncrossing partitions is an involution. -/
@[simp]
theorem reverse_reverse (π : NoncrossingPartition (univ : Finset (Fin n))) :
    reverse n (reverse n π) = π := by
  simpa using (reverse n).symm_apply_apply π

/-- A product over the parts of the reversal `reverse n π` is the product over the parts `B` of
`π` evaluated at the reversed parts `Fin.rev '' B`. -/
theorem prod_parts_reverse {M : Type*} [CommMonoid M]
    (π : NoncrossingPartition (univ : Finset (Fin n))) (g : Finset (Fin n) → M) :
    ∏ B ∈ (reverse n π).1.parts, g B = ∏ B ∈ π.1.parts, g (B.map Fin.revPerm.toEmbedding) := by
  rw [parts_reverse, prod_image fun B _ C _ h => map_injective _ h]

end TauCeti.NoncrossingPartition
