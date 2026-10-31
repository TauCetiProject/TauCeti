/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Rotate
public import TauCeti.Combinatorics.NoncrossingPartition.Basic

/-!
# Rotation of noncrossing partitions

The permutation `finRotate n` of `Fin n` moves each position `i` to `i + 1` and the last
position to `0`. Placing the positions `0, …, n - 1` around a circle, it turns the circle by one
step, so it preserves the cyclic order of any four positions. Since a crossing `a < b < c < d`
between two parts depends only on the cyclic order of `a, b, c, d`, moving every part of a
noncrossing partition of `Fin n` along `finRotate n` gives a noncrossing partition. This is an
order automorphism of the lattice `NC(n)`: the rotation of `NC(n)`.

## Main definitions

* `TauCeti.NoncrossingPartition.rotate n` — the order automorphism of `NC(n)` whose value on `π`
  has the parts `finRotate n '' B` for the parts `B` of `π`.

## Main results

* `TauCeti.NoncrossingPartition.parts_rotate` and
  `TauCeti.NoncrossingPartition.parts_rotate_symm` — the parts of `rotate n π` are the images of
  the parts of `π` under `finRotate n`, and those of `(rotate n).symm π` their images under its
  inverse.
* `TauCeti.NoncrossingPartition.mem_part_rotate` and
  `TauCeti.NoncrossingPartition.mem_part_rotate_symm` — two positions lie in a common part of
  `rotate n π` (of `(rotate n).symm π`) exactly when the positions before (after) them lie in a
  common part of `π`.
* `TauCeti.NoncrossingPartition.prod_parts_rotate` — a product over the parts of `rotate n π` is
  the product over the parts `B` of `π` evaluated at the rotated parts.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 9.
-/

public section

open Finset

namespace TauCeti.NoncrossingPartition

variable {n : ℕ}

/-- A permutation `g` of `Fin n` preserves the cyclic order of every four positions
`a < b < c < d`: their images are increasing up to a cyclic shift that starts at `g a`, `g d` or
`g b`. -/
private def PreservesCyclicOrder (g : Fin n ≃ Fin n) : Prop :=
  ∀ a b c d : Fin n, a < b → b < c → c < d →
    (g a < g b ∧ g b < g c ∧ g c < g d) ∨ (g d < g a ∧ g a < g b ∧ g b < g c) ∨
      (g b < g c ∧ g c < g d ∧ g d < g a)

/-- Pulling a noncrossing partition back along a permutation that preserves the cyclic order of
every four positions gives a noncrossing partition. -/
private theorem isNoncrossing_comap_copy {P : Finpartition (univ : Finset (Fin n))}
    (hP : P.IsNoncrossing) {g : Fin n ≃ Fin n} (hg : PreservesCyclicOrder g) :
    ((P.copy (image_univ_equiv g).symm).comap g).IsNoncrossing := by
  rw [Finpartition.isNoncrossing_iff, Finpartition.parts_comap]
  intro X hX Y hY a ha b hb c hc d hd hab hbc hcd
  obtain ⟨C, hC, rfl⟩ := mem_image.1 hX
  obtain ⟨D, hD, rfl⟩ := mem_image.1 hY
  simp only [mem_filter, mem_univ, true_and] at ha hb hc hd
  rw [Finpartition.copy_parts] at hC hD
  suffices C = D by rw [this]
  rw [Finpartition.isNoncrossing_iff] at hP
  rcases hg a b c d hab hbc hcd with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩
  · exact hP C hC D hD _ ha _ hb _ hc _ hd h₁ h₂ h₃
  · exact (hP D hD C hC _ hd _ ha _ hb _ hc h₁ h₂ h₃).symm
  · exact (hP D hD C hC _ hb _ hc _ hd _ ha h₁ h₂ h₃).symm

/-- The rotation `i ↦ i + 1` preserves the cyclic order of positions. -/
private theorem preservesCyclicOrder_finRotate : PreservesCyclicOrder (finRotate n) := by
  intro a b c d hab hbc hcd
  cases n with
  | zero => exact a.elim0
  | succ n =>
    have ha := coe_finRotate_of_ne_last (Fin.ne_last_of_lt (hab.trans (hbc.trans hcd)))
    have hb := coe_finRotate_of_ne_last (Fin.ne_last_of_lt (hbc.trans hcd))
    have hc := coe_finRotate_of_ne_last (Fin.ne_last_of_lt hcd)
    rw [Fin.lt_def] at hab hbc hcd
    by_cases hd : d = Fin.last n
    · subst hd
      right; left
      simp only [Fin.lt_def, ha, hb, hc, finRotate_last, Fin.val_zero]
      omega
    · left
      simp only [Fin.lt_def, ha, hb, hc, coe_finRotate_of_ne_last hd]
      omega

/-- The rotation `i ↦ i - 1` preserves the cyclic order of positions. -/
private theorem preservesCyclicOrder_finRotate_symm : PreservesCyclicOrder (finRotate n).symm := by
  intro a b c d hab hbc hcd
  cases n with
  | zero => exact a.elim0
  | succ n =>
    have hb := coe_finRotate_symm_of_ne_zero (a.zero_le.trans_lt hab).ne'
    have hc := coe_finRotate_symm_of_ne_zero (a.zero_le.trans_lt (hab.trans hbc)).ne'
    have hd := coe_finRotate_symm_of_ne_zero (a.zero_le.trans_lt (hab.trans (hbc.trans hcd))).ne'
    have hdn := d.is_lt
    rw [Fin.lt_def] at hab hbc hcd
    by_cases ha : a = 0
    · subst ha
      have ha : (finRotate (n + 1)).symm 0 = Fin.last n :=
        (finRotate (n + 1)).symm_apply_eq.2 finRotate_last.symm
      right; right
      simp only [Fin.lt_def, ha, hb, hc, hd, Fin.val_last, Fin.val_zero] at hab ⊢
      omega
    · have ha' : (a : ℕ) ≠ 0 := fun h => ha (Fin.ext (by rw [h, Fin.val_zero]))
      left
      simp only [Fin.lt_def, hb, hc, hd, coe_finRotate_symm_of_ne_zero ha]
      omega

/-- The *rotation* of noncrossing partitions of `Fin n`: each part `B` of `π` is moved along
`i ↦ i + 1` (with the last position going to `0`) to the part `finRotate n '' B` of
`rotate n π`. -/
def rotate (n : ℕ) :
    NoncrossingPartition (univ : Finset (Fin n)) ≃o NoncrossingPartition (univ : Finset (Fin n))
    where
  toFun π := ⟨(π.1.copy (image_univ_equiv (finRotate n).symm).symm).comap (finRotate n).symm,
    isNoncrossing_comap_copy π.2 preservesCyclicOrder_finRotate_symm⟩
  invFun π := ⟨(π.1.copy (image_univ_equiv (finRotate n)).symm).comap (finRotate n),
    isNoncrossing_comap_copy π.2 preservesCyclicOrder_finRotate⟩
  left_inv π := Subtype.ext <| Finpartition.ext <| by
    simp only [Finpartition.parts_comap_copy_equiv, image_image, Function.comp_def, map_map]
    simp
  right_inv π := Subtype.ext <| Finpartition.ext <| by
    simp only [Finpartition.parts_comap_copy_equiv, image_image, Function.comp_def, map_map]
    simp
  map_rel_iff' := Finpartition.comap_le_comap_iff

/-- The parts of the rotation `rotate n π` are the images of the parts of `π` under
`finRotate n`. -/
@[simp]
theorem parts_rotate (π : NoncrossingPartition (univ : Finset (Fin n))) :
    (rotate n π).1.parts = π.1.parts.image fun B => B.map (finRotate n).toEmbedding :=
  Finpartition.parts_comap_copy_equiv π.1 (finRotate n).symm

/-- The parts of the inverse rotation `(rotate n).symm π` are the images of the parts of `π` under
`(finRotate n).symm`. -/
@[simp]
theorem parts_rotate_symm (π : NoncrossingPartition (univ : Finset (Fin n))) :
    ((rotate n).symm π).1.parts = π.1.parts.image fun B => B.map (finRotate n).symm.toEmbedding :=
  Finpartition.parts_comap_copy_equiv π.1 (finRotate n)

/-- Two positions lie in a common part of the rotation `rotate n π` exactly when the positions
before them lie in a common part of `π`. -/
@[simp]
theorem mem_part_rotate (π : NoncrossingPartition (univ : Finset (Fin n))) {x y : Fin n} :
    y ∈ (rotate n π).1.part x ↔ (finRotate n).symm y ∈ π.1.part ((finRotate n).symm x) := by
  simp only [Finpartition.mem_part_iff_exists, parts_rotate, mem_image, exists_exists_and_eq_and,
    mem_map_equiv]

/-- Two positions lie in a common part of the inverse rotation `(rotate n).symm π` exactly when
the positions after them lie in a common part of `π`. -/
@[simp]
theorem mem_part_rotate_symm (π : NoncrossingPartition (univ : Finset (Fin n))) {x y : Fin n} :
    y ∈ ((rotate n).symm π).1.part x ↔ finRotate n y ∈ π.1.part (finRotate n x) := by
  simp only [Finpartition.mem_part_iff_exists, parts_rotate_symm, mem_image,
    exists_exists_and_eq_and, mem_map_equiv, Equiv.symm_symm]

/-- A product over the parts of the rotation `rotate n π` is the product over the parts `B` of `π`
evaluated at the rotated parts `finRotate n '' B`. -/
theorem prod_parts_rotate {M : Type*} [CommMonoid M]
    (π : NoncrossingPartition (univ : Finset (Fin n))) (g : Finset (Fin n) → M) :
    ∏ B ∈ (rotate n π).1.parts, g B = ∏ B ∈ π.1.parts, g (B.map (finRotate n).toEmbedding) := by
  rw [parts_rotate, prod_image fun B _ C _ h => map_injective _ h]

end TauCeti.NoncrossingPartition
