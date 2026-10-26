/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Multilinear.Basic
public import TauCeti.Probability.FreeProbability.Cumulant.Basic

/-!
# Multilinearity of free cumulants

Let `φ : A →ₗ[R] R` be a linear functional on an `R`-algebra `A`. Every position `i` of a finite
set `s` lies in exactly one part of a finite partition `P` of `s`, and appears exactly once in
the word read along that part. Hence the block moment `φ_P(a)` is linear in the entry `a i`,
and so is the free cumulant `κ_π(a)`, which is a linear combination of block moments by
Möbius inversion. In other words, the block moments and the free cumulants
`κ_n(a₁, …, aₙ)` are multilinear functionals of their arguments.

Multilinearity is the basic tool for computing with cumulants: it reduces cumulants of sums and
scalar multiples to cumulants of the summands, for example when splitting each argument into its
centred part and a multiple of `1`.

## Main definitions

For a finite linear order `α` of positions, such as `Fin n`, the functionals on words indexed by
all of `α` are bundled as multilinear maps `(α → A) → R`:

* `TauCeti.partitionMomentMultilinear φ P` — the block moment `a ↦ φ_P(a)`;
* `TauCeti.partitionCumulantMultilinear φ π` — the free cumulant `a ↦ κ_π(a)`;
* `TauCeti.freeCumulantMultilinear φ` — the free cumulant `a ↦ κ_α(a)`; for `α = Fin n` with
  `n ≥ 1` this is the `n`-th free cumulant `κ_n` as an element of
  `MultilinearMap R (fun _ : Fin n => A) R`.

## Main results

* `TauCeti.partitionMoment_update_add`, `TauCeti.partitionMoment_update_smul` — the block moment
  `φ_P(a)` is linear in each entry `a i` with `i ∈ s`.
* `TauCeti.partitionCumulant_update_add`, `TauCeti.partitionCumulant_update_smul`,
  `TauCeti.freeCumulant_update_add`, `TauCeti.freeCumulant_update_smul` — the free cumulants
  `κ_π(a)` and `κ_s(a)` are linear in each entry `a i` with `i ∈ s`.

## Implementation notes

The linearity of a block moment in a single entry is proved by writing the word of the part
containing that entry as a list, updated at one index via `List.Nodup.map_update`, and splitting
its product with `List.prod_set`. This follows the proof of multilinearity of ordered products in
Mathlib's `MultilinearMap.mkPiAlgebraFin`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 11.
-/

public section

open Finset Function

namespace TauCeti

variable {R A α : Type*} [LinearOrder α] {s : Finset α}

section Moment

variable [CommSemiring R] [Semiring A] [Algebra R A] (φ : A →ₗ[R] R) (a : α → A)

/-- Changing the entry at a position `i ∈ s` affects the block moment `φ_P(a)` only through the
moment of the part of `P` containing `i`, in which `a i` appears exactly once. -/
private theorem exists_partitionMoment_update (P : Finpartition s) {i : α} (hi : i ∈ s) :
    ∃ (p q : A) (c : R), ∀ x : A, partitionMoment φ (update a i x) P = φ (p * x * q) * c := by
  have hiB : i ∈ (P.part i).sort := mem_sort _ |>.2 (P.mem_part_self.2 hi)
  refine ⟨(((P.part i).sort.map a).take ((P.part i).sort.idxOf i)).prod,
    (((P.part i).sort.map a).drop ((P.part i).sort.idxOf i + 1)).prod,
    ∏ B ∈ P.parts.erase (P.part i), φ (B.sort.map a).prod, fun x => ?_⟩
  rw [partitionMoment_def, ← mul_prod_erase _ _ (P.part_mem.2 hi)]
  congr 1
  · rw [(sort_nodup _ _).map_update, ite_eq_left hiB, List.prod_set, List.length_map,
      ite_eq_left (List.idxOf_lt_length_iff.2 hiB)]
  · refine prod_congr rfl fun B hB => ?_
    have hiB : i ∉ B.sort := fun h =>
      (mem_erase.1 hB).1 (P.part_eq_of_mem (mem_erase.1 hB).2 ((mem_sort _).1 h)).symm
    rw [(sort_nodup _ _).map_update, ite_eq_right hiB]

/-- The block moment `φ_P(a)` is additive in each entry `a i` with `i ∈ s`. -/
@[simp]
theorem partitionMoment_update_add (P : Finpartition s) {i : α} (hi : i ∈ s) (x y : A) :
    partitionMoment φ (update a i (x + y)) P =
      partitionMoment φ (update a i x) P + partitionMoment φ (update a i y) P := by
  obtain ⟨p, q, c, h⟩ := exists_partitionMoment_update φ a P hi
  rw [h, h, h, mul_add, add_mul, map_add, add_mul]

/-- The block moment `φ_P(a)` is homogeneous in each entry `a i` with `i ∈ s`. -/
@[simp]
theorem partitionMoment_update_smul (P : Finpartition s) {i : α} (hi : i ∈ s) (c : R) (x : A) :
    partitionMoment φ (update a i (c • x)) P = c * partitionMoment φ (update a i x) P := by
  obtain ⟨p, q, d, h⟩ := exists_partitionMoment_update φ a P hi
  rw [h, h, mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul, mul_assoc]

end Moment

section Cumulant

variable [CommRing R] [Semiring A] [Algebra R A] (φ : A →ₗ[R] R) (a : α → A)

/-- The free cumulant `κ_π(a)` is additive in each entry `a i` with `i ∈ s`. -/
@[simp]
theorem partitionCumulant_update_add (π : NoncrossingPartition s) {i : α} (hi : i ∈ s)
    (x y : A) :
    partitionCumulant φ (update a i (x + y)) π =
      partitionCumulant φ (update a i x) π + partitionCumulant φ (update a i y) π := by
  simp only [partitionCumulant_def, partitionMoment_update_add φ a _ hi, mul_add,
    sum_add_distrib]

/-- The free cumulant `κ_π(a)` is homogeneous in each entry `a i` with `i ∈ s`. -/
@[simp]
theorem partitionCumulant_update_smul (π : NoncrossingPartition s) {i : α} (hi : i ∈ s)
    (c : R) (x : A) :
    partitionCumulant φ (update a i (c • x)) π = c * partitionCumulant φ (update a i x) π := by
  simp only [partitionCumulant_def, partitionMoment_update_smul φ a _ hi, mul_sum,
    mul_left_comm c]

/-- The free cumulant `κ_s(a)` of a word is additive in each entry `a i` with `i ∈ s`. -/
@[simp]
theorem freeCumulant_update_add {i : α} (hi : i ∈ s) (x y : A) :
    freeCumulant φ (update a i (x + y)) s =
      freeCumulant φ (update a i x) s + freeCumulant φ (update a i y) s := by
  simp only [freeCumulant_def, partitionCumulant_update_add φ a _ hi]

/-- The free cumulant `κ_s(a)` of a word is homogeneous in each entry `a i` with `i ∈ s`. -/
@[simp]
theorem freeCumulant_update_smul {i : α} (hi : i ∈ s) (c : R) (x : A) :
    freeCumulant φ (update a i (c • x)) s = c * freeCumulant φ (update a i x) s := by
  simp only [freeCumulant_def, partitionCumulant_update_smul φ a _ hi]

end Cumulant

section Multilinear

variable [Fintype α]

section Moment

variable [CommSemiring R] [Semiring A] [Algebra R A] (φ : A →ₗ[R] R)

/-- The block moment `a ↦ φ_P(a)` of a finite partition `P` of all positions of a finite linear
order `α`, as a multilinear map. -/
def partitionMomentMultilinear (P : Finpartition (univ : Finset α)) :
    MultilinearMap R (fun _ : α => A) R :=
  MultilinearMap.mk' (fun a => partitionMoment φ a P)
    (fun a _ x y => partitionMoment_update_add φ a P (mem_univ _) x y)
    (fun a _ c x => partitionMoment_update_smul φ a P (mem_univ _) c x)

/-- Evaluating the bundled block moment at a word gives its block moment. -/
@[simp]
theorem partitionMomentMultilinear_apply (P : Finpartition (univ : Finset α)) (a : α → A) :
    partitionMomentMultilinear φ P a = partitionMoment φ a P :=
  (rfl)

end Moment

section Cumulant

variable [CommRing R] [Semiring A] [Algebra R A] (φ : A →ₗ[R] R)

/-- The free cumulant `a ↦ κ_π(a)` of a noncrossing partition `π` of all positions of a finite
linear order `α`, as a multilinear map. -/
def partitionCumulantMultilinear (π : NoncrossingPartition (univ : Finset α)) :
    MultilinearMap R (fun _ : α => A) R :=
  MultilinearMap.mk' (fun a => partitionCumulant φ a π)
    (fun a _ x y => partitionCumulant_update_add φ a π (mem_univ _) x y)
    (fun a _ c x => partitionCumulant_update_smul φ a π (mem_univ _) c x)

/-- Evaluating the bundled free cumulant of `π` at a word gives its free cumulant. -/
@[simp]
theorem partitionCumulantMultilinear_apply (π : NoncrossingPartition (univ : Finset α))
    (a : α → A) : partitionCumulantMultilinear φ π a = partitionCumulant φ a π :=
  (rfl)

/-- The free cumulant `a ↦ κ_α(a)` of the words indexed by a finite linear order `α`, as a
multilinear map. For `α = Fin n` with `n ≥ 1` this is the `n`-th free cumulant
`κ_n(a₁, …, aₙ)`. -/
def freeCumulantMultilinear : MultilinearMap R (fun _ : α => A) R :=
  partitionCumulantMultilinear φ ⊤

/-- Evaluating the bundled free cumulant at a word gives the free cumulant of the whole word. -/
@[simp]
theorem freeCumulantMultilinear_apply (a : α → A) :
    freeCumulantMultilinear φ a = freeCumulant φ a univ := by
  rw [freeCumulantMultilinear, partitionCumulantMultilinear_apply, freeCumulant_def]

end Cumulant

end Multilinear

end TauCeti
