/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.End
public import TauCeti.Combinatorics.NoncrossingPartition.Rotate
public import TauCeti.Probability.FreeProbability.Cumulant.Basic

/-!
# Cyclic invariance of free cumulants under a trace

Free cumulants are defined from block moments by Möbius inversion on the lattice of noncrossing
partitions, so they transport along any order isomorphism `NC(s) ≃o NC(t)` that matches the block
moments of two words: the cumulants then match as well
(`TauCeti.partitionCumulant_eq_of_orderIso`). In particular the free cumulants of the two words
agree (`TauCeti.freeCumulant_eq_of_orderIso`).

The main application is to a *tracial* functional, `φ (x * y) = φ (y * x)`. Rotating the letters
of a word `a₁, …, aₙ` to `a₂, …, aₙ, a₁`, that is precomposing `a` with `finRotate n`, changes each
block moment `φ_π` into the block moment of the rotated partition `rotate n π`: a block `B` of `π`
not containing the last position is read in the same order after rotation, and a block containing
it has its last letter moved to the front, which does not change its moment under a trace. Hence
the free cumulants of a trace are invariant under cyclic rotation of their arguments,
`κ_n(a₂, …, aₙ, a₁) = κ_n(a₁, …, aₙ)`.

## Main results

* `TauCeti.partitionCumulant_eq_of_orderIso` and `TauCeti.freeCumulant_eq_of_orderIso` — free
  cumulants transport along order isomorphisms of noncrossing partition lattices that match block
  moments.
* `TauCeti.partitionMoment_comp_finRotate` and `TauCeti.partitionCumulant_comp_finRotate` — for a
  tracial `φ`, rotating the word rotates the partition.
* `TauCeti.freeCumulant_comp_finRotate` — free cumulants of a tracial `φ` are invariant under
  cyclic rotation of their arguments, and `TauCeti.freeCumulant_comp_finRotate_pow` under every
  power of the rotation.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 11.
-/

public section

open Finset

namespace TauCeti

variable {R A : Type*} [CommRing R] [Monoid A] (φ : A → R)

section OrderIso

variable {α β : Type*} [LinearOrder α] [LinearOrder β] {s : Finset α} {t : Finset β}
  {a : α → A} {b : β → A}

/-- Free cumulants transport along an order isomorphism `e : NC(s) ≃o NC(t)` that matches the
block moments of two words: if `φ_π(a) = φ_{e π}(b)` for every `π`, then
`κ_π(a) = κ_{e π}(b)`. -/
theorem partitionCumulant_eq_of_orderIso (e : NoncrossingPartition s ≃o NoncrossingPartition t)
    (h : ∀ π, partitionMoment φ a π.1 = partitionMoment φ b (e π).1)
    (π : NoncrossingPartition s) : partitionCumulant φ a π = partitionCumulant φ b (e π) := by
  refine (congrFun (eq_partitionCumulant_of_forall_sum_Iic φ a
    (fun π => partitionCumulant φ b (e π)) fun π => ?_) π).symm
  rw [h, ← sum_Iic_partitionCumulant φ b (e π)]
  exact sum_equiv e.toEquiv (fun σ => by simp) fun _ _ => rfl

/-- Free cumulants of two words agree when an order isomorphism `NC(s) ≃o NC(t)` matches their
block moments. -/
theorem freeCumulant_eq_of_orderIso (e : NoncrossingPartition s ≃o NoncrossingPartition t)
    (h : ∀ π, partitionMoment φ a π.1 = partitionMoment φ b (e π).1) :
    freeCumulant φ a s = freeCumulant φ b t := by
  rw [freeCumulant_def, partitionCumulant_eq_of_orderIso φ e h, e.map_top, freeCumulant_def]

end OrderIso

section Rotate

variable {n : ℕ} {φ}

/-- For a tracial `φ`, rotating the letters of a word `a₁, …, aₙ` to `a₂, …, aₙ, a₁` changes the
block moment of a noncrossing partition `π` into the block moment of the rotated partition
`rotate n π`. -/
theorem partitionMoment_comp_finRotate (hφ : ∀ x y, φ (x * y) = φ (y * x)) (a : Fin n → A)
    (π : NoncrossingPartition (univ : Finset (Fin n))) :
    partitionMoment φ (a ∘ finRotate n) π.1 =
      partitionMoment φ a (NoncrossingPartition.rotate n π).1 := by
  rw [partitionMoment_def, partitionMoment_def, NoncrossingPartition.prod_parts_rotate]
  refine prod_congr rfl fun B _ => ?_
  -- The two words along `B` differ by a cyclic rotation, which a trace does not see.
  obtain ⟨k, hk⟩ := (B.isRotated_sort_map_finRotate).map a
  rw [← List.map_map, ← hk, List.rotate_eq_drop_append_take_mod, List.prod_append, hφ,
    ← List.prod_append, List.take_append_drop]

/-- For a tracial `φ`, rotating the letters of a word `a₁, …, aₙ` to `a₂, …, aₙ, a₁` changes the
free cumulant of a noncrossing partition `π` into that of the rotated partition `rotate n π`. -/
theorem partitionCumulant_comp_finRotate (hφ : ∀ x y, φ (x * y) = φ (y * x)) (a : Fin n → A)
    (π : NoncrossingPartition (univ : Finset (Fin n))) :
    partitionCumulant φ (a ∘ finRotate n) π =
      partitionCumulant φ a (NoncrossingPartition.rotate n π) :=
  partitionCumulant_eq_of_orderIso φ _ (partitionMoment_comp_finRotate hφ a) π

/-- **Cyclic invariance of free cumulants.** For a tracial `φ`, the free cumulants are invariant
under cyclic rotation of their arguments, `κ_n(a₂, …, aₙ, a₁) = κ_n(a₁, …, aₙ)`. -/
theorem freeCumulant_comp_finRotate (hφ : ∀ x y, φ (x * y) = φ (y * x)) (a : Fin n → A) :
    freeCumulant φ (a ∘ finRotate n) univ = freeCumulant φ a univ :=
  freeCumulant_eq_of_orderIso φ _ (partitionMoment_comp_finRotate hφ a)

/-- For a tracial `φ`, the free cumulants are invariant under every cyclic rotation of their
arguments, `κ_n(a_{k+1}, …, aₙ, a₁, …, a_k) = κ_n(a₁, …, aₙ)`. -/
theorem freeCumulant_comp_finRotate_pow (hφ : ∀ x y, φ (x * y) = φ (y * x)) (a : Fin n → A)
    (k : ℕ) : freeCumulant φ (a ∘ ⇑(finRotate n ^ k)) univ = freeCumulant φ a univ := by
  rw [Equiv.Perm.coe_pow]
  induction k with
  | zero => rw [Function.iterate_zero, Function.comp_id]
  | succ k ih =>
    rw [Function.iterate_succ, ← Function.comp_assoc, freeCumulant_comp_finRotate hφ, ih]

end Rotate

end TauCeti
