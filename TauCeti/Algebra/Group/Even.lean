/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.Ring.Int.Parity

/-!
# Squares, powers and finite products

For integer powers of a common element `r` of a group, one of `r ^ m`, `r ^ n` and `r ^ m * r ^ n`
is a square (`TauCeti.isSquare_zpow_or_isSquare_zpow_or_isSquare_zpow_mul_zpow`), since one of
`m`, `n` and `m + n` is even.

A unit square factor does not change whether an element is a square
(`IsUnit.isSquare_sq_mul_iff`).

If all but the last entries of two finite families agree modulo squares, agreement of their
products modulo squares determines the last entry. This is useful when prescribing the last
coefficient of a diagonal quadratic form from its determinant. Similarly, if the full product over
a finset and every fiber away from a value `z` are squares in a commutative group, the remaining
fiber `k i = z` is also a square (`Finset.isSquare_prod_filter_of_isSquare_prod`).
-/

public section

namespace TauCeti

/-- For integer powers of a common element `r` of a group, one of `r ^ m`, `r ^ n` and
`r ^ m * r ^ n` is a square: one of `m`, `n` and `m + n` is even. -/
theorem isSquare_zpow_or_isSquare_zpow_or_isSquare_zpow_mul_zpow {G : Type*} [Group G] (r : G)
    (m n : ℤ) : IsSquare (r ^ m) ∨ IsSquare (r ^ n) ∨ IsSquare (r ^ m * r ^ n) := by
  obtain hm | hm := Int.even_or_odd m
  · exact .inl (hm.isSquare_zpow r)
  obtain hn | hn := Int.even_or_odd n
  · exact .inr (.inl (hn.isSquare_zpow r))
  · exact .inr (.inr (by rw [← zpow_add]; exact (hm.add_odd hn).isSquare_zpow r))

/-- Agreement modulo squares of two products over `s`, and of all their factors except the one
at `j ∈ s`, forces agreement of the factors at `j`. -/
theorem isSquare_div_of_isSquare_prod_div_prod
    {G ι : Type*} [CommGroup G] {s : Finset ι} {a b : ι → G} {j : ι} (hj : j ∈ s)
    (h : ∀ i ∈ s, i ≠ j → IsSquare (a i / b i))
    (hp : IsSquare ((∏ i ∈ s, a i) / ∏ i ∈ s, b i)) :
    IsSquare (a j / b j) := by
  classical
  rw [← s.mul_prod_erase a hj, ← s.mul_prod_erase b hj, mul_div_mul_comm,
    ← Finset.prod_div_distrib] at hp
  simpa using hp.div (Finset.isSquare_prod _ fun i hi ↦
    h i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi))

end TauCeti

/-- Multiplying by the square of a unit does not change whether an element is a square. -/
@[simp]
theorem IsUnit.isSquare_sq_mul_iff {M : Type*} [CommMonoid M] {u x : M} (hu : IsUnit u) :
    IsSquare (u ^ 2 * x) ↔ IsSquare x := by
  refine ⟨fun h ↦ ?_, fun ⟨r, hr⟩ ↦ ⟨u * r, by rw [hr, mul_mul_mul_comm, sq]⟩⟩
  have := (IsSquare.sq (↑hu.unit⁻¹ : M)).mul h
  rwa [← mul_assoc, ← mul_pow, hu.val_inv_mul, one_pow, one_mul] at this

namespace Finset

/-- In a commutative group, if the product of `w` over `s` is a square and its product over every
fiber `k i = m` with `m ≠ z` is a square, then its product over the fiber `k i = z` is a square. -/
theorem isSquare_prod_filter_of_isSquare_prod {G ι α : Type*} [CommGroup G] [DecidableEq α]
    (s : Finset ι) (k : ι → α) (w : ι → G) (z : α)
    (hfull : IsSquare (∏ i ∈ s, w i))
    (hne : ∀ m, m ≠ z → IsSquare (∏ i ∈ s with k i = m, w i)) :
    IsSquare (∏ i ∈ s with k i = z, w i) := by
  let P : Finset α := (s.image k).erase z
  have hsplit :
      ∏ i ∈ s, w i = (∏ i ∈ s with k i = z, w i) * ∏ m ∈ P, ∏ i ∈ s with k i = m, w i := by
    have hpart := (Finset.prod_fiberwise_of_maps_to (s := s) (g := k) (t := insert z P)
      (fun i hi ↦ by
        by_cases hkz : k i = z
        · simp [hkz]
        · exact Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨hkz, Finset.mem_image_of_mem k hi⟩))
      w).symm
    rw [hpart, Finset.prod_insert (Finset.notMem_erase z _)]
  have hP_sq : IsSquare (∏ m ∈ P, ∏ i ∈ s with k i = m, w i) :=
    Finset.isSquare_prod _ fun m hm ↦ hne m (Finset.ne_of_mem_erase hm)
  rw [hsplit] at hfull
  simpa [mul_inv_cancel_right] using hfull.mul hP_sq.inv

end Finset
