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
(`IsUnit.isSquare_sq_mul_iff`), and neither does a multiplicative equivalence
(`MulEquiv.isSquare_apply_iff`, with additive version `AddEquiv.even_apply_iff`).

If all but the last entries of two finite families agree modulo squares, agreement of their
products modulo squares determines the last entry. This is useful when prescribing the last
coefficient of a diagonal quadratic form from its determinant.
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

/-- A multiplicative equivalence preserves and reflects squares. -/
@[to_additive (attr := simp) /-- An additive equivalence preserves and reflects even elements. -/]
theorem MulEquiv.isSquare_apply_iff {F α β : Type*} [Mul α] [Mul β] [EquivLike F α β]
    [MulEquivClass F α β] (e : F) {a : α} : IsSquare (e a) ↔ IsSquare a :=
  ⟨fun ⟨r, hr⟩ ↦ ⟨EquivLike.inv e r, EquivLike.injective e <| by
      rw [map_mul, EquivLike.apply_inv_apply, hr]⟩,
    fun ⟨r, hr⟩ ↦ ⟨e r, by rw [hr, map_mul]⟩⟩
