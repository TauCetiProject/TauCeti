/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Center
public import Mathlib.Algebra.Group.Units.Defs

/-!
# Centralizers, conjugation by units, and images of commutative magmas

Basic membership lemmas for `Set.centralizer`:

* `Set.conj_mem_centralizer`: if conjugation by the inverse of a unit `u` maps a set `S` of a
  monoid into itself, then conjugation by `u` maps the centralizer of `S` into itself. Applying
  this twice shows that a double commutant is preserved by every unit whose conjugations preserve
  the original set in both directions, which is how spatially implemented automorphisms extend to
  von Neumann algebras.
* `Set.apply_mem_centralizer_range` (and its additive counterpart
  `Set.apply_mem_addCentralizer_range`): every value of a multiplicative homomorphism from a
  commutative magma lies in the centralizer of its range.
-/

public section

namespace Set

section Monoid

variable {M : Type*} [Monoid M] {S : Set M}

/-- Conjugation by a unit `u` maps the centralizer of `S` into itself when conjugation by `u⁻¹`
maps `S` into itself. -/
theorem conj_mem_centralizer (u : Mˣ) (hS : ∀ s ∈ S, ↑u⁻¹ * s * ↑u ∈ S) {x : M}
    (hx : x ∈ S.centralizer) : ↑u * x * ↑u⁻¹ ∈ S.centralizer := by
  intro s hs
  have h := hx _ (hS s hs)
  calc s * (↑u * x * ↑u⁻¹) = ↑u * ((↑u⁻¹ * s * ↑u) * x) * ↑u⁻¹ := by
        simp only [mul_assoc, Units.mul_inv_cancel_left]
    _ = ↑u * (x * (↑u⁻¹ * s * ↑u)) * ↑u⁻¹ := by rw [h]
    _ = ↑u * x * ↑u⁻¹ * s := by
        simp only [mul_assoc, Units.mul_inv, mul_one]

end Monoid

/-- Every value of a multiplicative homomorphism from a commutative magma lies in the centralizer
of its range. -/
@[to_additive (attr := simp) apply_mem_addCentralizer_range
  /-- Every value of an additive homomorphism from a commutative additive magma lies in the
  additive centralizer of its range. -/]
theorem apply_mem_centralizer_range {F M N : Type*} [Mul M] [IsMulCommutative M] [Mul N]
    [FunLike F M N] [MulHomClass F M N] (f : F) (x : M) :
    f x ∈ Set.centralizer (Set.range f) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨y, rfl⟩
  rw [← map_mul, mul_comm' y x, map_mul]

end Set
