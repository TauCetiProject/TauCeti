/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Center
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Units.Defs

/-!
# Centralizers, equivalences, and conjugation by units

Multiplicative equivalences commute with taking centralizers of subsets
(`MulEquivClass.centralizer_image`). Moreover, if conjugation by the inverse of a unit `u` maps a
set `S` of a monoid into itself, then conjugation by `u` maps the centralizer of `S` into itself.
Applying either fact twice shows that double commutants are transported by multiplicative
equivalences and preserved by units whose conjugations preserve the generating set in both
directions, which is how spatial unitary equivalences act on von Neumann algebras.
-/

public section

namespace MulEquivClass

/-- A multiplicative equivalence transports the centralizer of a subset to the centralizer of its
image. -/
@[to_additive /-- An additive equivalence transports the centralizer of a subset to the centralizer
of its image. -/]
theorem centralizer_image {F M N : Type*} [Mul M] [Mul N] [EquivLike F M N]
    [MulEquivClass F M N] (e : F) (S : Set M) :
    (e '' S).centralizer = e '' S.centralizer := by
  ext y
  obtain ⟨x, rfl⟩ := EquivLike.surjective e y
  simp only [Set.mem_centralizer_iff, Set.mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, ← map_mul, (EquivLike.injective e).eq_iff, exists_eq_right]

end MulEquivClass

namespace Set

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

end Set
