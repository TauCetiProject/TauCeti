/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Center
public import Mathlib.Algebra.Group.Units.Defs

/-!
# Centralizers, multiplicative equivalences, and conjugation by units

Multiplicative equivalences commute with taking centralizers (`Set.image_centralizer`). If
conjugation by the inverse of a unit `u` maps a set `S` of a monoid into itself, then conjugation
by `u` maps the centralizer of `S` into itself (`Set.conj_mem_centralizer`). Applying this twice
shows that a double commutant is preserved by every unit whose conjugations preserve the original
set in both directions, which is how spatially implemented automorphisms extend to von Neumann
algebras.
-/

public section

namespace Set

/-- A multiplicative equivalence maps the centralizer of a set onto the centralizer of its
image. -/
@[to_additive image_addCentralizer]
theorem image_centralizer {A B F : Type*} [Mul A] [Mul B] [EquivLike F A B]
    [MulEquivClass F A B] (e : F) (s : Set A) : (e '' s).centralizer = e '' s.centralizer := by
  ext b; refine ⟨fun hb ↦ ?_, ?_⟩
  · obtain ⟨c, rfl⟩ := EquivLike.surjective e b
    exact ⟨c, fun a ha ↦ EquivLike.injective e <| by
      rw [map_mul, map_mul]; exact hb (e a) ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩ _ ⟨x, hx, rfl⟩; rw [← map_mul, ← map_mul, ha x hx]

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
