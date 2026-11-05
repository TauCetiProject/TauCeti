/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Basic facts about subrings

The inclusion of a subring into itself is the identity homomorphism, and for a ring homomorphism
`f : A →+* B` into a commutative ring together with a submonoid `S ≤ A`, the elements of `B` that
multiply into the range of `f` under some element of `S` form a subring `f.denClearingSubring S`.

## Main definitions

* `RingHom.denClearingSubring`: the subring `{z : B | ∃ a : A, ∃ s ∈ S, z * f s = f a}` of elements
  clearing denominators along `S` into `f`.

## Main results

* `Subring.inclusion_rfl`: the inclusion `R ⊆ R` is `RingHom.id R`.
* `RingHom.mem_denClearingSubring`, `RingHom.apply_mem_denClearingSubring`: membership criterion for
  `f.denClearingSubring S` and containment of the image of `f`.
-/

public section

namespace Subring

/-- The inclusion of a subring into itself is the identity homomorphism. -/
@[simp]
theorem inclusion_rfl {A : Type*} [Ring A] (R : Subring A) :
    R.inclusion le_rfl = RingHom.id R :=
  rfl

end Subring

namespace RingHom

variable {A B : Type*} [Ring A] [CommRing B]

/-- For a ring homomorphism `f : A →+* B` into a commutative ring and a submonoid `S` of `A`, the
elements `z : B` satisfying `z * f s = f a` for some `a : A` and `s ∈ S` form a subring of `B`. -/
def denClearingSubring (f : A →+* B) (S : Submonoid A) : Subring B where
  carrier := {z | ∃ a : A, ∃ s ∈ S, z * f s = f a}
  one_mem' := ⟨1, 1, S.one_mem, by simp⟩
  mul_mem' := fun ⟨a₁, s₁, hs₁, h₁⟩ ⟨a₂, s₂, hs₂, h₂⟩ ↦
    ⟨a₁ * a₂, s₁ * s₂, S.mul_mem hs₁ hs₂, by rw [map_mul, mul_mul_mul_comm, h₁, h₂, ← map_mul]⟩
  zero_mem' := ⟨0, 1, S.one_mem, by simp⟩
  add_mem' := fun {z₁ z₂} ⟨a₁, s₁, hs₁, h₁⟩ ⟨a₂, s₂, hs₂, h₂⟩ ↦
    ⟨a₁ * s₂ + a₂ * s₁, s₁ * s₂, S.mul_mem hs₁ hs₂, by
      rw [map_mul, add_mul, ← mul_assoc z₁, ← mul_assoc z₂, mul_right_comm z₂, h₁, h₂]
      simp⟩
  neg_mem' := fun ⟨a, s, hs, h⟩ ↦ ⟨-a, s, hs, by rw [neg_mul, h, map_neg]⟩

/-- Membership criterion for `RingHom.denClearingSubring`. -/
@[simp]
theorem mem_denClearingSubring {f : A →+* B} {S : Submonoid A} {z : B} :
    z ∈ f.denClearingSubring S ↔ ∃ a : A, ∃ s ∈ S, z * f s = f a :=
  Iff.rfl

/-- Every element in the image of `f` clears denominators via `1 ∈ S`. -/
theorem apply_mem_denClearingSubring (f : A →+* B) (S : Submonoid A) (a : A) :
    f a ∈ f.denClearingSubring S :=
  ⟨a, 1, S.one_mem, by simp⟩

end RingHom
