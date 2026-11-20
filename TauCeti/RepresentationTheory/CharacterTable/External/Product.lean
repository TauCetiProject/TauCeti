/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Pairing

/-!
# External products of class functions

For class functions `f` of a group `G` and `g` of a group `H`, the function `(x, y) ↦ f(x) g(y)` is
a class function of `G × H`, their **external product**. On characters it is the character of the
external tensor product (`TauCeti.ClassFunction.ofCharacter_externalTensor`).

## Main definitions

* `TauCeti.ClassFunction.externalProduct`: the external product of class functions of `G` and `H`.

## Main results

* `TauCeti.ClassFunction.externalProduct_add_left`,
  `TauCeti.ClassFunction.externalProduct_smul_left` and their right-hand counterparts: the external
  product is bilinear.
* `TauCeti.ClassFunction.map_externalProduct` and `TauCeti.ClassFunction.invMap_externalProduct`:
  changing coefficients and inverting the group element act on both factors.
* `TauCeti.ClassFunction.characterPairing_externalProduct`: the character pairing of external
  products is the product of the pairings of the factors.
-/

public section

namespace TauCeti

namespace ClassFunction

section Semiring

variable {k G H : Type*} [Semiring k] [Group G] [Group H]

/-- The **external product** of a class function `f` of `G` and a class function `g` of `H` is the
class function `(x, y) ↦ f(x) g(y)` of `G × H`. For two characters it is the character of the
external tensor product (`TauCeti.ClassFunction.ofCharacter_externalTensor`). -/
def externalProduct (f : ClassFunction k G) (g : ClassFunction k H) : ClassFunction k (G × H) :=
  ⟨fun p => f.1 p.1 * g.1 p.2, mem_iff.2 fun p c => by
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv, mem_iff.1 f.2 p.1 c.1,
      mem_iff.1 g.2 p.2 c.2]⟩

/-- The external product evaluates to the product of the values on the two components. -/
@[simp]
theorem externalProduct_apply (f : ClassFunction k G) (g : ClassFunction k H) (p : G × H) :
    (externalProduct f g).1 p = f.1 p.1 * g.1 p.2 :=
  (rfl)

/-- The external product with the zero class function on the left is zero. -/
@[simp]
theorem externalProduct_zero_left (g : ClassFunction k H) :
    externalProduct (0 : ClassFunction k G) g = 0 := by
  ext
  simp

/-- The external product with the zero class function on the right is zero. -/
@[simp]
theorem externalProduct_zero_right (f : ClassFunction k G) :
    externalProduct f (0 : ClassFunction k H) = 0 := by
  ext
  simp

/-- The external product is additive in its left factor. -/
@[simp]
theorem externalProduct_add_left (f₁ f₂ : ClassFunction k G) (g : ClassFunction k H) :
    externalProduct (f₁ + f₂) g = externalProduct f₁ g + externalProduct f₂ g := by
  ext
  simp [add_mul]

/-- The external product is additive in its right factor. -/
@[simp]
theorem externalProduct_add_right (f : ClassFunction k G) (g₁ g₂ : ClassFunction k H) :
    externalProduct f (g₁ + g₂) = externalProduct f g₁ + externalProduct f g₂ := by
  ext
  simp [mul_add]

/-- The external product is linear in its left factor. -/
@[simp]
theorem externalProduct_smul_left (c : k) (f : ClassFunction k G) (g : ClassFunction k H) :
    externalProduct (c • f) g = c • externalProduct f g := by
  ext
  simp [mul_assoc]

/-- Changing coefficients commutes with forming external products. -/
@[simp]
theorem map_externalProduct {k' : Type*} [Semiring k'] (σ : k →+* k') (f : ClassFunction k G)
    (g : ClassFunction k H) :
    map σ (externalProduct f g) = externalProduct (map σ f) (map σ g) := by
  ext
  simp

/-- Inverting the group element of `G × H` inverts both components of an external product. -/
@[simp]
theorem invMap_externalProduct (f : ClassFunction k G) (g : ClassFunction k H) :
    invMap (externalProduct f g) = externalProduct (invMap f) (invMap g) := by
  ext
  simp

end Semiring

/-- Over a commutative semiring, the external product is linear in its right factor. -/
@[simp]
theorem externalProduct_smul_right {k G H : Type*} [CommSemiring k] [Group G] [Group H] (c : k)
    (f : ClassFunction k G) (g : ClassFunction k H) :
    externalProduct f (c • g) = c • externalProduct f g := by
  ext
  simp [mul_left_comm]

/-- **The character pairing of external products factors** as the product of the pairings on the
two factors. -/
@[simp]
theorem characterPairing_externalProduct {k G H : Type*} [Semifield k] [Group G] [Group H]
    [Fintype G] [Fintype H] (f₁ f₂ : ClassFunction k G) (g₁ g₂ : ClassFunction k H) :
    characterPairing (externalProduct f₁ g₁) (externalProduct f₂ g₂) =
      characterPairing f₁ f₂ * characterPairing g₁ g₂ := by
  simp only [characterPairing_apply, externalProduct_apply, Nat.card_prod, Nat.cast_mul, mul_inv,
    Fintype.sum_prod_type, Prod.fst_inv, Prod.snd_inv]
  simp_rw [mul_mul_mul_comm (f₁.1 _), ← Finset.mul_sum, ← Finset.sum_mul]
  ring

end ClassFunction

end TauCeti
