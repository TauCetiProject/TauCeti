/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.PinPlusPlane.Basic

/-!
# The action on the square root of two in the `Pin⁺` lift

The lift `pinLift` depends on a square root `r2` of two. Changing this root to its negative
multiplies the lift of `w : WreathC2` by `(-1) ^ (coordC w).val`: only the swap coordinate
contributes. Consequently an automorphism sending `r2` to `(-1) ^ ε.val * r2` acts on the
lift by the sign `(-1) ^ (ε * coordC w).val`.

`pinLift_mul_map_mul_inv` computes the resulting twisted factor set. In addition to the
ordinary dihedral factor set, its exponent contains `ε * coordC h`. For the induced
representation of a quadratic extension, these are the characters of two and of the
extension, respectively. This is the cochain calculation that produces the cup-product
correction in the Evens norm of a Kummer class.

The naturality statements hold for field homomorphisms; no topology or Galois group is needed.

## References

* J.-P. Serre, *L'invariant de Witt de la forme Tr(x²)*, Comment. Math. Helv. **59** (1984),
  651–676, second proof of Théorème 1′.
* B. Kahn, *Classes de Stiefel-Whitney de formes quadratiques et de représentations galoisiennes
  réelles*, Invent. Math. **78** (1984), 223–256, Lemme II.2.1.
-/

public section

namespace TauCeti

open Matrix DihedralGroup WreathC2

section Naturality

variable {F E : Type*} [Field F] [Field E]

/-- The unit vector defining the swap lift is natural under field homomorphisms. -/
@[simp]
theorem map_pinT (φ : F →+* E) (r2 : F) : (pinT r2).map φ = pinT (φ r2) := by
  simp [pinT_def, Matrix.map_smul' _ _ _ (map_mul φ), Matrix.map_sub]

/-- Negating the square root of two negates the unit vector defining the swap lift. -/
@[simp]
theorem pinT_neg (r2 : F) : pinT (-r2) = -pinT r2 := by
  simp [pinT_def]

variable [NeZero (2 : F)] [NeZero (2 : E)] {r2 : F}

/-- The dihedral lift is natural under field homomorphisms, with the square root mapped too. -/
@[simp]
theorem map_pinDihedral (hr2 : r2 ^ 2 = 2) (φ : F →+* E) (z : DihedralGroup 8) :
    (pinDihedral hr2 z).map φ =
      pinDihedral (r2 := φ r2) (by
        simpa only [map_pow, map_ofNat] using congrArg φ hr2) z := by
  cases z <;> simp [Matrix.map_mul, Matrix.map_pow]

/-- The section lift is natural under field homomorphisms, with the square root mapped too. -/
@[simp]
theorem map_pinLift (hr2 : r2 ^ 2 = 2) (φ : F →+* E) (w : WreathC2) :
    (pinLift hr2 w).map φ =
      pinLift (r2 := φ r2) (by
        simpa only [map_pow, map_ofNat] using congrArg φ hr2) w := by
  simp [pinLift_def]

end Naturality

section Sign

variable {F : Type*} [Field F] [NeZero (2 : F)] {r2 : F}

/-- Changing the square root of two changes a section lift by the sign of its swap coordinate. -/
@[simp]
theorem pinLift_neg (hr2 : r2 ^ 2 = 2) (w : WreathC2) :
    pinLift (r2 := -r2) (by simpa using hr2) w =
      (-1 : F) ^ (coordC w).val • pinLift hr2 w := by
  rw [pinLift_def, pinLift_def, wreathSection_apply]
  generalize coordA w = a, coordB w = b, coordC w = c
  have hbit : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hbit a with rfl | rfl <;>
    rcases hbit b with rfl | rfl <;>
    rcases hbit c with rfl | rfl <;>
    norm_num [pinDihedral_r, pinDihedral_sr, pinT_neg, pow_succ,
      Matrix.mul_neg, Matrix.neg_mul, ZMod.val_zero, ZMod.val_one_eq_one_mod,
      ZMod.val_ofNat]

/-- If a field endomorphism changes the square root of two by a sign, its action on the lift
is that sign raised to the swap coordinate. -/
theorem map_pinLift_of_map_root (hr2 : r2 ^ 2 = 2) (φ : F →+* F) (ε : ZMod 2)
    (hφ : φ r2 = (-1 : F) ^ ε.val * r2) (w : WreathC2) :
    (pinLift hr2 w).map φ = (-1 : F) ^ (ε * coordC w).val • pinLift hr2 w := by
  rw [map_pinLift]
  have hbit : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hbit ε with rfl | rfl
  · simp only [ZMod.val_zero, pow_zero, one_mul] at hφ
    simp only [zero_mul, ZMod.val_zero, pow_zero, one_smul]
    congr 1
  · simp only [ZMod.val_one, pow_one, neg_one_mul] at hφ
    simp only [one_mul]
    convert pinLift_neg hr2 w using 1
    congr 1

/-- The twisted factor set of the section lift is the dihedral factor set plus the product
of the sign of the square root of two with the swap coordinate of the second argument. -/
theorem pinLift_mul_map_mul_inv (hr2 : r2 ^ 2 = 2) (φ : F →+* F) (ε : ZMod 2)
    (hφ : φ r2 = (-1 : F) ^ ε.val * r2) (g h : WreathC2) :
    pinLift hr2 g * (pinLift hr2 h).map φ * (pinLift hr2 (g * h))⁻¹ =
      (-1 : F) ^ (wreathD16Cocycle (g, h) + ε * coordC h).val •
        (1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [map_pinLift_of_map_root hr2 φ ε hφ, Matrix.mul_smul, Matrix.smul_mul,
    pinLift_mul_mul_inv]
  generalize wreathD16Cocycle (g, h) = c, ε * coordC h = d
  have hbit : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hbit c with rfl | rfl <;>
    rcases hbit d with rfl | rfl <;>
    norm_num [ZMod.val_zero, ZMod.val_one, ZMod.val_ofNat]

end Sign

end TauCeti
