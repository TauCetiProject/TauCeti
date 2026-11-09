/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Twisting a monoid algebra by a character

Let `χ : G →* kˣ` be a character of a monoid `G` with values in the units of a commutative
semiring `k`. Multiplying every basis element `g` of the monoid algebra `k[G]` by the scalar
`χ g` is multiplicative, because `χ (g * h) = χ g * χ h`, so it extends to an algebra
endomorphism `MonoidAlgebra.charTwist χ` of `k[G]`; twisting by `χ⁻¹` undoes it, so it is an
algebra automorphism. On coefficients it is the pointwise product
`(charTwist χ x).coeff g = χ g * x.coeff g`.

On a representation `ρ`, an element `x` acts on the twisted representation
`Representation.charTwist χ ρ` as `charTwist χ x` acts on `ρ`
(`Representation.asAlgebraHom_charTwist`). The twists compose like the characters,
`charTwist χ ∘ charTwist ψ = charTwist (χ * ψ)`, so the twist by a character of order two, such as
the sign character of a symmetric group, is an involution. The twist by the sign character is the
automorphism `σ ↦ sgn(σ) σ` of the group algebra of a symmetric group, which exchanges the row
symmetrizer and the column antisymmetrizer of a Young tableau and its transpose.

## Main definitions and results

* `MonoidAlgebra.charTwist χ`: the algebra automorphism of `k[G]` with
  `charTwist χ (single g a) = single g (χ g * a)` (`MonoidAlgebra.charTwist_single`).
* `MonoidAlgebra.coeff_charTwist`: its coefficients are `χ g * x.coeff g`.
* `MonoidAlgebra.charTwist_charTwist` and `MonoidAlgebra.charTwist_symm`: twists compose like
  characters, and the inverse twist is the twist by the inverse character.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 4, §4.1, for
  the twist by the sign character.
-/

public section

namespace MonoidAlgebra

variable {k G : Type*} [CommSemiring k] [Monoid G]

/-- The basis elements of `k[G]` scaled by a character, `g ↦ χ g • g`, as a monoid hom
`G →* k[G]`. -/
private noncomputable def charTwistMonoidHom (χ : G →* kˣ) : G →* MonoidAlgebra k G where
  toFun g := single g (χ g : k)
  map_one' := by rw [map_one, Units.val_one, one_def]
  map_mul' g h := by rw [single_mul_single, map_mul, Units.val_mul]

private theorem charTwistMonoidHom_apply (χ : G →* kˣ) (g : G) :
    charTwistMonoidHom χ g = single g (χ g : k) :=
  (rfl)

/-- The algebra endomorphism of `k[G]` scaling each basis element `g` by `χ g`. -/
private noncomputable def charTwistAlgHom (χ : G →* kˣ) :
    MonoidAlgebra k G →ₐ[k] MonoidAlgebra k G :=
  lift k (MonoidAlgebra k G) G (charTwistMonoidHom χ)

private theorem charTwistAlgHom_single (χ : G →* kˣ) (g : G) (a : k) :
    charTwistAlgHom χ (single g a) = single g ((χ g : k) * a) := by
  rw [charTwistAlgHom, lift_single, charTwistMonoidHom_apply, smul_single, smul_eq_mul, mul_comm]

private theorem charTwistAlgHom_comp (χ ψ : G →* kˣ) :
    (charTwistAlgHom χ).comp (charTwistAlgHom ψ) = charTwistAlgHom (χ * ψ) := by
  refine algHom_ext (fun g ↦ ?_) (AlgHom.ext fun a ↦ ?_)
  · simp only [AlgHom.comp_apply, charTwistAlgHom_single, MonoidHom.mul_apply, Units.val_mul,
      mul_one]
  · simp only [AlgHom.comp_apply, singleOneAlgHom_apply, charTwistAlgHom_single, map_one,
      Units.val_one, one_mul]

private theorem charTwistAlgHom_one : charTwistAlgHom (1 : G →* kˣ) = AlgHom.id k _ := by
  refine algHom_ext (fun g ↦ ?_) (AlgHom.ext fun a ↦ ?_)
  · simp only [charTwistAlgHom_single, MonoidHom.one_apply, Units.val_one, one_mul,
      AlgHom.id_apply]
  · simp only [AlgHom.comp_apply, singleOneAlgHom_apply, charTwistAlgHom_single, map_one,
      Units.val_one, one_mul, AlgHom.id_apply]

/-- The **twist of `k[G]` by a character** `χ : G →* kˣ`: the algebra automorphism multiplying the
basis element `g` by the scalar `χ g`, with inverse the twist by `χ⁻¹`. -/
noncomputable def charTwist (χ : G →* kˣ) : MonoidAlgebra k G ≃ₐ[k] MonoidAlgebra k G :=
  AlgEquiv.ofAlgHom (charTwistAlgHom χ) (charTwistAlgHom χ⁻¹)
    (by rw [charTwistAlgHom_comp, (mul_inv_cancel χ : χ * χ⁻¹ = 1), charTwistAlgHom_one])
    (by rw [charTwistAlgHom_comp, (inv_mul_cancel χ : χ⁻¹ * χ = 1), charTwistAlgHom_one])

/-- The twist by `χ` scales the basis element `g` by `χ g`. -/
@[simp]
theorem charTwist_single (χ : G →* kˣ) (g : G) (a : k) :
    charTwist χ (single g a) = single g ((χ g : k) * a) :=
  charTwistAlgHom_single χ g a

/-- The twist by `χ` sends `of g` to `χ g • of g`. -/
theorem charTwist_of (χ : G →* kˣ) (g : G) : charTwist χ (of k G g) = (χ g : k) • of k G g := by
  rw [of_apply, charTwist_single, mul_one, smul_single, smul_eq_mul, mul_one]

/-- The coefficients of a twisted element are the coefficients of the element multiplied
pointwise by the character. -/
@[simp]
theorem coeff_charTwist (χ : G →* kˣ) (x : MonoidAlgebra k G) (g : G) :
    (charTwist χ x).coeff g = (χ g : k) * x.coeff g := by
  classical
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, coeff_add, coeff_add, Finsupp.add_apply, Finsupp.add_apply,
      hx, hy, mul_add]
  | single h a =>
    rw [charTwist_single, coeff_single, coeff_single, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs with hhg
    · rw [hhg]
    · rw [mul_zero]

/-- Twists compose like the characters: twisting by `ψ` and then by `χ` is twisting by
`χ * ψ`. -/
@[simp]
theorem charTwist_charTwist (χ ψ : G →* kˣ) (x : MonoidAlgebra k G) :
    charTwist χ (charTwist ψ x) = charTwist (χ * ψ) x :=
  congr($(charTwistAlgHom_comp χ ψ) x)

/-- The twist by the trivial character is the identity. -/
@[simp]
theorem charTwist_one : charTwist (1 : G →* kˣ) = AlgEquiv.refl :=
  AlgEquiv.ext fun x ↦ congr($(charTwistAlgHom_one (k := k) (G := G)) x)

/-- The inverse of the twist by `χ` is the twist by `χ⁻¹`. -/
@[simp]
theorem charTwist_symm (χ : G →* kˣ) : (charTwist χ).symm = charTwist χ⁻¹ :=
  (rfl)

/-- The twist by a character of order dividing two is an involution. -/
theorem charTwist_involutive {χ : G →* kˣ} (hχ : χ * χ = 1) :
    Function.Involutive (charTwist χ) := fun x ↦ by
  rw [charTwist_charTwist, hχ, charTwist_one, AlgEquiv.coe_refl, id_eq]

end MonoidAlgebra
