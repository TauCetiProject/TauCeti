/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Form

/-!
# Changes of frame and of coefficients for the unitary group of a form

Let `R` be a commutative ring with an involution `star` and `A` a square matrix over `R`, with
unitary group `Matrix.unitaryGroupOf A = {g ∈ GL_n(R) : star g * A * g = A}`. This file records
the two ways of moving such a group to another one.

* **Change of frame.** If `x ∈ GL_n(R)` carries the form of Gram matrix `A` to that of `B`, that
  is `star x * A * x = B`, then conjugation `g ↦ x⁻¹ * g * x` is an isomorphism
  `unitaryGroupOf A ≃* unitaryGroupOf B` (`Matrix.unitaryGroupOf.conjEquiv`). This is how the
  unitary group of a hermitian matrix is read in the coordinates of a frame in which the form is
  standard, for instance an orthonormal frame.
* **Change of coefficients.** A ring homomorphism `f : R →+* S` commuting with the involutions maps
  `unitaryGroupOf A` to `unitaryGroupOf (A.map f)` (`Matrix.unitaryGroupOf.mapHom`), injectively
  when `f` is injective. This is how the rational points of a unitary group over a number field
  are read in a completion, or in the adeles.

## Main declarations

* `Matrix.star_inv_mul_mul_inv_eq`: if `star x * A * x = B` then `star x⁻¹ * B * x⁻¹ = A`.
* `Matrix.unitaryGroupOf.conjEquiv`: the isomorphism `unitaryGroupOf A ≃* unitaryGroupOf B`, with
  `Matrix.unitaryGroupOf.conjEquiv_trans` for two successive changes of frame and
  `Matrix.unitaryGroupOf.conjEquiv_symm` for its inverse.
* `Matrix.unitaryGroupOf.mapHom`: the change of coefficients along a `star`-compatible ring
  homomorphism (`Matrix.unitaryGroupOf.coe_mapHom`: it is `GeneralLinearGroup.map f` on elements),
  injective for injective `f` (`Matrix.unitaryGroupOf.mapHom_injective`).
-/

public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
section Semiring

variable {R : Type*} [Semiring R] [StarRing R]

/-- A change of frame `x` with `star x * A * x = B` can be undone: `star x⁻¹ * B * x⁻¹ = A`. -/
theorem star_inv_mul_mul_inv_eq {A B : Matrix n n R} {x : GL n R}
    (hx : star (x : Matrix n n R) * A * x = B) :
    star (↑x⁻¹ : Matrix n n R) * B * (↑x⁻¹ : Matrix n n R) = A := by
  subst hx
  calc star (↑x⁻¹ : Matrix n n R) * (star (x : Matrix n n R) * A * x) * ↑x⁻¹ =
        star ((x : Matrix n n R) * ↑x⁻¹) * A * ((x : Matrix n n R) * ↑x⁻¹) := by
          simp only [star_mul, Matrix.mul_assoc]
    _ = A := by simp

namespace unitaryGroupOf

variable {A B C : Matrix n n R}

/-- **Change of frame**: for `x ∈ GL_n(R)` with `star x * A * x = B`, conjugation
`g ↦ x⁻¹ * g * x` is an isomorphism `unitaryGroupOf A ≃* unitaryGroupOf B`, with inverse
`h ↦ x * h * x⁻¹`. -/
def conjEquiv (x : GL n R) (hx : star (x : Matrix n n R) * A * x = B) :
    unitaryGroupOf A ≃* unitaryGroupOf B where
  toFun g := ⟨x⁻¹ * g * x, inv_mul_mul_mem_unitaryGroupOf hx g.property⟩
  invFun h := ⟨x * h * x⁻¹, by
    simpa only [inv_inv] using
      inv_mul_mul_mem_unitaryGroupOf (x := x⁻¹) (star_inv_mul_mul_inv_eq hx) h.property⟩
  left_inv g := Subtype.ext <| by group
  right_inv h := Subtype.ext <| by group
  map_mul' g h := Subtype.ext <| by
    simp only [Subgroup.coe_mul]
    group

/-- The image of `g` under a change of frame `x` is `x⁻¹ * g * x`. -/
@[simp]
theorem coe_conjEquiv_apply (x : GL n R) (hx : star (x : Matrix n n R) * A * x = B)
    (g : unitaryGroupOf A) : (conjEquiv x hx g : GL n R) = x⁻¹ * g * x :=
  (rfl)

/-- The inverse of a change of frame `x` is conjugation `h ↦ x * h * x⁻¹`. Not `@[simp]`: simp
proves it from `conjEquiv_symm` and `coe_conjEquiv_apply`. -/
theorem coe_conjEquiv_symm_apply (x : GL n R) (hx : star (x : Matrix n n R) * A * x = B)
    (h : unitaryGroupOf B) : ((conjEquiv x hx).symm h : GL n R) = x * h * x⁻¹ :=
  (rfl)

/-- The inverse of the change of frame `x` is the change of frame `x⁻¹`. -/
@[simp]
theorem conjEquiv_symm (x : GL n R) (hx : star (x : Matrix n n R) * A * x = B) :
    (conjEquiv x hx).symm = conjEquiv x⁻¹ (star_inv_mul_mul_inv_eq hx) :=
  MulEquiv.ext fun h => Subtype.ext <| by simp [coe_conjEquiv_symm_apply]

/-- The change of frame by the identity is the identity. -/
@[simp]
theorem conjEquiv_one (hx : star ((1 : GL n R) : Matrix n n R) * A * (1 : GL n R) = A) :
    conjEquiv 1 hx = MulEquiv.refl (unitaryGroupOf A) :=
  MulEquiv.ext fun g => Subtype.ext <| by simp

/-- Two successive changes of frame `x` and `y` are the change of frame `x * y`. -/
theorem conjEquiv_trans {x y : GL n R} (hx : star (x : Matrix n n R) * A * x = B)
    (hy : star (y : Matrix n n R) * B * y = C) :
    (conjEquiv x hx).trans (conjEquiv y hy) =
      conjEquiv (x * y) (by
        rw [Units.val_mul, star_eq_conjTranspose,
          conjTranspose_mul_mul_mul_of_star_mul_mul_eq hx, ← star_eq_conjTranspose, hy]) :=
  MulEquiv.ext fun g => Subtype.ext <| by
    simp only [MulEquiv.trans_apply, coe_conjEquiv_apply]
    group

end unitaryGroupOf

end Semiring

section CommRing

variable {R S : Type*} [CommRing R] [StarRing R] [CommRing S] [StarRing S]
variable {A : Matrix n n R}

namespace unitaryGroupOf

variable (A) in
/-- **Change of coefficients**: the homomorphism `unitaryGroupOf A →* unitaryGroupOf (A.map f)`
induced by a ring homomorphism `f` commuting with the involutions. -/
def mapHom (f : R →+* S) (hf : ∀ a, f (star a) = star (f a)) :
    unitaryGroupOf A →* unitaryGroupOf (A.map f) :=
  ((GeneralLinearGroup.map f).comp (unitaryGroupOf A).subtype).codRestrict _
    fun g => map_mem_unitaryGroupOf hf g.property

/-- The change of coefficients is the change of coefficients `GL_n(R) → GL_n(S)` along `f`. -/
@[simp]
theorem coe_mapHom (f : R →+* S) (hf : ∀ a, f (star a) = star (f a)) (g : unitaryGroupOf A) :
    (mapHom A f hf g : GL n S) = GeneralLinearGroup.map f (g : GL n R) :=
  (rfl)

/-- The change of coefficients applies `f` to the entries. -/
theorem val_mapHom (f : R →+* S) (hf : ∀ a, f (star a) = star (f a)) (g : unitaryGroupOf A) :
    ((mapHom A f hf g : GL n S) : Matrix n n S) = ((g : GL n R) : Matrix n n R).map f :=
  (rfl)

/-- The change of coefficients along an injective ring homomorphism is injective. -/
theorem mapHom_injective {f : R →+* S} (hf : ∀ a, f (star a) = star (f a))
    (hinj : Function.Injective f) : Function.Injective (mapHom A f hf) := fun g h hgh => by
  refine unitaryGroupOf.ext <| Matrix.map_injective hinj ?_
  simpa only [val_mapHom] using congrArg (fun k : unitaryGroupOf (A.map f) ↦
    ((k : GL n S) : Matrix n n S)) hgh

end unitaryGroupOf

end CommRing

end Matrix
