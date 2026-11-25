/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Unitization
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.K2

/-!
# Relative algebraic `K₂` of a nonunital algebra

Let `A` be a possibly nonunital algebra over a commutative ring `R`, and `A⁺ = Unitization R A`
its forced unitization, used even when `A` already has a unit. The augmentation
`ε : A⁺ → R`, `(r, a) ↦ r`, induces a homomorphism `K₂(A⁺) → K₂(R)` of Milnor's algebraic `K₂`,
and the **relative `K₂`** of `A` is its kernel. For `R = ℤ` this is the reduced `K₂` of the
nonunital ring `A`, computed on its Dorroh unitization.

The scalar inclusion `s : R → A⁺` is a ring homomorphism with `ε ∘ s = id`, so `K₂(s)` splits
`K₂(ε)`: every class of `A⁺` is the product of its relative part and the class `K₂(s ∘ ε)(x)`
coming from the scalars, and `K₂(A⁺)` is the product of relative `K₂` and `K₂(R)`. A homomorphism
of nonunital algebras induces a homomorphism of relative `K₂` through the induced map of forced
unitizations, which preserves the augmentation. The zero algebra has trivial relative `K₂`, since
its unitization is `R` itself.

This is the `K₂` counterpart of the relative `K₁` of
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.RelativeK1`.

## Main definitions

* `TauCeti.relativeAlgebraicK2`: the kernel of `K₂(A⁺) → K₂(R)`.
* `TauCeti.relativeAlgebraicK2.projection`: the projection of `K₂(A⁺)` onto relative `K₂` along
  the classes coming from the scalars.
* `TauCeti.relativeAlgebraicK2.unitizationEquiv`: the splitting
  `K₂(A⁺) ≃* relativeAlgebraicK2 R A × K₂(R)`.
* `TauCeti.relativeAlgebraicK2.map`: the homomorphism induced by a homomorphism of nonunital
  algebras.

## Main results

* `TauCeti.mem_relativeAlgebraicK2_iff_map_eq_one`: an element of `K₂(A⁺)` is relative exactly
  when the augmentation sends its underlying Steinberg element to `1` in `St(R)`.
* `TauCeti.AlgebraicK2.map_fstHom_map_algebraMap`: the augmentation is a left inverse of the
  scalar inclusion on `K₂`.
* `TauCeti.relativeAlgebraicK2.coe_projection_mul_map_algebraMap`: every class of `A⁺` is its
  relative part times a class coming from the scalars.
* `TauCeti.relativeAlgebraicK2_eq_bot`: the zero algebra has trivial relative `K₂`.
* `TauCeti.relativeAlgebraicK2.map_projection`, `TauCeti.relativeAlgebraicK2.map_id`,
  `TauCeti.relativeAlgebraicK2.map_comp`: naturality of the projection and functoriality.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §5,
  for the Steinberg group and `K₂`.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter II, Exercise 2.4, for `K`-groups of a nonunital ring as kernels
  on its unitization, and Chapter III, §5, for `K₂`.
-/

public section

noncomputable section

namespace TauCeti

variable (R A : Type*) [CommRing R] [NonUnitalRing A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

/-- The **relative algebraic `K₂`** of a possibly nonunital algebra `A`: the kernel of the
homomorphism `K₂(A⁺) → K₂(R)` induced by the augmentation of the forced unitization
`A⁺ = Unitization R A`. For `R = ℤ` it is the reduced `K₂` of the nonunital ring `A`. -/
def relativeAlgebraicK2 : Subgroup (AlgebraicK2 (Unitization R A)) :=
  (AlgebraicK2.map (Unitization.fstHom R A : Unitization R A →+* R)).ker

variable {R A}

/-- A class of `A⁺` is relative exactly when the augmentation sends it to the trivial class. -/
@[simp]
theorem mem_relativeAlgebraicK2_iff {x : AlgebraicK2 (Unitization R A)} :
    x ∈ relativeAlgebraicK2 R A ↔
      AlgebraicK2.map (Unitization.fstHom R A : Unitization R A →+* R) x = 1 :=
  MonoidHom.mem_ker

/-- A class of `A⁺` is relative exactly when the augmentation sends its underlying Steinberg
element to `1` in `St(R)`. -/
theorem mem_relativeAlgebraicK2_iff_map_eq_one {x : AlgebraicK2 (Unitization R A)} :
    x ∈ relativeAlgebraicK2 R A ↔
      IndexedSteinbergGroup.map (Unitization.fstHom R A : Unitization R A →+* R)
        (x : SteinbergGroup (Unitization R A)) = 1 := by
  rw [mem_relativeAlgebraicK2_iff, ← AlgebraicK2.coe_map_apply, OneMemClass.coe_eq_one]

/-- The augmentation is a left inverse of the scalar inclusion on algebraic `K₂`. -/
theorem AlgebraicK2.map_fstHom_map_algebraMap (x : AlgebraicK2 R) :
    AlgebraicK2.map (Unitization.fstHom R A : Unitization R A →+* R)
      (AlgebraicK2.map (algebraMap R (Unitization R A)) x) = x := by
  simp [AlgebraicK2.map_map]

/-- The zero algebra has trivial relative `K₂`: its forced unitization is `R`, through the
augmentation. -/
theorem relativeAlgebraicK2_eq_bot [Subsingleton A] : relativeAlgebraicK2 R A = ⊥ := by
  refine (MonoidHom.ker_eq_bot_iff _).2 (Function.LeftInverse.injective
    (g := AlgebraicK2.map (algebraMap R (Unitization R A))) fun x ↦ ?_)
  have h : (algebraMap R (Unitization R A)).comp (Unitization.fstHom R A : Unitization R A →+* R) =
      RingHom.id _ :=
    RingHom.ext fun u ↦ Unitization.ext (by simp) (Subsingleton.elim _ _)
  rw [AlgebraicK2.map_map, h, AlgebraicK2.map_id, MonoidHom.id_apply]

namespace relativeAlgebraicK2

variable (R A) in
/-- The projection of `K₂(A⁺)` onto relative `K₂` along the classes coming from the scalars,
`x ↦ x · s(ε(x))⁻¹`, where `ε` is induced by the augmentation and `s` by the scalar inclusion. -/
def projection : AlgebraicK2 (Unitization R A) →* relativeAlgebraicK2 R A :=
  (MonoidHom.id _ / (AlgebraicK2.map (algebraMap R (Unitization R A))).comp
    (AlgebraicK2.map (Unitization.fstHom R A : Unitization R A →+* R))).codRestrict _
    fun x ↦ by simp [← RingHom.comp_assoc]

/-- The relative part of a class `x` of `A⁺` is `x · s(ε(x))⁻¹`. -/
theorem coe_projection_apply (x : AlgebraicK2 (Unitization R A)) :
    (projection R A x : AlgebraicK2 (Unitization R A)) =
      x * (AlgebraicK2.map (algebraMap R (Unitization R A))
        (AlgebraicK2.map (Unitization.fstHom R A : Unitization R A →+* R) x))⁻¹ := by
  simp [projection, div_eq_mul_inv]

/-- The projection is the identity on relative classes. -/
@[simp]
theorem projection_coe (x : relativeAlgebraicK2 R A) : projection R A x = x := by
  ext
  simp [coe_projection_apply, (mem_relativeAlgebraicK2_iff.1 x.property)]

/-- The projection kills the classes coming from the scalars. -/
@[simp]
theorem projection_map_algebraMap (y : AlgebraicK2 R) :
    projection R A (AlgebraicK2.map (algebraMap R (Unitization R A)) y) = 1 := by
  ext
  simp [coe_projection_apply]

/-- Every class of `A⁺` is the product of its relative part and the class coming from the
scalars, the image of `x` under the map induced by `s ∘ ε`. -/
@[simp]
theorem coe_projection_mul_map_algebraMap (x : AlgebraicK2 (Unitization R A)) :
    (projection R A x : AlgebraicK2 (Unitization R A)) *
        AlgebraicK2.map ((algebraMap R (Unitization R A)).comp
          (Unitization.fstHom R A : Unitization R A →+* R)) x = x := by
  rw [← AlgebraicK2.map_map, coe_projection_apply, inv_mul_cancel_right]

variable (R A) in
/-- The augmentation splitting of `K₂` of a forced unitization: `K₂(A⁺)` is the product of the
relative `K₂` of `A` and `K₂(R)`, through the projection and the augmentation, with inverse
`(y, z) ↦ y · s(z)`. -/
def unitizationEquiv : AlgebraicK2 (Unitization R A) ≃* relativeAlgebraicK2 R A × AlgebraicK2 R :=
  MonoidHom.toMulEquiv
    ((projection R A).prod (AlgebraicK2.map (Unitization.fstHom R A : Unitization R A →+* R)))
    ((relativeAlgebraicK2 R A).subtype.coprod (AlgebraicK2.map (algebraMap R (Unitization R A))))
    (by ext x; simp [AlgebraicK2.map_map])
    (by ext ⟨y, z⟩ <;> simp [mem_relativeAlgebraicK2_iff.1 y.property])

/-- The splitting sends a class to its relative part and its augmentation. -/
@[simp]
theorem unitizationEquiv_apply (x : AlgebraicK2 (Unitization R A)) :
    unitizationEquiv R A x =
      (projection R A x, AlgebraicK2.map (Unitization.fstHom R A : Unitization R A →+* R) x) :=
  (rfl)

/-- The inverse of the splitting multiplies a relative class by the image of a class of `R`
under the scalar inclusion. -/
@[simp]
theorem unitizationEquiv_symm_apply (y : relativeAlgebraicK2 R A) (z : AlgebraicK2 R) :
    (unitizationEquiv R A).symm (y, z) =
      (y : AlgebraicK2 (Unitization R A)) * AlgebraicK2.map (algebraMap R (Unitization R A)) z :=
  (rfl)

section Map

variable {B C : Type*} [NonUnitalRing B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
  [NonUnitalRing C] [Module R C] [IsScalarTower R C C] [SMulCommClass R C C]

/-- The homomorphism of relative `K₂` induced by a homomorphism of nonunital algebras, through the
induced map of forced unitizations. -/
def map (f : A →ₙₐ[R] B) : relativeAlgebraicK2 R A →* relativeAlgebraicK2 R B :=
  ((AlgebraicK2.map (Unitization.map f : Unitization R A →+* Unitization R B)).comp
    (relativeAlgebraicK2 R A).subtype).codRestrict _ fun x ↦ by
      rw [mem_relativeAlgebraicK2_iff, MonoidHom.comp_apply, AlgebraicK2.map_map,
        ← AlgHom.comp_toRingHom, Unitization.fstHom_comp_map]
      exact mem_relativeAlgebraicK2_iff.1 x.property

/-- The induced homomorphism of relative `K₂` is the induced homomorphism of `K₂(A⁺)`. -/
@[simp]
theorem coe_map_apply (f : A →ₙₐ[R] B) (x : relativeAlgebraicK2 R A) :
    (map f x : AlgebraicK2 (Unitization R B)) =
      AlgebraicK2.map (Unitization.map f : Unitization R A →+* Unitization R B) x :=
  (rfl)

/-- The projection onto relative `K₂` is natural for homomorphisms of nonunital algebras. -/
theorem map_projection (f : A →ₙₐ[R] B) (x : AlgebraicK2 (Unitization R A)) :
    map f (projection R A x) =
      projection R B
        (AlgebraicK2.map (Unitization.map f : Unitization R A →+* Unitization R B) x) := by
  ext
  simp only [coe_map_apply, coe_projection_apply, map_mul, map_inv]
  congr 2
  simp only [AlgebraicK2.map_map, ← AlgHom.comp_toRingHom, Unitization.fstHom_comp_map]
  rw [← RingHom.comp_assoc, AlgHom.comp_algebraMap]

/-- The identity homomorphism induces the identity of relative `K₂`. -/
@[simp]
theorem map_id : map (NonUnitalAlgHom.id R A) = MonoidHom.id (relativeAlgebraicK2 R A) := by
  ext x
  simp [Unitization.map_id]

/-- Relative `K₂` is functorial. -/
theorem map_comp (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) :
    map (g.comp f) = (map g).comp (map f) := by
  ext x
  simp only [coe_map_apply, MonoidHom.comp_apply, Unitization.map_comp, AlgHom.comp_toRingHom,
    AlgebraicK2.map_comp]

end Map

end relativeAlgebraicK2

end TauCeti
