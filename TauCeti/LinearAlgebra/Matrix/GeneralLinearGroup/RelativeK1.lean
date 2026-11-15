/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Unitization
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable

/-!
# Relative algebraic `K₁` of a nonunital algebra

Let `A` be a possibly nonunital algebra over a commutative ring `R`, and `A⁺ = Unitization R A`
its forced unitization, used even when `A` already has a unit. The augmentation
`A⁺ → R`, `(r, a) ↦ r`, induces a homomorphism `K₁(A⁺) → K₁(R)`, and the **relative `K₁`** of `A`
is its kernel. This is the `K₁`-group of a nonunital algebra; for a unital `A` it is computed with
the forced unitization all the same. The scalar inclusion `R → A⁺` splits the augmentation, so
every class of `A⁺` is the product of its relative part and the class of a scalar matrix.

Invertible matrices over `A⁺` whose scalar part is the identity, that is matrices `1 + a` with
entries of `a` in `A`, have relative classes. A homomorphism of nonunital algebras induces a
homomorphism of relative `K₁` through the induced map of forced unitizations, which preserves the
augmentation.

Relative `K₁` is the group paired with the relative cyclic cohomology of `A` by Connes' odd pairing
(`TauCeti.relativeAlgebraicK1.oddPairing`).

## Main definitions

* `TauCeti.relativeAlgebraicK1`: the kernel of `K₁(A⁺) → K₁(R)`.
* `TauCeti.relativeAlgebraicK1.projection`: the projection of `K₁(A⁺)` onto relative `K₁` along
  the classes of scalar matrices.
* `TauCeti.relativeAlgebraicK1.map`: the homomorphism induced by a homomorphism of nonunital
  algebras.

## Main results

* `TauCeti.AlgebraicK1.mk_mem_relativeAlgebraicK1`: an invertible matrix over `A⁺` with identity
  scalar part has a relative class.
* `TauCeti.relativeAlgebraicK1.projection_coe`,
  `TauCeti.relativeAlgebraicK1.projection_map_algebraMap`: the projection is the identity on
  relative classes and kills the classes of scalar matrices.
* `TauCeti.relativeAlgebraicK1.coe_projection_mul_map_algebraMap`: every class of `A⁺` is its
  relative part times the class of a scalar matrix.
* `TauCeti.relativeAlgebraicK1.map_projection`: the projection is natural.
* `TauCeti.relativeAlgebraicK1.map_id`, `TauCeti.relativeAlgebraicK1.map_comp`: functoriality.

## References

* J. Rosenberg, *Algebraic K-Theory and Its Applications*, GTM 147 (1994), Chapters 1 and 2, for
  `K`-groups of nonunital rings through their unitization.
* A. Connes, *Noncommutative Geometry*, Chapter III, §3, for the `K`-theory of a nonunital algebra
  as a kernel on its unitization in the pairing with cyclic cohomology.
-/

public section

noncomputable section

namespace TauCeti

variable (R A : Type*) [CommRing R] [NonUnitalRing A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

/-- The **relative algebraic `K₁`** of a possibly nonunital algebra `A`: the kernel of the
homomorphism `K₁(A⁺) → K₁(R)` induced by the augmentation of the forced unitization
`A⁺ = Unitization R A`. -/
def relativeAlgebraicK1 : Subgroup (AlgebraicK1 (Unitization R A)) :=
  (AlgebraicK1.map (Unitization.fstHom R A : Unitization R A →+* R)).ker

variable {R A}

/-- A class of `A⁺` is relative exactly when the augmentation sends it to the trivial class. -/
@[simp]
theorem mem_relativeAlgebraicK1_iff {x : AlgebraicK1 (Unitization R A)} :
    x ∈ relativeAlgebraicK1 R A ↔
      AlgebraicK1.map (Unitization.fstHom R A : Unitization R A →+* R) x = 1 :=
  MonoidHom.mem_ker

/-- An invertible matrix over `A⁺` whose scalar part is the identity matrix has a relative
class. -/
theorem AlgebraicK1.mk_mem_relativeAlgebraicK1 {n : ℕ} {u : GL (Fin n) (Unitization R A)}
    (hu : (Unitization.fstHom R A : Unitization R A →+* R).mapMatrix
      (u : Matrix (Fin n) (Fin n) (Unitization R A)) = 1) :
    AlgebraicK1.mk (Unitization R A) n u ∈ relativeAlgebraicK1 R A := by
  rw [mem_relativeAlgebraicK1_iff, AlgebraicK1.map_mk]
  convert map_one (AlgebraicK1.mk R n)
  exact Units.ext hu

/-- The augmentation is a left inverse of the scalar inclusion on algebraic `K₁`. -/
theorem AlgebraicK1.map_fstHom_map_algebraMap (x : AlgebraicK1 R) :
    AlgebraicK1.map (Unitization.fstHom R A : Unitization R A →+* R)
      (AlgebraicK1.map (algebraMap R (Unitization R A)) x) = x := by
  rw [AlgebraicK1.map_map]
  convert DFunLike.congr_fun AlgebraicK1.map_id x
  ext r
  simp

namespace relativeAlgebraicK1

variable (R A) in
/-- The projection of `K₁(A⁺)` onto relative `K₁` along the classes of scalar matrices,
`x ↦ x · s(ε(x))⁻¹`, where `ε` is induced by the augmentation and `s` by the scalar inclusion. -/
def projection : AlgebraicK1 (Unitization R A) →* relativeAlgebraicK1 R A :=
  (MonoidHom.id _ / (AlgebraicK1.map (algebraMap R (Unitization R A))).comp
    (AlgebraicK1.map (Unitization.fstHom R A : Unitization R A →+* R))).codRestrict _
    fun x ↦ by simp [← RingHom.comp_assoc]

/-- The relative part of a class `x` of `A⁺` is `x · s(ε(x))⁻¹`. -/
theorem coe_projection_apply (x : AlgebraicK1 (Unitization R A)) :
    (projection R A x : AlgebraicK1 (Unitization R A)) =
      x * (AlgebraicK1.map (algebraMap R (Unitization R A))
        (AlgebraicK1.map (Unitization.fstHom R A : Unitization R A →+* R) x))⁻¹ := by
  simp [projection, div_eq_mul_inv]

/-- The projection is the identity on relative classes. -/
@[simp]
theorem projection_coe (x : relativeAlgebraicK1 R A) : projection R A x = x := by
  ext
  simp [coe_projection_apply, (mem_relativeAlgebraicK1_iff.1 x.2)]

/-- The projection kills the classes of scalar matrices. -/
@[simp]
theorem projection_map_algebraMap (y : AlgebraicK1 R) :
    projection R A (AlgebraicK1.map (algebraMap R (Unitization R A)) y) = 1 := by
  ext
  simp [coe_projection_apply]

/-- Every class of `A⁺` is the product of its relative part and the class of a scalar matrix,
the image of `x` under the map induced by `s ∘ ε`. -/
@[simp]
theorem coe_projection_mul_map_algebraMap (x : AlgebraicK1 (Unitization R A)) :
    (projection R A x : AlgebraicK1 (Unitization R A)) *
        AlgebraicK1.map ((algebraMap R (Unitization R A)).comp
          (Unitization.fstHom R A : Unitization R A →+* R)) x = x := by
  rw [← AlgebraicK1.map_map, coe_projection_apply, inv_mul_cancel_right]

section Map

variable {B C : Type*} [NonUnitalRing B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
  [NonUnitalRing C] [Module R C] [IsScalarTower R C C] [SMulCommClass R C C]

/-- The homomorphism of relative `K₁` induced by a homomorphism of nonunital algebras, through the
induced map of forced unitizations. -/
def map (f : A →ₙₐ[R] B) : relativeAlgebraicK1 R A →* relativeAlgebraicK1 R B :=
  ((AlgebraicK1.map (Unitization.map f : Unitization R A →+* Unitization R B)).comp
    (relativeAlgebraicK1 R A).subtype).codRestrict _ fun x ↦ by
      rw [mem_relativeAlgebraicK1_iff, MonoidHom.comp_apply, AlgebraicK1.map_map,
        ← AlgHom.comp_toRingHom, Unitization.fstHom_comp_map]
      exact mem_relativeAlgebraicK1_iff.1 x.2

/-- The induced homomorphism of relative `K₁` is the induced homomorphism of `K₁(A⁺)`. -/
@[simp]
theorem coe_map_apply (f : A →ₙₐ[R] B) (x : relativeAlgebraicK1 R A) :
    (map f x : AlgebraicK1 (Unitization R B)) =
      AlgebraicK1.map (Unitization.map f : Unitization R A →+* Unitization R B) x :=
  (rfl)

/-- The projection onto relative `K₁` is natural for homomorphisms of nonunital algebras. -/
theorem map_projection (f : A →ₙₐ[R] B) (x : AlgebraicK1 (Unitization R A)) :
    map f (projection R A x) =
      projection R B
        (AlgebraicK1.map (Unitization.map f : Unitization R A →+* Unitization R B) x) := by
  ext
  simp only [coe_map_apply, coe_projection_apply, map_mul, map_inv]
  congr 2
  simp only [AlgebraicK1.map_map, ← AlgHom.comp_toRingHom, Unitization.fstHom_comp_map]
  rw [← RingHom.comp_assoc, AlgHom.comp_algebraMap]

/-- The identity homomorphism induces the identity of relative `K₁`. -/
@[simp]
theorem map_id : map (NonUnitalAlgHom.id R A) = MonoidHom.id (relativeAlgebraicK1 R A) := by
  ext x
  simp [Unitization.map_id]

/-- Relative `K₁` is functorial. -/
theorem map_comp (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) :
    map (g.comp f) = (map g).comp (map f) := by
  ext x
  simp only [coe_map_apply, MonoidHom.comp_apply, Unitization.map_comp, AlgHom.comp_toRingHom,
    AlgebraicK1.map_comp]

end Map

end relativeAlgebraicK1

end TauCeti
