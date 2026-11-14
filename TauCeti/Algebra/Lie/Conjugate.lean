/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Star.Basic
import TauCeti.Algebra.Lie.Basic

/-!
# The conjugate of a Lie algebra over a star ring

For a Lie algebra `L` over a commutative star ring `R` (complex conjugation for `R = ℂ`), the
*conjugate* Lie algebra `TauCeti.ConjLieAlgebra L` is the Lie ring `L`, with `c : R` acting as
`star c`. An `R`-linear Lie homomorphism into the conjugate is the same as a bracket-preserving
`starRingEnd R`-semilinear map, so the conjugate turns constructions of conjugate-linear maps
(through a universal property, say) into constructions of `R`-linear ones.

## Main definitions

* `TauCeti.ConjLieAlgebra L`: the conjugate Lie algebra.
* `TauCeti.ConjLieAlgebra.toConj`: the identity of the underlying Lie ring, as a `ℤ`-linear Lie
  equivalence from `L` to its conjugate.
* `TauCeti.ConjLieAlgebra.lieHomOfSemilinear`: a bracket-preserving conjugate-linear map, as an
  `R`-linear Lie homomorphism into the conjugate.
* `TauCeti.ConjLieAlgebra.semilinearOfLieHom`: an `R`-linear Lie homomorphism into the conjugate,
  as a conjugate-linear map.
-/

@[expose] public section

namespace TauCeti

/-- The conjugate of a Lie algebra `L` over a star ring `R`: the Lie ring `L`, with `c : R` acting
as `star c`. -/
def ConjLieAlgebra (L : Type*) : Type _ := L

variable (R : Type*) [CommRing R] [StarRing R] (L : Type*) [LieRing L] [LieAlgebra R L]

namespace ConjLieAlgebra

instance : LieRing (ConjLieAlgebra L) := inferInstanceAs (LieRing L)

instance : Module R (ConjLieAlgebra L) := Module.compHom L (starRingEnd R)

instance : LieAlgebra R (ConjLieAlgebra L) where
  lie_smul c x y := lie_smul (L := L) (M := L) (starRingEnd R c) x y

variable {R L}

/-- The identity of the underlying Lie ring, from `L` to its conjugate. -/
def toConj : L ≃ₗ⁅ℤ⁆ ConjLieAlgebra L where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- `TauCeti.ConjLieAlgebra.toConj` conjugates the scalars. -/
@[simp]
theorem toConj_smul (c : R) (x : L) :
    toConj (c • x) = star c • (toConj x : ConjLieAlgebra L) :=
  congrArg (· • x) (star_star c).symm

/-- The inverse of `TauCeti.ConjLieAlgebra.toConj` conjugates the scalars. -/
@[simp]
theorem toConj_symm_smul (c : R) (x : ConjLieAlgebra L) :
    toConj.symm (c • x) = star c • toConj.symm x :=
  rfl

/-- Iterating the adjoint action in the conjugate is iterating it in `L`. -/
theorem toConj_ad_pow (x y : L) (k : ℕ) :
    toConj ((LieAlgebra.ad R L x ^ k) y) =
      (LieAlgebra.ad R (ConjLieAlgebra L) (toConj x) ^ k) (toConj y) := by
  rw [ad_pow_apply_eq_ad_pow_apply R ℤ, ← ad_pow_apply_eq_ad_pow_apply ℤ R]
  exact toConj.toLieHom.map_ad_pow x k y

variable {L' : Type*} [LieRing L'] [LieAlgebra R L']

/-- A bracket-preserving conjugate-linear map, as an `R`-linear Lie homomorphism into the
conjugate. -/
def lieHomOfSemilinear (f : L →ₛₗ[starRingEnd R] L') (hf : ∀ x y, f ⁅x, y⁆ = ⁅f x, f y⁆) :
    L →ₗ⁅R⁆ ConjLieAlgebra L' where
  toFun x := toConj (f x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' c x := by rw [f.map_smulₛₗ, toConj_smul, starRingEnd_apply, star_star, RingHom.id_apply]
  map_lie' {x y} := by rw [hf, LieEquiv.map_lie]

/-- `TauCeti.ConjLieAlgebra.lieHomOfSemilinear f` is `f` followed by `toConj`. -/
@[simp]
theorem lieHomOfSemilinear_apply (f : L →ₛₗ[starRingEnd R] L')
    (hf : ∀ x y, f ⁅x, y⁆ = ⁅f x, f y⁆) (x : L) :
    lieHomOfSemilinear f hf x = toConj (f x) :=
  rfl

/-- An `R`-linear Lie homomorphism into the conjugate, as a conjugate-linear map. -/
def semilinearOfLieHom (g : L →ₗ⁅R⁆ ConjLieAlgebra L') : L →ₛₗ[starRingEnd R] L' where
  toFun x := toConj.symm (g x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' c x := by rw [map_smul, toConj_symm_smul, starRingEnd_apply]

/-- `TauCeti.ConjLieAlgebra.semilinearOfLieHom g` is `g` followed by `toConj.symm`. -/
@[simp]
theorem semilinearOfLieHom_apply (g : L →ₗ⁅R⁆ ConjLieAlgebra L') (x : L) :
    semilinearOfLieHom g x = toConj.symm (g x) :=
  rfl

/-- The conjugate-linear map of an `R`-linear Lie homomorphism into the conjugate preserves
brackets. -/
theorem semilinearOfLieHom_lie (g : L →ₗ⁅R⁆ ConjLieAlgebra L') (x y : L) :
    semilinearOfLieHom g ⁅x, y⁆ = ⁅semilinearOfLieHom g x, semilinearOfLieHom g y⁆ := by
  simp only [semilinearOfLieHom_apply, LieHom.map_lie, LieEquiv.map_lie]

/-- Packaging a conjugate-linear map as a Lie homomorphism into the conjugate and back returns the
original map. -/
@[simp]
theorem semilinearOfLieHom_lieHomOfSemilinear (f : L →ₛₗ[starRingEnd R] L')
    (hf : ∀ x y, f ⁅x, y⁆ = ⁅f x, f y⁆) :
    semilinearOfLieHom (lieHomOfSemilinear f hf) = f :=
  LinearMap.ext fun x => toConj.symm_apply_apply (f x)

/-- Unpacking a Lie homomorphism into the conjugate as a conjugate-linear map and back returns the
original homomorphism. -/
@[simp]
theorem lieHomOfSemilinear_semilinearOfLieHom (g : L →ₗ⁅R⁆ ConjLieAlgebra L') :
    lieHomOfSemilinear (semilinearOfLieHom g) (semilinearOfLieHom_lie g) = g :=
  LieHom.ext fun x => toConj.apply_symm_apply (g x)

end ConjLieAlgebra

end TauCeti
