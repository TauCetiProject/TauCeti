/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.ULift
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Additive maps on free abelian groups and linear maps on free modules

An additive map from the free abelian group `S →₀ ℤ` on a type `S` to an abelian group `M` is
determined by its values on the points of `S`. For a commutative ring `R` and an `R`-module `M`,
so is an `R`-linear map from the free `R`-module `S →₀ R` to `M`, and in both cases every family
of values occurs. `Finsupp.intLinearMapEquiv` identifies the two: it extends an additive map on
the integral chains to the `R`-linear map on the chains with coefficients in `R` with the same
values on the points of `S`. The extension agrees with the original map on the chains whose
coefficients are integers cast into `R`.

## Main declarations

* `Finsupp.map_single_int`: an additive map on `S →₀ ℤ` sends `single q k` to `k` times its value
  at `single q 1`.
* `Finsupp.intLinearMapEquiv`: additive maps on `S →₀ ℤ` are `R`-linear maps on `S →₀ R`.
* `Finsupp.intLinearMapEquiv_apply_single`, `Finsupp.intLinearMapEquiv_apply_mapRange`: its values
  on the points of `S`, and on the chains with integer coefficients.
* `Finsupp.intLinearMapEquiv_symm_apply_single`: the additive map recovered from an `R`-linear map.
* `Finsupp.intLinearMapEquivModuleCat`: the same identification for additive maps into `R`, with
  the `R`-linear forms read as morphisms of `ModuleCat R` into `R` lifted to the universe of `S`,
  as in the `R`-dual of a chain complex of free modules.
* `Finsupp.intLinearMapEquivModuleCat_apply`,
  `Finsupp.intLinearMapEquivModuleCat_symm_apply_single`: its values, and the additive map
  recovered from a morphism.
-/

public section

namespace Finsupp

variable {S : Type*}

/-- An additive map on the free abelian group on `S` sends `single q k` to `k` times its value at
`single q 1`. -/
theorem map_single_int {M F : Type*} [AddCommGroup M] [FunLike F (S →₀ ℤ) M]
    [AddMonoidHomClass F (S →₀ ℤ) M] (a : F) (q : S) (k : ℤ) :
    a (single q k) = k • a (single q 1) := by
  rw [← map_zsmul, smul_single_one]

variable (S) (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- **Additive maps on a free abelian group are linear maps on the free module.** For a
commutative ring `R` and an `R`-module `M`, an additive map from the free abelian group on `S` to
`M` extends to the `R`-linear map from the free `R`-module on `S` to `M` with the same values on
the points of `S`. -/
noncomputable def intLinearMapEquiv : ((S →₀ ℤ) →ₗ[ℤ] M) ≃ₗ[R] ((S →₀ R) →ₗ[R] M) :=
  (llift M ℤ R S).symm ≪≫ₗ llift M R R S

variable {S R M}

/-- The `R`-linear map associated with an additive map `a` sends a chain `c` to the sum of the
values of `a` at the points of `S`, weighted by the coefficients of `c`. -/
theorem intLinearMapEquiv_apply (a : (S →₀ ℤ) →ₗ[ℤ] M) (c : S →₀ R) :
    intLinearMapEquiv S R M a c = c.sum fun p r ↦ r • a (single p 1) := by
  simp [intLinearMapEquiv]

/-- The `R`-linear map associated with an additive map `a` sends `single p r` to `r` times the
value of `a` at `single p 1`. -/
@[simp]
theorem intLinearMapEquiv_apply_single (a : (S →₀ ℤ) →ₗ[ℤ] M) (p : S) (r : R) :
    intLinearMapEquiv S R M a (single p r) = r • a (single p 1) := by
  rw [intLinearMapEquiv_apply]
  exact sum_single_index (zero_smul R _)

/-- The `R`-linear map associated with an additive map `a`, evaluated on a chain whose
coefficients are the integers of a chain `c` cast into `R`, is the value of `a` on `c`. -/
-- Not `@[simp]`: `simp` rewrites `Int.castAddHom R` to the cast function, so the left-hand side is
-- not in simp normal form. The change of coefficients is stated along the additive map
-- `Int.castAddHom R`, as for `Finsupp.mapRange_intMatrixMap`.
theorem intLinearMapEquiv_apply_mapRange (a : (S →₀ ℤ) →ₗ[ℤ] M) (c : S →₀ ℤ) :
    intLinearMapEquiv S R M a (mapRange (Int.castAddHom R) (map_zero _) c) = a c := by
  rw [intLinearMapEquiv_apply]
  refine (sum_mapRange_index fun p ↦ zero_smul R (a (single p 1))).trans ?_
  conv_rhs => rw [← sum_single c, map_finsuppSum]
  exact sum_congr fun p _ ↦ by
    rw [Int.coe_castAddHom, Int.cast_smul_eq_zsmul, ← map_single_int]

/-- The additive map recovered from an `R`-linear map `b` on the free `R`-module on `S` sends
`single p k` to `k` times the value of `b` at `single p 1`. -/
@[simp]
theorem intLinearMapEquiv_symm_apply_single (b : (S →₀ R) →ₗ[R] M) (p : S) (k : ℤ) :
    (intLinearMapEquiv S R M).symm b (single p k) = k • b (single p 1) := by
  rw [map_single_int]
  conv_rhs => rw [← (intLinearMapEquiv S R M).apply_symm_apply b]
  rw [intLinearMapEquiv_apply_single, one_smul]

end Finsupp

/-! ### Linear forms as morphisms of `ModuleCat` -/

namespace Finsupp

universe u

variable (S : Type u) (R : Type*) [CommRing R]

/-- `Finsupp.intLinearMapEquiv` for additive maps into `R`, with the `R`-linear forms read as
morphisms of `ModuleCat R` into `R` lifted to the universe of `S`: the form in which the `R`-dual of
a chain complex of free `R`-modules is taken. -/
noncomputable def intLinearMapEquivModuleCat :
    ((S →₀ ℤ) →ₗ[ℤ] R) ≃ₗ[R] (ModuleCat.of R (S →₀ R) ⟶ ModuleCat.of R (ULift.{u} R)) :=
  intLinearMapEquiv S R R ≪≫ₗ (LinearEquiv.congrRight ULift.moduleEquiv).symm ≪≫ₗ
    (ModuleCat.homLinearEquiv (S := R) (M := ModuleCat.of R (S →₀ R))
      (N := ModuleCat.of R (ULift.{u} R))).symm

variable {S R}

/-- The value of `Finsupp.intLinearMapEquivModuleCat` is that of `Finsupp.intLinearMapEquiv`. -/
theorem intLinearMapEquivModuleCat_apply (a : (S →₀ ℤ) →ₗ[ℤ] R) (c : S →₀ R) :
    (intLinearMapEquivModuleCat S R a c).down = intLinearMapEquiv S R R a c :=
  -- The two outer equivalences only wrap the linear map into a morphism of `ModuleCat` and its
  -- values into `ULift`, and `simp` does not see through the coercion of the morphism to a function
  -- (`ConcreteCategory.hom`), so the identity is closed by unfolding.
  (rfl)

/-- The additive map recovered from a morphism `φ` of `ModuleCat R` out of the free `R`-module on
`S` sends `single p k` to `k` times the value of `φ` at `single p 1`. -/
@[simp]
theorem intLinearMapEquivModuleCat_symm_apply_single
    (φ : ModuleCat.of R (S →₀ R) ⟶ ModuleCat.of R (ULift.{u} R)) (p : S) (k : ℤ) :
    (intLinearMapEquivModuleCat S R).symm φ (single p k) = k • (φ (single p 1)).down := by
  rw [map_single_int]
  conv_rhs => rw [← (intLinearMapEquivModuleCat S R).apply_symm_apply φ]
  rw [intLinearMapEquivModuleCat_apply, intLinearMapEquiv_apply_single, one_smul]

end Finsupp
