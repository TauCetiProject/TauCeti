/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Linear maps out of quotient-ring modules

For an ideal `J` of a commutative ring `R` and an `R`-module `M`, evaluation at `1` identifies the
linear maps `R ⧸ J → M` with the elements of `M` killed by `J`:
`Hom_R(R ⧸ J, M) ≅ M[J]`. This is the quotient form of Mathlib's `ringLmapEquivSelf`, which is the
case `J = 0`. In Matlis duality it identifies the layer `E[𝔪ⁿ]` of an injective hull `E` with the
Matlis dual of `R ⧸ 𝔪ⁿ`.

For an `R ⧸ I`-module `M`, an `R`-linear map to `N` takes values in `N[I]`.
Factoring through this submodule identifies `Hom_R(M, N)` with `Hom_{R/I}(M, N[I])`.
For `N = R`, the target is the dual with values in the annihilator of `I`; comparison
with the `R ⧸ I`-valued dual requires an isomorphism of these coefficient modules.
No finiteness, freeness or self-injectivity assumption is needed.

## Main declarations

* `LinearMap.apply_quotient_mk_eq_smul_apply_one`: a linear map `f` out of `R ⧸ J` is determined
  by `f 1`, taking the value `r • f 1` at the class of `r`.
* `Ideal.quotientLinearMapEquivTorsionBySet`: the linear equivalence
  `((R ⧸ J) →ₗ[R] M) ≃ₗ[R] torsionBySet R M J`, given by evaluation at `1`.
* `Ideal.linearMapEquivLinearMapTorsionBySet`: the general torsion-valued comparison for
  maps out of an arbitrary `R ⧸ I`-module, compatible with evaluation and precomposition.
-/

public section

noncomputable section

namespace LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {J : Ideal R}

/-- A linear map out of `R ⧸ J` takes the value `r • f 1` at the class of `r`. -/
theorem apply_quotient_mk_eq_smul_apply_one (f : (R ⧸ J) →ₗ[R] M) (r : R) :
    f (Ideal.Quotient.mk J r) = r • f 1 := by
  rw [← Ideal.Quotient.algebraMap_eq, Algebra.algebraMap_eq_smul_one, map_smul]

end LinearMap

namespace Ideal

open Submodule

variable {R : Type*} [CommRing R]

/-- A compatible action of `R ⧸ I` makes every element of the module annihilated by `I`. -/
theorem isTorsionBySet_of_isScalarTower (I : Ideal R) (M : Type*) [AddCommMonoid M]
    [Module R M] [Module (R ⧸ I) M] [IsScalarTower R (R ⧸ I) M] :
    Module.IsTorsionBySet R M I := by
  intro x r
  rw [← IsScalarTower.algebraMap_smul (R ⧸ I)]
  simp [Quotient.algebraMap_eq, Quotient.eq_zero_iff_mem.mpr r.property]

variable (J : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]

/-- Evaluation at `1` identifies linear maps `R ⧸ J → M` with the elements of `M` killed by `J`. -/
def quotientLinearMapEquivTorsionBySet :
    ((R ⧸ J) →ₗ[R] M) ≃ₗ[R] torsionBySet R M J where
  toFun f := ⟨f 1, (mem_torsionBySet_iff _ _).mpr fun j => by
    rw [← f.apply_quotient_mk_eq_smul_apply_one, Ideal.Quotient.eq_zero_iff_mem.mpr j.prop,
      map_zero]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := J.liftQ (LinearMap.toSpanSingleton R M x) fun j hj => by
    simpa using (mem_torsionBySet_iff _ _).mp x.prop ⟨j, hj⟩
  left_inv f := LinearMap.ext fun y => by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [f.apply_quotient_mk_eq_smul_apply_one, ← Ideal.Quotient.mk_eq_mk, liftQ_apply,
      LinearMap.toSpanSingleton_apply]
  right_inv x := Subtype.ext <| by
    dsimp only
    rw [← map_one (Ideal.Quotient.mk J), ← Ideal.Quotient.mk_eq_mk, liftQ_apply,
      LinearMap.toSpanSingleton_apply_one]

@[simp]
theorem coe_quotientLinearMapEquivTorsionBySet_apply (f : (R ⧸ J) →ₗ[R] M) :
    (J.quotientLinearMapEquivTorsionBySet M f : M) = f 1 :=
  (rfl)

@[simp]
theorem quotientLinearMapEquivTorsionBySet_symm_apply_mk (x : torsionBySet R M J) (r : R) :
    (J.quotientLinearMapEquivTorsionBySet M).symm x (Ideal.Quotient.mk J r) = r • (x : M) := by
  rw [quotientLinearMapEquivTorsionBySet, LinearEquiv.coe_symm_mk, ← Ideal.Quotient.mk_eq_mk,
    liftQ_apply, LinearMap.toSpanSingleton_apply]

section QuotientModule

variable {R : Type*} [CommRing R] (I : Ideal R)
  (M N : Type*) [AddCommMonoid M] [Module R M] [Module (R ⧸ I) M]
  [IsScalarTower R (R ⧸ I) M] [AddCommGroup N] [Module R N]

/-- Factoring through the submodule killed by `I` identifies `R`-linear maps out of an
`R ⧸ I`-module with `R ⧸ I`-linear maps to that submodule. In particular, the `R`-dual
of `M` is the `R ⧸ I`-dual with values in the annihilator of `I`. -/
def linearMapEquivLinearMapTorsionBySet :
    (M →ₗ[R] N) ≃ₗ[R] (M →ₗ[R ⧸ I] torsionBySet R N I) where
  toFun f := (f.codRestrict (torsionBySet R N I) fun x ↦
    (mem_torsionBySet_iff _ _).mpr fun r ↦ by
      rw [← map_smul, I.isTorsionBySet_of_isScalarTower M, map_zero]).extendScalarsOfSurjective
        Quotient.mk_surjective
  invFun g := (torsionBySet R N I).subtype.comp (g.restrictScalars R)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {M N}

/-- The coefficient comparison preserves evaluation after inclusion into `N`. -/
@[simp]
theorem coe_linearMapEquivLinearMapTorsionBySet_apply (f : M →ₗ[R] N) (x : M) :
    (I.linearMapEquivLinearMapTorsionBySet M N f x : N) = f x :=
  (rfl)

/-- The inverse coefficient comparison is inclusion of the values into `N`. -/
@[simp]
theorem linearMapEquivLinearMapTorsionBySet_symm_apply
    (f : M →ₗ[R ⧸ I] torsionBySet R N I) (x : M) :
    (I.linearMapEquivLinearMapTorsionBySet M N).symm f x = (f x : N) :=
  (rfl)

/-- The coefficient comparison commutes with precomposition by a quotient-linear map. -/
@[simp]
theorem linearMapEquivLinearMapTorsionBySet_comp {P : Type*} [AddCommMonoid P] [Module R P]
    [Module (R ⧸ I) P] [IsScalarTower R (R ⧸ I) P]
    (f : M →ₗ[R] N) (g : P →ₗ[R ⧸ I] M) :
    I.linearMapEquivLinearMapTorsionBySet P N (f.comp (g.restrictScalars R)) =
      (I.linearMapEquivLinearMapTorsionBySet M N f).comp g := by
  ext x
  rfl

end QuotientModule

end Ideal
