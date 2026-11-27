/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Duals over a quotient ring

If `I` is an ideal of a commutative ring `R`, an `R`-linear map from an `R ⧸ I`-module
`M` to `N` takes values in the submodule `N[I]` killed by `I`. Factoring through this
submodule identifies `Hom_R(M, N)` with `Hom_{R/I}(M, N[I])`.

`Ideal.linearMapEquivTorsionBySet` constructs this identification and its naturality in
the source. For `N = R`, its target is the dual with values in the annihilator of `I`,
not generally the dual with values in `R ⧸ I`. This distinction matters when changing
coefficients in duality: replacing that annihilator by `R ⧸ I` requires an isomorphism
of these coefficient modules.

No finiteness, freeness or self-injectivity assumption is needed.
-/

public section

namespace Ideal

open Submodule

variable {R : Type*} [CommRing R] (I : Ideal R)
  (M N : Type*) [AddCommGroup M] [Module R M] [Module (R ⧸ I) M]
  [IsScalarTower R (R ⧸ I) M] [AddCommGroup N] [Module R N]

/-- Factoring through the submodule killed by `I` identifies `R`-linear maps out of an
`R ⧸ I`-module with `R ⧸ I`-linear maps to that submodule. In particular, the `R`-dual
of `M` is the `R ⧸ I`-dual with values in the annihilator of `I`. -/
def linearMapEquivTorsionBySet :
    (M →ₗ[R] N) ≃ₗ[R] (M →ₗ[R ⧸ I] torsionBySet R N I) where
  toFun f := (f.codRestrict (torsionBySet R N I) fun x ↦ by
    rw [mem_torsionBySet_iff]
    intro r
    rw [← map_smul]
    have hr : (r : R) • x = 0 := by
      rw [← IsScalarTower.algebraMap_smul (R ⧸ I), Quotient.algebraMap_eq,
        Quotient.eq_zero_iff_mem.mpr r.property, zero_smul]
    rw [hr, map_zero]).extendScalarsOfSurjective Quotient.mk_surjective
  invFun g := (torsionBySet R N I).subtype.comp (g.restrictScalars R)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {M N}

/-- The coefficient comparison preserves evaluation after inclusion into `N`. -/
@[simp]
theorem coe_linearMapEquivTorsionBySet_apply (f : M →ₗ[R] N) (x : M) :
    (I.linearMapEquivTorsionBySet M N f x : N) = f x :=
  (rfl)

/-- The inverse coefficient comparison is inclusion of the values into `N`. -/
@[simp]
theorem linearMapEquivTorsionBySet_symm_apply
    (f : M →ₗ[R ⧸ I] torsionBySet R N I) (x : M) :
    (I.linearMapEquivTorsionBySet M N).symm f x = (f x : N) :=
  (rfl)

/-- The coefficient comparison commutes with precomposition by a quotient-linear map. -/
@[simp]
theorem linearMapEquivTorsionBySet_comp {P : Type*} [AddCommGroup P] [Module R P]
    [Module (R ⧸ I) P] [IsScalarTower R (R ⧸ I) P]
    (f : M →ₗ[R] N) (g : P →ₗ[R ⧸ I] M) :
    I.linearMapEquivTorsionBySet P N (f.comp (g.restrictScalars R)) =
      (I.linearMapEquivTorsionBySet M N f).comp g := by
  ext x
  rfl

end Ideal
