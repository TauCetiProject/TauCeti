/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.FieldTheory.Minpoly

/-!
# Algebra homomorphisms between finite-dimensional fields

This file contains dimension and conjugacy criteria for algebra homomorphisms between fields.
-/

public section

namespace TauCeti

section Finrank

variable {K L M : Type*} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
  [FiniteDimensional K L] [FiniteDimensional K M]

/-- An algebra homomorphism between finite-dimensional field extensions of equal finrank promotes
to an algebra equivalence. -/
noncomputable def algEquivOfFinrankEq (f : L →ₐ[K] M)
    (hfin : Module.finrank K L = Module.finrank K M) : L ≃ₐ[K] M :=
  AlgEquiv.ofBijective f
    ⟨f.injective,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
        (f := f.toLinearMap)).mp f.injective⟩

@[simp]
theorem algEquivOfFinrankEq_apply (f : L →ₐ[K] M)
    (hfin : Module.finrank K L = Module.finrank K M) (x : L) :
    algEquivOfFinrankEq f hfin x = f x :=
  AlgEquiv.ofBijective_apply f _ x

end Finrank

variable {L M : Type*} [Field L] [Field M] [Algebra ℚ L] [Algebra ℚ M]
  {d : ℤ} {y : L} {z : M}

/-- If `y` and `z` are square roots of the same integer and `ℚ(y)` is quadratic, any
`ℚ`-embedding from the field containing `z` into the Galois number field containing `y` can be
adjusted by a target automorphism to carry `z` to `y`. -/
theorem exists_algHom_apply_eq_of_sq_eq [IsGalois ℚ L]
    (hy : y ^ 2 = algebraMap ℤ L d)
    (hydegree : Module.finrank ℚ (IntermediateField.adjoin ℚ {y}) = 2)
    (hz : z ^ 2 = algebraMap ℤ M d) (hφ : Nonempty (M →ₐ[ℚ] L)) :
    ∃ φ : M →ₐ[ℚ] L, φ z = y := by
  obtain ⟨φ⟩ := hφ
  have hyQ : y ^ 2 = algebraMap ℚ L ((d : ℤ) : ℚ) := by
    rw [hy, IsScalarTower.algebraMap_apply ℤ ℚ L]
    norm_num
  have hzQ : z ^ 2 = algebraMap ℚ M ((d : ℤ) : ℚ) := by
    rw [hz, IsScalarTower.algebraMap_apply ℤ ℚ M]
    norm_num
  have hyint : IsIntegral ℚ y := IsGalois.integral ℚ y
  have hmin : minpoly ℚ y = Polynomial.X ^ 2 - Polynomial.C ((d : ℤ) : ℚ) := by
    apply Algebra.minpoly_eq_X_sq_sub_C_of_sq_eq_of_natDegree_eq_two hyQ
    rw [← IntermediateField.adjoin.finrank hyint, hydegree]
  have hroot : Polynomial.aeval (φ z) (minpoly ℚ y) = 0 := by
    have hφz : (φ z) ^ 2 = algebraMap ℚ L ((d : ℤ) : ℚ) := by
      rw [← map_pow, hzQ, φ.commutes]
    simp [hmin, hφz]
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root hyint.isAlgebraic hroot
  exact ⟨σ.toAlgHom.comp φ, hσ⟩

end TauCeti
