/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
import TauCeti.FieldTheory.Minpoly

/-!
# Conjugating square roots by algebra homomorphisms

If `y` and `z` are square roots of the same scalar `r : K` and `K(y)` is quadratic, any
`K`-algebra homomorphism from the algebra containing `z` into the normal field containing `y`
can be adjusted to carry `z` to `y`.
-/

public section

namespace TauCeti

variable {K L M : Type*} [Field K] [Field L] [Semiring M] [Algebra K L] [Algebra K M]
  {r : K} {y : L} {z : M}

/-- If `y` and `z` are square roots of the same scalar and `K(y)` is quadratic, any
`K`-algebra homomorphism from the algebra containing `z` into the normal field containing `y` can
be adjusted by an automorphism of the target to carry `z` to `y`. -/
theorem exists_algHom_apply_eq_of_sq_eq [Normal K L]
    (hy : y ^ 2 = algebraMap K L r)
    (hydegree : Module.finrank K (IntermediateField.adjoin K {y}) = 2)
    (hz : z ^ 2 = algebraMap K M r) (hφ : Nonempty (M →ₐ[K] L)) :
    ∃ φ : M →ₐ[K] L, φ z = y := by
  obtain ⟨φ⟩ := hφ
  have hyint : IsIntegral K y := .of_pow two_pos (hy ▸ isIntegral_algebraMap)
  have hmin : minpoly K y = Polynomial.X ^ 2 - Polynomial.C r := by
    apply Algebra.minpoly_eq_X_sq_sub_C_of_sq_eq_of_natDegree_eq_two hy
    rw [← IntermediateField.adjoin.finrank hyint, hydegree]
  have hroot : Polynomial.aeval (φ z) (minpoly K y) = 0 := by
    have hφz : (φ z) ^ 2 = algebraMap K L r := by
      rw [← map_pow, hz, φ.commutes]
    simp [hmin, hφz]
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root hyint.isAlgebraic hroot
  exact ⟨σ.toAlgHom.comp φ, hσ⟩

end TauCeti
