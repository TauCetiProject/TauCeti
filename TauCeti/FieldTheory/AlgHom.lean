/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
import TauCeti.FieldTheory.Minpoly

/-!
# Moving roots by algebra homomorphisms

If `y` and `z` are square roots of the same scalar `r : K` and `K(y)` is quadratic, any
`K`-algebra homomorphism from the algebra containing `z` into the normal field containing `y`
can be adjusted to carry `z` to `y`. Also, an `n`th root of a unit of `K` in `L` maps under a
`K`-embedding `L → E` of fields to the underlying element of a unit of `E` with the same `n`th
power.

## Main statements

* `TauCeti.exists_algHom_apply_eq_of_sq_eq`: a `K`-algebra homomorphism can be adjusted by an
  automorphism of the target to carry one square root of a scalar to another.
* `AlgHom.exists_unit_pow_eq_map`: an embedding carries an `n`th root of a unit of `K` to the
  underlying element of a unit of the target.
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
    refine Algebra.minpoly_eq_X_pow_sub_C_of_pow_eq_of_natDegree_eq two_ne_zero hy ?_
    rw [← IntermediateField.adjoin.finrank hyint, hydegree]
  have hroot : Polynomial.aeval (φ z) (minpoly K y) = 0 := by
    have hφz : (φ z) ^ 2 = algebraMap K L r := by
      rw [← map_pow, hz, φ.commutes]
    simp [hmin, hφz]
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root hyint.isAlgebraic hroot
  exact ⟨σ.toAlgHom.comp φ, hσ⟩

end TauCeti

variable {K L E : Type*} [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E] {n : ℕ}

/-- If `s ^ n = b` in `L`, then the image of `s` under a `K`-embedding `ι : L → E` is the
underlying element of a unit of `E` whose `n`-th power is `b`. -/
theorem AlgHom.exists_unit_pow_eq_map [NeZero n] (ι : L →ₐ[K] E)
    (b : Kˣ) {s : L} (hs : s ^ n = algebraMap K L b) :
    ∃ β : Eˣ, (β : E) = ι s ∧ β ^ n = Units.map (algebraMap K E).toMonoidHom b := by
  have hs0 : ι s ≠ 0 := (map_ne_zero_iff _ ι.injective).2 <| by
    rintro rfl
    rw [zero_pow (NeZero.ne n), eq_comm, map_eq_zero] at hs
    exact b.ne_zero hs
  exact ⟨Units.mk0 (ι s) hs0, rfl, Units.ext <| by simp [← map_pow, hs]⟩
