/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Rat

/-!
# Natural numbers invertible in semirings and algebras

A natural number that is a unit in `K` stays nonzero in every nontrivial `K`-algebra `L`. Results
stated over an extension, such as the separable closure `Kˢ`, often need `(m : L) ≠ 0`, while the
hypothesis available is `IsUnit (m : K)`.

In a `ℚ`-algebra every positive natural number is invertible, so dividing by `k + 1` and
multiplying by `k + 1` cancel. This is how termwise integration of power series inverts
differentiation.

## Main results

* `IsUnit.natCast_ne_zero_of_algebra`: if `(m : K)` is a unit then `(m : L) ≠ 0`.
* `IsUnit.neZero_natCast`: a natural number invertible in a nontrivial semiring is nonzero.
* `TauCeti.inv_natCast_add_one_smul_mul_natCast_add_one`: `(k + 1)⁻¹ • a * (k + 1) = a` in a
  `ℚ`-algebra.
-/

public section

/-- A natural number invertible in `K` is nonzero in every nontrivial `K`-algebra `L`. -/
theorem IsUnit.natCast_ne_zero_of_algebra {K L : Type*} [CommSemiring K] [Semiring L]
    [Nontrivial L] [Algebra K L] {m : ℕ} (hm : IsUnit (m : K)) : (m : L) ≠ 0 := by
  simpa using (hm.map (algebraMap K L)).ne_zero

/-- A natural number invertible in a nontrivial semiring is nonzero as a natural number. -/
theorem IsUnit.neZero_natCast {R : Type*} [Semiring R] [Nontrivial R] {m : ℕ}
    (hm : IsUnit (m : R)) : NeZero m :=
  ⟨fun h ↦ hm.ne_zero (by rw [h, Nat.cast_zero])⟩

namespace TauCeti

/-- Dividing by `k + 1` and multiplying by `k + 1` cancel in a `ℚ`-algebra. -/
theorem inv_natCast_add_one_smul_mul_natCast_add_one {R : Type*} [Semiring R] [Algebra ℚ R]
    (a : R) (k : ℕ) : ((k : ℚ) + 1)⁻¹ • a * ((k : R) + 1) = a := by
  have hcast : (k : R) + 1 = algebraMap ℚ R ((k : ℚ) + 1) := by simp
  rw [hcast, ← Algebra.commutes, ← Algebra.smul_def, smul_smul]
  simp [Nat.cast_add_one_ne_zero]

end TauCeti
