/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Field.Rat

/-!
# Natural numbers invertible in semirings and algebras

A natural number that is a unit in `K` stays nonzero in every nontrivial `K`-algebra `L`. Results
stated over an extension, such as the separable closure `Kˢ`, often need `(m : L) ≠ 0`, while the
hypothesis available is `IsUnit (m : K)`, which holds for every `m ≠ 0` in a `ℚ`-algebra.
Likewise a subalgebra over `K` is closed under division by such a natural number.

## Main results

* `IsUnit.natCast_ne_zero_of_algebra`: if `(m : K)` is a unit then `(m : L) ≠ 0`.
* `IsUnit.neZero_natCast`: a natural number invertible in a nontrivial semiring is nonzero.
* `TauCeti.isUnit_natCast_of_ne_zero`: every nonzero natural number is a unit in a `ℚ`-algebra.
* `Subalgebra.natCast_mul_mem_iff`: if `(m : K)` is a unit, a `K`-subalgebra contains `m * t`
  exactly when it contains `t`.
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

/-- Every nonzero natural number is a unit in a `ℚ`-algebra. -/
theorem TauCeti.isUnit_natCast_of_ne_zero {K : Type*} [Semiring K] [Algebra ℚ K] {m : ℕ}
    (hm : m ≠ 0) : IsUnit (m : K) := by
  simpa using (Nat.cast_ne_zero.2 hm : (m : ℚ) ≠ 0).isUnit.map (algebraMap ℚ K)

/-- A subalgebra over `K` contains `m * t` exactly when it contains `t`, provided the natural
number `m` is invertible in `K`. -/
theorem Subalgebra.natCast_mul_mem_iff {K L : Type*} [CommSemiring K] [Semiring L] [Algebra K L]
    (T : Subalgebra K L) {m : ℕ} (hm : IsUnit (m : K)) {t : L} : (m : L) * t ∈ T ↔ t ∈ T := by
  rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul K]
  exact Submodule.smul_mem_iff_of_isUnit (Subalgebra.toSubmodule T) hm
