/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Elementary transvections of a free module

For two distinct generators `a ≠ b` of the free module `ι →₀ R` over a ring `R` and `c ∈ R`, the
elementary transvection `Finsupp.transvection hab c` sends `x` to `x + single b (x a * c)`: it
sends the generator `a` to `a + c b` and fixes the other generators. It is Mathlib's
`LinearEquiv.transvection` for the coordinate form at `a` and the vector `single b c`, which this
form kills because `a ≠ b`, so its group laws come from Mathlib's.

## Main results

* `Finsupp.transvection_apply`: the transvection sends `x` to `x + single b (x a * c)`.
* `Finsupp.transvection_trans`, `Finsupp.transvection_symm`, `Finsupp.transvection_zero`:
  transvections along the same pair of generators compose by adding their coefficients.
* `Finsupp.mapRange_transvection`: transvections commute with changes of coefficients along a
  ring homomorphism.
-/

public section

namespace Finsupp

variable {R ι : Type*} [Ring R] {a b : ι}

/-- The elementary transvection of the free module `ι →₀ R` adding `c` times the generator `b` to
the generator `a`: it sends `x` to `x + single b (x a * c)`, so `single a r` to
`single a r + single b (r * c)`, and fixes the other generators. It is Mathlib's
`LinearEquiv.transvection` for the coordinate form at `a` and the vector `single b c`, which this
form kills because `a ≠ b`. -/
noncomputable def transvection (hab : a ≠ b) (c : R) : (ι →₀ R) ≃ₗ[R] (ι →₀ R) :=
  LinearEquiv.transvection (f := lapply a) (v := single b c) (by simp [hab])

variable (hab : a ≠ b) (c : R)

theorem transvection_apply (x : ι →₀ R) : transvection hab c x = x + single b (x a * c) := by
  simp [transvection, LinearMap.transvection.apply, smul_single]

/-- The transvection only changes the coefficient of `b`. -/
@[simp]
theorem transvection_apply_of_ne (x : ι →₀ R) {j : ι} (hj : j ≠ b) :
    transvection hab c x j = x j := by
  simp [transvection_apply, single_eq_of_ne hj]

/-- The transvection adds `c` times the coefficient of `a` to the coefficient of `b`. -/
@[simp]
theorem transvection_apply_right (x : ι →₀ R) : transvection hab c x b = x b + x a * c := by
  simp [transvection_apply]

@[simp]
theorem transvection_single_self (r : R) :
    transvection hab c (single a r) = single a r + single b (r * c) := by
  simp [transvection_apply]

@[simp]
theorem transvection_single_of_ne {i : ι} (hi : i ≠ a) (r : R) :
    transvection hab c (single i r) = single i r := by
  simp [transvection_apply, single_eq_of_ne hi.symm]

@[simp]
theorem transvection_zero : transvection hab (0 : R) = LinearEquiv.refl R (ι →₀ R) := by
  simp [transvection]

/-- Transvections along the same pair of generators compose by adding their coefficients. -/
@[simp]
theorem transvection_trans (c' : R) :
    (transvection hab c).trans (transvection hab c') = transvection hab (c + c') := by
  rw [transvection, transvection, transvection,
    LinearEquiv.transvection.trans_of_left_eq (by simp [hab]) (by simp [hab]) (by simp [hab])]
  congr 1
  rw [single_add, add_comm]

@[simp]
theorem transvection_symm : (transvection hab c).symm = transvection hab (-c) := by
  rw [transvection, transvection, LinearEquiv.transvection.symm_eq (by simp [hab]) (by simp [hab])]
  congr 1
  rw [single_neg]

/-- Transvections commute with changes of coefficients along a ring homomorphism. -/
theorem mapRange_transvection {R' : Type*} [Ring R'] (g : R →+* R') (x : ι →₀ R) :
    mapRange g (map_zero g) (transvection hab c x) =
      transvection hab (g c) (mapRange g (map_zero g) x) := by
  ext j
  by_cases hj : j = b
  · subst hj
    simp
  · simp [hj]

end Finsupp
