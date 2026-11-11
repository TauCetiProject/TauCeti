/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing

/-!
# The Cayley chart on square roots of `-1`

Let `j` be an element of a ring `A` with `j * j = -1` and in which `2` is a unit. In the ring of
endomorphisms of a real vector space, or of a vector bundle, such a `j` is a complex structure,
and the other complex structures near `j` are parametrized by the endomorphisms anticommuting with
`j` (the `j`-antilinear ones): an antilinear `η` with `1 + η` invertible gives the complex
structure

`cayleyParam j η = (1 + η)⁻¹ * j * (1 + η)`,

and every square root `J` of `-1` with `j + J` invertible arises in this way from exactly one such
`η`, namely its Cayley coordinate

`cayleyCoord j J = (j - J) * (j + J)⁻¹`.

For endomorphism fields of a surface, `cayleyParam` is the formula by which Robbin and Salamon
parametrize local slices of the space of complex structures. On the sets above the two maps can be
rewritten as `j * (1 + η) * (1 - η)⁻¹` and `-(1 + j * J) * (1 - j * J)⁻¹`: they are the inverse
Cayley transform and the Cayley transform of linear complex structures, which
`TauCeti.SymplecticForm.Compatible.cayleyEquiv` restricts to the complex structures tamed by a
symplectic form on a finite-dimensional vector space. Here the algebra is done in an arbitrary
ring, so that it applies verbatim to pointwise endomorphisms and to Banach algebras of
endomorphism fields. The inverses are `Ring.inverse`.

## Main definitions

* `TauCeti.cayleyParam j η`: the square root `(1 + η)⁻¹ * j * (1 + η)` of `-1`.
* `TauCeti.cayleyCoord j J`: the Cayley coordinate `(j - J) * (j + J)⁻¹` of `J` relative to `j`.
* `TauCeti.cayleyEquiv`: for `j * j = -1` and `2` a unit, the bijection `cayleyParam j` from the
  `j`-antilinear `η` with `1 + η` invertible onto the square roots `J` of `-1` with `j + J`
  invertible, with inverse `cayleyCoord j`.

## Main results

* `TauCeti.cayleyParam_mul_self`: `cayleyParam j η` is a square root of `-1`.
* `TauCeti.cayleyParam_eq_iff`, `TauCeti.cayleyCoord_eq_iff`: the defining equations
  `j * (1 + η) = (1 + η) * J` and `j - J = η * (j + J)`; `TauCeti.cayleyParam_mul_inverse`: the
  conjugation identity `cayleyParam j η * (1 + η)⁻¹ = (1 + η)⁻¹ * j`.
* `TauCeti.one_add_mul_add_cayleyParam`, `TauCeti.one_add_cayleyCoord_mul_add`: the identities
  `(1 + η) * (j + cayleyParam j η) = 2 * j` and `(1 + cayleyCoord j J) * (j + J) = 2 * j`, which
  make the two invertibility conditions correspond.
* `TauCeti.cayleyCoord_mul_eq_neg_mul`: the Cayley coordinate of a square root of `-1` is
  `j`-antilinear.
* `TauCeti.cayleyCoord_cayleyParam`, `TauCeti.cayleyParam_cayleyCoord`: the two maps are mutually
  inverse.

## References

* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699, §7 (local slices of the space of complex structures).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, §2.5 (the Cayley transform of linear complex structures).
-/

public section

noncomputable section

namespace TauCeti

variable {A : Type*} [Ring A] {j η J : A}

/-- The **Cayley parametrization** `(1 + η)⁻¹ * j * (1 + η)` of the square roots of `-1` near `j`,
with `Ring.inverse` as inverse. For `j * j = -1` and `1 + η` invertible it is again a square root
of `-1` (`cayleyParam_mul_self`); on the `j`-antilinear `η` it inverts the Cayley coordinate
`cayleyCoord j` (`cayleyEquiv`). -/
def cayleyParam (j η : A) : A :=
  Ring.inverse (1 + η) * j * (1 + η)

/-- The defining formula of `cayleyParam`. -/
lemma cayleyParam_def (j η : A) : cayleyParam j η = Ring.inverse (1 + η) * j * (1 + η) := (rfl)

/-- The **Cayley coordinate** `(j - J) * (j + J)⁻¹` of `J` relative to `j`, with `Ring.inverse` as
inverse. For square roots `j`, `J` of `-1` it anticommutes with `j` (`cayleyCoord_mul_eq_neg_mul`),
and when `j + J` is invertible `cayleyParam j` recovers `J` from it (`cayleyParam_cayleyCoord`). -/
def cayleyCoord (j J : A) : A :=
  (j - J) * Ring.inverse (j + J)

/-- The defining formula of `cayleyCoord`. -/
lemma cayleyCoord_def (j J : A) : cayleyCoord j J = (j - J) * Ring.inverse (j + J) := (rfl)

/-- The defining formula of `cayleyParam j`, as a function of `η`. -/
lemma cayleyParam_eq_fun (j : A) : cayleyParam j = fun η ↦ Ring.inverse (1 + η) * j * (1 + η) :=
  (rfl)

/-- The defining formula of `cayleyCoord j`, as a function of `J`. -/
lemma cayleyCoord_eq_fun (j : A) : cayleyCoord j = fun J ↦ (j - J) * Ring.inverse (j + J) :=
  (rfl)

/-- The parametrization sends `0` to `j`. -/
@[simp]
lemma cayleyParam_zero (j : A) : cayleyParam j 0 = j := by
  simp [cayleyParam_def]

/-- The Cayley coordinate of `j` relative to itself is `0`. -/
@[simp]
lemma cayleyCoord_self (j : A) : cayleyCoord j j = 0 := by
  simp [cayleyCoord_def]

/-- `cayleyParam j η = J` exactly when `j * (1 + η) = (1 + η) * J`, for `1 + η` invertible. -/
lemma cayleyParam_eq_iff (hη : IsUnit (1 + η)) :
    cayleyParam j η = J ↔ j * (1 + η) = (1 + η) * J := by
  obtain ⟨u, hu⟩ := hη
  rw [cayleyParam_def, ← hu, Ring.inverse_unit, mul_assoc, Units.inv_mul_eq_iff_eq_mul]

/-- `cayleyCoord j J = η` exactly when `j - J = η * (j + J)`, for `j + J` invertible. -/
lemma cayleyCoord_eq_iff (hJ : IsUnit (j + J)) :
    cayleyCoord j J = η ↔ j - J = η * (j + J) := by
  obtain ⟨u, hu⟩ := hJ
  rw [cayleyCoord_def, ← hu, Ring.inverse_unit, Units.mul_inv_eq_iff_eq_mul]

/-- The parametrization conjugates `j` by `1 + η`: `(1 + η) * cayleyParam j η = j * (1 + η)`. -/
lemma one_add_mul_cayleyParam (hη : IsUnit (1 + η)) :
    (1 + η) * cayleyParam j η = j * (1 + η) :=
  ((cayleyParam_eq_iff hη).1 rfl).symm

/-- The parametrization conjugates `j` by `1 + η`:
`cayleyParam j η * (1 + η)⁻¹ = (1 + η)⁻¹ * j`. -/
lemma cayleyParam_mul_inverse (hη : IsUnit (1 + η)) :
    cayleyParam j η * Ring.inverse (1 + η) = Ring.inverse (1 + η) * j := by
  obtain ⟨u, hu⟩ := hη
  rw [cayleyParam_def, ← hu, Ring.inverse_unit, Units.mul_inv_cancel_right]

/-- **The Cayley parametrization gives square roots of `-1`.** -/
theorem cayleyParam_mul_self (hj : j * j = -1) (hη : IsUnit (1 + η)) :
    cayleyParam j η * cayleyParam j η = -1 := by
  obtain ⟨u, hu⟩ := hη
  rw [cayleyParam_def, ← hu, Ring.inverse_unit]
  simp only [mul_assoc, Units.mul_inv_cancel_left]
  rw [← mul_assoc j j, hj, neg_one_mul, mul_neg, Units.inv_mul]

/-- For `j`-antilinear `η`, the sum `j + cayleyParam j η` is `2 * j` up to the factor `1 + η`. -/
lemma one_add_mul_add_cayleyParam (hη' : η * j = -(j * η)) (hη : IsUnit (1 + η)) :
    (1 + η) * (j + cayleyParam j η) = 2 * j := by
  rw [mul_add, one_add_mul_cayleyParam hη, add_mul, one_mul, mul_add, mul_one, hη']
  noncomm_ring

/-- For a square root `j` of `-1` in a ring in which `2` is a unit, `2 * j` is a unit. -/
private lemma isUnit_two_mul_of_mul_self_eq_neg_one (h2 : IsUnit (2 : A)) (hj : j * j = -1) :
    IsUnit (2 * j) :=
  h2.mul (isUnit_mul_self_iff.mp (hj.symm ▸ isUnit_neg_one))

/-- For a square root `j` of `-1` in a ring in which `2` is a unit, and `j`-antilinear `η` with
`1 + η` invertible, the sum `j + cayleyParam j η` is invertible. -/
lemma isUnit_add_cayleyParam (h2 : IsUnit (2 : A)) (hj : j * j = -1)
    (hη' : η * j = -(j * η)) (hη : IsUnit (1 + η)) : IsUnit (j + cayleyParam j η) := by
  have h := one_add_mul_add_cayleyParam hη' hη
  obtain ⟨u, hu⟩ := hη
  rw [← hu] at h
  exact (Units.isUnit_units_mul u _).1
    (by rw [h]; exact isUnit_two_mul_of_mul_self_eq_neg_one h2 hj)

/-- For `j + J` invertible, `1 + cayleyCoord j J` is `2 * j` up to the factor `j + J`. -/
lemma one_add_cayleyCoord_mul_add (hJ : IsUnit (j + J)) :
    (1 + cayleyCoord j J) * (j + J) = 2 * j := by
  obtain ⟨u, hu⟩ := hJ
  rw [add_mul, cayleyCoord_def, ← hu, Ring.inverse_unit, Units.inv_mul_cancel_right, hu]
  noncomm_ring

/-- For a square root `j` of `-1` in a ring in which `2` is a unit, and `j + J` invertible,
`1 + cayleyCoord j J` is invertible. -/
lemma isUnit_one_add_cayleyCoord (h2 : IsUnit (2 : A)) (hj : j * j = -1)
    (hJ : IsUnit (j + J)) : IsUnit (1 + cayleyCoord j J) := by
  have h := one_add_cayleyCoord_mul_add hJ
  obtain ⟨u, hu⟩ := hJ
  rw [← hu] at h
  exact (Units.isUnit_mul_units _ u).1
    (by rw [h]; exact isUnit_two_mul_of_mul_self_eq_neg_one h2 hj)

/-- For square roots `j`, `J` of `-1`, `j + J` intertwines `j` and `J`. When `j + J` is
invertible, this says that conjugation by `j + J` carries `j` to `J`. -/
lemma add_mul_eq_mul_add_of_mul_self_eq_neg_one (hj : j * j = -1) (hJJ : J * J = -1) :
    (j + J) * j = J * (j + J) := by
  rw [add_mul, mul_add, hj, hJJ, add_comm]

/-- For square roots `j`, `J` of `-1`, `(j + J)⁻¹` intertwines `j` and `J`. When `j + J` is
invertible, this says that conjugation by `(j + J)⁻¹` carries `j` to `J`; otherwise both sides
are `0`. -/
lemma inverse_add_mul_eq_mul_inverse_add_of_mul_self_eq_neg_one (hj : j * j = -1)
    (hJJ : J * J = -1) : Ring.inverse (j + J) * j = J * Ring.inverse (j + J) := by
  by_cases hJ : IsUnit (j + J)
  · obtain ⟨u, hu⟩ := hJ
    -- Clear the inverses: the claim becomes `j * (j + J) = (j + J) * J`.
    rw [← hu, Ring.inverse_unit, Units.inv_mul_eq_iff_eq_mul, ← mul_assoc,
      Units.eq_mul_inv_iff_mul_eq, hu, add_comm j J,
      add_mul_eq_mul_add_of_mul_self_eq_neg_one hJJ hj]
  · simp [Ring.inverse_non_unit _ hJ]

/-- **The Cayley coordinate is antilinear.** For square roots `j`, `J` of `-1`, the Cayley
coordinate of `J` relative to `j` anticommutes with `j`. -/
theorem cayleyCoord_mul_eq_neg_mul (hj : j * j = -1) (hJJ : J * J = -1) :
    cayleyCoord j J * j = -(j * cayleyCoord j J) := by
  -- Move `j` past `(j + J)⁻¹`, turning it into `J`; what remains is `(j - J) * J = -(j * (j - J))`.
  rw [cayleyCoord_def, mul_assoc, inverse_add_mul_eq_mul_inverse_add_of_mul_self_eq_neg_one hj hJJ,
    ← mul_assoc, ← mul_assoc, ← neg_mul, sub_mul, mul_sub, hj, hJJ]
  noncomm_ring

/-- **The Cayley parametrization inverts the Cayley coordinate.** -/
@[simp]
theorem cayleyParam_cayleyCoord (h2 : IsUnit (2 : A)) (hj : j * j = -1) (hJJ : J * J = -1)
    (hJ : IsUnit (j + J)) : cayleyParam j (cayleyCoord j J) = J := by
  rw [cayleyParam_eq_iff (isUnit_one_add_cayleyCoord h2 hj hJ)]
  have h := one_add_cayleyCoord_mul_add hJ
  obtain ⟨u, hu⟩ := hJ
  -- Multiply by the unit `j + J` on the right: both sides become `2 * j * j`.
  rw [← Units.mul_left_inj u, hu]
  calc j * (1 + cayleyCoord j J) * (j + J)
      = (1 + cayleyCoord j J) * (j + J) * j := by rw [mul_assoc, h, two_mul, mul_add, add_mul]
    _ = (1 + cayleyCoord j J) * J * (j + J) := by
        rw [mul_assoc, add_mul_eq_mul_add_of_mul_self_eq_neg_one hj hJJ, ← mul_assoc]

/-- **The Cayley coordinate inverts the Cayley parametrization** on the `j`-antilinear `η`. -/
@[simp]
theorem cayleyCoord_cayleyParam (h2 : IsUnit (2 : A)) (hj : j * j = -1)
    (hη' : η * j = -(j * η)) (hη : IsUnit (1 + η)) : cayleyCoord j (cayleyParam j η) = η := by
  rw [cayleyCoord_eq_iff (isUnit_add_cayleyParam h2 hj hη' hη)]
  have h := one_add_mul_cayleyParam (j := j) hη
  rw [add_mul, one_mul, mul_add, mul_one, neg_eq_iff_eq_neg.mp hη'.symm] at h
  -- `h` says `J + η * J = j - η * j` for `J = cayleyParam j η`.
  calc j - cayleyParam j η
      = j - cayleyParam j η + (cayleyParam j η + η * cayleyParam j η - (j + -(η * j))) := by
        rw [h, sub_self, add_zero]
    _ = η * (j + cayleyParam j η) := by noncomm_ring

variable (j) in
/-- **The Cayley chart.** For a square root `j` of `-1` in a ring in which `2` is a unit,
`cayleyParam j` is a bijection from the `j`-antilinear `η` with `1 + η` invertible onto the square
roots `J` of `-1` with `j + J` invertible, with inverse `cayleyCoord j`. -/
def cayleyEquiv (h2 : IsUnit (2 : A)) (hj : j * j = -1) :
    {η : A // η * j = -(j * η) ∧ IsUnit (1 + η)} ≃ {J : A // J * J = -1 ∧ IsUnit (j + J)} where
  toFun η := ⟨cayleyParam j η, cayleyParam_mul_self hj η.2.2,
    isUnit_add_cayleyParam h2 hj η.2.1 η.2.2⟩
  invFun J := ⟨cayleyCoord j J, cayleyCoord_mul_eq_neg_mul hj J.2.1,
    isUnit_one_add_cayleyCoord h2 hj J.2.2⟩
  left_inv η := Subtype.ext (cayleyCoord_cayleyParam h2 hj η.2.1 η.2.2)
  right_inv J := Subtype.ext (cayleyParam_cayleyCoord h2 hj J.2.1 J.2.2)

/-- The underlying map of `cayleyEquiv` is `cayleyParam`. -/
@[simp]
lemma coe_cayleyEquiv_apply (h2 : IsUnit (2 : A)) (hj : j * j = -1)
    (η : {η : A // η * j = -(j * η) ∧ IsUnit (1 + η)}) :
    (cayleyEquiv j h2 hj η : A) = cayleyParam j η := (rfl)

/-- The underlying map of the inverse of `cayleyEquiv` is `cayleyCoord`. -/
@[simp]
lemma coe_cayleyEquiv_symm_apply (h2 : IsUnit (2 : A)) (hj : j * j = -1)
    (J : {J : A // J * J = -1 ∧ IsUnit (j + J)}) :
    ((cayleyEquiv j h2 hj).symm J : A) = cayleyCoord j J := (rfl)

end TauCeti
