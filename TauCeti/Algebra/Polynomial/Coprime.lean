/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Algebra.Polynomial.Basic

/-!
# Coprimality of normalised linear factors

The factors `1 - a X` and `1 - b X` are coprime when `a - b` is a unit. This is useful
for separating spectral summands over coefficient rings, where distinct scalars alone
need not be separated by a unit.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R] {a b : R}

/-- Normalised linear factors are coprime if the difference of their parameters is a unit.
Neither parameter itself needs to be a unit. -/
theorem isCoprime_one_sub_C_mul_X_of_isUnit_sub (hab : IsUnit (a - b)) :
    IsCoprime (1 - C a * X) (1 - C b * X) := by
  obtain ⟨c, hc⟩ := hab
  refine ⟨C (-(c⁻¹ : Rˣ) * b), C ((c⁻¹ : Rˣ) * a), ?_⟩
  have h : (c⁻¹ : Rˣ) * (a - b) = (1 : R) := by rw [← hc]; simp
  calc
    C (-(c⁻¹ : Rˣ) * b) * (1 - C a * X) +
        C ((c⁻¹ : Rˣ) * a) * (1 - C b * X) = C ((c⁻¹ : Rˣ) * (a - b)) := by
      simp only [map_mul, map_neg, map_sub]
      ring
    _ = 1 := by rw [h, map_one]

end Polynomial
