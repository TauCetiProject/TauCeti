/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Log
public import TauCeti.RingTheory.PowerSeries.Derivative

/-!
# The Mahler derivation of power series

The *Mahler derivation* of `R⟦X⟧` is the derivation `∂ = (1 + X) d/dX`. Writing `Y = 1 + X`,
it is the derivation `Y d/dY`, so it acts on the powers `Y ^ a` by `∂ (Y ^ a) = a Y ^ a`. Under the
Amice transform, which sends the Dirac measure at `a ∈ ℤ_p` to `(1 + X) ^ a`, the derivation `∂`
is therefore the transform of multiplying a measure by the coordinate function `x`; this is
proved in `TauCeti.NumberTheory.Padics.Measure.Moments`, where it turns integrals of `x ^ k` into
constant coefficients of iterated Mahler derivatives.

Over a `ℚ`-algebra, substituting `exp X - 1` for `X` conjugates `∂` to the ordinary derivative,
because `d/dX (exp X) = exp X = 1 + (exp X - 1)`. Consequently the constant coefficient of
`∂ ^ k F` is `k !` times the `k`-th coefficient of `F (exp X - 1)`, which is how the moments of a
measure are read off from the exponential substitution in its Amice transform.

## Main definitions

* `PowerSeries.mahlerDerivation R`: the derivation `(1 + X) d/dX` of `R⟦X⟧`.

## Main results

* `PowerSeries.coeff_mahlerDerivation`: the `n`-th coefficient of `∂ F` is
  `(n + 1) a_{n + 1} + n a_n`.
* `PowerSeries.map_iterate_mahlerDerivation`: iterates of `∂` commute with coefficient maps.
* `PowerSeries.derivative_subst_exp_sub_one`: `d/dX (F (exp X - 1)) = (∂ F) (exp X - 1)`.
* `PowerSeries.constantCoeff_iterate_mahlerDerivation`: the constant coefficient of `∂ ^ k F`
  is `k !` times the `k`-th coefficient of `F (exp X - 1)`.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.5.1,
  Lemma 3.29 and Corollary 3.30.
* P. Colmez, *Fonctions d'une variable p-adique*, §II.2.
-/

public section

namespace PowerSeries

variable (R : Type*) [CommSemiring R]

/-- The Mahler derivation `(1 + X) d/dX` of `R⟦X⟧`. It is `Y d/dY` in the variable
`Y = 1 + X`, and under the Amice transform it corresponds to multiplying a measure on `ℤ_p` by the
coordinate function. -/
noncomputable def mahlerDerivation : Derivation R R⟦X⟧ R⟦X⟧ := (1 + X : R⟦X⟧) • derivative

variable {R}

theorem mahlerDerivation_apply (f : R⟦X⟧) :
    mahlerDerivation R f = (1 + X) * d⁄dX f := (rfl)

/-- The coefficients of the Mahler derivation: `coeff n (∂ f) = (n + 1) a_{n + 1} + n a_n`. -/
theorem coeff_mahlerDerivation (f : R⟦X⟧) (n : ℕ) :
    coeff n (mahlerDerivation R f) = (n + 1) * coeff (n + 1) f + n * coeff n f := by
  rw [mahlerDerivation_apply, add_mul, one_mul, map_add, coeff_derivative]
  rcases n with _ | n
  · simp [mul_comm]
  · rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

@[simp]
theorem mahlerDerivation_C (r : R) : mahlerDerivation R (C r) = 0 := by
  simp [mahlerDerivation_apply]

@[simp]
theorem mahlerDerivation_X : mahlerDerivation R X = 1 + X := by
  simp [mahlerDerivation_apply]

/-- The Mahler derivation commutes with change of coefficients. -/
theorem map_mahlerDerivation {S : Type*} [CommSemiring S] (f : R →+* S) (F : R⟦X⟧) :
    map f (mahlerDerivation R F) = mahlerDerivation S (map f F) := by
  simp [mahlerDerivation_apply]

/-- Iterates of the Mahler derivation commute with change of coefficients. -/
theorem map_iterate_mahlerDerivation {S : Type*} [CommSemiring S] (f : R →+* S) (F : R⟦X⟧)
    (k : ℕ) : map f ((mahlerDerivation R)^[k] F) = (mahlerDerivation S)^[k] (map f F) := by
  induction k generalizing F with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, map_mahlerDerivation]

-- `∂X = 1 + X` rejects both `d/dX` and `X d/dX`.
example : mahlerDerivation ℤ X = 1 + X := by simp

example : mahlerDerivation ℤ ((1 + X) ^ 2) = C 2 * (1 + X) ^ 2 := by
  rw [mahlerDerivation_apply, derivative_pow]
  simp
  ring

section Exp

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- Substituting `exp X - 1` conjugates the Mahler derivation to the ordinary derivative:
`d/dX (F (exp X - 1)) = (∂ F) (exp X - 1)`. -/
theorem derivative_subst_exp_sub_one (F : A⟦X⟧) :
    d⁄dX (F.subst (exp A - 1)) = (mahlerDerivation A F).subst (exp A - 1) := by
  have h := HasSubst.exp_sub_one (A := A)
  have hderiv : d⁄dX (exp A - 1) = 1 + (exp A - 1) := by
    simp only [map_sub, derivative_exp, derivative_one, sub_zero, add_sub_cancel]
  calc
    d⁄dX (F.subst (exp A - 1)) =
        (d⁄dX F).subst (exp A - 1) * d⁄dX (exp A - 1) := derivative_subst h
    _ = (1 + (exp A - 1)) * (d⁄dX F).subst (exp A - 1) := by
      rw [hderiv, mul_comm]
    _ = ((1 + X) * d⁄dX F).subst (exp A - 1) := by
      rw [subst_mul h, subst_add h, subst_X h, ← coe_substAlgHom h, map_one]
    _ = (mahlerDerivation A F).subst (exp A - 1) := by
      rw [mahlerDerivation_apply]

/-- The iterated form of `derivative_subst_exp_sub_one`. -/
theorem iterate_derivative_subst_exp_sub_one (F : A⟦X⟧) (k : ℕ) :
    d⁄dX^[k] (F.subst (exp A - 1)) = ((mahlerDerivation A)^[k] F).subst (exp A - 1) := by
  induction k generalizing F with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, derivative_subst_exp_sub_one,
      ih]

/-- The constant coefficient of `∂ ^ k F` is `k !` times the `k`-th coefficient of
`F (exp X - 1)`. -/
theorem constantCoeff_iterate_mahlerDerivation (F : A⟦X⟧) (k : ℕ) :
    constantCoeff ((mahlerDerivation A)^[k] F) = k.factorial * coeff k (F.subst (exp A - 1)) := by
  have h0 : constantCoeff (exp A - 1) = 0 := by simp [constantCoeff_exp]
  have hsubst :
      constantCoeff (((mahlerDerivation A)^[k] F).subst (exp A - 1)) =
        constantCoeff ((mahlerDerivation A)^[k] F) := by
    rw [constantCoeff_eq, constantCoeff_subst_of_constantCoeff_zero h0,
      Algebra.algebraMap_self, RingHom.id_apply]
  calc
    constantCoeff ((mahlerDerivation A)^[k] F) =
        constantCoeff (((mahlerDerivation A)^[k] F).subst (exp A - 1)) := hsubst.symm
    _ = constantCoeff (d⁄dX^[k] (F.subst (exp A - 1))) := by
      rw [iterate_derivative_subst_exp_sub_one]
    _ = k.factorial * coeff k (F.subst (exp A - 1)) :=
      constantCoeff_iterate_derivative _ _

end Exp

end PowerSeries
