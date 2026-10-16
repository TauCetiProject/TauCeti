/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module
public import Mathlib.Algebra.QuadraticAlgebra.Discriminant
public import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import TauCeti.Algebra.Polynomial.QuadraticDiscriminant
import Mathlib.Tactic.Ring

/-!
# Quadratic étale algebras

A quadratic algebra over a commutative ring is étale when its discriminant is a unit.
Over a field this is the nonzero-discriminant criterion, including in characteristic two.

## References

* Mathlib's `Mathlib.RingTheory.Etale.StandardEtale`, for `StandardEtalePair` and its
  universal mapping API.
-/

public section

open Polynomial

namespace QuadraticAlgebra

private noncomputable def quadraticEtalePair {R : Type*} [CommRing R]
    (a b : R) (hd : IsUnit (discr a b)) : StandardEtalePair R where
  f := X ^ 2 - (C b * X + C a)
  monic_f := monic_X_pow_sub degree_linear_lt
  g := 1
  cond := by
    have hsep := separable_quadratic_of_isUnit_discrim
      (a := (1 : R)) (b := -b) (c := -a) (by simpa [discrim, discr_def] using hd)
    have hf : C (1 : R) * X ^ 2 + C (-b) * X + C (-a) = X ^ 2 - (C b * X + C a) := by
      simp only [map_one, map_neg, one_mul]
      ring
    rw [hf] at hsep
    obtain ⟨p, q, hpq⟩ := (separable_def' _).mp hsep
    exact ⟨q, p, 0, by simpa only [pow_zero, mul_comm, add_comm] using hpq⟩

/-- A quadratic algebra over a commutative ring with unit discriminant is étale. -/
theorem etale_of_isUnit_discr {R : Type*} [CommRing R] {a b : R} (hd : IsUnit (discr a b)) :
    Algebra.Etale R (QuadraticAlgebra R a b) := by
  let P := quadraticEtalePair a b hd
  have hx : P.X * P.X = a • (1 : P.Ring) + b • P.X := by
    have h := P.hasMap_X.1
    -- Reduce the presentation's polynomial in the relation for its canonical generator.
    change aeval P.X (X ^ 2 - (C b * X + C a)) = 0 at h
    simpa [pow_two, Algebra.smul_def, sub_eq_zero, add_comm] using h
  have hω : P.HasMap (ω : QuadraticAlgebra R a b) := by
    constructor
    -- Reduce `P.f` in the root condition of `HasMap`.
    · change aeval ω (X ^ 2 - (C b * X + C a)) = 0
      simp [pow_two, omega_mul_omega_eq_add, Algebra.smul_def, add_comm]
    -- Reduce `P.g = 1` in the localization condition of `HasMap`.
    · change IsUnit (aeval ω (1 : R[X]))
      simp
  let f : P.Ring →ₐ[R] QuadraticAlgebra R a b := P.lift ω hω
  let g : QuadraticAlgebra R a b →ₐ[R] P.Ring := lift ⟨P.X, hx⟩
  have hfg : f.comp g = AlgHom.id R (QuadraticAlgebra R a b) := by
    apply algHom_ext
    simp [f, g]
  have hgf : g.comp f = AlgHom.id R P.Ring := by
    apply P.hom_ext
    simp [f, g]
  exact Algebra.Etale.of_equiv (AlgEquiv.ofAlgHom f g hfg hgf)

/-- A quadratic algebra over a field with nonzero discriminant is étale. -/
theorem etale_of_discr_ne_zero {K : Type*} [Field K] {a b : K} (hd : discr a b ≠ 0) :
    Algebra.Etale K (QuadraticAlgebra K a b) :=
  etale_of_isUnit_discr (isUnit_iff_ne_zero.mpr hd)

end QuadraticAlgebra
