/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
public import TauCeti.Algebra.DualNumber.Basic
import Mathlib.RingTheory.DualNumber

/-!
# Quadratic algebras with a repeated root

The quadratic algebra `QuadraticAlgebra R 0 0` is `R[X]/(X²)`, which is Mathlib's ring of
dual numbers `R[ε]`. The equivalence `algEquivDualNumber` sends the generator `ω` to `ε`; it
is the lift at `ε`, with inverse `DualNumber.lift` at `ω`.

More generally, when the defining polynomial `X² - bX - a` of `QuadraticAlgebra R a b` is
the square `(X - r)²`, that is `a = -r²` and `b = 2r`, the change of generator `ω ↦ ω - r`
identifies the algebra with the dual numbers (`algEquivDualNumberOfDoubleRoot`).

In such an algebra the norm of `x + yω` is `(x + ry)²`, and over a reduced ring the
nilpotent elements are exactly those with `x + ry = 0`. In particular the algebra is not
reduced over a nontrivial ring, since the dual numbers are not. Whenever `b = 0`, the trace of
`x + yω` is `2x`.
-/

public section

open DualNumber TrivSqZeroExt

namespace QuadraticAlgebra

variable {R : Type*} [CommRing R]

/-- The quadratic algebra with defining polynomial `X²` is the ring of dual numbers, with
`ω ↦ ε`. -/
def algEquivDualNumber : QuadraticAlgebra R 0 0 ≃ₐ[R] R[ε] :=
  AlgEquiv.ofAlgHom (lift ⟨ε, by simp [eps_mul_eps]⟩)
    (DualNumber.lift ⟨(Algebra.ofId R _, ω), by ext <;> simp, fun _ ↦ Commute.all _ _⟩)
    (DualNumber.algHom_ext (by simp)) (algHom_ext (by simp))

@[simp]
theorem algEquivDualNumber_omega : algEquivDualNumber (ω : QuadraticAlgebra R 0 0) = ε := by
  simp [algEquivDualNumber]

@[simp]
theorem fst_algEquivDualNumber (z : QuadraticAlgebra R 0 0) :
    (algEquivDualNumber z).fst = z.re := by
  simp [algEquivDualNumber]

@[simp]
theorem snd_algEquivDualNumber (z : QuadraticAlgebra R 0 0) :
    (algEquivDualNumber z).snd = z.im := by
  simp [algEquivDualNumber]

theorem algEquivDualNumber_symm_eps :
    (algEquivDualNumber (R := R)).symm ε = ω := by
  rw [AlgEquiv.symm_apply_eq, algEquivDualNumber_omega]

/-- The inverse of `algEquivDualNumber` reads off the two coordinates of a dual number. -/
@[simp]
theorem algEquivDualNumber_symm_apply (x : R[ε]) :
    (algEquivDualNumber (R := R)).symm x = ⟨x.fst, x.snd⟩ := by
  rw [AlgEquiv.symm_apply_eq]
  ext <;> simp

/-- A quadratic algebra whose defining polynomial is `(X - r)²` is the ring of dual numbers,
with `ω ↦ r + ε`. -/
def algEquivDualNumberOfDoubleRoot {a b : R} (r : R) (ha : a = -r ^ 2) (hb : b = 2 * r) :
    QuadraticAlgebra R a b ≃ₐ[R] R[ε] :=
  (changeGeneratorEquiv 0 0 1 r (by simp [ha]) (by simp [hb])).trans algEquivDualNumber

@[simp]
theorem fst_algEquivDualNumberOfDoubleRoot {a b : R} (r : R) (ha : a = -r ^ 2)
    (hb : b = 2 * r) (z : QuadraticAlgebra R a b) :
    (algEquivDualNumberOfDoubleRoot r ha hb z).fst = z.re + r * z.im := by
  simp [algEquivDualNumberOfDoubleRoot, mul_comm]

@[simp]
theorem snd_algEquivDualNumberOfDoubleRoot {a b : R} (r : R) (ha : a = -r ^ 2)
    (hb : b = 2 * r) (z : QuadraticAlgebra R a b) :
    (algEquivDualNumberOfDoubleRoot r ha hb z).snd = z.im := by
  simp [algEquivDualNumberOfDoubleRoot]

theorem algEquivDualNumberOfDoubleRoot_omega {a b : R} (r : R) (ha : a = -r ^ 2)
    (hb : b = 2 * r) :
    algEquivDualNumberOfDoubleRoot r ha hb (ω : QuadraticAlgebra R a b) = inl r + ε := by
  ext <;> simp

/-- The inverse of `algEquivDualNumberOfDoubleRoot` sends `x + yε` to `(x - ry) + yω`. -/
@[simp]
theorem algEquivDualNumberOfDoubleRoot_symm_apply {a b : R} (r : R) (ha : a = -r ^ 2)
    (hb : b = 2 * r) (x : R[ε]) :
    (algEquivDualNumberOfDoubleRoot r ha hb).symm x = ⟨x.fst - r * x.snd, x.snd⟩ := by
  rw [AlgEquiv.symm_apply_eq]
  ext <;> simp

/-- When the defining polynomial is `(X - r)²`, the norm of `x + yω` is `(x + ry)²`. -/
theorem norm_eq_sq_of_double_root {a b : R} (r : R) (ha : a = -r ^ 2) (hb : b = 2 * r)
    (z : QuadraticAlgebra R a b) : norm z = (z.re + r * z.im) ^ 2 := by
  subst ha hb
  rw [norm_def]
  ring

/-- When `b = 0`, so in particular in `QuadraticAlgebra R 0 0`, the trace of `x + yω` is
`2x`. -/
theorem trace_eq_two_mul_re {a : R} (z : QuadraticAlgebra R a 0) : trace z = 2 * z.re := by
  simp [trace_def]

/-- Over a reduced ring, when the defining polynomial is `(X - r)²`, an element `x + yω` is
nilpotent exactly when `x + ry = 0`. For `QuadraticAlgebra R 0 0` (take `r = 0`) the
nilpotent elements form the line `R ω`. -/
theorem isNilpotent_iff_of_double_root [IsReduced R] {a b : R} (r : R) (ha : a = -r ^ 2)
    (hb : b = 2 * r) {z : QuadraticAlgebra R a b} :
    IsNilpotent z ↔ z.re + r * z.im = 0 := by
  rw [← IsNilpotent.map_iff (algEquivDualNumberOfDoubleRoot r ha hb).injective,
    isNilpotent_iff_isNilpotent_fst, isNilpotent_iff_eq_zero,
    fst_algEquivDualNumberOfDoubleRoot]

/-- Over a nontrivial ring, a quadratic algebra whose defining polynomial is `(X - r)²` is not
reduced, since the dual numbers are not. -/
theorem not_isReduced_of_double_root [Nontrivial R] {a b : R} (r : R) (ha : a = -r ^ 2)
    (hb : b = 2 * r) : ¬IsReduced (QuadraticAlgebra R a b) := fun _ ↦
  DualNumber.not_isReduced <|
    isReduced_of_injective (algEquivDualNumberOfDoubleRoot r ha hb).symm (AlgEquiv.injective _)

end QuadraticAlgebra
