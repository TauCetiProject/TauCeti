/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Quadratic algebras with a repeated root

The quadratic algebra `QuadraticAlgebra R 0 0` is `R[X]/(X²)`, which is Mathlib's ring of
dual numbers `R[ε]`. The equivalence `algEquivDualNumber` sends the generator `ω` to `ε`; it
is the lift at `ε`, with inverse `DualNumber.lift` at `ω`.

More generally, when the defining polynomial `X² - bX - a` of `QuadraticAlgebra R a b` is
the square `(X - r)²`, that is `a = -r²` and `b = 2r`, the change of generator `ω ↦ ω - r`
identifies the algebra with the dual numbers (`algEquivDualNumberOfDoubleRoot`).

In the repeated-root algebra the norm of `x + yω` is `x²`, its trace is `2x`, and over a
reduced ring the nilpotent elements are exactly those with vanishing constant coefficient.
In particular the algebra is not reduced over a nontrivial ring.
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

/-- In the repeated-root algebra the norm of `x + yω` is `x²`. -/
theorem norm_eq_re_mul_re (z : QuadraticAlgebra R 0 0) : norm z = z.re * z.re := by
  simp [norm_def]

/-- In the repeated-root algebra the trace of `x + yω` is `2x`. -/
theorem trace_eq_two_mul_re (z : QuadraticAlgebra R 0 0) : trace z = 2 * z.re := by
  simp [trace_def]

/-- Over a reduced ring, an element of the repeated-root algebra is nilpotent exactly when
its constant coefficient vanishes; the nilpotent elements form the line `R ω`. -/
theorem isNilpotent_iff_re_eq_zero [IsReduced R] {z : QuadraticAlgebra R 0 0} :
    IsNilpotent z ↔ z.re = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨2, ?_⟩⟩
  · simpa using (h.map (lift (A := R) ⟨0, by simp⟩)).eq_zero
  · ext <;> simp [sq, h]

/-- Over a nontrivial ring, the repeated-root algebra is not reduced: `ω` is a nonzero
nilpotent. -/
theorem not_isReduced [Nontrivial R] : ¬IsReduced (QuadraticAlgebra R 0 0) := fun _ ↦
  (show (ω : QuadraticAlgebra R 0 0) ≠ 0 by simp [QuadraticAlgebra.ext_iff])
    (IsNilpotent.eq_zero (x := (ω : QuadraticAlgebra R 0 0)) ⟨2, by ext <;> simp [sq]⟩)

end QuadraticAlgebra
