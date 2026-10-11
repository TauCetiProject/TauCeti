/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Basic
import Mathlib.Data.Int.GCD

/-!
# Content and primitive parts of integral binary quadratic forms

The content of an integral binary quadratic form is the nonnegative gcd of its three
coefficients. Dividing by it gives a primitive form whenever the original form is nonzero.
The content is also the gcd of all represented values, which makes it invariant under
proper integral changes of variables. Scaling the form multiplies its content by the
absolute value of the scalar and its discriminant by the scalar's square.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §2.
-/

public section

open scoped MatrixGroups

namespace TauCeti.BinaryQuadraticForm

section CommRing

variable {R : Type*} [CommRing R]

/-- Multiply every coefficient of a binary quadratic form by a scalar. -/
def scale (f : BinaryQuadraticForm R) (r : R) : BinaryQuadraticForm R :=
  ⟨r * f.a, r * f.b, r * f.c⟩

/-- The leading coefficient of a scaled form. -/
@[simp] theorem scale_a (f : BinaryQuadraticForm R) (r : R) : (f.scale r).a = r * f.a := (rfl)

/-- The middle coefficient of a scaled form. -/
@[simp] theorem scale_b (f : BinaryQuadraticForm R) (r : R) : (f.scale r).b = r * f.b := (rfl)

/-- The last coefficient of a scaled form. -/
@[simp] theorem scale_c (f : BinaryQuadraticForm R) (r : R) : (f.scale r).c = r * f.c := (rfl)

/-- Scaling a form multiplies each represented value by the scalar. -/
@[simp] theorem eval_scale (f : BinaryQuadraticForm R) (r x y : R) :
    (f.scale r).eval x y = r * f.eval x y := by
  simp only [eval_def, scale_a, scale_b, scale_c]
  ring

/-- Scaling a form multiplies its discriminant by the square of the scalar. -/
@[simp] theorem discrim_scale (f : BinaryQuadraticForm R) (r : R) :
    (f.scale r).discrim = r ^ 2 * f.discrim := by
  simp only [discrim_def, discrim, scale_a, scale_b, scale_c]
  ring

/-- Scaling the coefficients commutes with a proper change of variables. -/
theorem scale_smul (f : BinaryQuadraticForm R) (r : R) (γ : Matrix.SpecialLinearGroup (Fin 2) R) :
    (γ • f).scale r = γ • f.scale r := by
  ext <;> simp only [scale_a, scale_b, scale_c, smul_a, smul_b, smul_c] <;> ring

/-- Scaling by a nonzero scalar is injective over a domain. -/
theorem scale_injective [IsDomain R] {r : R} (hr : r ≠ 0) :
    Function.Injective (fun f : BinaryQuadraticForm R ↦ f.scale r) := by
  intro f g h
  ext
  · exact mul_left_cancel₀ hr (congrArg BinaryQuadraticForm.a h)
  · exact mul_left_cancel₀ hr (congrArg BinaryQuadraticForm.b h)
  · exact mul_left_cancel₀ hr (congrArg BinaryQuadraticForm.c h)

end CommRing

/-- The nonnegative gcd of the three coefficients of an integral binary quadratic form. -/
def content (f : BinaryQuadraticForm ℤ) : ℕ :=
  Int.gcd f.a (Int.gcd f.b f.c)

/-- The content is the gcd of the leading coefficient and the gcd of the other two. -/
theorem content_def (f : BinaryQuadraticForm ℤ) :
    f.content = Int.gcd f.a (Int.gcd f.b f.c) := (rfl)

/-- An integral binary quadratic form is primitive when its coefficients have gcd one. -/
def IsPrimitive (f : BinaryQuadraticForm ℤ) : Prop := f.content = 1

/-- Primitivity is equivalent to content one. -/
theorem isPrimitive_iff (f : BinaryQuadraticForm ℤ) : f.IsPrimitive ↔ f.content = 1 := Iff.rfl

/-- A natural number divides the content exactly when it divides all three coefficients. -/
theorem dvd_content_iff (f : BinaryQuadraticForm ℤ) (n : ℕ) :
    n ∣ f.content ↔ (n : ℤ) ∣ f.a ∧ (n : ℤ) ∣ f.b ∧ (n : ℤ) ∣ f.c := by
  rw [content_def, Int.dvd_gcd_iff, Int.natCast_dvd_natCast, Int.dvd_gcd_iff]

/-- The content divides the leading coefficient. -/
theorem content_dvd_a (f : BinaryQuadraticForm ℤ) : (f.content : ℤ) ∣ f.a :=
  ((f.dvd_content_iff f.content).mp dvd_rfl).1

/-- The content divides the middle coefficient. -/
theorem content_dvd_b (f : BinaryQuadraticForm ℤ) : (f.content : ℤ) ∣ f.b :=
  ((f.dvd_content_iff f.content).mp dvd_rfl).2.1

/-- The content divides the last coefficient. -/
theorem content_dvd_c (f : BinaryQuadraticForm ℤ) : (f.content : ℤ) ∣ f.c :=
  ((f.dvd_content_iff f.content).mp dvd_rfl).2.2

/-- Content zero occurs exactly for the form with all coefficients zero. -/
@[simp] theorem content_eq_zero_iff (f : BinaryQuadraticForm ℤ) :
    f.content = 0 ↔ f = ⟨0, 0, 0⟩ := by
  simp [content_def, BinaryQuadraticForm.ext_iff]

/-- Every nonzero binary quadratic form has positive content. -/
theorem content_pos_iff (f : BinaryQuadraticForm ℤ) :
    0 < f.content ↔ f ≠ ⟨0, 0, 0⟩ := by
  simp [Nat.pos_iff_ne_zero]

/-- The content of a scalar multiple is the absolute scalar times the original content. -/
@[simp] theorem content_scale (f : BinaryQuadraticForm ℤ) (r : ℤ) :
    (f.scale r).content = r.natAbs * f.content := by
  simp only [content_def, scale_a, scale_b, scale_c, Int.gcd_eq_natAbs_gcd_natAbs,
    Int.natAbs_mul, Int.natAbs_natCast, Nat.gcd_mul_left]

/-- Divide all three coefficients by the content. The zero form has zero primitive part. -/
def primitivePart (f : BinaryQuadraticForm ℤ) : BinaryQuadraticForm ℤ :=
  ⟨f.a / f.content, f.b / f.content, f.c / f.content⟩

/-- The leading coefficient of the primitive part. -/
@[simp] theorem primitivePart_a (f : BinaryQuadraticForm ℤ) :
    f.primitivePart.a = f.a / f.content := (rfl)

/-- The middle coefficient of the primitive part. -/
@[simp] theorem primitivePart_b (f : BinaryQuadraticForm ℤ) :
    f.primitivePart.b = f.b / f.content := (rfl)

/-- The last coefficient of the primitive part. -/
@[simp] theorem primitivePart_c (f : BinaryQuadraticForm ℤ) :
    f.primitivePart.c = f.c / f.content := (rfl)

/-- The original form is its content times its primitive part, including for the zero form. -/
@[simp] theorem scale_primitivePart_content (f : BinaryQuadraticForm ℤ) :
    f.primitivePart.scale f.content = f := by
  ext
  · simpa [mul_comm] using Int.ediv_mul_cancel f.content_dvd_a
  · simpa [mul_comm] using Int.ediv_mul_cancel f.content_dvd_b
  · simpa [mul_comm] using Int.ediv_mul_cancel f.content_dvd_c

/-- The primitive part of a nonzero form has content one. -/
theorem isPrimitive_primitivePart (f : BinaryQuadraticForm ℤ) (hf : f ≠ ⟨0, 0, 0⟩) :
    f.primitivePart.IsPrimitive := by
  rw [isPrimitive_iff]
  have h := congrArg content f.scale_primitivePart_content
  rw [content_scale, Int.natAbs_natCast] at h
  exact (mul_left_cancel₀ (Nat.ne_of_gt ((f.content_pos_iff).mpr hf))
    (h.trans (Nat.mul_one _).symm))

/-- A form's discriminant is the square of its content times its primitive discriminant. -/
theorem discrim_eq_content_sq_mul (f : BinaryQuadraticForm ℤ) :
    f.discrim = (f.content : ℤ) ^ 2 * f.primitivePart.discrim := by
  rw [← discrim_scale, scale_primitivePart_content]

/-- Divisibility of every represented value is equivalent to divisibility of the content. -/
theorem dvd_content_iff_forall_eval (f : BinaryQuadraticForm ℤ) (n : ℕ) :
    n ∣ f.content ↔ ∀ x y : ℤ, (n : ℤ) ∣ f.eval x y := by
  rw [dvd_content_iff]
  constructor
  · rintro ⟨ha, hb, hc⟩ x y
    rw [eval_def]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_left ha _)
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hb _) _))
      (dvd_mul_of_dvd_left hc _)
  · intro h
    refine ⟨by simpa using h 1 0, ?_, by simpa using h 0 1⟩
    have hb := dvd_sub (dvd_sub (h 1 1) (h 1 0)) (h 0 1)
    simpa [eval_def, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hb

/-- Proper integral changes of variables preserve the content. -/
@[simp] theorem content_smul (f : BinaryQuadraticForm ℤ)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : (γ • f).content = f.content := by
  have h (g : BinaryQuadraticForm ℤ) (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      g.content ∣ (δ • g).content := by
    apply ((δ • g).dvd_content_iff_forall_eval g.content).mpr
    intro x y
    rw [eval_smul]
    exact (g.dvd_content_iff_forall_eval g.content).mp dvd_rfl _ _
  exact Nat.dvd_antisymm (by simpa using h (γ • f) γ⁻¹) (h f γ)

/-- Taking primitive parts commutes with proper integral changes of variables. -/
theorem primitivePart_smul (f : BinaryQuadraticForm ℤ)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (γ • f).primitivePart = γ • f.primitivePart := by
  by_cases hf : f = ⟨0, 0, 0⟩
  · subst f
    ext <;> simp [primitivePart_a, primitivePart_b, primitivePart_c, content_def]
  · apply scale_injective (r := (f.content : ℤ)) (by
      exact_mod_cast (f.content_pos_iff.mpr hf).ne')
    dsimp only
    rw [← content_smul f γ, scale_primitivePart_content, content_smul,
      scale_smul, scale_primitivePart_content]

/-- The discriminant of a primitive part is invariant under proper changes of variables. -/
@[simp] theorem discrim_primitivePart_smul (f : BinaryQuadraticForm ℤ)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (γ • f).primitivePart.discrim = f.primitivePart.discrim := by
  rw [primitivePart_smul, discrim_smul]

end TauCeti.BinaryQuadraticForm
