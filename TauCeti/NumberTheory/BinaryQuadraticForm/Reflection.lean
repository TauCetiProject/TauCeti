/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Content
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ConjJ

/-!
# Reflection of binary quadratic forms

Reflection is the substitution `(x, y) ↦ (x, -y)`, sending `(a, b, c)` to `(a, -b, c)`.
It is an involution, preserves content and discriminant, commutes with primitive normalization,
and carries properly equivalent forms to properly equivalent forms, so it descends to the
involution `reflectedClass` of the proper classes of primitive positive definite forms. These are
the form-side operations needed by the improper-automorphism criterion for binary integral lattices.
-/

public section

open Matrix
open scoped MatrixGroups

namespace TauCeti.BinaryQuadraticForm

variable {R : Type*}

/-- Reflection in the second variable of a binary quadratic form. -/
def reflected [Neg R] (f : BinaryQuadraticForm R) : BinaryQuadraticForm R :=
  ⟨f.a, -f.b, f.c⟩

@[simp] theorem reflected_a [Neg R] (f : BinaryQuadraticForm R) : f.reflected.a = f.a := (rfl)

@[simp] theorem reflected_b [Neg R] (f : BinaryQuadraticForm R) : f.reflected.b = -f.b := (rfl)

@[simp] theorem reflected_c [Neg R] (f : BinaryQuadraticForm R) : f.reflected.c = f.c := (rfl)

/-- Reflecting twice gives the original form. -/
@[simp] theorem reflected_reflected [InvolutiveNeg R] (f : BinaryQuadraticForm R) :
    f.reflected.reflected = f := by
  ext <;> simp

/-- Reflection is substitution of the negative second variable. -/
@[simp] theorem eval_reflected [Ring R] (f : BinaryQuadraticForm R) (x y : R) :
    f.reflected.eval x y = f.eval x (-y) := by
  simp only [eval_def, reflected_a, reflected_b, reflected_c, neg_mul, mul_neg, neg_sq]

/-- Reflection preserves the discriminant. -/
@[simp] theorem discrim_reflected [CommRing R] (f : BinaryQuadraticForm R) :
    f.reflected.discrim = f.discrim := by
  simp [discrim_def, _root_.discrim]

/-- An external distributive scalar action on the coefficients commutes with reflection. -/
@[simp] theorem reflected_smul' {S : Type*} [AddGroup R] [DistribSMul S R]
    (r : S) (f : BinaryQuadraticForm R) :
    (r • f).reflected = r • f.reflected := by
  ext <;> simp

/-- Reflection preserves the content of an integral form. -/
@[simp] theorem content_reflected (f : BinaryQuadraticForm ℤ) :
    f.reflected.content = f.content := by
  simp [content_def, reflected]

/-- Reflection preserves primitivity of an integral binary form. -/
@[simp] theorem isPrimitive_reflected_iff (f : BinaryQuadraticForm ℤ) :
    f.reflected.IsPrimitive ↔ f.IsPrimitive := by
  rw [isPrimitive_iff, isPrimitive_iff, content_reflected]

/-- Reflection preserves the primitive positive definite forms of discriminant `-n`. -/
theorem reflected_mem_posDef_inf_primitiveForms_iff {n : ℕ} [NeZero n]
    {f : BinaryQuadraticForm ℤ} :
    f.reflected ∈ posDef n ⊓ primitiveForms (-n) ↔ f ∈ posDef n ⊓ primitiveForms (-n) := by
  simp only [mem_posDef_inf_primitiveForms, discrim_reflected, reflected_a,
    isPrimitive_reflected_iff]

/-- Primitive normalization commutes with reflection, including for the zero form. -/
@[simp] theorem primPart_reflected (f : BinaryQuadraticForm ℤ) :
    f.reflected.primPart = f.primPart.reflected := by
  ext
  · simp
  · simp only [primPart_b, content_reflected, reflected_b]
    exact Int.neg_ediv_of_dvd f.content_dvd_b
  · simp

/-- Reflection intertwines a proper change of variables with its canonical coordinate conjugate. -/
@[simp] theorem reflected_smul [CommRing R] (γ : SL(2, R)) (f : BinaryQuadraticForm R) :
    (γ • f).reflected = SpecialLinearGroup.conjJ γ • f.reflected := by
  ext
  all_goals simp only [reflected_a, reflected_b, reflected_c, smul_a, smul_b, smul_c]
  all_goals simp only [SpecialLinearGroup.coe_conjJ, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals ring

/-- The reflection `(a, b, c) ↦ (a, -b, c)` on proper classes of primitive positive definite
forms of discriminant `-n`; it is well defined since `reflected_smul` carries properly equivalent
forms to properly equivalent forms. -/
def reflectedClass (n : ℕ) [NeZero n] : PosDefProperClass n → PosDefProperClass n :=
  Quotient.map (fun f ↦ ⟨(f : BinaryQuadraticForm ℤ).reflected,
      reflected_mem_posDef_inf_primitiveForms_iff.2 f.2⟩)
    fun f g h ↦ by
      obtain ⟨γ, rfl⟩ := MulAction.mem_orbit_iff.1 h
      exact MulAction.mem_orbit_iff.2 ⟨SpecialLinearGroup.conjJ γ, Subtype.ext <|
        (SubMulAction.val_smul _ _).trans (reflected_smul γ (g : BinaryQuadraticForm ℤ)).symm⟩

/-- The reflection of the class of a form is the class of the reflected form. -/
@[simp] theorem reflectedClass_mk {n : ℕ} [NeZero n] (f : ↥(posDef n ⊓ primitiveForms (-n))) :
    reflectedClass n (Quotient.mk _ f) = Quotient.mk _ ⟨(f : BinaryQuadraticForm ℤ).reflected,
      reflected_mem_posDef_inf_primitiveForms_iff.2 f.2⟩ :=
  (rfl)

/-- Reflection on proper classes is an involution. -/
theorem reflectedClass_involutive (n : ℕ) [NeZero n] : Function.Involutive (reflectedClass n) :=
  Quotient.ind fun _ ↦ congrArg (Quotient.mk _) (Subtype.ext (reflected_reflected _))

end TauCeti.BinaryQuadraticForm
