/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Int.GCD

/-!
# Content and primitive forms of fixed discriminant

The content of an integral binary quadratic form is the nonnegative gcd of its three
coefficients. Dividing by it gives a primitive form whenever the original form is nonzero.
The content is also the gcd of all represented values, which makes it invariant under
proper integral changes of variables. Scaling the form multiplies its content by the
absolute value of the scalar and its discriminant by the scalar's square.
Dividing a nonzero integer vector by its gcd gives coprime coordinates and divides
every represented value by the square of that gcd.

The invariance of discriminant and primitivity packages primitive forms of a fixed
discriminant in the subaction `primitiveForms D`, stable under `SL(2, ℤ)`. This gives the
carrier for proper-equivalence and orbit constructions among forms of that discriminant.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §2.
-/

public section

open scoped MatrixGroups

namespace TauCeti.BinaryQuadraticForm

/-- Dividing a nonzero integer vector by its gcd gives coprime coordinates and scales
its represented value by the square of the gcd. -/
theorem exists_isCoprime_eval_eq_gcd_sq_mul (f : BinaryQuadraticForm ℤ) (x y : ℤ)
    (hxy : x ≠ 0 ∨ y ≠ 0) :
    ∃ u v : ℤ, IsCoprime u v ∧ x = u * Int.gcd x y ∧ y = v * Int.gcd x y ∧
      f.eval x y = (Int.gcd x y : ℤ) ^ 2 * f.eval u v := by
  have hgcd : 0 < Int.gcd x y := by
    rcases hxy with hx | hy
    · exact Int.gcd_pos_of_ne_zero_left y hx
    · exact Int.gcd_pos_of_ne_zero_right x hy
  obtain ⟨u, v, huv, hx, hy⟩ := Int.exists_gcd_one hgcd
  refine ⟨u, v, Int.isCoprime_iff_gcd_eq_one.mpr huv, hx, hy, ?_⟩
  calc
    f.eval x y = f.eval (u * Int.gcd x y) (v * Int.gcd x y) := congrArg₂ f.eval hx hy
    _ = (Int.gcd x y : ℤ) ^ 2 * f.eval u v := by
      simp only [eval_def]
      ring

/-- The nonnegative gcd of the three coefficients of an integral binary quadratic form. -/
def content (f : BinaryQuadraticForm ℤ) : ℕ :=
  Int.gcd f.a (Int.gcd f.b f.c)

/-- The content is the gcd of the leading coefficient and the gcd of the other two. -/
theorem content_def (f : BinaryQuadraticForm ℤ) :
    f.content = Int.gcd f.a (Int.gcd f.b f.c) := (rfl)

/-- The zero form has content zero. -/
@[simp] theorem content_zero : (0 : BinaryQuadraticForm ℤ).content = 0 := by
  simp [content_def]

/-- An integral binary quadratic form is primitive when its coefficients have gcd one. -/
def IsPrimitive (f : BinaryQuadraticForm ℤ) : Prop := f.content = 1

/-- Primitivity is equivalent to content one. -/
theorem isPrimitive_iff (f : BinaryQuadraticForm ℤ) : f.IsPrimitive ↔ f.content = 1 := Iff.rfl

/-- The zero form is not primitive. -/
@[simp] theorem not_isPrimitive_zero : ¬ (0 : BinaryQuadraticForm ℤ).IsPrimitive := by
  simp [isPrimitive_iff]

/-- A primitive integral form is nonzero. -/
theorem IsPrimitive.ne_zero {f : BinaryQuadraticForm ℤ} (hf : f.IsPrimitive) : f ≠ 0 := by
  rintro rfl
  exact not_isPrimitive_zero hf

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
    f.content = 0 ↔ f = 0 := by
  simp [content_def, BinaryQuadraticForm.ext_iff]

/-- Every nonzero binary quadratic form has positive content. -/
theorem content_pos_iff (f : BinaryQuadraticForm ℤ) :
    0 < f.content ↔ f ≠ 0 := by
  simp [Nat.pos_iff_ne_zero]

/-- The content of a scalar multiple is the absolute scalar times the original content. -/
@[simp] theorem content_smul' (f : BinaryQuadraticForm ℤ) (r : ℤ) :
    (r • f).content = r.natAbs * f.content := by
  simp only [content_def, smul_a', smul_b', smul_c', smul_eq_mul, Int.gcd_eq_natAbs_gcd_natAbs,
    Int.natAbs_mul, Int.natAbs_natCast, Nat.gcd_mul_left]

/-- Natural scalar multiplication multiplies the content by that scalar. -/
@[simp] theorem content_nsmul (f : BinaryQuadraticForm ℤ) (n : ℕ) :
    (n • f).content = n * f.content := by
  simpa only [natCast_zsmul, Int.natAbs_natCast] using content_smul' f (n : ℤ)

/-- Negation preserves the content. -/
@[simp] theorem content_neg (f : BinaryQuadraticForm ℤ) : (-f).content = f.content := by
  simpa only [neg_one_smul, Int.natAbs_neg, Int.natAbs_one, one_mul] using content_smul' f (-1)

/-- Divide all three coefficients by the content. The zero form has zero primitive part. -/
def primPart (f : BinaryQuadraticForm ℤ) : BinaryQuadraticForm ℤ :=
  ⟨f.a / f.content, f.b / f.content, f.c / f.content⟩

/-- The leading coefficient of the primitive part. -/
@[simp] theorem primPart_a (f : BinaryQuadraticForm ℤ) :
    f.primPart.a = f.a / f.content := (rfl)

/-- The middle coefficient of the primitive part. -/
@[simp] theorem primPart_b (f : BinaryQuadraticForm ℤ) :
    f.primPart.b = f.b / f.content := (rfl)

/-- The last coefficient of the primitive part. -/
@[simp] theorem primPart_c (f : BinaryQuadraticForm ℤ) :
    f.primPart.c = f.c / f.content := (rfl)

/-- The primitive part of the zero form is zero. -/
@[simp] theorem primPart_zero : (0 : BinaryQuadraticForm ℤ).primPart = 0 := by
  ext <;> simp

/-- The original form is its content times its primitive part, including for the zero form. -/
@[simp] theorem content_smul_primPart (f : BinaryQuadraticForm ℤ) :
    f.content • f.primPart = f := by
  ext
  · simpa [smul_eq_mul, nsmul_eq_mul, mul_comm] using Int.ediv_mul_cancel f.content_dvd_a
  · simpa [smul_eq_mul, nsmul_eq_mul, mul_comm] using Int.ediv_mul_cancel f.content_dvd_b
  · simpa [smul_eq_mul, nsmul_eq_mul, mul_comm] using Int.ediv_mul_cancel f.content_dvd_c

/-- A form has zero primitive part exactly when the form itself is zero. -/
@[simp] theorem primPart_eq_zero_iff (f : BinaryQuadraticForm ℤ) :
    f.primPart = 0 ↔ f = 0 := by
  constructor
  · intro h
    have hf := f.content_smul_primPart
    rw [h, smul_zero] at hf
    exact hf.symm
  · rintro rfl
    exact primPart_zero

/-- The primitive part of a nonzero form has content one. -/
theorem isPrimitive_primPart (f : BinaryQuadraticForm ℤ) (hf : f ≠ 0) :
    f.primPart.IsPrimitive := by
  rw [isPrimitive_iff]
  have h := congrArg content f.content_smul_primPart
  rw [content_nsmul] at h
  exact (mul_left_cancel₀ (Nat.ne_of_gt ((f.content_pos_iff).mpr hf))
    (h.trans (Nat.mul_one _).symm))

/-- A primitive form is its own primitive part. -/
@[simp] theorem IsPrimitive.primPart_eq {f : BinaryQuadraticForm ℤ} (hf : f.IsPrimitive) :
    f.primPart = f := by
  ext <;> simp [(isPrimitive_iff f).mp hf]

/-- A scalar multiple of a primitive form has content the absolute scalar. -/
theorem content_smul_of_isPrimitive (f : BinaryQuadraticForm ℤ) (r : ℤ)
    (hf : f.IsPrimitive) : (r • f).content = r.natAbs := by
  rw [content_smul', (isPrimitive_iff f).mp hf, mul_one]

/-- Primitive normalization of a scalar multiple retains only the sign of the scalar.
The formula also holds when either the scalar or the form is zero. -/
theorem primPart_smul' (f : BinaryQuadraticForm ℤ) (r : ℤ) :
    (r • f).primPart = r.sign • f.primPart := by
  by_cases hf : f = 0
  · simp [hf]
  by_cases hr : r = 0
  · simp [hr]
  have hc : (r • f).content ≠ 0 := by
    rw [content_smul']
    exact mul_ne_zero (Int.natAbs_ne_zero.mpr hr) (f.content_pos_iff.mpr hf).ne'
  have hrs : (r.natAbs : ℤ) * r.sign = r := by
    simpa only [mul_comm] using Int.sign_mul_natAbs r
  apply smul_right_injective (M := BinaryQuadraticForm ℤ)
    (r := ((r • f).content : ℤ)) (by exact_mod_cast hc)
  dsimp only
  calc
    ((r • f).content : ℤ) • (r • f).primPart = r • f := by
      rw [natCast_zsmul, content_smul_primPart]
    _ = r • ((f.content : ℤ) • f.primPart) := by
      rw [natCast_zsmul, content_smul_primPart]
    _ = ((r • f).content : ℤ) • (r.sign • f.primPart) := by
      rw [smul_smul, smul_smul, content_smul', Nat.cast_mul,
        mul_right_comm (r.natAbs : ℤ) (f.content : ℤ) r.sign, hrs]

/-- For a primitive form, scalar normalization retains the sign times the form itself. -/
theorem primPart_smul_of_isPrimitive (f : BinaryQuadraticForm ℤ) (r : ℤ)
    (hf : f.IsPrimitive) : (r • f).primPart = r.sign • f := by
  rw [primPart_smul', hf.primPart_eq]

/-- Primitive normalization commutes with negation. -/
@[simp] theorem primPart_neg (f : BinaryQuadraticForm ℤ) : (-f).primPart = -f.primPart := by
  simpa only [neg_one_smul, Int.sign_neg, Int.sign_one] using primPart_smul' f (-1)

/-- The decomposition into positive content and a primitive form is unique. -/
theorem eq_smul_iff_of_isPrimitive (f g : BinaryQuadraticForm ℤ) {c : ℕ}
    (hc : 0 < c) (hg : g.IsPrimitive) :
    f = (c : ℤ) • g ↔ f.content = c ∧ f.primPart = g := by
  constructor
  · intro h
    rw [h]
    constructor
    · rw [content_smul_of_isPrimitive _ _ hg, Int.natAbs_natCast]
    · rw [primPart_smul_of_isPrimitive _ _ hg,
        Int.sign_eq_one_of_pos (by exact_mod_cast hc), one_smul]
  · rintro ⟨hc, hg⟩
    rw [← hc, ← hg, natCast_zsmul, content_smul_primPart]

/-- A form's discriminant is the square of its content times its primitive discriminant. -/
theorem discrim_eq_content_sq_mul (f : BinaryQuadraticForm ℤ) :
    f.discrim = (f.content : ℤ) ^ 2 * f.primPart.discrim := by
  rw [← discrim_smul', natCast_zsmul, content_smul_primPart]

/-- Divisibility of every represented value is equivalent to divisibility of the content. -/
theorem dvd_content_iff_forall_eval (f : BinaryQuadraticForm ℤ) (n : ℕ) :
    n ∣ f.content ↔ ∀ x y : ℤ, (n : ℤ) ∣ f.eval x y := by
  rw [dvd_content_iff]
  constructor
  · rintro ⟨ha, hb, hc⟩ x y
    obtain ⟨a', ha⟩ := ha
    obtain ⟨b', hb⟩ := hb
    obtain ⟨c', hc⟩ := hc
    refine ⟨a' * x ^ 2 + b' * x * y + c' * y ^ 2, ?_⟩
    rw [eval_def, ha, hb, hc]
    ring
  · intro h
    refine ⟨by simpa using h 1 0, ?_, by simpa using h 0 1⟩
    have hb : f.b = f.eval 1 1 - f.eval 1 0 - f.eval 0 1 := by
      simp only [eval_def]
      ring
    rw [hb]
    exact dvd_sub (dvd_sub (h 1 1) (h 1 0)) (h 0 1)

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

/-- Primitivity is preserved by proper integral changes of variables. -/
@[simp] theorem isPrimitive_smul_iff (f : BinaryQuadraticForm ℤ)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : (γ • f).IsPrimitive ↔ f.IsPrimitive := by
  rw [isPrimitive_iff, isPrimitive_iff, content_smul]

/-- Primitive forms of fixed discriminant, with the proper special-linear action. -/
def primitiveForms (D : ℤ) :
    SubMulAction (Matrix.SpecialLinearGroup (Fin 2) ℤ) (BinaryQuadraticForm ℤ) where
  carrier := {f | f.discrim = D ∧ f.IsPrimitive}
  smul_mem' γ f := by
    rintro ⟨hf, hprim⟩
    exact ⟨(discrim_smul γ f).trans hf, (isPrimitive_smul_iff f γ).mpr hprim⟩

/-- Membership in the primitive fixed-discriminant forms. -/
@[simp] theorem mem_primitiveForms (D : ℤ) (f : BinaryQuadraticForm ℤ) :
    f ∈ primitiveForms D ↔ f.discrim = D ∧ f.IsPrimitive := by
  rfl

/-- Taking primitive parts commutes with proper integral changes of variables. -/
theorem primPart_smul (f : BinaryQuadraticForm ℤ)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (γ • f).primPart = γ • f.primPart := by
  by_cases hf : f = 0
  · subst f
    simp
  · apply smul_right_injective (M := BinaryQuadraticForm ℤ) (r := (f.content : ℤ)) (by
      exact_mod_cast (f.content_pos_iff.mpr hf).ne')
    dsimp only
    calc
      (f.content : ℤ) • (γ • f).primPart = γ • f := by
        rw [← content_smul f γ, natCast_zsmul, content_smul_primPart]
      _ = γ • ((f.content : ℤ) • f.primPart) := by
        rw [natCast_zsmul, content_smul_primPart]
      _ = (f.content : ℤ) • (γ • f.primPart) := (smul_comm _ _ _).symm

/-- The discriminant of a primitive part is invariant under proper changes of variables. -/
@[simp] theorem discrim_primPart_smul (f : BinaryQuadraticForm ℤ)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (γ • f).primPart.discrim = f.primPart.discrim := by
  rw [primPart_smul, discrim_smul]

end TauCeti.BinaryQuadraticForm
