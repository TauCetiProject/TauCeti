/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Int.Even
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Even bilinear forms and integer quadratic forms

An even symmetric integer bilinear form determines a quadratic form by taking half of each
self-pairing. Polarization recovers the bilinear form, and every integer quadratic form is
recovered from its polar form. In particular, an integer quadratic form is determined by its
polar form.

The half-norm convention agrees with Nikulin, *Integral symmetric bilinear forms and some of
their applications*, §1.1.
-/

public section

namespace TauCeti

universe u

variable {M : Type u} [AddCommGroup M] [Module ℤ M]

/-- The quadratic form whose polar form is an even symmetric integral bilinear form. -/
def _root_.LinearMap.BilinForm.halfNormQuadratic
    (B : _root_.LinearMap.BilinForm ℤ M) (hB : B.IsSymm)
    (heven : ∀ x, Even (B x x)) : QuadraticForm ℤ M where
  toFun x := B x x / 2
  toFun_smul a x := by
    have hx := Int.two_mul_ediv_two_of_even (heven x)
    have hax := Int.two_mul_ediv_two_of_even (heven (a • x))
    have hs : B (a • x) (a • x) = a * a * B x x := by
      simp [LinearMap.smul_apply, mul_assoc]
    rw [← int_smul_eq_zsmul (inferInstance : Module ℤ M) a x] at hs hax
    have hscaled := congrArg (fun z : ℤ ↦ a * a * z) hx
    apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
    calc
      _ = a * a * B x x := hax.trans hs
      _ = 2 * ((a * a) • (B x x / 2)) := by
        rw [smul_eq_mul]
        nlinarith [hscaled]
  exists_companion' := ⟨B, by
    intro x y
    have hx := Int.two_mul_ediv_two_of_even (heven x)
    have hy := Int.two_mul_ediv_two_of_even (heven y)
    have hxy := Int.two_mul_ediv_two_of_even (heven (x + y))
    have hsum : B (x + y) (x + y) = B x x + B y y + 2 * B x y := by
      simp only [map_add, LinearMap.add_apply]
      nlinarith [hB.eq x y]
    rw [hsum] at hxy
    omega⟩

/-- The quadratic form of an even bilinear form evaluates to half its self-pairing. -/
@[simp]
theorem _root_.LinearMap.BilinForm.halfNormQuadratic_apply
    (B : _root_.LinearMap.BilinForm ℤ M) (hB : B.IsSymm)
    (heven : ∀ x, Even (B x x)) (x : M) :
    B.halfNormQuadratic hB heven x = B x x / 2 :=
  by simp [LinearMap.BilinForm.halfNormQuadratic]

/-- Twice the half-norm recovers the self-pairing. -/
-- `simpNF` reduces the left side via `halfNormQuadratic_apply`, so this is not a simp lemma.
theorem _root_.LinearMap.BilinForm.two_mul_halfNormQuadratic
    (B : _root_.LinearMap.BilinForm ℤ M) (hB : B.IsSymm)
    (heven : ∀ x, Even (B x x)) (x : M) :
    2 * B.halfNormQuadratic hB heven x = B x x := by
  rw [LinearMap.BilinForm.halfNormQuadratic_apply]
  exact Int.two_mul_ediv_two_of_even (heven x)

/-- The polar form of the half-norm quadratic form is the original bilinear form. -/
@[simp]
theorem _root_.LinearMap.BilinForm.polarBilin_halfNormQuadratic
    (B : _root_.LinearMap.BilinForm ℤ M) (hB : B.IsSymm)
    (heven : ∀ x, Even (B x x)) :
    (B.halfNormQuadratic hB heven).polarBilin = B := by
  apply LinearMap.ext₂
  intro x y
  have hxy := B.two_mul_halfNormQuadratic hB heven (x + y)
  have hx := B.two_mul_halfNormQuadratic hB heven x
  have hy := B.two_mul_halfNormQuadratic hB heven y
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  simp only [map_add, LinearMap.add_apply] at hxy
  nlinarith [hB.eq x y]

/-- The diagonal of the polar form of an integer quadratic form is twice its value. -/
-- `simpNF` proves this using `QuadraticMap.polarBilin_apply_apply` and `polar_self`.
theorem _root_.QuadraticForm.polarBilin_self (Q : _root_.QuadraticForm ℤ M) (x : M) :
    Q.polarBilin x x = 2 * Q x := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self]
  simp only [two_smul, two_mul]

/-- The polar form of an integer quadratic form has even diagonal. -/
theorem _root_.QuadraticForm.even_polarBilin_self (Q : _root_.QuadraticForm ℤ M) (x : M) :
    Even (Q.polarBilin x x) := by
  rw [Q.polarBilin_self]
  exact even_two_mul (Q x)

/-- Taking the half-norm of the polar form recovers the quadratic form. -/
@[simp]
theorem _root_.QuadraticForm.halfNormQuadratic_polarBilin (Q : _root_.QuadraticForm ℤ M) :
    LinearMap.BilinForm.halfNormQuadratic Q.polarBilin
      (by constructor; intro x y; exact QuadraticMap.polar_comm Q x y)
      (Q.even_polarBilin_self) = Q := by
  apply QuadraticMap.ext
  intro x
  apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
  rw [LinearMap.BilinForm.two_mul_halfNormQuadratic, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar_self, two_smul]
  ring

/-- Integer quadratic forms with equal polar forms are equal. -/
theorem _root_.QuadraticForm.eq_of_polarBilin_eq (Q₁ Q₂ : _root_.QuadraticForm ℤ M)
    (h : Q₁.polarBilin = Q₂.polarBilin) : Q₁ = Q₂ := by
  apply QuadraticMap.ext
  intro x
  have hdiag := congrArg (fun B : LinearMap.BilinForm ℤ M ↦ B x x) h
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_smul] at hdiag
  omega

/-- The polar form of an integer quadratic form is symmetric with even diagonal. -/
theorem _root_.QuadraticForm.isSymm_polarBilin_and_even_polarBilin_self
    (Q : _root_.QuadraticForm ℤ M) :
    Q.polarBilin.IsSymm ∧ ∀ x, Even (Q.polarBilin x x) := by
  constructor
  · constructor
    intro x y
    exact QuadraticMap.polar_comm Q x y
  · exact Q.even_polarBilin_self

/-- An even symmetric integer bilinear form is the polar form of a unique quadratic form. -/
theorem _root_.LinearMap.BilinForm.existsUnique_polarBilin
    (B : _root_.LinearMap.BilinForm ℤ M) (hB : B.IsSymm)
    (heven : ∀ x, Even (B x x)) :
    ∃! Q : _root_.QuadraticForm ℤ M, Q.polarBilin = B := by
  refine ⟨B.halfNormQuadratic hB heven, B.polarBilin_halfNormQuadratic hB heven, ?_⟩
  intro Q hQ
  exact QuadraticForm.eq_of_polarBilin_eq Q _
    (hQ.trans (B.polarBilin_halfNormQuadratic hB heven).symm)

/-- A symmetric integer bilinear form has even diagonal exactly when it is a polar form. -/
theorem _root_.LinearMap.BilinForm.even_iff_exists_polarBilin
    (B : _root_.LinearMap.BilinForm ℤ M) (hB : B.IsSymm) :
    (∀ x, Even (B x x)) ↔ ∃ Q : _root_.QuadraticForm ℤ M, Q.polarBilin = B := by
  constructor
  · intro heven
    exact ⟨B.halfNormQuadratic hB heven, B.polarBilin_halfNormQuadratic hB heven⟩
  · rintro ⟨Q, rfl⟩
    exact QuadraticForm.even_polarBilin_self Q

end TauCeti
