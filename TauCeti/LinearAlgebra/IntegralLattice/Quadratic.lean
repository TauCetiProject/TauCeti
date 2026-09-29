/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Even
public import Mathlib.Algebra.Group.Int.Even

/-!
# The quadratic form of an even integral lattice

An even symmetric integral bilinear form has a unique integer quadratic form whose polar form
is the original bilinear form. Its value at `x` is half the self-pairing at `x`. This provides
the quadratic description of an even lattice without inverting two in the coefficient ring.

The construction works for any `ℤ`-module with a symmetric bilinear form whose diagonal is
even. In particular it applies to the integral restriction of an even lattice.

The half-norm convention agrees with Nikulin, *Integral symmetric bilinear forms and some of
their applications*, §1.1.
-/

public section

namespace TauCeti

universe u

variable {M : Type u} [AddCommGroup M] [Module ℤ M]

/-- The quadratic form whose polar form is an even symmetric integral bilinear form. -/
def halfNormQuadratic (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm)
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
theorem halfNormQuadratic_apply (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm)
    (heven : ∀ x, Even (B x x)) (x : M) :
    halfNormQuadratic B hB heven x = B x x / 2 :=
  by simp [halfNormQuadratic]

/-- Twice the half-norm recovers the self-pairing. -/
theorem two_mul_halfNormQuadratic (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm)
    (heven : ∀ x, Even (B x x)) (x : M) :
    2 * halfNormQuadratic B hB heven x = B x x := by
  rw [halfNormQuadratic_apply]
  exact Int.two_mul_ediv_two_of_even (heven x)

/-- The polar form of the half-norm quadratic form is the original bilinear form. -/
@[simp]
theorem polarBilin_halfNormQuadratic (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm)
    (heven : ∀ x, Even (B x x)) :
    (halfNormQuadratic B hB heven).polarBilin = B := by
  apply LinearMap.ext₂
  intro x y
  have hxy := two_mul_halfNormQuadratic B hB heven (x + y)
  have hx := two_mul_halfNormQuadratic B hB heven x
  have hy := two_mul_halfNormQuadratic B hB heven y
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  simp only [map_add, LinearMap.add_apply] at hxy
  nlinarith [hB.eq x y]

/-- The polar form of an integer quadratic form has even diagonal. -/
theorem even_polarBilin_self (Q : QuadraticForm ℤ M) (x : M) :
    Even (Q.polarBilin x x) := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self]
  exact ⟨Q x, by simp [two_mul]⟩

/-- Taking the half-norm of the polar form recovers the quadratic form. -/
@[simp]
theorem halfNormQuadratic_polarBilin (Q : QuadraticForm ℤ M) :
    halfNormQuadratic Q.polarBilin
      (by constructor; intro x y; exact QuadraticMap.polar_comm Q x y)
      (even_polarBilin_self Q) = Q := by
  apply QuadraticMap.ext
  intro x
  apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
  rw [two_mul_halfNormQuadratic, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar_self, two_smul]
  ring

namespace IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The integer quadratic form of an even integral lattice, with value half the integral norm. -/
noncomputable def quadraticForm (L : IntegralLattice V) (hL : L.IsEven) : QuadraticForm ℤ L :=
  halfNormQuadratic L.integralForm L.isSymm_integralForm
    (fun x ↦ by
      have hx := (L.even_integralNorm_iff x).mpr ((L.isEven_iff_forall_norm).mp hL x)
      simpa only [L.integralNorm_apply] using hx)

/-- The quadratic form of an even lattice evaluates to half the integral norm. -/
@[simp]
theorem quadraticForm_apply (L : IntegralLattice V) (hL : L.IsEven) (x : L) :
    L.quadraticForm hL x = L.integralNorm x / 2 := by
  rw [quadraticForm, halfNormQuadratic_apply, L.integralNorm_apply]

/-- The polar form of the lattice quadratic form is its integral bilinear form. -/
@[simp]
theorem polarBilin_quadraticForm (L : IntegralLattice V) (hL : L.IsEven) :
    (L.quadraticForm hL).polarBilin = L.integralForm :=
  polarBilin_halfNormQuadratic _ _ _

/-- An integral lattice is even exactly when its integral form is the polar form of an integer
quadratic form. -/
theorem isEven_iff_exists_polarBilin_eq_integralForm (L : IntegralLattice V) :
    L.IsEven ↔ ∃ Q : QuadraticForm ℤ L, Q.polarBilin = L.integralForm := by
  constructor
  · intro hL
    exact ⟨L.quadraticForm hL, L.polarBilin_quadraticForm hL⟩
  · rintro ⟨Q, hQ⟩
    apply (L.isEven_iff_forall_norm).mpr
    intro x
    refine ⟨Q x, ?_⟩
    have h : L.integralNorm x = 2 * Q x := by
      rw [L.integralNorm_apply, ← hQ, QuadraticMap.polarBilin_apply_apply,
        QuadraticMap.polar_self, two_smul]
      ring
    rw [← L.integralNorm_cast, h]
    push_cast
    ring

/-- The half-norm quadratic form is the unique quadratic form with polar form equal to the
integral form of an even lattice. -/
theorem quadraticForm_eq_of_polarBilin_eq (L : IntegralLattice V) (hL : L.IsEven)
    (Q : QuadraticForm ℤ L) (hQ : Q.polarBilin = L.integralForm) :
    Q = L.quadraticForm hL := by
  apply QuadraticMap.ext
  intro x
  apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
  calc
    2 * Q x = Q.polarBilin x x := by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_smul]
      ring
    _ = L.integralForm x x := by rw [hQ]
    _ = 2 * L.quadraticForm hL x := (two_mul_halfNormQuadratic _ _ _ x).symm

end IntegralLattice

end TauCeti
