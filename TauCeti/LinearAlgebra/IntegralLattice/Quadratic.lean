/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Even
public import TauCeti.LinearAlgebra.QuadraticForm.Even

/-!
# The quadratic form of an even integral lattice

An even symmetric integral bilinear form has a unique integer quadratic form whose polar form
is the original bilinear form. Its value at `x` is half the self-pairing at `x`. This provides
the quadratic description of an even lattice without inverting two in the coefficient ring.

The general construction for any `ℤ`-module is in `TauCeti.LinearAlgebra.QuadraticForm.Even`.
This file applies it to the integral restriction of an even lattice.

The half-norm convention agrees with Nikulin, *Integral symmetric bilinear forms and some of
their applications*, §1.1.
-/

public section

namespace TauCeti

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
theorem eq_quadraticForm_of_polarBilin_eq (L : IntegralLattice V) (hL : L.IsEven)
    (Q : QuadraticForm ℤ L) (hQ : Q.polarBilin = L.integralForm) :
    Q = L.quadraticForm hL :=
  quadraticForm_eq_of_polarBilin_eq Q (L.quadraticForm hL)
    (hQ.trans (L.polarBilin_quadraticForm hL).symm)

end IntegralLattice

end TauCeti
