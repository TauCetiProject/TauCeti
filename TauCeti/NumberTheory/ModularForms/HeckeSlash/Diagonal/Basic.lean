/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.DiagonalCosets
public import TauCeti.NumberTheory.ModularForms.SlashActionRat

/-!
# The rational slash action of a diagonal Hecke representative

This file treats the rational diagonal Hecke representatives `natDiagGL 2 a`, specifically
the scalar ones, and records how the weight-`k` rational slash action sees them: `diag(c, c)`
acts trivially on the upper half-plane, so it only contributes the automorphy factor, which is
`c ^ (k - 2)`.

## Main results

* `ModularForm.rat_slash_natDiagGL_const`: a nonzero constant rational diagonal acts by
  `c ^ (k - 2)`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.3.
-/

public section

open Matrix UpperHalfPlane HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace ModularForm

/-- A nonzero constant natural diagonal acts through the rational weight-`k` slash by
`c ^ (k - 2)`. -/
@[simp]
lemma rat_slash_natDiagGL_const {c : ℕ} [NeZero c] (k : ℤ) (f : ℍ → ℂ) :
    f ∣[k] natDiagGL 2 ![c, c] = (c : ℂ) ^ (k - 2) • f := by
  have hc : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hvec : ![c, c] = fun _ : Fin 2 ↦ c := by
    funext i
    fin_cases i <;> rfl
  rw [hvec, natDiagGL_const_eq_scalar 2 hc, ModularForm.rat_slash,
    Matrix.GeneralLinearGroup.map_scalar]
  let u : ℝˣ := Units.map (algebraMap ℚ ℝ)
    (Units.mk0 (c : ℚ) (by exact_mod_cast hc.ne'))
  rw [ModularForm.slash_scalar k u]
  have hu : (((u : ℝ) : ℂ)) = (c : ℂ) := by simp [u]
  rw [hu]

end ModularForm

end
