/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.ProperAction

/-!
# `GL(2, ℝ)` acts on the upper half-plane by isometries

Mathlib's action `UpperHalfPlane.glAction` of `GL(2, ℝ)` on `ℍ` sends `z` to `(az + b)/(cz + d)`
when `det g > 0` and to `(a conj z + b)/(c conj z + d)` when `det g < 0`. Mathlib proves that
`SL(2, ℝ)` acts by isometries of the hyperbolic distance. This file extends that to the whole of
`GL(2, ℝ)`, including the orientation-reversing, antiholomorphic elements of negative
determinant, and to `PGL(2, ℝ)`.

A matrix of positive determinant acts as its determinant-normalized class in `PSL(2, ℝ)`
(`UpperHalfPlane.glPosToPSL2R_smul`), which is an isometry. A matrix `g` of negative determinant
is `J * (J * g)`, where `UpperHalfPlane.J = diag(-1, 1)` acts by the reflection `z ↦ -conj z` in the
imaginary axis and `J * g` has positive determinant.

## Main declarations

* `TauCeti.UpperHalfPlane.isometry_J_smul`: the action of `UpperHalfPlane.J` is an isometry.
* `TauCeti.UpperHalfPlane.instIsIsometricSMulGL`: every element of `GL(2, ℝ)` acts on `ℍ` by an
  isometry.
* `TauCeti.UpperHalfPlane.instIsIsometricSMulPGL`: every element of `PGL(2, ℝ)` acts on `ℍ` by an
  isometry.

## References

* Svetlana Katok, *Fuchsian Groups*, §1.1.
* Alan Beardon, *The Geometry of Discrete Groups*, §7.2.
-/

public section

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups

namespace TauCeti.UpperHalfPlane

/-- The orientation-reversing involution `UpperHalfPlane.J : z ↦ -conj z` acts on `ℍ` by an
isometry. -/
theorem isometry_J_smul : Isometry (J • · : ℍ → ℍ) :=
  Isometry.of_dist_eq fun z w ↦ by
    rw [UpperHalfPlane.dist_eq, UpperHalfPlane.dist_eq, coe_J_smul, coe_J_smul, dist_neg_neg,
      Complex.dist_conj_conj, J_smul_im, J_smul_im]

/-- Every element of `GL(2, ℝ)` acts on the upper half-plane by an isometry of the hyperbolic
distance, including the elements of negative determinant, which act antiholomorphically by
`z ↦ (a conj z + b)/(c conj z + d)`. -/
instance instIsIsometricSMulGL : IsIsometricSMul (GL (Fin 2) ℝ) ℍ where
  isometry_smul g := by
    -- a matrix of positive determinant acts as its determinant-normalized class in `PSL(2, ℝ)`
    have hpos {h : GL (Fin 2) ℝ} (hh : 0 < (h.det : ℝ)) : Isometry (h • · : ℍ → ℍ) := by
      have e (z : ℍ) : glPosToPSL2R ⟨h, hh⟩ • z = h • z := glPosToPSL2R_smul ⟨h, hh⟩ z
      simpa only [e] using isometry_smul ℍ (glPosToPSL2R ⟨h, hh⟩)
    rcases g.det.ne_zero.lt_or_gt with hg | hg
    · -- `g = J * (J * g)` and `J * g` has positive determinant
      have hJg : 0 < ((J * g).det : ℝ) := by simpa using hg
      have hcomp : (g • · : ℍ → ℍ) = (J • ·) ∘ ((J * g) • ·) := by
        funext z
        simp [smul_smul, ← mul_assoc, ← sq]
      rw [hcomp]
      exact isometry_J_smul.comp (hpos hJg)
    · exact hpos hg

/-- Every element of `PGL(2, ℝ)` acts on the upper half-plane by an isometry of the hyperbolic
distance. -/
instance instIsIsometricSMulPGL : IsIsometricSMul PGL(2, ℝ) ℍ where
  isometry_smul q := by
    induction q using Matrix.ProjGenLinGroup.induction_on with | mk g =>
    simpa only [pglMk_smul] using isometry_smul ℍ g

end TauCeti.UpperHalfPlane
