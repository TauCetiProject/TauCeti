/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.SquareClassGroup.Multiplicative
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

/-!
# Determinant square classes of orthogonal transformations

The determinant of an orthogonal transformation of a finite-dimensional space is a unit. Reducing
that unit modulo squares gives a homomorphism from the orthogonal group to the square-class group.
This construction only uses the orthogonal group and does not require a characteristic assumption.

## Main definitions and results

* `QuadraticMap.orthogonalDetSquareClass`: the determinant modulo squares on `O(Q)`.
* `QuadraticMap.orthogonalDetSquareClass_apply`: its value on an orthogonal
  transformation.
* `QuadraticMap.ker_orthogonalDetSquareClass`: for a nondegenerate form over a field in which
  `-1` is not a square, its kernel is the special orthogonal group, since the determinant of an
  orthogonal transformation is `±1`.
-/

public section

open TauCeti

namespace QuadraticMap

universe u v w

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- The determinant of an orthogonal transformation, reduced modulo squares. -/
noncomputable def orthogonalDetSquareClass {N : Type w} [AddCommMonoid N] [Module K N]
    [FiniteDimensional K V]
    (Q : QuadraticMap K V N) :
    TauCeti.QuadraticMap.orthogonalGroup Q →* (Kˣ ⧸ Subgroup.square Kˣ) :=
  let _ := Module.finBasis K V
  squareClassHom.comp <|
    LinearEquiv.det.comp (TauCeti.QuadraticMap.orthogonalGroup Q).subtype

/-- The determinant square-class map evaluates by taking the determinant modulo squares. -/
@[simp]
theorem orthogonalDetSquareClass_apply {N : Type w} [AddCommMonoid N] [Module K N]
    [FiniteDimensional K V]
    (Q : QuadraticMap K V N) (g : TauCeti.QuadraticMap.orthogonalGroup Q) :
    orthogonalDetSquareClass Q g = squareClassHom (LinearEquiv.det (g : V ≃ₗ[K] V)) := by
  rw [orthogonalDetSquareClass]
  rfl

/-- **The determinant square class detects `SO(Q)`** when `-1` is not a square. The determinant of
an orthogonal transformation of a nondegenerate form is `±1`, and the class of `-1` is nontrivial
exactly when `-1` is not a square. -/
theorem ker_orthogonalDetSquareClass [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : Q.Nondegenerate) (h : ¬IsSquare (-1 : K)) :
    (orthogonalDetSquareClass Q).ker = specialOrthogonalWithin Q := by
  have h2 : (2 : K) ≠ 0 := fun h0 ↦
    h ⟨1, by rw [mul_one]; exact (eq_neg_of_add_eq_zero_left (by rw [one_add_one_eq_two, h0])).symm⟩
  let _ : Invertible (2 : K) := invertibleOfNonzero h2
  ext g
  rw [MonoidHom.mem_ker, orthogonalDetSquareClass_apply, squareClassHom_eq_one_iff,
    mem_specialOrthogonalWithin_iff, ← orthogonalDet_apply]
  refine ⟨fun hsq ↦ ?_, fun h1 ↦ by rw [h1]; exact IsSquare.one⟩
  have hsq2 := congrArg Units.val
    (TauCeti.QuadraticMap.orthogonalDet_sq ((nondegenerate_polar_iff.mpr hQ).1) g)
  rw [Units.val_pow_eq_pow_val, Units.val_one, sq_eq_one_iff] at hsq2
  rcases hsq2 with h1 | h1
  · exact Units.ext h1
  · have h2 := hsq.map (Units.coeHom K)
    rw [Units.coeHom_apply, h1] at h2
    exact absurd h2 h

end QuadraticMap
