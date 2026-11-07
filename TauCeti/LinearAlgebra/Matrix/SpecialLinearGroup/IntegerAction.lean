/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.SemidirectProduct
public import TauCeti.RepresentationTheory.ToMultiplicative

/-!
# The integral special linear action on column vectors

`TauCeti.slTwoAction` is the action of `SL₂(ℤ)` on the multiplicative copy of `ℤ²`,
so that it can be used directly in `SemidirectProduct`. Restriction along a subgroup's
inclusion gives the action defining `ℤ² ⋊ G` for `G ≤ SL₂(ℤ)`.

The action is faithful. Its values on upper and lower transvections fix the column-vector
convention: the upper transvection sends `(x, y)` to `(x + t*y, y)`, not `(x, t*x + y)`.
The semidirect-product examples also record multiplication and conjugation under restriction
to any subgroup.

The construction uses `Matrix.SpecialLinearGroup.toLin'` and `Representation.toMulAut`.
For the associated semidirect-product pairs, see Anantharaman–Popa,
*An Introduction to II₁ Factors*, Example 14.2.8.
-/

public section

namespace TauCeti

open Matrix

/-- The action of `SL₂(ℤ)` on the multiplicative copy of `ℤ²` by multiplication on
column vectors. -/
def slTwoAction : SpecialLinearGroup (Fin 2) ℤ →* MulAut (Multiplicative (Fin 2 → ℤ)) :=
  Representation.toMulAut (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (SpecialLinearGroup.toLin' (n := Fin 2) (R := ℤ)))

/-- The action on the underlying column vector is matrix-vector multiplication. -/
@[simp]
theorem slTwoAction_apply (g : SpecialLinearGroup (Fin 2) ℤ)
    (v : Multiplicative (Fin 2 → ℤ)) :
    slTwoAction g v = Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v.toAdd) := by
  simp [slTwoAction, SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply]

/-- Distinct special linear matrices induce distinct automorphisms of the integral lattice. -/
theorem slTwoAction_injective : Function.Injective slTwoAction := by
  intro g h heq
  apply SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.ext
  intro v
  have hv := congrArg (fun f : MulAut (Multiplicative (Fin 2 → ℤ)) ↦
    (f (Multiplicative.ofAdd v)).toAdd) heq
  simpa only [slTwoAction_apply, toAdd_ofAdd,
    SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply] using hv

/-- An upper transvection adds a multiple of the second coordinate to the first. -/
theorem slTwoAction_upper_transvection (t : ℤ) (v : Multiplicative (Fin 2 → ℤ)) :
    slTwoAction (SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1)
      zero_ne_one t) v = Multiplicative.ofAdd ![v.toAdd 0 + t * v.toAdd 1, v.toAdd 1] := by
  rw [slTwoAction_apply]
  congr 1
  ext i
  fin_cases i <;> simp [SpecialLinearGroup.transvection_coe, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]

/-- A lower transvection adds a multiple of the first coordinate to the second. -/
theorem slTwoAction_lower_transvection (t : ℤ) (v : Multiplicative (Fin 2 → ℤ)) :
    slTwoAction (SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0)
      one_ne_zero t) v = Multiplicative.ofAdd ![v.toAdd 0, t * v.toAdd 0 + v.toAdd 1] := by
  rw [slTwoAction_apply]
  congr 1
  ext i
  fin_cases i <;> simp [SpecialLinearGroup.transvection_coe, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]

-- The upper unit shear sends the second basis vector to their sum and fixes the first.
example : slTwoAction (SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1)
    zero_ne_one (1 : ℤ)) (Multiplicative.ofAdd ![0, 1]) =
      Multiplicative.ofAdd ![1, 1] := by
  rw [slTwoAction_upper_transvection]
  simp

example : slTwoAction (SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1)
    zero_ne_one (1 : ℤ)) (Multiplicative.ofAdd ![1, 0]) =
      Multiplicative.ofAdd ![1, 0] := by
  rw [slTwoAction_upper_transvection]
  simp

-- Restriction needs only composition with the subgroup inclusion; no new action is required.
example (G : Subgroup (SpecialLinearGroup (Fin 2) ℤ))
    (x y : Multiplicative (Fin 2 → ℤ) ⋊[slTwoAction.comp G.subtype] G) :
    (x * y).left.toAdd = x.left.toAdd +
      ((x.right : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ y.left.toAdd := by
  simp [SemidirectProduct.mul_left]

example (G : Subgroup (SpecialLinearGroup (Fin 2) ℤ)) (g : G) (v : Fin 2 → ℤ) :
    (SemidirectProduct.inr g * SemidirectProduct.inl (Multiplicative.ofAdd v) *
        SemidirectProduct.inr g⁻¹ :
      Multiplicative (Fin 2 → ℤ) ⋊[slTwoAction.comp G.subtype] G) =
      SemidirectProduct.inl (Multiplicative.ofAdd
        (((g : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v)) := by
  rw [← SemidirectProduct.inl_aut]
  simp

end TauCeti
