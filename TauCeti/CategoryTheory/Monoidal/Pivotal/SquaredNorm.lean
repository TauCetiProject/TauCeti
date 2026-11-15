/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Spherical
public import TauCeti.CategoryTheory.Monoidal.Rigid.SquaredNorm

/-!
# Bidual traces and squared norms in a pivotal category

In a pivotal monoidal category `C`, every object `X` has a canonical isomorphism
`pivotalIsoApp X : X ≅ Xᘁᘁ`. Composing an endomorphism `f : X ⟶ X` with `(pivotalIsoApp X).hom`
turns the pivot-free bidual trace `TauCeti.doubleDualTrace` into the pivotal right trace
`TauCeti.rightTrace f`, while precomposing with `(pivotalIsoApp X).inv` and taking the right
adjoint mate turns it into `TauCeti.leftTrace f` via the Freyd–Yetter identity
`φ_{Xᘁ} = (φ_X⁻¹)ᘁ`.

In particular, the squared norm `TauCeti.squaredNorm` of `pivotalIsoApp X` is the product
`leftDim X ≫ rightDim X` of the left and right categorical dimensions of `X`
(`TauCeti.squaredNorm_pivotalIsoApp`), which in a spherical category is
`quantumDim X ≫ quantumDim X`.

## Main declarations

* `TauCeti.doubleDualTrace_comp_pivotalIsoApp_hom` and `TauCeti.doubleDualTrace_pivotalIsoApp_hom`:
  comparison of `doubleDualTrace` with `rightTrace` and `rightDim`;
* `TauCeti.doubleDualTrace_rightAdjointMate_pivotalIsoApp_inv_comp` and
  `TauCeti.doubleDualTrace_rightAdjointMate_pivotalIsoApp_inv`: comparison of `doubleDualTrace` on
  mates with `leftTrace` and `leftDim`;
* `TauCeti.squaredNorm_pivotalIsoApp` and `TauCeti.squaredNorm_pivotalIsoApp_eq_quantumDim`:
  `squaredNorm (pivotalIsoApp X)` equals `leftDim X ≫ rightDim X`, and `quantumDim X ≫ quantumDim X`
  in a spherical category.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005), §2.1
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §7.21
-/

public section

open CategoryTheory MonoidalCategory

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [PivotalCategory C]

/-- Postcomposing an endomorphism `f : X ⟶ X` with `(pivotalIsoApp X).hom` identifies its
`doubleDualTrace` with `rightTrace f`. -/
theorem doubleDualTrace_comp_pivotalIsoApp_hom {X : C} (f : X ⟶ X) :
    doubleDualTrace (f ≫ (pivotalIsoApp X).hom) = rightTrace f := by
  rw [doubleDualTrace_def, rightTrace_eq_pivotalIsoApp, comp_whiskerRight_assoc]

/-- The `doubleDualTrace` of `(pivotalIsoApp X).hom` is the right dimension of `X`. -/
@[simp]
theorem doubleDualTrace_pivotalIsoApp_hom (X : C) :
    doubleDualTrace (pivotalIsoApp X).hom = rightDim X := by
  simpa using doubleDualTrace_comp_pivotalIsoApp_hom (𝟙 X)

/-- Precomposing `f : X ⟶ X` with `(pivotalIsoApp X).inv` and taking the right adjoint mate
identifies its `doubleDualTrace` with `leftTrace f`, by the Freyd–Yetter identity. -/
theorem doubleDualTrace_rightAdjointMate_pivotalIsoApp_inv_comp {X : C} (f : X ⟶ X) :
    doubleDualTrace (rightAdjointMate ((pivotalIsoApp X).inv ≫ f)) = leftTrace f := by
  rw [comp_rightAdjointMate, ← pivotalIsoApp_rightDual, doubleDualTrace_comp_pivotalIsoApp_hom,
    rightTrace_rightAdjointMate]

/-- The `doubleDualTrace` of `((pivotalIsoApp X).inv)ᘁ` is the left dimension of `X`. -/
@[simp]
theorem doubleDualTrace_rightAdjointMate_pivotalIsoApp_inv (X : C) :
    doubleDualTrace (rightAdjointMate (pivotalIsoApp X).inv) = leftDim X := by
  simpa using doubleDualTrace_rightAdjointMate_pivotalIsoApp_inv_comp (𝟙 X)

/-- **Comparison of squared norm with pivotal dimensions**: the squared norm of `X` with respect to
`pivotalIsoApp X` is `leftDim X ≫ rightDim X`. -/
theorem squaredNorm_pivotalIsoApp (X : C) :
    squaredNorm (pivotalIsoApp X) = leftDim X ≫ rightDim X := by
  rw [squaredNorm_def, doubleDualTrace_pivotalIsoApp_hom,
    doubleDualTrace_rightAdjointMate_pivotalIsoApp_inv, scalar_comm]

/-- In a spherical category, the squared norm of `pivotalIsoApp X` is the square of the quantum
dimension of `X`. -/
theorem squaredNorm_pivotalIsoApp_eq_quantumDim [SphericalCategory C] (X : C) :
    squaredNorm (pivotalIsoApp X) = quantumDim X ≫ quantumDim X := by
  rw [squaredNorm_pivotalIsoApp, ← quantumDim_eq_leftDim, ← quantumDim_eq_rightDim]

end TauCeti
