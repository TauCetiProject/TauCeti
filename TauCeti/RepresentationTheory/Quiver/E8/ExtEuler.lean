/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.E8.EulerForm
public import TauCeti.RepresentationTheory.Quiver.Representation.Projective.Simple.ExtEuler
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin

/-!
# The Ext-Euler matrix of the oriented `E₈` quiver

The first-arrow resolution of each vertex simple computes its Ext-Euler characteristic against
another vertex simple. In the order `0, …, 7` of `Quiver.E8.vertexEquiv`, these values form the
upper triangular Euler matrix `I - A`, where `A` counts arrows. Its symmetrization is the positive
definite `E₈` Cartan matrix. Thus the categorical values on these eight simples agree with the
combinatorial Euler and root-system matrices.

The computation uses the vertex-simple resolution and the oriented `E₈` Euler matrix already
available in Tau Ceti. See Assem--Simson--Skowroński, *Elements of the Representation Theory of
Associative Algebras I*, Chapter III, Section 3.
-/

public section

namespace TauCeti.Quiver.E8

open CategoryTheory
open scoped _root_.Matrix

variable (k : Type) [Field k]

/-- The matrix of Ext-Euler values between the eight vertex simples of the oriented `E₈` quiver.
Rows and columns follow `vertexEquiv`; rows are the first argument of the Euler pairing. -/
noncomputable def extEulerMatrix : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun i j ↦
    extEuler k (isEulerAdmissible_vertexSimpleModule k E8 (vertexEquiv i)
      (vertexSimpleModule k E8 (vertexEquiv j))
      (finiteDimensional_vertexSimpleModule_obj k E8 (vertexEquiv j) (vertexEquiv i))
      (fun a _ ↦ finiteDimensional_vertexSimpleModule_obj k E8 (vertexEquiv j) a))

/-- An Ext-Euler matrix entry is the Kronecker delta minus the number of arrows between
the two numbered vertices. -/
@[simp]
theorem extEulerMatrix_apply (i j : Fin 8) :
    extEulerMatrix k i j =
      (if i = j then 1 else 0) - (Fintype.card (vertexEquiv i ⟶ vertexEquiv j) : ℤ) := by
  rw [extEulerMatrix, Matrix.of_apply,
    extEuler_vertexSimpleModule_vertexSimpleModule]
  simp only [vertexEquiv.injective.eq_iff, Nat.card_eq_fintype_card]

/-- The categorical Ext-Euler matrix is the combinatorial Euler matrix `I - A`. -/
theorem extEulerMatrix_eq_eulerForm :
    extEulerMatrix k =
      ((eulerForm E8).toMatrix (Pi.basisFun ℤ E8)).submatrix vertexEquiv vertexEquiv := by
  ext i j
  simp only [extEulerMatrix_apply, Matrix.submatrix_apply,
    LinearMap.BilinForm.toMatrix_apply, Pi.basisFun_apply, eulerForm_single_single,
    vertexEquiv.injective.eq_iff]

/-- In the numbered simple basis, the categorical Ext-Euler matrix is the explicit upper
triangular `E₈` Euler matrix. -/
theorem extEulerMatrix_eq :
    extEulerMatrix k =
      !![1, 0, -1,  0,  0,  0,  0,  0;
         0, 1,  0, -1,  0,  0,  0,  0;
         0, 0,  1, -1,  0,  0,  0,  0;
         0, 0,  0,  1, -1,  0,  0,  0;
         0, 0,  0,  0,  1, -1,  0,  0;
         0, 0,  0,  0,  0,  1, -1,  0;
         0, 0,  0,  0,  0,  0,  1, -1;
         0, 0,  0,  0,  0,  0,  0,  1] := by
  rw [extEulerMatrix_eq_eulerForm, submatrix_toMatrix_eulerForm]

/-- The symmetrization of the categorical Ext-Euler pairing on the vertex simples is the
`E₈` Cartan matrix. -/
theorem extEulerMatrix_add_transpose :
    extEulerMatrix k + (extEulerMatrix k)ᵀ = CartanMatrix.E 8 := by
  rw [extEulerMatrix_eq_eulerForm, submatrix_toMatrix_eulerForm_add_transpose]

/-- The symmetrized categorical Ext-Euler matrix is positive definite over `ℚ`. -/
theorem posDef_map_intCast_extEulerMatrix_add_transpose :
    ((extEulerMatrix k + (extEulerMatrix k)ᵀ).map (Int.cast : ℤ → ℚ)).PosDef := by
  rw [extEulerMatrix_add_transpose]
  exact posDef_map_intCast_cartanMatrix_E8

end TauCeti.Quiver.E8
