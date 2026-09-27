/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Kronecker.EulerForm
public import TauCeti.RepresentationTheory.Quiver.Representation.Projective.Simple.ExtEuler
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-!
# The Cartan and Euler matrices of the `A₂` quiver

The one-arrow generalized Kronecker quiver is the oriented Dynkin quiver `1 ⟶ 2`. This file
checks the Cartan and Euler conventions of the Grothendieck--Euler formalism on that smallest
nontrivial example. Vertices are ordered source first, unlike
`TauCeti.Quiver.Kronecker.vertexEquiv`, whose target-first order is adapted to upper-triangular
path-algebra matrices.

For an arrow type with one element, the two indecomposable projectives have dimension vectors
`(1, 1)` and `(0, 1)`. Thus, with simple coordinates in the rows and projectives in the columns,
the Cartan matrix is

```text
[1 0]
[1 1].
```

The Ringel Euler matrix is `[1, -1; 0, 1]`. Its product with the transposed Cartan matrix is the
identity on either side, and its symmetrization is the type `A₂` Cartan matrix. The final theorem
computes the same Euler matrix categorically: it applies the Ext-Euler calculation obtained from
the length-one projective resolutions of the two vertex simples.

## Main results

* `TauCeti.Quiver.Kronecker.projectiveDimensionMatrix_eq_cartanMatrixA2`: the projective
  path-counting matrix is `[1, 0; 1, 1]`.
* `TauCeti.Quiver.Kronecker.submatrix_toMatrix_eulerForm_eq_eulerMatrixA2`: the quiver Euler
  matrix is
  `[1, -1; 0, 1]`.
* `TauCeti.Quiver.Kronecker.eulerMatrixA2_add_transpose`: its symmetrization is
  `CartanMatrix.A 2`.
* `TauCeti.Quiver.Kronecker.extEulerMatrix_A2_eq`: the Ext-Euler matrix of the vertex simples is
  the same Euler matrix.

## References

See Assem--Simson--Skowroński, *Elements of the Representation Theory of Associative Algebras
I*, Chapter III, Sections 2--3.
-/

public section

namespace TauCeti

open _root_.Quiver
open scoped _root_.Matrix

universe u v

namespace Quiver.Kronecker

variable {A : Type v} [Unique A]

/-- The Cartan matrix `[1, 0; 1, 1]` of the quiver `1 ⟶ 2`, with simple coordinates in the
rows and indecomposable projectives in the columns. -/
def cartanMatrixA2 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 1, 1]

/-- The entries of the `A₂` Cartan matrix. -/
@[simp]
theorem cartanMatrixA2_apply (i j : Fin 2) :
    cartanMatrixA2 i j = !![1, 0; 1, 1] i j := by
  rw [cartanMatrixA2]

/-- The columns of the `A₂` Cartan matrix are the dimension vectors of its indecomposable
projectives. In particular, they are `P₁ = (1, 1)` and `P₂ = (0, 1)`. -/
theorem projectiveDimensionMatrix_eq_cartanMatrixA2 (k : Type u) [Field k] :
    (fun i j : Fin 2 ↦
      (dimVector (indecProjRep k (Kronecker A) (![src, tgt] j)) (![src, tgt] i) : ℤ)) =
        cartanMatrixA2 := by
  ext i j
  rw [dimVector_indecProjRep]
  fin_cases i <;> fin_cases j <;> simp [cartanMatrixA2]

/-- An entry of the projective dimension matrix is the corresponding Cartan matrix entry. -/
@[simp]
theorem projectiveDimensionMatrix_apply (k : Type u) [Field k] (i j : Fin 2) :
    (Module.finrank k ((indecProjRep k (Kronecker A) (![src, tgt] j)).obj
      ((CategoryTheory.Paths.of (Kronecker A)).obj (![src, tgt] i))) : ℤ) = cartanMatrixA2 i j := by
  simpa only [dimVector_apply] using
    congrFun (congrFun (projectiveDimensionMatrix_eq_cartanMatrixA2 k) i) j

/-- The Ringel Euler matrix `[1, -1; 0, 1]` of the quiver `1 ⟶ 2`, with vertices ordered source
first. -/
def eulerMatrixA2 : Matrix (Fin 2) (Fin 2) ℤ := !![1, -1; 0, 1]

/-- The entries of the `A₂` Ringel Euler matrix. -/
@[simp]
theorem eulerMatrixA2_apply (i j : Fin 2) :
    eulerMatrixA2 i j = !![1, -1; 0, 1] i j := by
  rw [eulerMatrixA2]

/-- The Ringel Euler matrix of `1 ⟶ 2` is `[1, -1; 0, 1]` in source-first coordinates. -/
theorem submatrix_toMatrix_eulerForm_eq_eulerMatrixA2 :
    ((eulerForm (Kronecker A)).toMatrix (Pi.basisFun ℤ (Kronecker A))).submatrix
      ![src, tgt] ![src, tgt] = eulerMatrixA2 := by
  let _ : Fintype A := Unique.fintype
  ext i j
  simp only [Matrix.submatrix_apply, LinearMap.BilinForm.toMatrix_apply,
    Pi.basisFun_apply]
  fin_cases i <;> fin_cases j <;> rw [eulerForm_apply] <;>
    simp [eulerMatrixA2, Fintype.card_unique]

omit A [Unique A] in
/-- The transposed Cartan matrix times the Euler matrix is the identity. This is the first half of
the integral identity `E = C⁻ᵀ`. -/
@[simp]
theorem cartanMatrixA2_transpose_mul_eulerMatrixA2 :
    cartanMatrixA2ᵀ * eulerMatrixA2 = 1 := by
  decide

omit A [Unique A] in
/-- The Euler matrix times the transposed Cartan matrix is the identity. Together with
`cartanMatrixA2_transpose_mul_eulerMatrixA2`, this proves `E = C⁻ᵀ` over `ℤ`. -/
@[simp]
theorem eulerMatrixA2_mul_cartanMatrixA2_transpose :
    eulerMatrixA2 * cartanMatrixA2ᵀ = 1 := by
  decide

omit A [Unique A] in
/-- The symmetrized Euler matrix of `1 ⟶ 2` is the type `A₂` Cartan matrix. -/
@[simp]
theorem eulerMatrixA2_add_transpose :
    eulerMatrixA2 + eulerMatrixA2ᵀ = CartanMatrix.A 2 := by
  rw [CartanMatrix.A_two]
  decide

/-- The Ext-Euler matrix computed from the length-one projective resolutions of the vertex simples
is the Ringel Euler matrix `[1, -1; 0, 1]`. This checks the arrow orientation and transpose
conventions against the categorical pairing. -/
theorem extEulerMatrix_A2_eq (k : Type v) [Field k] :
    (fun i j : Fin 2 ↦
      let si : Kronecker A := ![src, tgt] i
      let sj : Kronecker A := ![src, tgt] j
      extEuler k (isEulerAdmissible_vertexSimpleModule k (Kronecker A) si
        (vertexSimpleModule k (Kronecker A) sj)
        (finiteDimensional_vertexSimpleModule_obj (k := k) (Q := Kronecker A) sj si)
        (fun a _ ↦ finiteDimensional_vertexSimpleModule_obj
          (k := k) (Q := Kronecker A) sj a))) = eulerMatrixA2 := by
  let _ : Fintype A := Unique.fintype
  ext i j
  let si : Kronecker A := ![src, tgt] i
  let sj : Kronecker A := ![src, tgt] j
  have hdim (s : Kronecker A) :
      (fun a ↦
        (dimVector ((quiverRepFunctor k (Kronecker A)).obj
          (vertexSimpleModule k (Kronecker A) s)) a : ℤ)) = Pi.single s 1 := by
    rw [dimVector_eq_of_iso (vertexSimpleModuleIso k (Kronecker A) s), dimVector_simpleRep]
    funext a
    simp [Pi.single_apply]
  rw [extEuler_vertexSimpleModule_eq_eulerForm k (Kronecker A) si
    (vertexSimpleModule k (Kronecker A) sj)
    (finiteDimensional_vertexSimpleModule_obj (k := k) (Q := Kronecker A) sj si)
    (fun a _ ↦ finiteDimensional_vertexSimpleModule_obj
      (k := k) (Q := Kronecker A) sj a)]
  rw [hdim si, hdim sj]
  dsimp [si, sj]
  simpa only [Matrix.submatrix_apply, LinearMap.BilinForm.toMatrix_apply, Pi.basisFun_apply] using
    congrFun (congrFun submatrix_toMatrix_eulerForm_eq_eulerMatrixA2 i) j

/-- An Ext-Euler pairing of vertex simples is the corresponding Ringel Euler matrix entry. -/
@[simp]
theorem extEulerMatrix_A2_apply (k : Type v) [Field k] (i j : Fin 2) :
    extEuler k (isEulerAdmissible_vertexSimpleModule k (Kronecker A) (![src, tgt] i)
      (vertexSimpleModule k (Kronecker A) (![src, tgt] j))
      (finiteDimensional_vertexSimpleModule_obj (k := k) (Q := Kronecker A)
        (![src, tgt] j) (![src, tgt] i))
      (fun a _ ↦ finiteDimensional_vertexSimpleModule_obj
        (k := k) (Q := Kronecker A) (![src, tgt] j) a)) = eulerMatrixA2 i j := by
  exact congrFun (congrFun (extEulerMatrix_A2_eq k) i) j

end Quiver.Kronecker

end TauCeti
