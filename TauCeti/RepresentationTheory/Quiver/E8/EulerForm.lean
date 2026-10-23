/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.E8.Basic
public import TauCeti.RepresentationTheory.Quiver.EulerForm
import TauCeti.LinearAlgebra.Matrix.PosDef.Basic
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin

/-!
# The Euler and Tits forms of the oriented `E₈` quiver

This file computes the Euler form of the oriented `E₈` quiver in its simple dimension vectors.
The nodes are numbered as in Mathlib's
`CartanMatrix.E 8`, which is Bourbaki's numbering shifted down by one: the diagram is the chain
`0 - 2 - 3 - 4 - 5 - 6 - 7` with the node `1` attached to the trivalent node `3`. Every edge is
oriented from its smaller node to its larger one, so the seven arrows are

```text
0 ⟶ 2,  1 ⟶ 3,  2 ⟶ 3,  3 ⟶ 4,  4 ⟶ 5,  5 ⟶ 6,  6 ⟶ 7.
```

Writing `A` for the matrix of arrow counts, `A i j = #(i ⟶ j)`, the Euler form
`⟨x, y⟩ = ∑ᵢ xᵢ yᵢ - ∑_{i ⟶ j} xᵢ yⱼ` has the nonsymmetric matrix `I - A` in the simple dimension
vectors, and its symmetrization `(I - A) + (I - A)ᵀ = 2I - (A + Aᵀ)` is the Cartan matrix
`CartanMatrix.E 8`: the Gram matrix of the `E₈` root lattice in its simple roots. That Gram matrix
is positive definite, so the Tits form of the quiver is positive definite and the quiver is
acyclic. The Euler form itself is not symmetric, as its matrix shows.

## Main results

* `TauCeti.Quiver.E8.submatrix_toMatrix_eulerForm`: the matrix `I - A` of the Euler form, written
  out.
* `TauCeti.Quiver.E8.submatrix_toMatrix_eulerForm_add_transpose` and
  `TauCeti.Quiver.E8.submatrix_toMatrix_titsPolarForm`: its symmetrization, the Gram matrix of the
  polarized Tits form, is `CartanMatrix.E 8`.
* `TauCeti.Quiver.E8.titsForm_posDef`: the Tits form is positive definite.

## References

* Ibrahim Assem, Daniel Simson and Andrzej Skowroński, *Elements of the Representation Theory of
  Associative Algebras I*, Chapter III, Section 3 (the Euler form of a quiver in the simple
  dimension vectors) and Chapter VII (the Tits form and the Dynkin diagrams).
-/

public section

namespace TauCeti

open _root_.Quiver DoubledQuiver
open scoped _root_.Matrix

namespace Quiver.E8

/-- **The Euler matrix of the `E₈` quiver** in the simple dimension vectors is `I - A`, for `A`
the matrix of arrow counts: the entry `(i, j)` is `⟨αᵢ, αⱼ⟩ = δᵢⱼ - #(i ⟶ j)`. -/
theorem submatrix_toMatrix_eulerForm :
    ((eulerForm E8).toMatrix (Pi.basisFun ℤ E8)).submatrix vertexEquiv vertexEquiv =
      !![1, 0, -1,  0,  0,  0,  0,  0;
         0, 1,  0, -1,  0,  0,  0,  0;
         0, 0,  1, -1,  0,  0,  0,  0;
         0, 0,  0,  1, -1,  0,  0,  0;
         0, 0,  0,  0,  1, -1,  0,  0;
         0, 0,  0,  0,  0,  1, -1,  0;
         0, 0,  0,  0,  0,  0,  1, -1;
         0, 0,  0,  0,  0,  0,  0,  1] := by
  ext i j
  rw [Matrix.submatrix_apply, LinearMap.BilinForm.toMatrix_apply, Pi.basisFun_apply,
    Pi.basisFun_apply, eulerForm_single_single, card_hom]
  simp only [vertexEquiv.injective.eq_iff]
  fin_cases i <;> fin_cases j <;> decide

/-- **The symmetrized Euler matrix of the `E₈` quiver is the `E₈` Cartan matrix**:
`(I - A) + (I - A)ᵀ = 2I - (A + Aᵀ)` is `CartanMatrix.E 8`. -/
theorem submatrix_toMatrix_eulerForm_add_transpose :
    ((eulerForm E8).toMatrix (Pi.basisFun ℤ E8)).submatrix vertexEquiv vertexEquiv +
        (((eulerForm E8).toMatrix (Pi.basisFun ℤ E8)).submatrix vertexEquiv vertexEquiv)ᵀ =
      CartanMatrix.E 8 := by
  rw [submatrix_toMatrix_eulerForm, CartanMatrix.E_eight_eq]
  decide

/-- **The Gram matrix of the polarized Tits form of the `E₈` quiver is the `E₈` Cartan matrix.** -/
theorem submatrix_toMatrix_titsPolarForm :
    ((titsPolarForm E8).toMatrix (Pi.basisFun ℤ E8)).submatrix vertexEquiv vertexEquiv =
      CartanMatrix.E 8 := by
  ext i j
  have h := congrFun (congrFun submatrix_toMatrix_eulerForm_add_transpose i) j
  simpa only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.transpose_apply,
    LinearMap.BilinForm.toMatrix_apply, titsPolarForm_def] using h

/-- **The Tits form of the `E₈` quiver is positive definite.** -/
theorem titsForm_posDef : (titsForm E8).PosDef := by
  rw [titsForm_posDef_iff_posDef_toMatrix]
  have h : (titsPolarForm E8).toMatrix (Pi.basisFun ℤ E8) =
      (CartanMatrix.E 8).submatrix vertexEquiv.symm vertexEquiv.symm := by
    ext i j
    simpa only [Matrix.submatrix_apply, Equiv.apply_symm_apply] using
      congrFun (congrFun submatrix_toMatrix_titsPolarForm (vertexEquiv.symm i)) (vertexEquiv.symm j)
  rw [h]
  exact (Matrix.posDef_map_intCast_iff.mp posDef_map_intCast_cartanMatrix_E8).submatrix
    vertexEquiv.symm.injective

end Quiver.E8

end TauCeti
