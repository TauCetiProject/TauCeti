/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram
public import TauCeti.RepresentationTheory.Quiver.Acyclic.TitsForm
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Orientation
import TauCeti.LinearAlgebra.Matrix.PosDef.Basic
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin

/-!
# The oriented `E₈` quiver and its Euler form

This file fixes one orientation of the `E₈` Dynkin diagram and computes the Euler form of the
resulting quiver in its simple dimension vectors. The nodes are numbered as in Mathlib's
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

## Main definitions

* `TauCeti.Quiver.E8`: the oriented `E₈` quiver, the orientation of the diagram of
  `CartanMatrix.E 8` from smaller to larger nodes.
* `TauCeti.Quiver.E8.vertexEquiv`: its vertices are the eight nodes `Fin 8`.

## Main results

* `TauCeti.Quiver.E8.card_hom`: there is one arrow `i ⟶ j` when `i < j` are joined in the
  diagram, and none otherwise.
* `TauCeti.Quiver.E8.submatrix_toMatrix_eulerForm`: the matrix `I - A` of the Euler form, written
  out.
* `TauCeti.Quiver.E8.submatrix_toMatrix_eulerForm_add_transpose` and
  `TauCeti.Quiver.E8.submatrix_toMatrix_titsPolarForm`: its symmetrization, the Gram matrix of the
  polarized Tits form, is `CartanMatrix.E 8`.
* `TauCeti.Quiver.E8.titsForm_posDef`: the Tits form is positive definite.
* `TauCeti.Quiver.E8.isAcyclic`: the orientation is acyclic.

## References

* Ibrahim Assem, Daniel Simson and Andrzej Skowroński, *Elements of the Representation Theory of
  Associative Algebras I*, Chapter III, Section 3 (the Euler form of a quiver in the simple
  dimension vectors) and Chapter VII (the Tits form and the Dynkin diagrams).
* N. Bourbaki, *Lie groups and Lie algebras, Chapters 4–6*, Plate VII, for the numbering of the
  `E₈` diagram and its Cartan matrix.
-/

public section

namespace TauCeti

open _root_.Quiver DoubledQuiver
open scoped _root_.Matrix

namespace Quiver

/-- **The oriented `E₈` quiver.** Its vertices are the eight nodes of the `E₈` Dynkin diagram,
numbered as in `CartanMatrix.E 8`, and each of the seven edges of the diagram carries one arrow,
directed from its smaller node to its larger one. -/
abbrev E8 : Type :=
  OrientedQuiver (diagramGraph (CartanMatrix.E 8)) (Orientation.ofLinearOrder _)

namespace E8

/-- The vertices of the `E₈` quiver are the eight nodes of the diagram. -/
def vertexEquiv : Fin 8 ≃ E8 :=
  OrientedQuiver.vertexEquiv _ _

@[simp]
theorem vertexEquiv_apply (i : Fin 8) : vertexEquiv i = OrientedQuiver.vertex _ _ i :=
  OrientedQuiver.vertexEquiv_apply _ _ i

instance : Fintype E8 :=
  Fintype.ofEquiv (Fin 8) vertexEquiv

instance : DecidableEq E8 :=
  vertexEquiv.symm.decidableEq

/-- Each space of arrows of the `E₈` quiver is finite; it is a subsingleton, the quiver being
thin. -/
noncomputable instance (i j : E8) : Fintype (i ⟶ j) :=
  Fintype.ofFinite _

/-- **The arrows of the `E₈` quiver**: there is exactly one arrow `i ⟶ j` when the nodes `i < j`
are joined by an edge of the `E₈` diagram, and there are no others. -/
theorem card_hom (i j : Fin 8) :
    Fintype.card (vertexEquiv i ⟶ vertexEquiv j) =
      if i < j ∧ (diagramGraph (CartanMatrix.E 8)).Adj i j then 1 else 0 := by
  rw [Fintype.card_eq_nat_card, vertexEquiv_apply, vertexEquiv_apply,
    Nat.card_congr (OrientedQuiver.homEquiv _ _ i j)]
  simp only [Orientation.mem_ofLinearOrder_iff]
  split_ifs with h
  · exact Nat.card_eq_one_iff_unique.2 ⟨⟨fun _ _ ↦ Subtype.ext rfl⟩, ⟨⟨h.2, h.1⟩⟩⟩
  · exact @Nat.card_of_isEmpty _ ⟨fun p ↦ h ⟨p.2, p.1⟩⟩

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

/-- **The Tits form of the `E₈` quiver is positive definite**, because its polarization has the
positive definite Gram matrix `CartanMatrix.E 8`. -/
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

/-- The orientation of the `E₈` quiver is acyclic. -/
theorem isAcyclic : Quiver.IsAcyclic E8 :=
  isAcyclic_of_titsForm_posDef titsForm_posDef

end E8

end Quiver

end TauCeti
