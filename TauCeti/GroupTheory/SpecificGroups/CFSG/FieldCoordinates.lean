/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius

/-!
# Finite-field coordinates for groups of Lie type

The fixed-point constructions of finite groups of Lie type use matrices over algebraic closures
of prime fields, while concrete finite matrix groups are naturally written over Mathlib's
`GaloisField p e`. This file supplies the coordinate bridge between those realizations of the
field with `p ^ e` elements.

For a valid Lie-type index `d`, `TauCeti.ValidLieTypeIndex.galoisFieldEmbedding` embeds Mathlib's
finite field into `d.Closure` with image the `d.fieldOrder`-Frobenius-fixed field. The results below
lift that embedding entrywise to matrices and invertible matrices. In particular, a matrix over
the closure comes from finite-field coordinates exactly when each of its entries is fixed by the
field Frobenius.

The Suzuki comparison is the immediate consumer: its fixed-point carrier is defined over the
closure, while the explicit four-dimensional matrix group is defined over
`GaloisField 2 (2 * m + 1)`. No group comparison is made here; these results identify only the
coefficient fields and their matrix coordinates.

## Main results

* `TauCeti.ValidLieTypeIndex.exists_matrix_map_galoisFieldEmbedding_iff`: a matrix over the closure
  comes from the finite field exactly when all its entries are Frobenius-fixed.
* `TauCeti.ValidLieTypeIndex.matrix_map_galoisFieldEmbedding_injective`: entrywise scalar extension
  along the finite-field embedding is injective.
* `TauCeti.ValidLieTypeIndex.generalLinearGroup_map_galoisFieldEmbedding_injective`: scalar
  extension embeds the corresponding general linear groups.
* `TauCeti.ValidLieTypeIndex.mem_range_generalLinearGroup_map_galoisFieldEmbedding_iff`: an
  invertible matrix over the closure comes from the finite field exactly when its entries are
  Frobenius-fixed.

## References

* M. Suzuki, *On a class of doubly transitive groups*, Annals of Mathematics **75** (1962),
  105--145.
-/

public section

namespace TauCeti.ValidLieTypeIndex

noncomputable section

variable (d : ValidLieTypeIndex)

/-- Entrywise scalar extension from Mathlib's finite field to the closure is injective. -/
theorem matrix_map_galoisFieldEmbedding_injective {m n : Type*} :
    Function.Injective
      (fun A : Matrix m n (GaloisField d.characteristic d.fieldExponent) ↦
        A.map d.galoisFieldEmbedding) :=
  Matrix.map_injective d.galoisFieldEmbedding_injective

variable {d}

/-- A matrix over the closure has coordinates in Mathlib's finite field exactly when every entry
belongs to the image of the chosen finite-field embedding. -/
theorem exists_matrix_map_galoisFieldEmbedding_iff {m n : Type*}
    (A : Matrix m n d.Closure) :
    (∃ B : Matrix m n (GaloisField d.characteristic d.fieldExponent),
        B.map d.galoisFieldEmbedding = A) ↔
      ∀ i j, A i j ∈ RingHom.range d.galoisFieldEmbedding := by
  constructor
  · rintro ⟨B, rfl⟩ i j
    exact ⟨B i j, rfl⟩
  · intro hA
    choose B hB using hA
    exact ⟨B, Matrix.ext fun i j ↦ hB i j⟩

/-- A matrix over the closure has finite-field coordinates exactly when every entry is fixed by
the `q`-power Frobenius. -/
theorem exists_matrix_map_galoisFieldEmbedding_iff_frobenius
    {m n : Type*} (A : Matrix m n d.Closure) :
    (∃ B : Matrix m n (GaloisField d.characteristic d.fieldExponent),
        B.map d.galoisFieldEmbedding = A) ↔
      ∀ i j, (A i j) ^ d.fieldOrder = A i j := by
  rw [exists_matrix_map_galoisFieldEmbedding_iff]
  simp only [ValidLieTypeIndex.mem_range_galoisFieldEmbedding_iff]

variable (d)

/-- Scalar extension from Mathlib's finite field embeds the general linear group into the general
linear group over the closure. -/
theorem generalLinearGroup_map_galoisFieldEmbedding_injective
    {n : Type*} [Fintype n] [DecidableEq n] :
    Function.Injective
      (Matrix.GeneralLinearGroup.map (n := n) d.galoisFieldEmbedding) := by
  exact Units.map_injective (Matrix.map_injective d.galoisFieldEmbedding_injective)

variable {d}

/-- An invertible matrix over the closure comes by scalar extension from Mathlib's finite field
exactly when every matrix entry is fixed by the `q`-power Frobenius.

This is not a `simp` lemma: `MonoidHom.mem_range` already unfolds the left-hand side into an
existential, so it is not in `simp`-normal form. -/
theorem mem_range_generalLinearGroup_map_galoisFieldEmbedding_iff
    {n : Type*} [Fintype n] [DecidableEq n]
    (g : Matrix.GeneralLinearGroup n d.Closure) :
    g ∈ MonoidHom.range (Matrix.GeneralLinearGroup.map (n := n) d.galoisFieldEmbedding) ↔
      ∀ i j, (g i j) ^ d.fieldOrder = g i j := by
  constructor
  · rintro ⟨g₀, rfl⟩ i j
    exact d.mem_range_galoisFieldEmbedding_iff.mp
      ⟨g₀ i j, Matrix.GeneralLinearGroup.map_apply d.galoisFieldEmbedding i j g₀⟩
  · intro hg
    obtain ⟨A, hA⟩ :=
      (d.exists_matrix_map_galoisFieldEmbedding_iff_frobenius (g : Matrix n n d.Closure)).mpr hg
    have hAmap : d.galoisFieldEmbedding.mapMatrix A = (g : Matrix n n d.Closure) :=
      (RingHom.mapMatrix_apply d.galoisFieldEmbedding A).trans hA
    have hdet : A.det ≠ 0 := by
      intro hzero
      have hmapdet : d.galoisFieldEmbedding A.det = (g : Matrix n n d.Closure).det := by
        calc
          d.galoisFieldEmbedding A.det = (d.galoisFieldEmbedding.mapMatrix A).det :=
            d.galoisFieldEmbedding.map_det A
          _ = (g : Matrix n n d.Closure).det := congrArg Matrix.det hAmap
      have hdetzero : (g : Matrix n n d.Closure).det = 0 := by
        rw [← hmapdet, hzero, map_zero]
      exact (Matrix.isUnits_det_units g).ne_zero hdetzero
    obtain ⟨g₀, hg₀⟩ : ∃ g₀ : Matrix.GeneralLinearGroup n
        (GaloisField d.characteristic d.fieldExponent), (g₀ : Matrix n n _) = A := by
      exact (Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.mpr hdet)
    refine ⟨g₀, Units.ext ?_⟩
    apply Matrix.ext
    intro i j
    calc
      Matrix.GeneralLinearGroup.map d.galoisFieldEmbedding g₀ i j =
          d.galoisFieldEmbedding (g₀ i j) :=
        Matrix.GeneralLinearGroup.map_apply d.galoisFieldEmbedding i j g₀
      _ = d.galoisFieldEmbedding (A i j) :=
        congrArg d.galoisFieldEmbedding (congrFun (congrFun hg₀ i) j)
      _ = d.galoisFieldEmbedding.mapMatrix A i j :=
        (congrFun (congrFun (RingHom.mapMatrix_apply d.galoisFieldEmbedding A) i) j).symm
      _ = g i j := congrFun (congrFun hAmap i) j

end

end TauCeti.ValidLieTypeIndex
