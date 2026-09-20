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
`GaloisField 2 (2 * m + 1)`. The underlying field-embedding results are stated generally, then
specialized to the chosen finite-field embedding.

## Main result

* `Matrix.GeneralLinearGroup.mem_range_map_iff`: scalar extension along a field embedding has
  precisely the invertible matrices whose entries lie in the embedding's range.
* `Matrix.GeneralLinearGroup.mem_range_map_galoisFieldEmbedding_iff`: an
  invertible matrix over the closure comes from the finite field exactly when its entries are
  Frobenius-fixed.

## References

* M. Suzuki, *On a class of doubly transitive groups*, Annals of Mathematics **75** (1962),
  105--145.
-/

public section

open TauCeti
open TauCeti.ValidLieTypeIndex

noncomputable section

namespace Matrix

variable {d : ValidLieTypeIndex}

/-- A matrix is obtained by applying a field embedding entrywise exactly when all of its entries
lie in the range of that embedding. -/
theorem exists_map_iff_mem_range
    {K L m n : Type*} [Field K] [Field L] (f : K →+* L) (A : Matrix m n L) :
    (∃ B : Matrix m n K, B.map f = A) ↔ ∀ i j, A i j ∈ RingHom.range f := by
  change A ∈ Set.range (Pi.map fun _ ↦ Pi.map fun _ ↦ f) ↔ _
  rw [Set.range_piMap]
  constructor
  · intro hA i j
    have hi := hA i (Set.mem_univ i)
    rw [Set.range_piMap] at hi
    exact hi j (Set.mem_univ j)
  · intro hA i _
    rw [Set.range_piMap]
    exact fun j _ ↦ hA i j

/-- A matrix over the closure has finite-field coordinates exactly when every entry is fixed by
the `q`-power Frobenius. -/
theorem exists_map_galoisFieldEmbedding_iff_frobenius
    {m n : Type*} (A : Matrix m n d.Closure) :
    (∃ B : Matrix m n (GaloisField d.characteristic d.fieldExponent),
        B.map d.galoisFieldEmbedding = A) ↔
      ∀ i j, (A i j) ^ d.fieldOrder = A i j := by
  rw [exists_map_iff_mem_range]
  exact forall_congr' fun _ ↦ forall_congr' fun _ ↦
    d.mem_range_galoisFieldEmbedding_iff

end Matrix

namespace Matrix.GeneralLinearGroup

variable {d : ValidLieTypeIndex}

/-- Scalar extension along a field embedding has precisely the invertible matrices whose entries
lie in the embedding's range.

Unlike `mem_range_map_val_iff`, no condition on the inverse matrix is needed: over a field, a
matrix whose entries descend and whose determinant is nonzero remains invertible before scalar
extension. -/
theorem mem_range_map_iff
    {K L n : Type*} [Field K] [Field L] [Fintype n] [DecidableEq n]
    (f : K →+* L) (g : Matrix.GeneralLinearGroup n L) :
    g ∈ MonoidHom.range (Matrix.GeneralLinearGroup.map (n := n) f) ↔
      ∀ i j, g i j ∈ RingHom.range f := by
  constructor
  · rintro ⟨g₀, rfl⟩ i j
    exact ⟨g₀ i j, Matrix.GeneralLinearGroup.map_apply f i j g₀⟩
  · intro hg
    obtain ⟨A, hA⟩ := (Matrix.exists_map_iff_mem_range f
      (g : Matrix n n L)).mpr hg
    have hAmap : f.mapMatrix A = (g : Matrix n n L) :=
      (RingHom.mapMatrix_apply f A).trans hA
    have hdet : A.det ≠ 0 := by
      intro hzero
      have hmapdet : f A.det = (g : Matrix n n L).det := by
        calc
          f A.det = (f.mapMatrix A).det := f.map_det A
          _ = (g : Matrix n n L).det := congrArg Matrix.det hAmap
      have hdetzero : (g : Matrix n n L).det = 0 := by
        rw [← hmapdet, hzero, map_zero]
      exact (Matrix.isUnits_det_units g).ne_zero hdetzero
    obtain ⟨g₀, hg₀⟩ : ∃ g₀ : Matrix.GeneralLinearGroup n K,
        (g₀ : Matrix n n K) = A := by
      exact (Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.mpr hdet)
    refine ⟨g₀, Units.ext ?_⟩
    apply Matrix.ext
    intro i j
    calc
      Matrix.GeneralLinearGroup.map f g₀ i j = f (g₀ i j) :=
        Matrix.GeneralLinearGroup.map_apply f i j g₀
      _ = f (A i j) := congrArg f (congrFun (congrFun hg₀ i) j)
      _ = f.mapMatrix A i j :=
        (congrFun (congrFun (RingHom.mapMatrix_apply f A) i) j).symm
      _ = g i j := congrFun (congrFun hAmap i) j

/-- An invertible matrix over the closure comes by scalar extension from Mathlib's finite field
exactly when every matrix entry is fixed by the `q`-power Frobenius.

This is not a `simp` lemma: `MonoidHom.mem_range` already unfolds the left-hand side into an
existential, so it is not in `simp`-normal form. -/
theorem mem_range_map_galoisFieldEmbedding_iff
    {n : Type*} [Fintype n] [DecidableEq n]
    (g : Matrix.GeneralLinearGroup n d.Closure) :
    g ∈ MonoidHom.range (Matrix.GeneralLinearGroup.map (n := n) d.galoisFieldEmbedding) ↔
      ∀ i j, (g i j) ^ d.fieldOrder = g i j := by
  rw [mem_range_map_iff]
  exact forall_congr' fun _ ↦ forall_congr' fun _ ↦
    d.mem_range_galoisFieldEmbedding_iff

end Matrix.GeneralLinearGroup

end
