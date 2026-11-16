/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Invertible matrices over subfields

Unlike general subalgebras (`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Subalgebra`), where
descent of an invertible matrix requires checking both the matrix and its inverse, an invertible
matrix over a field `L` whose entries lie in a subfield `E` automatically has nonzero determinant
in `E` and therefore lifts to `GL ι E`. In particular, the inverse matrix also has entries in `E`,
and the image of `GL ι E →* GL ι L` is cut out purely by entrywise membership in `E`.

## Main definitions

* `Matrix.GeneralLinearGroup.liftOfMem`: lift an element of `GL ι L` with entries in a subfield
  `E` to `GL ι E`.

## Main results

* `Matrix.GeneralLinearGroup.map_subtype_liftOfMem`: pushing `liftOfMem E A hA` forward along
  `SubringClass.subtype E` recovers `A`.
* `Matrix.GeneralLinearGroup.map_algebraMap_liftOfMem`: pushing `liftOfMem E A hA` forward along
  `algebraMap E L` recovers `A`.
* `Matrix.GeneralLinearGroup.coe_liftOfMem_apply`: the entries of `liftOfMem E A hA` agree with
  those of `A`.
* `Matrix.GeneralLinearGroup.mem_range_map_subtype_iff`: an element of `GL ι L` lies in the range
  of `GL ι E →* GL ι L` if and only if all of its entries lie in `E`.
* `Matrix.GeneralLinearGroup.inv_apply_mem`: if every entry of `A : GL ι L` lies in `E`, then
  every entry of `A⁻¹` lies in `E`.
-/

public section

namespace Matrix.GeneralLinearGroup

variable {L S ι : Type*} [Field L] [SetLike S L] [SubfieldClass S L]
  [Fintype ι] [DecidableEq ι]

/-- **Lifting an invertible matrix to a subfield.** If every entry of `A : GL ι L` lies in a
subfield `E`, then its determinant is nonzero in `E`, so `A` lifts to `GL ι E`. -/
noncomputable def liftOfMem (E : S) (A : GL ι L) (hA : ∀ i j, (A : Matrix ι ι L) i j ∈ E) :
    GL ι E :=
  let M : Matrix ι ι E := Matrix.of fun i j ↦ ⟨(A : Matrix ι ι L) i j, hA i j⟩
  have hM : (SubringClass.subtype E).mapMatrix M = (A : Matrix ι ι L) := by
    ext i j
    simp only [M, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      SubringClass.coe_subtype]
  have hdet : M.det ≠ 0 := by
    intro h0
    have hdetA : (A : Matrix ι ι L).det = 0 := by
      rw [← hM, ← RingHom.map_det (SubringClass.subtype E) M, h0, map_zero]
    exact A.det_ne_zero hdetA
  Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet

/-- Pushing `liftOfMem E A hA` forward along `SubringClass.subtype E` recovers `A`. -/
@[simp]
theorem map_subtype_liftOfMem (E : S) (A : GL ι L) (hA : ∀ i j, (A : Matrix ι ι L) i j ∈ E) :
    Matrix.GeneralLinearGroup.map (SubringClass.subtype E) (liftOfMem E A hA) = A := by
  ext i j
  simp only [liftOfMem, Matrix.GeneralLinearGroup.map_apply, val_mkOfDetNeZero, Matrix.of_apply,
    SubringClass.coe_subtype]

/-- Pushing `liftOfMem E A hA` forward along `algebraMap E L` recovers `A`. -/
@[simp]
theorem map_algebraMap_liftOfMem (E : S) (A : GL ι L) (hA : ∀ i j, (A : Matrix ι ι L) i j ∈ E) :
    Matrix.GeneralLinearGroup.map (algebraMap E L) (liftOfMem E A hA) = A := by
  ext i j
  simp only [liftOfMem, Matrix.GeneralLinearGroup.map_apply, val_mkOfDetNeZero, Matrix.of_apply,
    Algebra.algebraMap_ofSubsemiring_apply]

/-- The entries of `liftOfMem E A hA` coerce to the entries of `A`. -/
@[simp]
theorem coe_liftOfMem_apply (E : S) (A : GL ι L) (hA : ∀ i j, (A : Matrix ι ι L) i j ∈ E)
    (i j : ι) :
    ((liftOfMem E A hA : Matrix ι ι E) i j : L) = (A : Matrix ι ι L) i j := by
  have h := congrArg (fun u : GL ι L ↦ (u : Matrix ι ι L) i j) (map_subtype_liftOfMem E A hA)
  simpa only [Matrix.GeneralLinearGroup.map_apply, SubringClass.coe_subtype] using h

/-- **Range of `GL ι E →* GL ι L` for a subfield.** An invertible matrix over `L` comes from a
subfield `E` if and only if all of its entries lie in `E`. -/
theorem mem_range_map_subtype_iff (E : S) (A : GL ι L) :
    A ∈ (Matrix.GeneralLinearGroup.map (n := ι) (SubringClass.subtype E)).range ↔
      ∀ i j, (A : Matrix ι ι L) i j ∈ E := by
  constructor
  · rintro ⟨B, rfl⟩ i j
    rw [Matrix.GeneralLinearGroup.map_apply, SubringClass.coe_subtype]
    exact SetLike.coe_mem _
  · intro hA
    exact ⟨liftOfMem E A hA, map_subtype_liftOfMem E A hA⟩

/-- **Inverse-entry closure over a subfield.** If every entry of `A : GL ι L` lies in a subfield
`E`, then every entry of `A⁻¹` also lies in `E`. -/
theorem inv_apply_mem (E : S) (A : GL ι L) (hA : ∀ i j, (A : Matrix ι ι L) i j ∈ E) (i j : ι) :
    ((A⁻¹ : GL ι L) : Matrix ι ι L) i j ∈ E := by
  have hmem : A⁻¹ ∈ (Matrix.GeneralLinearGroup.map (n := ι) (SubringClass.subtype E)).range :=
    inv_mem ((mem_range_map_subtype_iff E A).mpr hA)
  exact (mem_range_map_subtype_iff E A⁻¹).mp hmem i j

end Matrix.GeneralLinearGroup
