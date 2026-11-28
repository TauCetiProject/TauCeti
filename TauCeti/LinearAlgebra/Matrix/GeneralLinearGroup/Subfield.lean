/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Invertible matrices over subfields

Unlike general subalgebras (`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Subalgebra`), where
descent of an invertible matrix requires checking both the matrix and its inverse, an invertible
matrix over a field `L` whose entries lie in a subfield `E` automatically has nonzero determinant
in `E` and therefore lifts to `GL ι E`. In particular, the inverse matrix also has entries in `E`,
and the image of `GL ι E →* GL ι L` is cut out purely by entrywise membership in `E`.

## Main results

* `Matrix.GeneralLinearGroup.mem_range_map_subtype_iff`: an element of `GL ι L` lies in the range
  of `GL ι E →* GL ι L` if and only if all of its entries lie in `E`.
* `Matrix.GeneralLinearGroup.inv_apply_mem`: if every entry of `A : GL ι L` lies in `E`, then
  every entry of `A⁻¹` lies in `E`.
-/

public section

namespace Matrix.GeneralLinearGroup

variable {L S ι : Type*} [Field L] [SetLike S L] [SubfieldClass S L]
  [Fintype ι] [DecidableEq ι]

/-- **Range of `GL ι E →* GL ι L` for a subfield.** An invertible matrix over `L` comes from a
subfield `E` if and only if all of its entries lie in `E`. -/
theorem mem_range_map_subtype_iff (E : S) (A : GL ι L) :
    A ∈ (Matrix.GeneralLinearGroup.map (n := ι) (SubringClass.subtype E)).range ↔
      ∀ i j, (A : Matrix ι ι L) i j ∈ E := by
  refine ⟨?_, fun hA ↦ ?_⟩
  · rintro ⟨u, rfl⟩ i j
    exact SetLike.coe_mem _
  · let B : Matrix ι ι E := Matrix.of fun i j ↦ ⟨(A : Matrix ι ι L) i j, hA i j⟩
    have hB : B.map (SubringClass.subtype E) = (A : Matrix ι ι L) := by
      ext i j
      rfl
    have hdet : B.det ≠ 0 := fun h ↦ by
      have h0 : (A : Matrix ι ι L).det = 0 := by
        rw [← hB, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
      exact A.det.ne_zero h0
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero B hdet, Units.ext ?_⟩
    ext i j
    rfl

/-- **Inverse-entry closure over a subfield.** If every entry of `A : GL ι L` lies in a subfield
`E`, then every entry of `A⁻¹` also lies in `E`. -/
theorem inv_apply_mem (E : S) (A : GL ι L) (hA : ∀ i j, (A : Matrix ι ι L) i j ∈ E) (i j : ι) :
    ((A⁻¹ : GL ι L) : Matrix ι ι L) i j ∈ E := by
  obtain ⟨u, hu⟩ := (mem_range_map_subtype_iff E A).mpr hA
  have hinv : A⁻¹ = Matrix.GeneralLinearGroup.map (SubringClass.subtype E) u⁻¹ := by
    rw [← hu, map_inv]
  rw [hinv]
  exact SetLike.coe_mem _

end Matrix.GeneralLinearGroup
