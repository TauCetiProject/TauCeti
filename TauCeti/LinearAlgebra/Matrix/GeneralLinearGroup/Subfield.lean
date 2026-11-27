/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Descend

/-!
# Invertible matrices over subfields

Unlike general subalgebras (`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Subalgebra`), where
descent of an invertible matrix requires checking both the matrix and its inverse, an invertible
matrix over a field `L` whose entries lie in a subfield `E` automatically has nonzero determinant
in `E` and therefore lifts to `GL ι E`. In particular, the inverse matrix also has entries in `E`,
and the image of `GL ι E →* GL ι L` is cut out purely by entrywise membership in `E`.

## Main results

* `Matrix.GeneralLinearGroup.inv_apply_mem`: if every entry of `A : GL ι L` lies in `E`, then
  every entry of `A⁻¹` lies in `E`.
* `Matrix.GeneralLinearGroup.mem_range_map_subtype_iff`: an element of `GL ι L` lies in the range
  of `GL ι E →* GL ι L` if and only if all of its entries lie in `E`.
-/

public section

namespace Matrix.GeneralLinearGroup

variable {L S ι : Type*} [Field L] [SetLike S L] [SubfieldClass S L]
  [Fintype ι] [DecidableEq ι]

private theorem det_mem (E : S) (M : Matrix ι ι L) (hM : ∀ i j, M i j ∈ E) :
    M.det ∈ E := by
  rw [Matrix.det_apply]
  exact sum_mem fun σ _ ↦ zsmul_mem (prod_mem fun i _ ↦ hM (σ i) i) _

/-- **Inverse-entry closure over a subfield.** If every entry of `A : GL ι L` lies in a subfield
`E`, then every entry of `A⁻¹` also lies in `E`. -/
theorem inv_apply_mem (E : S) (A : GL ι L) (hA : ∀ i j, (A : Matrix ι ι L) i j ∈ E) (i j : ι) :
    ((A⁻¹ : GL ι L) : Matrix ι ι L) i j ∈ E := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul,
    Ring.inverse_eq_inv', Matrix.adjugate_apply]
  refine mul_mem (inv_mem (det_mem E (A : Matrix ι ι L) hA)) (det_mem E _ fun r c ↦ ?_)
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]
    split_ifs <;> [exact one_mem E; exact zero_mem E]
  · exact hA r c

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
    let H : Subgroup (GL ι L) :=
      { carrier := {g | ∀ i j, (g : Matrix ι ι L) i j ∈ E}
        one_mem' i j := by
          simp only [Units.val_one, Matrix.one_apply]
          split_ifs <;> [exact one_mem E; exact zero_mem E]
        mul_mem' ha hb i j := by
          rw [Units.val_mul, Matrix.mul_apply]
          exact sum_mem fun k _ ↦ mul_mem (ha i k) (hb k j)
        inv_mem' ha := inv_apply_mem E _ ha }
    have hz : TauCeti.CoefficientDescent.entries (Subgroup.zpowers A).subtype ⊆
        Set.range (SubringClass.subtype E) := by
      intro x hx
      obtain ⟨⟨g, hg⟩, i, j, rfl⟩ := TauCeti.CoefficientDescent.mem_entries_iff.mp hx
      exact ⟨⟨(g : Matrix ι ι L) i j, (Subgroup.zpowers_le (H := H)).mpr hA hg i j⟩, rfl⟩
    exact ⟨TauCeti.CoefficientDescent.descend Subtype.val_injective hz ⟨A, Subgroup.mem_zpowers A⟩,
      TauCeti.CoefficientDescent.map_descend Subtype.val_injective hz ⟨A, Subgroup.mem_zpowers A⟩⟩

end Matrix.GeneralLinearGroup
