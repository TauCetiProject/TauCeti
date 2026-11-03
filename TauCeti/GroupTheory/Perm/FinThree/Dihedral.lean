/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Fin
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic
import TauCeti.GroupTheory.Perm.FinThree.Basic

/-!
# The symmetric group on three points is the dihedral group of order six

The transposition `σ = (0 1)` and the cycle `τ = (0 1 2) = finRotate 3` generate `S₃`
(`TauCeti.closure_finRotate_three_swap_eq_top`). The two involutions `σ` and `στ` therefore
generate it too, and their product is `τ`, of order three, so the recognition criterion
`TauCeti.dihedralGroupMulEquiv` identifies `S₃` with `DihedralGroup 3`: the rotation `r i` goes to
`τ ^ i` and the reflection `sr i` to `σ τ ^ i`. This is the identification under which character
tables computed for `DihedralGroup 3` are read as character tables of `S₃`.

## Main definitions

* `TauCeti.dihedralGroupThreeMulEquivPerm`: the isomorphism `DihedralGroup 3 ≃* Equiv.Perm (Fin 3)`
  sending `r 1` to `τ` and `sr 0` to `σ`.

## Main results

* `TauCeti.dihedralGroupThreeMulEquivPerm_r` and `TauCeti.dihedralGroupThreeMulEquivPerm_sr`:
  the images of the rotations and reflections.
* `TauCeti.dihedralGroupThreeMulEquivPerm_r_two` and
  `TauCeti.dihedralGroupThreeMulEquivPerm_sr_two`: the images of `r 2` and `sr 2`, written as
  conjugates of `τ` and `σ`.
-/

public section

namespace TauCeti

/-- The product of the involutions `σ = (0 1)` and `στ` is `τ = (0 1 2)`. -/
private theorem swap_mul_swap_mul_finRotate :
    Equiv.swap (0 : Fin 3) 1 * (Equiv.swap 0 1 * finRotate 3) = finRotate 3 := by
  decide

/-- The two involutions `σ` and `στ` generate `S₃`. -/
private theorem closure_swap_swap_mul_finRotate :
    Subgroup.closure {Equiv.swap (0 : Fin 3) 1, Equiv.swap 0 1 * finRotate 3} = ⊤ := by
  rw [eq_top_iff, ← closure_finRotate_three_swap_eq_top, Subgroup.closure_le]
  have hσ : Equiv.swap (0 : Fin 3) 1 ∈
      Subgroup.closure {Equiv.swap (0 : Fin 3) 1, Equiv.swap 0 1 * finRotate 3} :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hστ : Equiv.swap (0 : Fin 3) 1 * finRotate 3 ∈
      Subgroup.closure {Equiv.swap (0 : Fin 3) 1, Equiv.swap 0 1 * finRotate 3} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  rintro g (rfl | rfl)
  · have h := mul_mem hσ hστ
    rwa [swap_mul_swap_mul_finRotate] at h
  · exact hσ

/-- **The dihedral group of order six is `S₃`**: the isomorphism sending the rotation `r 1` to
`τ = (0 1 2)` and the reflection `sr 0` to `σ = (0 1)`, so that `r i ↦ τ ^ i` and
`sr i ↦ σ τ ^ i`. -/
noncomputable def dihedralGroupThreeMulEquivPerm : DihedralGroup 3 ≃* Equiv.Perm (Fin 3) :=
  dihedralGroupMulEquiv (s := Equiv.swap 0 1) (t := Equiv.swap 0 1 * finRotate 3)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [swap_mul_swap_mul_finRotate]; exact orderOf_eq_prime (by decide) (by decide))
    closure_swap_swap_mul_finRotate

/-- The rotation `r i` goes to `τ ^ i`. -/
@[simp]
theorem dihedralGroupThreeMulEquivPerm_r (i : ZMod 3) :
    dihedralGroupThreeMulEquivPerm (.r i) = finRotate 3 ^ (i.cast : ℤ) := by
  rw [dihedralGroupThreeMulEquivPerm, dihedralGroupMulEquiv_apply, dihedralHom_r,
    swap_mul_swap_mul_finRotate]

/-- The reflection `sr i` goes to `σ τ ^ i`. -/
@[simp]
theorem dihedralGroupThreeMulEquivPerm_sr (i : ZMod 3) :
    dihedralGroupThreeMulEquivPerm (.sr i) = Equiv.swap 0 1 * finRotate 3 ^ (i.cast : ℤ) := by
  rw [dihedralGroupThreeMulEquivPerm, dihedralGroupMulEquiv_apply, dihedralHom_sr,
    swap_mul_swap_mul_finRotate]

/-- The rotation `r 2` goes to the conjugate `σ τ σ⁻¹` of `τ`. -/
theorem dihedralGroupThreeMulEquivPerm_r_two :
    dihedralGroupThreeMulEquivPerm (.r 2) =
      Equiv.swap 0 1 * finRotate 3 * (Equiv.swap 0 1)⁻¹ := by
  rw [dihedralGroupThreeMulEquivPerm_r]
  decide

/-- The reflection `sr 2` goes to the conjugate `(1 2) σ (1 2)⁻¹` of `σ`. -/
theorem dihedralGroupThreeMulEquivPerm_sr_two :
    dihedralGroupThreeMulEquivPerm (.sr 2) =
      Equiv.swap 1 2 * Equiv.swap 0 1 * (Equiv.swap 1 2)⁻¹ := by
  rw [dihedralGroupThreeMulEquivPerm_sr]
  decide

end TauCeti
