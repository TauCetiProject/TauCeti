/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Block-diagonal embeddings of unitary groups of general forms

For matrices `J : Matrix n n R` and `J' : Matrix m m R` over a commutative ring with involution,
`TauCeti.unitaryGroupOfBlockSum J J'` embeds `unitaryGroupOf J × unitaryGroupOf J'` as the
block-diagonal matrices `diag(a, b)` in `unitaryGroupOf (fromBlocks J 0 0 J')`. When `J'` is
invertible, an element `g` of `unitaryGroupOf (fromBlocks J 0 0 J')` has the form `diag(a, 1)`
if and only if its second block of columns is that of the identity matrix
(`TauCeti.mem_range_unitaryGroupOfBlockSum_left_iff`), and symmetrically when `J` is invertible
(`TauCeti.mem_range_unitaryGroupOfBlockSum_right_iff`).

## Main definitions

* `TauCeti.unitaryGroupOfBlockSum`: the group homomorphism `(a, b) ↦ diag(a, b)` from
  `unitaryGroupOf J × unitaryGroupOf J'` to `unitaryGroupOf (fromBlocks J 0 0 J')`.

## Main results

* `TauCeti.val_unitaryGroupOfBlockSum`: the underlying matrix of `unitaryGroupOfBlockSum`.
* `TauCeti.unitaryGroupOfBlockSum_injective`: `unitaryGroupOfBlockSum` is injective.
* `TauCeti.mem_range_unitaryGroupOfBlockSum_left_iff`: characterization of `diag(a, 1)` when `J'`
  is invertible.
* `TauCeti.mem_range_unitaryGroupOfBlockSum_right_iff`: characterization of `diag(1, b)` when `J`
  is invertible.

## References

* Adapted from `grh-lean` (<https://github.com/lsernau/grh-lean>, commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0),
  `src/Lib/Adelic/Unitary/ComponentsAndBlockSums.lean` (`New.U.sum`) and
  `src/Lib/Adelic/Unitary/RationalPoints.lean` (`New.U.mem_range_sum_left`,
  `New.U.mem_range_sum_right`).
-/

public section

open Matrix

namespace TauCeti

variable {R : Type*} [CommRing R] [StarRing R]
  {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The block-diagonal embedding `(a, b) ↦ diag(a, b)` of `unitaryGroupOf J × unitaryGroupOf J'`
into `unitaryGroupOf (fromBlocks J 0 0 J')`. -/
def unitaryGroupOfBlockSum (J : Matrix n n R) (J' : Matrix m m R) :
    unitaryGroupOf J × unitaryGroupOf J' →* unitaryGroupOf (fromBlocks J 0 0 J') where
  toFun x :=
    ⟨{ val := fromBlocks (x.fst : GL n R).val 0 0 (x.snd : GL m R).val
       inv := fromBlocks (x.fst : GL n R).inv 0 0 (x.snd : GL m R).inv
       val_inv := by simp [fromBlocks_multiply]
       inv_val := by simp [fromBlocks_multiply] },
      Matrix.mem_unitaryGroupOf_iff.mpr <| by
        have h1 := Matrix.mem_unitaryGroupOf_iff.mp x.fst.property
        have h2 := Matrix.mem_unitaryGroupOf_iff.mp x.snd.property
        simp only [Matrix.star_eq_conjTranspose] at h1 h2 ⊢
        simp [fromBlocks_conjTranspose, fromBlocks_multiply, h1, h2]⟩
  map_one' := Subtype.ext <| Units.ext <| by simp [fromBlocks_one]
  map_mul' x y := Subtype.ext <| Units.ext <| by simp [fromBlocks_multiply]

/-- The underlying matrix of `unitaryGroupOfBlockSum J J' (a, b)` is `fromBlocks a 0 0 b`. -/
@[simp]
theorem val_unitaryGroupOfBlockSum (J : Matrix n n R) (J' : Matrix m m R)
    (x : unitaryGroupOf J × unitaryGroupOf J') :
    ((unitaryGroupOfBlockSum J J' x : GL (n ⊕ m) R) : Matrix (n ⊕ m) (n ⊕ m) R) =
      fromBlocks ((x.fst : GL n R) : Matrix n n R) 0 0 ((x.snd : GL m R) : Matrix m m R) := by
  rfl

/-- `unitaryGroupOfBlockSum J J'` is injective. -/
theorem unitaryGroupOfBlockSum_injective (J : Matrix n n R) (J' : Matrix m m R) :
    Function.Injective (unitaryGroupOfBlockSum J J') := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  have hmat := congrArg (fun g : unitaryGroupOf (fromBlocks J 0 0 J') ↦
    ((g : GL (n ⊕ m) R) : Matrix (n ⊕ m) (n ⊕ m) R)) h
  simp only [val_unitaryGroupOfBlockSum, fromBlocks_inj] at hmat
  exact Prod.ext (Subtype.ext (Units.ext hmat.left))
    (Subtype.ext (Units.ext hmat.right.right.right))

/-- When `J'` is invertible, an element `g ∈ unitaryGroupOf (fromBlocks J 0 0 J')` is of the form
`diag(a, 1)` for some `a ∈ unitaryGroupOf J` iff its second block of columns is `(0; 1)`. -/
theorem mem_range_unitaryGroupOfBlockSum_left_iff {J : Matrix n n R} {J' : Matrix m m R}
    (hJ' : IsUnit J') (g : unitaryGroupOf (fromBlocks J 0 0 J')) :
    (∃ a : unitaryGroupOf J, unitaryGroupOfBlockSum J J' (a, 1) = g) ↔
      ((g : GL (n ⊕ m) R) : Matrix (n ⊕ m) (n ⊕ m) R).toCols₂ = fromRows 0 1 := by
  refine ⟨?_, fun hcols ↦ ?_⟩
  · rintro ⟨a, rfl⟩
    simp [← fromCols_fromRows_eq_fromBlocks]
  obtain ⟨A, B, C, D, hg⟩ : ∃ A B C D,
      ((g : GL (n ⊕ m) R) : Matrix (n ⊕ m) (n ⊕ m) R) = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks _).symm⟩
  obtain ⟨rfl, rfl⟩ : B = 0 ∧ D = 1 := by
    simpa [hg, ← fromCols_fromRows_eq_fromBlocks, fromRows_ext_iff] using hcols
  obtain ⟨hA, -, hC⟩ : Aᴴ * J * A + Cᴴ * J' * C = J ∧ Cᴴ * J' = 0 ∧ J' * C = 0 := by
    simpa [hg, fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroupOf_iff.mp g.property
  have hC0 : C = 0 := by
    rw [← nonsing_inv_mul_cancel_left J' C ((isUnit_iff_isUnit_det _).mp hJ'), hC, Matrix.mul_zero]
  subst hC0
  have hA_unit : IsUnit A := by
    have hg_det : IsUnit ((fromBlocks A 0 0 (1 : Matrix m m R)).det) := by
      rw [← hg]
      exact (isUnit_iff_isUnit_det _).mp g.val.isUnit
    rw [det_fromBlocks_zero₁₂, det_one, mul_one] at hg_det
    exact (isUnit_iff_isUnit_det A).mpr hg_det
  refine ⟨⟨hA_unit.unit, Matrix.mem_unitaryGroupOf_iff.mpr ?_⟩, Subtype.ext (Units.ext ?_)⟩
  · simpa [Matrix.star_eq_conjTranspose] using hA
  · simp [hg]

/-- When `J` is invertible, an element `g ∈ unitaryGroupOf (fromBlocks J 0 0 J')` is of the form
`diag(1, b)` for some `b ∈ unitaryGroupOf J'` iff its first block of columns is `(1; 0)`. -/
theorem mem_range_unitaryGroupOfBlockSum_right_iff {J : Matrix n n R} {J' : Matrix m m R}
    (hJ : IsUnit J) (g : unitaryGroupOf (fromBlocks J 0 0 J')) :
    (∃ b : unitaryGroupOf J', unitaryGroupOfBlockSum J J' (1, b) = g) ↔
      ((g : GL (n ⊕ m) R) : Matrix (n ⊕ m) (n ⊕ m) R).toCols₁ = fromRows 1 0 := by
  refine ⟨?_, fun hcols ↦ ?_⟩
  · rintro ⟨b, rfl⟩
    simp [← fromCols_fromRows_eq_fromBlocks]
  obtain ⟨A, B, C, D, hg⟩ : ∃ A B C D,
      ((g : GL (n ⊕ m) R) : Matrix (n ⊕ m) (n ⊕ m) R) = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks _).symm⟩
  obtain ⟨rfl, rfl⟩ : A = 1 ∧ C = 0 := by
    simpa [hg, ← fromCols_fromRows_eq_fromBlocks, fromRows_ext_iff] using hcols
  obtain ⟨hB, -, hD⟩ : J * B = 0 ∧ Bᴴ * J = 0 ∧ Bᴴ * J * B + Dᴴ * J' * D = J' := by
    simpa [hg, fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroupOf_iff.mp g.property
  have hB0 : B = 0 := by
    rw [← nonsing_inv_mul_cancel_left J B ((isUnit_iff_isUnit_det _).mp hJ), hB, Matrix.mul_zero]
  subst hB0
  have hD_unit : IsUnit D := by
    have hg_det : IsUnit ((fromBlocks (1 : Matrix n n R) 0 0 D).det) := by
      rw [← hg]
      exact (isUnit_iff_isUnit_det _).mp g.val.isUnit
    rw [det_fromBlocks_zero₁₂, det_one, one_mul] at hg_det
    exact (isUnit_iff_isUnit_det D).mpr hg_det
  refine ⟨⟨hD_unit.unit, Matrix.mem_unitaryGroupOf_iff.mpr ?_⟩, Subtype.ext (Units.ext ?_)⟩
  · simpa [Matrix.star_eq_conjTranspose] using hD
  · simp [hg]

end TauCeti
