/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Braid.Basic
import Mathlib.GroupTheory.NoncommCoprod

/-!
# Braid inclusions on blocks of strands

`BraidGroup.appendHom m n` and `BraidGroup.shiftHom m n` place braids on the first `m` and last
`n` strands of `m + n` strands, respectively. These homomorphisms extend `BraidGroup.castAdd`
and `BraidGroup.natAdd` to include the empty blocks. The two images commute, giving
`BraidGroup.blockSum m n` on pairs of braids.
-/

public section

namespace TauCeti.BraidGroup

/-- Place a braid on the last `n` strands, adding `m` uncrossed strands before it. -/
def shiftHom (m : ℕ) : (n : ℕ) → BraidGroup n →* BraidGroup (m + n)
  | 0 => 1
  | _ + 1 => natAdd m

/-- On nonempty blocks the inclusion is the existing `natAdd`. -/
theorem shiftHom_succ (m n : ℕ) : shiftHom m (n + 1) = natAdd m := (rfl)

/-- The empty braid has trivial image. -/
@[simp]
theorem shiftHom_zero (m : ℕ) (b : BraidGroup 0) : shiftHom m 0 b = 1 := (rfl)

/-- A crossing in the right block is shifted by the length of the left block. -/
@[simp]
theorem shiftHom_sigma (m n : ℕ) (i : Fin (n - 1)) :
    shiftHom m n (sigma i) = sigma ⟨m + i, by have := i.isLt; omega⟩ := by
  cases n with
  | zero => exact i.elim0
  | succ n => rw [shiftHom_succ, natAdd_sigma]; rfl

/-- Transport along an equality of strand counts sends each generator to the same crossing. -/
theorem cast_sigma {n k : ℕ} (h : n = k) (i : Fin (n - 1)) :
    MulEquiv.cast (M := BraidGroup) h (sigma i) =
      sigma (Fin.cast (congrArg (· - 1) h) i) := by
  subst k
  simp [MulEquiv.cast_apply]

/-- Adding no strands gives the identity homomorphism after identifying the strand counts. -/
theorem shiftHom_zero_left (n : ℕ) :
    shiftHom 0 n = (MulEquiv.cast (M := BraidGroup) (Nat.zero_add n).symm).toMonoidHom := by
  apply hom_ext
  intro i
  rw [shiftHom_sigma, MulEquiv.coe_toMonoidHom, cast_sigma]
  congr 1
  apply Fin.ext
  simp

/-- Place a braid on the first `m` strands, adding `n` uncrossed strands after it. -/
def appendHom : (m n : ℕ) → BraidGroup m →* BraidGroup (m + n)
  | 0, _ => 1
  | m + 1, n =>
    (MulEquiv.cast (M := BraidGroup) (by omega : m + n + 1 = m + 1 + n)).toMonoidHom.comp
      (castAdd n)

/-- On a nonempty first block, this is `castAdd` with the target strand count reindexed. -/
theorem appendHom_succ (m n : ℕ) :
    appendHom (m + 1) n =
      (MulEquiv.cast (M := BraidGroup) (by omega : m + n + 1 = m + 1 + n)).toMonoidHom.comp
        (castAdd n) :=
  (rfl)

/-- The empty first braid has trivial image. -/
@[simp]
theorem appendHom_zero (n : ℕ) (b : BraidGroup 0) : appendHom 0 n b = 1 := (rfl)

/-- A crossing in the first block keeps its index. -/
@[simp]
theorem appendHom_sigma (m n : ℕ) (i : Fin (m - 1)) :
    appendHom m n (sigma i) = sigma ⟨i, by have := i.isLt; omega⟩ := by
  cases m with
  | zero => exact i.elim0
  | succ m =>
    rw [appendHom_succ, MonoidHom.comp_apply, castAdd_sigma, MulEquiv.coe_toMonoidHom, cast_sigma]
    rfl

/-- Adding no strands after a braid leaves it unchanged. -/
@[simp]
theorem appendHom_zero_right (m : ℕ) : appendHom m 0 = MonoidHom.id (BraidGroup m) := by
  apply hom_ext
  intro i
  rw [appendHom_sigma, MonoidHom.id_apply]
  rfl

/-- Braids supported on the two disjoint blocks commute. -/
theorem commute_appendHom_shiftHom {m n : ℕ} (a : BraidGroup m) (b : BraidGroup n) :
    Commute (appendHom m n a) (shiftHom m n b) := by
  induction a using sigma_induction_on with
  | one => rw [map_one]; exact Commute.one_left _
  | mul a a' ha ha' => rw [map_mul]; exact ha.mul_left ha'
  | inv a ha => rw [map_inv]; exact ha.inv_left
  | sigma i =>
    induction b using sigma_induction_on with
    | one => rw [map_one]; exact Commute.one_right _
    | mul b b' hb hb' => rw [map_mul]; exact hb.mul_right hb'
    | inv b hb => rw [map_inv]; exact hb.inv_right
    | sigma j =>
      rw [appendHom_sigma, shiftHom_sigma]
      refine sigma_mul_sigma_comm (Or.inl ?_)
      simp only
      have := i.isLt
      omega

/-- Place two braids side by side on the first `m` and last `n` strands. -/
def blockSum (m n : ℕ) : BraidGroup m × BraidGroup n →* BraidGroup (m + n) :=
  (appendHom m n).noncommCoprod (shiftHom m n) commute_appendHom_shiftHom

/-- The side-by-side braid is the product of the two block images. -/
theorem blockSum_apply {m n : ℕ} (a : BraidGroup m) (b : BraidGroup n) :
    blockSum m n (a, b) = appendHom m n a * shiftHom m n b :=
  (rfl)

/-- A side-by-side braid with an empty first block is the braid in its second block. -/
@[simp]
theorem blockSum_zero_left {n : ℕ} (a : BraidGroup 0) (b : BraidGroup n) :
    blockSum 0 n (a, b) = shiftHom 0 n b := by
  rw [blockSum_apply, appendHom_zero, one_mul]

/-- A side-by-side braid with an empty second block is the braid in its first block. -/
@[simp]
theorem blockSum_zero_right {m : ℕ} (a : BraidGroup m) (b : BraidGroup 0) :
    blockSum m 0 (a, b) = a := by
  rw [blockSum_apply, shiftHom_zero, appendHom_zero_right, MonoidHom.id_apply, mul_one]

end TauCeti.BraidGroup
