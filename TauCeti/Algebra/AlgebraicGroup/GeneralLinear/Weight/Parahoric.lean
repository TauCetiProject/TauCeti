/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Levi.Basic

/-!
# Parahoric subgroups of `GL_k` attached to a labelling

A labelling `τ : Fin k → ℕ` of the indices splits them into blocks. Over a local ring `W`, its
parahoric subgroup is the preimage of the weight parabolic
`TauCeti.GeneralLinear.weightParabolicPoints` of `τ` over the residue field: the matrices whose
entries from a smaller to a larger label lie in the maximal ideal. It contains the Levi subgroup
`TauCeti.GeneralLinear.leviSubgroup` of `τ`. The labelling `twoBlockLabel r` splits the indices
into those below `r` and the others.

## Main definitions

* `TauCeti.GeneralLinear.parahoricSubgroup`: the block-triangular modulo the maximal ideal
  subgroup of a labelling.
* `TauCeti.GeneralLinear.twoBlockLabel`: the labelling of a split into two blocks.

## Main results

* `TauCeti.GeneralLinear.mem_parahoricSubgroup_iff`: membership in terms of entries.
* `TauCeti.GeneralLinear.leviSubgroup_le_parahoricSubgroup`: the Levi subgroup lies in the
  parahoric subgroup.

## References

* The formal proof whose route the consumers of this file follow: the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207.
-/

public section

open IsLocalRing

namespace TauCeti.GeneralLinear

variable (W : Type*) [CommRing W] [IsLocalRing W] {k : ℕ}

/-- The parahoric subgroup `P_τ(W)` of a labelling `τ` of the indices: the `g ∈ GL_k(W)` with
`g i j` in the maximal ideal whenever `τ i < τ j`, that is, the preimage of the weight parabolic
of `τ` over the residue field (`mem_parahoricSubgroup_iff`). -/
noncomputable def parahoricSubgroup (τ : Fin k → ℕ) : Subgroup (GL (Fin k) W) :=
  (weightParabolicPoints ℤ τ (ResidueField W)).comap
    (Matrix.GeneralLinearGroup.map (residue W))

variable {W}

/-- Membership in the parahoric subgroup: the entries from a smaller to a larger label lie in
the maximal ideal. -/
@[simp]
theorem mem_parahoricSubgroup_iff (τ : Fin k → ℕ) (g : GL (Fin k) W) :
    g ∈ parahoricSubgroup W τ ↔
      ∀ i j, τ i < τ j → (g : Matrix (Fin k) (Fin k) W) i j ∈ maximalIdeal W := by
  simp [parahoricSubgroup, Matrix.GeneralLinearGroup.map_apply, residue_eq_zero_iff]

/-- The Levi subgroup of a labelling lies in its parahoric subgroup. -/
theorem leviSubgroup_le_parahoricSubgroup (τ : Fin k → ℕ) :
    leviSubgroup W τ ≤ parahoricSubgroup W τ := fun g hg ↦
  (mem_parahoricSubgroup_iff τ g).mpr fun i j h ↦ by
    rw [(mem_leviSubgroup_iff τ g).mp hg i j h.ne]
    exact zero_mem _

/-- The labelling `τ_r`: `0` on the indices `b < r` and `1` on the others. -/
def twoBlockLabel (r : ℕ) (b : Fin k) : ℕ := if (b : ℕ) < r then 0 else 1

/-- `τ_r` is `0` on the indices below `r`. -/
@[simp]
theorem twoBlockLabel_of_lt {r : ℕ} {b : Fin k} (h : (b : ℕ) < r) : twoBlockLabel r b = 0 := by
  simp [twoBlockLabel, h]

/-- `τ_r` is `1` on the indices from `r` on. -/
@[simp]
theorem twoBlockLabel_of_le {r : ℕ} {b : Fin k} (h : r ≤ (b : ℕ)) : twoBlockLabel r b = 1 := by
  simp [twoBlockLabel, Nat.not_lt.mpr h]

/-- `τ_r` vanishes exactly on the indices below `r`. -/
@[simp]
theorem twoBlockLabel_eq_zero_iff (r : ℕ) (b : Fin k) : twoBlockLabel r b = 0 ↔ (b : ℕ) < r := by
  simp [twoBlockLabel]

/-- `τ_r` takes the larger value exactly on the indices from `r` on. -/
@[simp]
theorem twoBlockLabel_lt_iff (r : ℕ) (b b' : Fin k) :
    twoBlockLabel r b < twoBlockLabel r b' ↔ (b : ℕ) < r ∧ r ≤ (b' : ℕ) := by
  unfold twoBlockLabel
  split_ifs <;> simp_all

end TauCeti.GeneralLinear
