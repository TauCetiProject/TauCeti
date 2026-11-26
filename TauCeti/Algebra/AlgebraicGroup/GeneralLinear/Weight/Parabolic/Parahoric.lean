/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Levi.Basic

/-!
# Parahoric subgroups of `GL_k` attached to a labelling

A labelling `τ : Fin k → ℕ` of the indices splits them into blocks. Over a local ring `W`, its
parahoric subgroup is the preimage of the weight parabolic
`TauCeti.GeneralLinear.weightParabolicPoints` of `τ` over the residue field: the matrices whose
entry `(i, j)` lies in the maximal ideal whenever the row label `τ i` is strictly smaller than
the column label `τ j`. It contains the Levi subgroup `TauCeti.GeneralLinear.leviSubgroup` of `τ`.

The point of the construction: after reduction to the residue field, an element of the parahoric
subgroup preserves, for every threshold `t`, the span of the standard basis vectors `e b` with
`τ b ≥ t` (it maps `e j` into the span of the `e i` with `τ i ≥ τ j`). For the two-block
labelling `TauCeti.GeneralLinear.twoBlockLabel r` with `0 < r < k`, the span of the `e b` with
`b ≥ r` is the unique nonzero proper threshold subspace; for `r = 0` or `r ≥ k` there is none. In
the letter matrices of a Frobenius cycle
(`TauCeti.FrobeniusCycle.p_dvd_letterMatrix_of_mem_parahoricSubgroup`), the entries forced into
the maximal ideal give divisibility by `p` of the entry `(i, j)` when `τ i < τ j` at an even
letter, and, since odd letters use the inverse transpose, when `τ j < τ i` at an odd letter.

## Main definitions

* `TauCeti.GeneralLinear.parahoricSubgroup`: the block-triangular modulo the maximal ideal
  subgroup of a labelling.

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

/-- The parahoric subgroup is the preimage of the weight parabolic of `τ` over the residue
field. -/
theorem parahoricSubgroup_def (τ : Fin k → ℕ) :
    parahoricSubgroup W τ = (weightParabolicPoints ℤ τ (ResidueField W)).comap
      (Matrix.GeneralLinearGroup.map (residue W)) := (rfl)

/-- Membership in the parahoric subgroup: the entry `(i, j)` lies in the maximal ideal whenever
the row label `τ i` is strictly smaller than the column label `τ j`. -/
@[simp]
theorem mem_parahoricSubgroup_iff (τ : Fin k → ℕ) (g : GL (Fin k) W) :
    g ∈ parahoricSubgroup W τ ↔
      ∀ i j, τ i < τ j → (g : Matrix (Fin k) (Fin k) W) i j ∈ maximalIdeal W := by
  simp [parahoricSubgroup_def, Matrix.GeneralLinearGroup.map_apply, residue_eq_zero_iff]

/-- For a constant labelling, the parahoric subgroup is all of `GL_k(W)`. -/
@[simp]
theorem parahoricSubgroup_const (c : ℕ) : parahoricSubgroup W (k := k) (fun _ ↦ c) = ⊤ :=
  eq_top_iff.mpr fun g _ ↦ (mem_parahoricSubgroup_iff _ g).mpr fun _ _ h ↦ (lt_irrefl _ h).elim

/-- The Levi subgroup of a labelling lies in its parahoric subgroup. -/
theorem leviSubgroup_le_parahoricSubgroup (τ : Fin k → ℕ) :
    leviSubgroup W τ ≤ parahoricSubgroup W τ := fun g hg ↦
  (mem_parahoricSubgroup_iff τ g).mpr fun i j h ↦ by
    rw [(mem_leviSubgroup_iff τ g).mp hg i j h.ne]
    exact zero_mem _

end TauCeti.GeneralLinear
