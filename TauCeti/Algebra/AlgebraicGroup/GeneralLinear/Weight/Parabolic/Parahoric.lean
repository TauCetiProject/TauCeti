/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Block.Triangular

/-!
# Parahoric subgroups of `GL_k` as preimages of weight parabolics

A labelling `τ : Fin k → ℕ` of the indices splits them into blocks. Over a local ring `W`, its
parahoric subgroup `TauCeti.parahoricSubgroup τ (maximalIdeal W)` consists of the matrices whose
entry `(i, j)` lies in the maximal ideal whenever the row label `τ i` is strictly smaller than the
column label `τ j`. This file identifies it with the preimage of the weight parabolic
`TauCeti.GeneralLinear.weightParabolicPoints` of `τ` over the residue field. It contains the Levi
subgroup `TauCeti.leviSubgroup τ W` (`TauCeti.leviSubgroup_le_parahoricSubgroup`).

The point of the construction: after reduction to the residue field, an element of the parahoric
subgroup preserves, for every threshold `t`, the span of the standard basis vectors `e b` with
`τ b ≥ t` (it maps `e j` into the span of the `e i` with `τ i ≥ τ j`). For the two-block
labelling `TauCeti.GeneralLinear.twoBlockLabel r` with `0 < r < k`, the span of the `e b` with
`b ≥ r` is the unique nonzero proper threshold subspace; for `r = 0` or `r ≥ k` there is none. In
the letter matrices of a Frobenius cycle
(`TauCeti.FrobeniusCycle.p_dvd_letterMatrix_of_mem_parahoricSubgroup`), the entries forced into
the maximal ideal give divisibility by `p` of the entry `(i, j)` when `τ i < τ j` at an even
letter, and, since odd letters use the inverse transpose, when `τ j < τ i` at an odd letter.

## Main results

* `TauCeti.GeneralLinear.comap_weightParabolicPoints_eq_parahoricSubgroup`: the preimage of the
  weight parabolic of `τ` over the residue field is the parahoric subgroup of `τ` for the maximal
  ideal.

## References

* The formal proof whose route the consumers of this file follow: the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207.
-/

public section

open IsLocalRing

namespace TauCeti.GeneralLinear

variable {W : Type*} [CommRing W] [IsLocalRing W] {k : ℕ}

/-- The preimage of the weight parabolic of `τ` over the residue field is the parahoric subgroup
of `τ` for the maximal ideal: the `g ∈ GL_k(W)` with `g i j` in the maximal ideal whenever
`τ i < τ j`. -/
theorem comap_weightParabolicPoints_eq_parahoricSubgroup (τ : Fin k → ℕ) :
    (weightParabolicPoints ℤ τ (ResidueField W)).comap
      (Matrix.GeneralLinearGroup.map (residue W)) = parahoricSubgroup τ (maximalIdeal W) := by
  ext g
  simp [Matrix.GeneralLinearGroup.map_apply, residue_eq_zero_iff]

end TauCeti.GeneralLinear
