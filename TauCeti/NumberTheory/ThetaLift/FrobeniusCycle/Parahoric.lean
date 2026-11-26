/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.Parahoric
public import TauCeti.NumberTheory.ThetaLift.FrobeniusCycle.Basic

/-!
# Letter matrices on the Levi and parahoric subgroups

For a Frobenius cycle and a labelling `τ` of the indices, this file compares the letter matrices
`g_s` with the Levi subgroup `TauCeti.GeneralLinear.leviSubgroup` and the parahoric subgroup
`TauCeti.GeneralLinear.parahoricSubgroup` of `τ`. For `g` in the parahoric subgroup, `p` divides
the entry `(i, j)` of `g_s` when `τ i < τ j` at an even letter `s` and, since odd letters use the
inverse transpose, when `τ j < τ i` at an odd letter `s`. For `g` in the Levi subgroup, the entries
of every `g_s` between indices of distinct labels vanish.

## Main results

* `TauCeti.FrobeniusCycle.p_dvd_letterMatrix_of_mem_parahoricSubgroup`: divisibility by `p` of the
  letter matrices of an element of the parahoric subgroup.
* `TauCeti.FrobeniusCycle.letterMatrix_apply_eq_zero_of_mem_leviSubgroup`: vanishing of the
  entries between distinct labels for an element of the Levi subgroup.

## References

* The formal proof whose route this follows: the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207, file
  `New/UpperBound/ElementaryDivisors/TwistingData.lean`
  (`New.FrobeniusCycle.p_dvd_letterMatrix_of_mem_parahoric`).
-/

public section

open IsLocalRing TauCeti.GeneralLinear

namespace TauCeti.FrobeniusCycle

variable {W : Type*} [CommRing W] [IsLocalRing W] {R : Type*} [CommRing R] {N : ℕ}
  (T : FrobeniusCycle W R N) {k : ℕ}

/-- For `g` in the parahoric subgroup of `τ`, `p` divides the entry `(i, j)` of the letter matrix
`g_s` if `s` is even and `τ i < τ j`, or if `s` is odd and `τ j < τ i`. -/
theorem p_dvd_letterMatrix_of_mem_parahoricSubgroup {τ : Fin k → ℕ} {g : GL (Fin k) W}
    (hg : g ∈ parahoricSubgroup W τ) {s : ZMod N} {i j : Fin k}
    (h : T.isEven s = true ∧ τ i < τ j ∨ T.isEven s = false ∧ τ j < τ i) :
    (T.p : R) ∣ T.letterMatrix s g i j := by
  rcases h with ⟨hs, h⟩ | ⟨hs, h⟩
  · rw [T.letterMatrix_of_isEven hs, Matrix.map_apply]
    exact T.dvd_ι_of_mem_maximalIdeal ((mem_parahoricSubgroup_iff τ g).mp hg i j h) s
  · rw [T.letterMatrix_of_not_isEven hs, Matrix.map_apply, Matrix.transpose_apply]
    exact T.dvd_ι_of_mem_maximalIdeal
      ((mem_parahoricSubgroup_iff τ _).mp ((parahoricSubgroup W τ).inv_mem hg) j i h) s

/-- For `g` in the Levi subgroup of `τ`, the entries of every letter matrix `g_s` between
indices of distinct labels vanish. -/
theorem letterMatrix_apply_eq_zero_of_mem_leviSubgroup {τ : Fin k → ℕ} {g : GL (Fin k) W}
    (hg : g ∈ leviSubgroup W τ) (s : ZMod N) {i j : Fin k} (h : τ i ≠ τ j) :
    T.letterMatrix s g i j = 0 := by
  cases hs : T.isEven s
  · rw [T.letterMatrix_of_not_isEven hs, Matrix.map_apply, Matrix.transpose_apply,
      (mem_leviSubgroup_iff τ _).mp ((leviSubgroup W τ).inv_mem hg) j i h.symm, map_zero]
  · rw [T.letterMatrix_of_isEven hs, Matrix.map_apply, (mem_leviSubgroup_iff τ g).mp hg i j h,
      map_zero]

end TauCeti.FrobeniusCycle
