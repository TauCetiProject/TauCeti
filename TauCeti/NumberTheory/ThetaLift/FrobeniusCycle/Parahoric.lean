/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Block.Triangular
public import TauCeti.NumberTheory.ThetaLift.FrobeniusCycle.Basic

/-!
# Letter matrices on the Levi and parahoric subgroups

For a Frobenius cycle and a labelling `τ : Fin k → α` of the indices, this file compares the
letter matrices `g_s` with the Levi subgroup `TauCeti.leviSubgroup τ W` and, for a linear order
`α`, the parahoric subgroup `TauCeti.parahoricSubgroup τ (maximalIdeal W)` of `τ`. For `g` in the
parahoric subgroup, `p` divides the entry `(i, j)` of `g_s` when `τ i < τ j` at an even letter
`s` and, since odd letters use the inverse transpose, when `τ j < τ i` at an odd letter `s`. For
`g` in the Levi subgroup, the entries of every `g_s` between indices of distinct labels vanish.

For a labelling `τ : Fin k → ℕ`, the Hopf-ideal subgroups `TauCeti.GeneralLinear.leviSubgroup W τ`
and `TauCeti.GeneralLinear.parahoricSubgroup W τ` have the same members as these
(`TauCeti.GeneralLinear.mem_leviSubgroup_iff`, `TauCeti.GeneralLinear.mem_parahoricSubgroup_iff`).

## Main results

* `TauCeti.FrobeniusCycle.p_dvd_letterMatrix_of_mem_parahoricSubgroup`: for `g` in the parahoric
  subgroup, `p` divides the entry `(i, j)` of `g_s` when `τ i < τ j` at an even letter `s` or
  `τ j < τ i` at an odd letter `s`.
* `TauCeti.FrobeniusCycle.letterMatrix_apply_eq_zero_of_mem_leviSubgroup`: vanishing of the
  entries between distinct labels for an element of the Levi subgroup.

## References

* The formal proof whose route this follows: the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207, file
  `New/UpperBound/ElementaryDivisors/TwistingData.lean`
  (`New.FrobeniusCycle.p_dvd_letterMatrix_of_mem_parahoric`).
-/

public section

open IsLocalRing

namespace TauCeti.FrobeniusCycle

variable {W : Type*} [CommRing W] [IsLocalRing W] {R : Type*} [CommRing R] {N : ℕ}
  (T : FrobeniusCycle W R N) {k : ℕ} {α : Type*}

/-- For `g` in the parahoric subgroup of `τ`, `p` divides the entry `(i, j)` of the letter matrix
`g_s` if `s` is even and `τ i < τ j`, or if `s` is odd and `τ j < τ i`. -/
theorem p_dvd_letterMatrix_of_mem_parahoricSubgroup [LinearOrder α] {τ : Fin k → α}
    {g : GL (Fin k) W} (hg : g ∈ parahoricSubgroup τ (maximalIdeal W)) {s : ZMod N}
    {i j : Fin k} (h : T.isEven s = true ∧ τ i < τ j ∨ T.isEven s = false ∧ τ j < τ i) :
    (T.p : R) ∣ T.letterMatrix s g i j := by
  rcases h with ⟨hs, h⟩ | ⟨hs, h⟩
  · rw [T.letterMatrix_of_isEven hs, Matrix.map_apply]
    exact T.dvd_ι_of_mem_maximalIdeal ((mem_parahoricSubgroup τ _).mp hg i j h) s
  · rw [T.letterMatrix_of_not_isEven hs, Matrix.map_apply, Matrix.transpose_apply]
    exact T.dvd_ι_of_mem_maximalIdeal
      ((mem_parahoricSubgroup τ _).mp ((parahoricSubgroup τ _).inv_mem hg) j i h) s

/-- For `g` in the Levi subgroup of `τ`, the entries of every letter matrix `g_s` between
indices of distinct labels vanish. -/
theorem letterMatrix_apply_eq_zero_of_mem_leviSubgroup {τ : Fin k → α} {g : GL (Fin k) W}
    (hg : g ∈ leviSubgroup τ W) (s : ZMod N) {i j : Fin k} (h : τ i ≠ τ j) :
    T.letterMatrix s g i j = 0 := by
  cases hs : T.isEven s
  · rw [T.letterMatrix_of_not_isEven hs, Matrix.map_apply, Matrix.transpose_apply,
      (mem_leviSubgroup τ).mp ((leviSubgroup τ W).inv_mem hg) j i h.symm, map_zero]
  · rw [T.letterMatrix_of_isEven hs, Matrix.map_apply, (mem_leviSubgroup τ).mp hg i j h,
      map_zero]

end TauCeti.FrobeniusCycle
