/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Elliptic.Gamma0

/-!
# The elliptic points of `Γ(N)`

The principal congruence subgroup `Γ(N)` is normal in `SL(2, ℤ)`, so a conjugate of `S` or of
`T⁻¹ S` lies in `Γ(N)` only if `S`, resp. `T⁻¹ S`, does. Both have lower-left entry `1`, so this
happens only at level `1`. Hence `Γ(N)` has no elliptic points for `N ≠ 1`, while `Γ(1)` is all of
`SL(2, ℤ)`, with one elliptic point of each order. These are the counts `ε₂` and `ε₃` of the
dimension formulas for `Γ(N)`.

## Main results

* `card_orderTwoElliptic_Gamma`, `card_orderThreeElliptic_Gamma`: the counts `ε₂(Γ(N))` and
  `ε₃(Γ(N))` are `1` at level `1` and `0` at every other level.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §3.9.
-/

public section

open Matrix.SpecialLinearGroup MulAction UpperHalfPlane CongruenceSubgroup ModularGroup
open scoped MatrixGroups

namespace TauCeti

variable {N : ℕ}

/-- A conjugate of a matrix with lower-left entry `1` lies in `Γ(N)` only at level `1`: as `Γ(N)`
is normal, the matrix itself would lie in `Γ(N)`, making `1` zero modulo `N`. -/
private theorem eq_one_of_conj_mem_Gamma {γ g : SL(2, ℤ)} (h : γ * g * γ⁻¹ ∈ Gamma N)
    (h10 : g 1 0 = 1) : N = 1 := by
  have hg : g ∈ Gamma N := by simpa [mul_assoc] using (Gamma_normal N).conj_mem _ h γ⁻¹
  by_contra hN
  have : Nontrivial (ZMod N) := ZMod.nontrivial_iff.mpr hN
  simpa [h10] using (Gamma_mem.mp hg).2.2.1

/-- **The count `ε₂(Γ(N))`**: `Γ(N)` has one elliptic point of order two at level `1`, and none
at any other level. -/
theorem card_orderTwoElliptic_Gamma :
    Nat.card {q : orbitRel.Quotient ((Gamma N).map sl2zToPSL2R) ℍ //
      cardStabilizerOnOrbit q = 2} = if N = 1 then 1 else 0 := by
  split_ifs with hN
  · subst hN
    rw [Gamma_one_top, ← Gamma0_one_top, card_orderTwoElliptic_Gamma0, Nat.card_eq_fintype_card]
    decide
  · exact (Gamma N).card_orderTwoElliptic_map_eq_zero fun _ h ↦
      hN (eq_one_of_conj_mem_Gamma h (by decide))

/-- **The count `ε₃(Γ(N))`**: `Γ(N)` has one elliptic point of order three at level `1`, and none
at any other level. -/
theorem card_orderThreeElliptic_Gamma :
    Nat.card {q : orbitRel.Quotient ((Gamma N).map sl2zToPSL2R) ℍ //
      cardStabilizerOnOrbit q = 3} = if N = 1 then 1 else 0 := by
  split_ifs with hN
  · subst hN
    rw [Gamma_one_top, ← Gamma0_one_top, card_orderThreeElliptic_Gamma0, Nat.card_eq_fintype_card]
    decide
  · exact (Gamma N).card_orderThreeElliptic_map_eq_zero fun _ h ↦
      hN (eq_one_of_conj_mem_Gamma h (by decide))

end TauCeti
