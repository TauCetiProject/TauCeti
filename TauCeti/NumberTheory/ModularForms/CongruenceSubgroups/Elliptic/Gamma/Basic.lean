/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Elliptic.Gamma.Zero

/-!
# The elliptic points of `Γ(N)`

The principal congruence subgroup `Γ(N)` is normal in `SL(2, ℤ)`, so a conjugate of `S` or of
`T⁻¹ S` lies in `Γ(N)` only if `S`, resp. `T⁻¹ S`, does. Both have lower-left entry `1`, which
is divisible by `N` only at level `1`
(`CongruenceSubgroup.dvd_apply_one_zero_of_conj_mem_Gamma`). Hence `Γ(N)` has no elliptic points
for `N ≠ 1`, while `Γ(1)` is all of `SL(2, ℤ)`, with one elliptic point of each order. These are
the counts `ε₂` and `ε₃` of the dimension formulas for `Γ(N)`.

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

/-- **The count `ε₂(Γ(N))`**: `Γ(N)` has one elliptic point of order two at level `1`, and none
at any other level. -/
theorem card_orderTwoElliptic_Gamma :
    Nat.card {q : orbitRel.Quotient ((Gamma N).map sl2zToPSL2R) ℍ //
      cardStabilizerOnOrbit q = 2} = if N = 1 then 1 else 0 := by
  split_ifs with hN
  · subst hN
    rw [Gamma_one_top, ← Gamma0_one_top, card_orderTwoElliptic_Gamma0, Nat.card_eq_fintype_card]
    decide
  · -- the lower-left entry of `S = !![0, -1; 1, 0]` is `1`
    refine (Gamma N).card_orderTwoElliptic_map_eq_zero fun _ h ↦ hN (Nat.dvd_one.mp ?_)
    exact_mod_cast (by simpa [coe_S] using dvd_apply_one_zero_of_conj_mem_Gamma h : (N : ℤ) ∣ 1)

/-- **The count `ε₃(Γ(N))`**: `Γ(N)` has one elliptic point of order three at level `1`, and none
at any other level. -/
theorem card_orderThreeElliptic_Gamma :
    Nat.card {q : orbitRel.Quotient ((Gamma N).map sl2zToPSL2R) ℍ //
      cardStabilizerOnOrbit q = 3} = if N = 1 then 1 else 0 := by
  split_ifs with hN
  · subst hN
    rw [Gamma_one_top, ← Gamma0_one_top, card_orderThreeElliptic_Gamma0, Nat.card_eq_fintype_card]
    decide
  · -- the lower-left entry of `T⁻¹ S = !![-1, -1; 1, 0]` is `1`
    refine (Gamma N).card_orderThreeElliptic_map_eq_zero fun _ h ↦ hN (Nat.dvd_one.mp ?_)
    exact_mod_cast (by simpa [coe_mul, coe_T_inv, coe_S, Matrix.mul_fin_two] using
      dvd_apply_one_zero_of_conj_mem_Gamma h : (N : ℤ) ∣ 1)

end TauCeti
