/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Rat.NumDenDvd
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeA.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Level

/-!
# Levels of the type A root lattices

The level of `Aₙ` is `2 (n + 1) / gcd(n, 2)`: it is `n + 1` for even `n` and
`2 (n + 1)` for odd `n`. The formula includes the rank-zero lattice, of level one.
These are levels of the even bilinear lattices, so they annihilate the half-norm
discriminant quadratic form, not merely its polar pairing.

The calculation uses `IntegralLattice.IsEven.level_eq_addOrderOf` and the first
fundamental weight's quadratic value computed in `TypeA.Basic`.

## References

* W. Ebeling, *Lattices and Codes*, Chapters 1 and 3.
-/

public section

namespace TauCeti
namespace IntegralLattice

/-- The level of `Aₙ` is `2 (n + 1) / gcd(n, 2)`, including `A₀`. -/
@[simp]
theorem level_typeARootLattice (n : ℕ) :
    (typeARootLattice n).level = 2 * (n + 1) / n.gcd 2 := by
  rw [(isEven_typeARootLattice n).level_eq_addOrderOf _
    (zmultiples_typeAFundamentalWeightClass n),
    discriminantQuadraticMap_typeAFundamentalWeightClass]
  rw [AddCircle.addOrderOf_coe_rat_one]
  have hgcd : n.gcd (2 * (n + 1)) = n.gcd 2 := by
    rw [Nat.mul_add, Nat.mul_one, Nat.add_comm (2 * n) 2, Nat.gcd_comm n (2 + 2 * n),
      Nat.gcd_add_mul_right_left, Nat.gcd_comm 2 n]
  have hden : (n : ℚ) / (2 * ((n : ℚ) + 1)) = (n : ℚ) / (2 * (n + 1) : ℕ) := by
    norm_cast
  rw [hden, Rat.den_natCast_div_natCast n (2 * (n + 1)) (by omega), hgcd]

/-- In even rank, the level of `Aₙ` is `n + 1`, including rank zero. -/
theorem level_typeARootLattice_of_even {n : ℕ} (hn : Even n) :
    (typeARootLattice n).level = n + 1 := by
  rw [level_typeARootLattice, Nat.gcd_eq_right_iff_dvd.mpr (even_iff_two_dvd.mp hn)]
  exact Nat.mul_div_cancel_left _ (by decide)

/-- In odd rank, the level of `Aₙ` is `2 (n + 1)`. -/
theorem level_typeARootLattice_of_odd {n : ℕ} (hn : Odd n) :
    (typeARootLattice n).level = 2 * (n + 1) := by
  rw [level_typeARootLattice, (Nat.coprime_two_right.mpr hn).gcd_eq_one, Nat.div_one]

end IntegralLattice
end TauCeti
