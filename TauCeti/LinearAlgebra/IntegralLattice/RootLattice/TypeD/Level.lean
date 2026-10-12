/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Level

/-!
# Levels of the checkerboard lattices

For positive `n`, the checkerboard lattice `Dₙ` has level `8 / gcd(n, 4)`.
Thus its level is `8` in odd rank, `4` in rank congruent to `2` modulo `4`, and
`2` in rank divisible by `4`. For `n ≥ 4` this is the type D root lattice,
whose simple-root Gram matrix is identified in `TypeD.SimpleRoots`.

The four discriminant classes computed in `TypeD.Basic` have quadratic values
`0`, `1/2`, `n/8`, and `n/8`. The level must annihilate all four values, not
merely the discriminant group. This gives the least common multiple of their
reduced denominators using `IntegralLattice.IsEven.level_dvd_iff`.

## References

* W. Ebeling, *Lattices and Codes*, Chapters 1 and 3.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, §4.7.1.
-/

public section

namespace TauCeti
namespace IntegralLattice

/-- The level of a positive-rank checkerboard lattice is `8 / gcd(n, 4)`. -/
@[simp]
theorem level_checkerboardLattice (n : ℕ) [NeZero n] :
    (checkerboardLattice n).level = 8 / n.gcd 4 := by
  have hhalf (N : ℕ) :
      N • (((1 : ℚ) / 2 : ℚ) : AddCircle (1 : ℚ)) = 0 ↔ 2 ∣ N := by
    simpa [addOrderOf_dvd_iff_nsmul_eq_zero] using
      (congrArg (· ∣ N) (_root_.AddCircle.addOrderOf_coe_rat (p := (1 : ℚ)) (q := 1 / 2)))
  have hspin (N : ℕ) :
      N • (((n : ℚ) / 8 : ℚ) : AddCircle (1 : ℚ)) = 0 ↔ ((n : ℚ) / 8).den ∣ N := by
    simpa [addOrderOf_dvd_iff_nsmul_eq_zero] using
      (congrArg (· ∣ N) (_root_.AddCircle.addOrderOf_coe_rat (p := (1 : ℚ)) (q := n / 8)))
  have h (N : ℕ) : (checkerboardLattice n).level ∣ N ↔
      2 ∣ N ∧ ((n : ℚ) / 8).den ∣ N := by
    rw [← Int.natCast_dvd_natCast, (isEven_checkerboardLattice n).level_dvd_iff]
    simp only [natCast_zsmul]
    constructor
    · intro h
      exact ⟨(hhalf N).mp (by simpa using h (checkerboardVectorClass n)),
        (hspin N).mp (by simpa using h (checkerboardSpinorClass n))⟩
    · rintro ⟨hv, hs⟩ a
      rcases checkerboardDiscriminantGroup_eq_zero_or_vectorClass_or_spinorClass_or_cospinorClass
          a with rfl | rfl | rfl | rfl <;> simp_all
  have hlevel : (checkerboardLattice n).level = Nat.lcm 2 ((n : ℚ) / 8).den := by
    apply Nat.dvd_antisymm
    · exact (h _).mpr ⟨Nat.dvd_lcm_left .., Nat.dvd_lcm_right ..⟩
    · exact Nat.lcm_dvd ((h _).mp dvd_rfl).1 ((h _).mp dvd_rfl).2
  have hden : ((n : ℚ) / 8).den = 8 / n.gcd 8 := by
    simpa [Rat.divInt_eq_div, Int.gcd_def, Nat.gcd_comm] using
      _root_.Rat.den_divInt (n : ℤ) 8
  rw [hlevel, hden]
  calc
    -- Put both arguments in `8 / d` form for `Nat.div_lcm_eq_div_gcd`.
    Nat.lcm 2 (8 / n.gcd 8) = Nat.lcm (8 / 4) (8 / n.gcd 8) := by norm_num
    _ = 8 / Nat.gcd 4 (n.gcd 8) :=
      Nat.div_lcm_eq_div_gcd (by decide) (Nat.gcd_dvd_right ..)
    _ = 8 / n.gcd 4 := by
      congr 1
      rw [← Nat.gcd_assoc, Nat.gcd_comm 4 n, Nat.gcd_assoc]
      norm_num

/-- An odd-rank checkerboard lattice has level `8`. -/
theorem level_checkerboardLattice_of_odd {n : ℕ} (hn : Odd n) :
    (checkerboardLattice n).level = 8 := by
  have : NeZero n := ⟨by obtain ⟨k, hk⟩ := hn; omega⟩
  have hgcd : n.gcd 4 = 1 := by
    simpa using (Nat.coprime_two_right.mpr hn).pow_right 2
  rw [level_checkerboardLattice, hgcd, Nat.div_one]

/-- A checkerboard lattice of rank congruent to `2` modulo `4` has level `4`. -/
theorem level_checkerboardLattice_of_mod_four_eq_two {n : ℕ}
    (hn : n % 4 = 2) : (checkerboardLattice n).level = 4 := by
  have : NeZero n := ⟨by omega⟩
  have hgcd : n.gcd 4 = 2 := by
    rw [Nat.gcd_comm n 4, Nat.gcd_rec, hn]
    norm_num
  rw [level_checkerboardLattice, hgcd]

/-- A positive-rank checkerboard lattice with rank divisible by `4` has level `2`. -/
theorem level_checkerboardLattice_of_four_dvd {n : ℕ} [NeZero n] (hn : 4 ∣ n) :
    (checkerboardLattice n).level = 2 := by
  rw [level_checkerboardLattice, Nat.gcd_eq_right_iff_dvd.mpr hn]

end IntegralLattice
end TauCeti
