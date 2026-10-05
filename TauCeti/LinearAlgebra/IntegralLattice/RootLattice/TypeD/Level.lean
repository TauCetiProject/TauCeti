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
  have hhalf : addOrderOf (((1 : ℚ) / 2 : ℚ) : AddCircle (1 : ℚ)) = 2 := by
    convert AddCircle.addOrderOf_coe_rat (p := (1 : ℚ)) (q := (1 : ℚ) / 2) using 1 <;>
      norm_num
  have hspin : addOrderOf (((n : ℚ) / 8 : ℚ) : AddCircle (1 : ℚ)) = ((n : ℚ) / 8).den := by
    simpa using AddCircle.addOrderOf_coe_rat (p := (1 : ℚ)) (q := (n : ℚ) / 8)
  have h (N : ℕ) : (checkerboardLattice n).level ∣ N ↔
      2 ∣ N ∧ ((n : ℚ) / 8).den ∣ N := by
    rw [← Int.natCast_dvd_natCast, (isEven_checkerboardLattice n).level_dvd_iff]
    simp only [natCast_zsmul]
    rw [← hhalf, ← hspin, addOrderOf_dvd_iff_nsmul_eq_zero,
      addOrderOf_dvd_iff_nsmul_eq_zero]
    constructor
    · intro h
      exact ⟨by simpa using h (checkerboardVectorClass n),
        by simpa using h (checkerboardSpinorClass n)⟩
    · rintro ⟨hv, hs⟩ a
      rcases checkerboardDiscriminantGroup_eq_zero_or_vectorClass_or_spinorClass_or_cospinorClass
          a with rfl | rfl | rfl | rfl <;> simp_all
  have hlevel : (checkerboardLattice n).level = Nat.lcm 2 ((n : ℚ) / 8).den := by
    apply Nat.dvd_antisymm
    · exact (h _).mpr ⟨Nat.dvd_lcm_left .., Nat.dvd_lcm_right ..⟩
    · exact Nat.lcm_dvd ((h _).mp dvd_rfl).1 ((h _).mp dvd_rfl).2
  rw [hlevel]
  have hden : ((n : ℚ) / 8).den = 8 / n.gcd 8 := by
    simpa [Rat.divInt_eq_div, Int.gcd_def, Nat.gcd_comm] using Rat.den_divInt (n : ℤ) 8
  rw [hden]
  calc
    Nat.lcm 2 (8 / n.gcd 8) = Nat.lcm (8 / 4) (8 / n.gcd 8) := rfl
    _ = 8 / Nat.gcd 4 (n.gcd 8) :=
      Nat.div_lcm_eq_div_gcd (by decide) (Nat.gcd_dvd_right ..)
    _ = 8 / n.gcd 4 := by
      congr 1
      rw [← Nat.gcd_assoc, Nat.gcd_comm 4 n, Nat.gcd_assoc]
      norm_num

end IntegralLattice
end TauCeti
