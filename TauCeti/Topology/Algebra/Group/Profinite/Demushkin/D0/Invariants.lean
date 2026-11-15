/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Character.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.D0.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Orientation
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.QInvariant
import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Abelianization
import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Finite
import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.IsDemushkin
import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Prescription

/-!
# The invariants of `D₀`: rank `3`, `q(D₀) = 2`, and orientation image `ℤ₂ˣ`

The dyadic group `D₀ = ⟨A, S, Y ∣ A²S⁴(S,Y)⟩` is the odd-rank dyadic normal form with `n = 3` and
`f = 2` (`TauCeti.d0Relator_eq_demushkinWordTwoOdd`), so it is a Demushkin group at `p = 2` by
`TauCeti.isDemushkin_presentedProP_demushkinWordTwoOdd`. Its rank is `3`, the topological
generator rank of its minimal presentation, so it is infinite, and its `q`-invariant is `2`, the
number of torsion elements of its abelianization `D₀^{ab} ≅ ℤ₂ × ℤ₂ × ℤ/2` computed in
`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Abelianization`. These are the invariants
`(n, q) = (3, 2)` of the group Labute denotes `D₀` (Labute, p. 106); the name and the marked
generators `A, S, Y` follow Roe–Turturean, §3.1.

The canonical character of `D₀`, the unique continuous character `D₀ → ℤ₂ˣ` with the prescription
property (`TauCeti.demushkinCharacter`), is its standard orientation
`TauCeti.standardD0Orientation`, with values `-1`, `1`, `(-3)⁻¹` on `A`, `S`, `Y`: these are the
tabulated character values `χ(x₁) = -1`, `χ(x₂) = 1`, `χ(x₃) = (1 - 2²)⁻¹` of the normal form
`x₁² x₂^{2^f} (x₂, x₃)` at `f = 2`, and the tabulated values are the prescription property. The
image of the canonical character is therefore all of `ℤ₂ˣ = {±1} × U^(2)`
(`TauCeti.range_standardD0Orientation`), the second invariant of `D₀` in the classification of
Demushkin groups: the invariants of `D₀` are `(n, Im χ) = (3, ℤ₂ˣ)`.

## Main results

* `TauCeti.isDemushkin_demushkinD0`: **`D₀` is a Demushkin group** at `p = 2`.
* `TauCeti.demushkinRank_demushkinD0`, `TauCeti.demushkinQ_demushkinD0`: its rank is `3` and
  `q(D₀) = 2`.
* `D₀` is infinite (an `Infinite demushkinD0` instance).
* `TauCeti.hasPrescriptionProperty_standardD0Orientation`,
  `TauCeti.demushkinCharacter_demushkinD0`: **the standard orientation of `D₀` is its canonical
  character**; with `TauCeti.range_standardD0Orientation`, `simp` then shows that the image of
  the canonical character of `D₀` is `ℤ₂ˣ`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §3,
  Theorems 3 and 4, and p. 106.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter III, §9.
* D. Roe, D. Turturean, *A Presentation of the Absolute Galois Group of ℚ₂*, preprint (2026),
  §3.1, <https://roed314.github.io/gq2/>.
-/

public section

namespace TauCeti

/-- **`D₀ = ⟨A, S, Y ∣ A²S⁴(S,Y)⟩` is a Demushkin group at `p = 2`**: its relator is the dyadic
odd-rank normal-form word with `n = 3` and `f = 2`. -/
theorem isDemushkin_demushkinD0 : IsDemushkin 2 demushkinD0 := by
  have h := isDemushkin_presentedProP_demushkinWordTwoOdd (n := 3) ⟨1, rfl⟩ (f := 2) two_pos
  rwa [← d0Relator_eq_demushkinWordTwoOdd] at h

/-- **`D₀` is a Demushkin group of rank `3`.** -/
@[simp]
theorem demushkinRank_demushkinD0 (hG : IsDemushkin 2 demushkinD0) : demushkinRank hG = 3 := by
  rw [demushkinRank_def, topologicalGeneratorRankNat_demushkinD0]

/-- **`D₀` is infinite**, being a Demushkin group of rank `3 ≥ 2`. -/
instance : Infinite demushkinD0 :=
  isDemushkin_demushkinD0.infinite_of_two_le_demushkinRank
    (by rw [demushkinRank_demushkinD0]; omega)

/-- **`q(D₀) = 2`**: the `q`-invariant of `D₀`, the number of torsion elements of its
abelianization `D₀^{ab} ≅ ℤ₂ × ℤ₂ × ℤ/2`. -/
@[simp]
theorem demushkinQ_demushkinD0 (hG : IsDemushkin 2 demushkinD0) : demushkinQ hG = 2 := by
  have hcard := nat_card_torsion_topologicalAbelianization_demushkinD0
  rw [demushkinQ_of_not_isMulTorsionFree _ fun h ↦ ?_, hcard]
  rw [CommGroup.isMulTorsionFree_iff_torsion_eq_bot.1 h, Subgroup.card_bot] at hcard
  omega

/-- **The standard orientation of `D₀` has the prescription property**: its values `-1`, `1`,
`(-3)⁻¹` on `A`, `S`, `Y` are the tabulated values `χ(x₁) = -1`, `χ(x₂) = 1`,
`χ(x₃)(1 - 2²) = 1` of the odd-rank dyadic normal form `x₁² x₂^{2^f} (x₂, x₃)` at `n = 3`,
`f = 2`. -/
theorem hasPrescriptionProperty_standardD0Orientation :
    HasPrescriptionProperty standardD0Orientation := by
  -- The `ℕ`-indexed generators of `D₀` are its marked generators.
  have h0 : presentedProPGen 2 3 {d0Relator} 0 = d0A := by simp [presentedProPGen_of_lt]
  have h1 : presentedProPGen 2 3 {d0Relator} 1 = d0S := by simp [presentedProPGen_of_lt]
  have h2 : presentedProPGen 2 3 {d0Relator} 2 = d0Y := by simp [presentedProPGen_of_lt]
  -- The relator of `D₀` is the odd-rank normal-form word at `n = 3`, `f = 2`.
  have key := hasPrescriptionProperty_presentedProP_demushkinWordTwoOdd_of_apply_eq 2 3
  rw [← d0Relator_eq_demushkinWordTwoOdd] at key
  refine key standardD0Orientation ?_ ?_ fun i hi₀ hi₂ ↦ ?_
  · rw [h0, standardD0Orientation_d0A]
  · rw [h2, standardD0Orientation_d0Y]
    exact negThreeUnit_inv_mul_one_sub_two_pow_two
  · rcases Nat.lt_or_ge i 3 with hi | hi
    · obtain rfl : i = 1 := by omega
      rw [h1, standardD0Orientation_d0S]
    · rw [presentedProPGen_eq_one_of_le _ _ _ hi, map_one]

/-- **The canonical character of `D₀` is its standard orientation**: the standard orientation has
the prescription property, and the canonical character is the only continuous character that
does. -/
@[simp]
theorem demushkinCharacter_demushkinD0 (hG : IsDemushkin 2 demushkinD0) :
    demushkinCharacter hG = standardD0Orientation :=
  (hasPrescriptionProperty_standardD0Orientation.eq_demushkinCharacter hG).symm

end TauCeti
