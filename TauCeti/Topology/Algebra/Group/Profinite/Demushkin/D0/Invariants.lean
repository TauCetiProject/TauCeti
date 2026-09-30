/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.D0.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.QInvariant
import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Abelianization
import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Finite
import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.IsDemushkin

/-!
# `D₀` is a Demushkin group of rank `3` with `q(D₀) = 2`

The dyadic group `D₀ = ⟨A, S, Y ∣ A²S⁴(S,Y)⟩` is the odd-rank dyadic normal form with `n = 3` and
`f = 2` (`TauCeti.d0Relator_eq_demushkinWordTwoOdd`), so it is a Demushkin group at `p = 2` by
`TauCeti.isDemushkin_presentedProP_demushkinWordTwoOdd`. Its rank is `3`, the topological
generator rank of its minimal presentation, so it is infinite, and its `q`-invariant is `2`, the
number of torsion elements of its abelianization `D₀^{ab} ≅ ℤ₂ × ℤ₂ × ℤ/2` computed in
`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Abelianization`. These are the invariants
`(n, q) = (3, 2)` of the group Labute denotes `D₀` (Labute, p. 106); the name and the marked
generators `A, S, Y` follow Roe–Turturean, §3.1.

## Main results

* `TauCeti.isDemushkin_demushkinD0`: **`D₀` is a Demushkin group** at `p = 2`.
* `TauCeti.demushkinRank_demushkinD0`, `TauCeti.demushkinQ_demushkinD0`: its rank is `3` and
  `q(D₀) = 2`.
* `D₀` is infinite (an `Infinite demushkinD0` instance).

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §3,
  Theorem 3, and p. 106.
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

end TauCeti
