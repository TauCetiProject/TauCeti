/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.ProP.Marked
public import TauCeti.NumberTheory.LocalField.ProP.Rank
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Orientation

/-!
# The marked pro-`2` Galois group of `ℚ₂`

The maximal pro-`2` Galois group of `ℚ₂` is the standard dyadic Demushkin group

`G_{ℚ₂}(2) ≃ D₀ = ⟨A, S, Y ∣ A² S⁴ (S, Y)⟩`,

and the isomorphism is marked: it carries the standard orientation of `D₀`, with values `-1`, `1`
and `(-3)⁻¹` on `A`, `S` and `Y`, to the cyclotomic orientation of `G_{ℚ₂}(2)`, which is onto
`ℤ₂ˣ`. The commutator convention is `(x, y) = x⁻¹ y⁻¹ x y`, and the quotient uses the closed normal
closure of the relator.

The theorem is not a separate classification. `ℚ₂` has degree `1`, which is odd, so it lies in the
odd dyadic branch (`TauCeti.isDyadicOddCase_ratPadic`) with `q(ℚ₂) = 2`
(`TauCeti.localRootOfUnityOrder_two_ratPadic`) and generator rank `3`. The marked odd-degree theorem
`TauCeti.absoluteGaloisGroupProP_two_marked_of_degree_odd` at `N = 1` presents `G_{ℚ₂}(2)` by the
relator `x₁² x₂⁴ (x₂, x₃)`, which is the defining relator of `D₀`
(`TauCeti.d0Relator_eq_demushkinWordTwoOdd`), with the cyclotomic orientation taking the values of
the standard orientation on the marked generators; the two characters then agree by
`TauCeti.standardD0Orientation_unique`.

The marking is what separates this statement from its inverse-normalized twin: with the geometric
normalization of reciprocity the value on `Y` would be `-3` instead of `(-3)⁻¹`, still a
Demushkin presentation of the same abstract group.

## Main results

* `TauCeti.localRootOfUnityOrder_two_ratPadic`: `q(ℚ₂) = 2`.
* `TauCeti.isDyadicOddCase_ratPadic`: `ℚ₂` lies in the odd dyadic branch.
* `TauCeti.topologicalGeneratorRankNat_absoluteGaloisGroupProP_two_ratPadic`: `G_{ℚ₂}(2)` has
  exactly `3` topological generators.
* `TauCeti.absoluteGaloisGroupProP_two_ratPadic_marked`: the marked isomorphism
  `G_{ℚ₂}(2) ≃ D₀`, and its unmarked corollary `TauCeti.absoluteGaloisGroupProP_two_ratPadic`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132,
  Theorem 8.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.5.12).
* D. Roe, D. Turturean, *A Presentation of the Absolute Galois Group of ℚ₂*, preprint (2026),
  <https://roed314.github.io/gq2/>.
-/

public section

namespace TauCeti

/-- Instance search for `Nontrivial ℚ_[2]` times out through the Henselian-ring instances; the
degree computations below need it. -/
local instance : Nontrivial ℚ_[2] := DivisionRing.toNontrivial

/-- `ℚ₂` contains the primitive square root of unity `-1`. -/
theorem ratPadicTwo_hasPrimitiveRoot : ∃ ζ : ℚ_[2], IsPrimitiveRoot ζ 2 :=
  ⟨-1, IsPrimitiveRoot.neg_one 0 (by norm_num)⟩

/-- `ℚ₂` lies in the odd dyadic branch: its degree over itself is `1`. -/
theorem isDyadicOddCase_ratPadic : IsDyadicOddCase ℚ_[2] :=
  (isDyadicOddCase_iff_odd_finrank ℚ_[2]).mpr (by simp)

/-- `q(ℚ₂) = 2`: the only `2`-power roots of unity of `ℚ₂` are `±1`. -/
theorem localRootOfUnityOrder_two_ratPadic :
    localRootOfUnityOrder 2 ℚ_[2] (finite_pPowerRootsOfUnity (p := 2) (by norm_num)) = 2 :=
  isDyadicOddCase_ratPadic.localRootOfUnityOrder_eq_two

/-- The maximal pro-`2` Galois group of `ℚ₂` has exactly `3 = [ℚ₂ : ℚ₂] + 2` topological
generators. -/
theorem topologicalGeneratorRankNat_absoluteGaloisGroupProP_two_ratPadic
    (hfg : IsTopologicallyFinitelyGenerated (absoluteGaloisGroupProP 2 ℚ_[2])) :
    topologicalGeneratorRankNat (absoluteGaloisGroupProP 2 ℚ_[2]) hfg = 3 := by
  rw [topologicalGeneratorRankNat_absoluteGaloisGroupProP_of_mu 2 ℚ_[2] hfg
    ratPadicTwo_hasPrimitiveRoot, Module.finrank_self]

/-- **The marked pro-`2` Galois group of `ℚ₂`.** There is an isomorphism
`e : G_{ℚ₂}(2) ≃ D₀ = ⟨A, S, Y ∣ A² S⁴ (S, Y)⟩` of topological groups along which the standard
orientation of `D₀` pulls back to the cyclotomic orientation of `G_{ℚ₂}(2)`, and that orientation
is onto `ℤ₂ˣ`. So the generators `e⁻¹ A`, `e⁻¹ S`, `e⁻¹ Y` have cyclotomic values `-1`, `1` and
`(-3)⁻¹` (`TauCeti.standardD0Orientation_d0A`, `TauCeti.standardD0Orientation_d0S`,
`TauCeti.standardD0Orientation_d0Y`).

This is `TauCeti.absoluteGaloisGroupProP_two_marked_of_degree_odd` at `N = 1`. -/
theorem absoluteGaloisGroupProP_two_ratPadic_marked :
    ∃ e : absoluteGaloisGroupProP 2 ℚ_[2] ≃ₜ* demushkinD0,
      standardD0Orientation.comp (e : absoluteGaloisGroupProP 2 ℚ_[2] →ₜ* demushkinD0) =
          cyclotomicOrientation 2 ℚ_[2] ratPadicTwo_hasPrimitiveRoot ∧
        Function.Surjective (cyclotomicOrientation 2 ℚ_[2] ratPadicTwo_hasPrimitiveRoot) := by
  have hmarked := absoluteGaloisGroupProP_two_marked_of_degree_odd ℚ_[2]
    ratPadicTwo_hasPrimitiveRoot (by simp)
  rw [show Module.finrank ℚ_[2] ℚ_[2] + 2 = 3 by simp, ← d0Relator_eq_demushkinWordTwoOdd]
    at hmarked
  obtain ⟨e, hA, hY, h⟩ := hmarked
  have hS := h 1 one_ne_zero (by norm_num) (by norm_num)
  have h0 : presentedProPGen 2 3 {d0Relator} 0 = d0A := by simp [presentedProPGen_of_lt]
  have h1 : presentedProPGen 2 3 {d0Relator} 1 = d0S := by simp [presentedProPGen_of_lt]
  have h2 : presentedProPGen 2 3 {d0Relator} 2 = d0Y := by simp [presentedProPGen_of_lt]
  rw [h0] at hA
  rw [h1] at hS
  rw [h2] at hY
  have hcomp : (cyclotomicOrientation 2 ℚ_[2] ratPadicTwo_hasPrimitiveRoot).comp
      (e.symm : demushkinD0 →ₜ* absoluteGaloisGroupProP 2 ℚ_[2]) = standardD0Orientation :=
    standardD0Orientation_unique _ hA hS (Units.ext (by
      rw [← mul_left_inj' (show (1 - 2 ^ 2 : ℤ_[2]) ≠ 0 by norm_num),
        negThreeUnit_inv_mul_one_sub_two_pow_two]
      exact hY))
  have heq : standardD0Orientation.comp (e : absoluteGaloisGroupProP 2 ℚ_[2] →ₜ* demushkinD0) =
      cyclotomicOrientation 2 ℚ_[2] ratPadicTwo_hasPrimitiveRoot := by
    ext x
    simp [← hcomp]
  refine ⟨e, heq, ?_⟩
  rw [← heq]
  exact standardD0Orientation_surjective.comp e.surjective

/-- `G_{ℚ₂}(2) ≃ D₀ = ⟨A, S, Y ∣ A² S⁴ (S, Y)⟩`, the unmarked form of
`TauCeti.absoluteGaloisGroupProP_two_ratPadic_marked`. -/
theorem absoluteGaloisGroupProP_two_ratPadic :
    Nonempty (absoluteGaloisGroupProP 2 ℚ_[2] ≃ₜ* demushkinD0) :=
  let ⟨e, _⟩ := absoluteGaloisGroupProP_two_ratPadic_marked
  ⟨e⟩

end TauCeti
