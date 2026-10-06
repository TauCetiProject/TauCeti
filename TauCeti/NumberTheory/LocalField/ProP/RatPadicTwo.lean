/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.OddDegree
public import TauCeti.NumberTheory.LocalField.ProP.Marked
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Orientation

import TauCeti.NumberTheory.LocalField.RootsOfUnity.Unramified

/-!
# The maximal pro-`2` Galois group of `ℚ₂` is `D₀`

This file computes the marked presentation of `G_{ℚ₂}(2)`, the maximal pro-`2` quotient of the
absolute Galois group of `ℚ₂`. The field `ℚ₂` contains exactly two `2`-power roots of unity,
namely `±1`, so `q(ℚ₂) = 2`; and its degree over itself is `N = 1`, which is odd. Thus `ℚ₂` lies in
the odd dyadic case, and `G_{ℚ₂}(2)` is a Demushkin group of rank `N + 2 = 3`. The odd-degree
marked theorem `TauCeti.absoluteGaloisGroupProP_two_marked_of_degree_odd` at `N = 1` presents it on
three generators by the relator `x₁² x₂⁴ (x₂, x₃)`. This relator is the defining relator of the
standard dyadic group `D₀ = ⟨A, S, Y ∣ A²S⁴(S,Y)⟩` (`TauCeti.d0Relator_eq_demushkinWordTwoOdd`).

The theorem recorded here is the marked form of the identification: there is an isomorphism
`e : G_{ℚ₂}(2) ≃ D₀` along which the standard orientation of `D₀` pulls back to the cyclotomic
orientation of `G_{ℚ₂}(2)`. The marked theorem gives the values `-1`, `1`, `(-3)⁻¹` of the
cyclotomic orientation on the preimages of `A`, `S`, `Y`. These are the values that characterize
`TauCeti.standardD0Orientation` (`TauCeti.standardD0Orientation_unique`). The standard orientation
is onto `ℤ₂ˣ`, so the cyclotomic orientation of `G_{ℚ₂}(2)` is surjective as well.

The fact that `ℚ₂` has no primitive fourth root of unity is the case `L = ℚ₂` of
`TauCeti.localRootOfUnityOrder_two_of_isUnramified`, since `ℚ₂` is unramified over itself.

## Main results

* `TauCeti.ratPadicTwo_hasPrimitiveRoot`: `ℚ₂` contains a primitive square root of unity.
* `TauCeti.localRootOfUnityOrder_two_ratPadic`: `q(ℚ₂) = 2`.
* `TauCeti.isDyadicOddCase_ratPadic`: `ℚ₂` lies in the odd dyadic case.
* `TauCeti.demushkinRank_absoluteGaloisGroupProP_two_ratPadic`: `G_{ℚ₂}(2)` has rank `3`.
* `TauCeti.absoluteGaloisGroupProP_two_ratPadic_marked`: **the marked identification
  `G_{ℚ₂}(2) ≃ D₀`**, carrying the standard orientation to the cyclotomic orientation, which is
  surjective.
* `TauCeti.absoluteGaloisGroupProP_two_ratPadic`: its unmarked corollary `G_{ℚ₂}(2) ≃ D₀`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter VII, §5.
* D. Roe, D. Turturean, *A Presentation of the Absolute Galois Group of ℚ₂*, preprint (2026),
  §3.1, <https://roed314.github.io/gq2/>.
-/

public section

namespace TauCeti

/-- A shortcut for `Nontrivial ℚ_[2]`, needed by `Module.finrank_self`. Without it, instance search
first tries the path through `HenselianLocalRing` and `IsAdicComplete`, and times out. -/
local instance : Nontrivial ℚ_[2] := DivisionRing.toNontrivial

/-- `ℚ₂` contains a primitive square root of unity, namely `-1`. -/
theorem ratPadicTwo_hasPrimitiveRoot : ∃ ζ : ℚ_[2], IsPrimitiveRoot ζ 2 :=
  ⟨-1, .neg_one_of_two_ne_zero two_ne_zero⟩

/-- **`q(ℚ₂) = 2`**: the `2`-power roots of unity in `ℚ₂` are `±1`. This is the unramified case
`TauCeti.localRootOfUnityOrder_two_of_isUnramified`, for `ℚ₂` over itself. -/
theorem localRootOfUnityOrder_two_ratPadic :
    localRootOfUnityOrder 2 ℚ_[2] (finite_pPowerRootsOfUnity (p := 2) two_ne_zero) = 2 :=
  -- `ℚ₂` is unramified over itself: its normalized valuation restricts to itself.
  have : IsUnramified ℚ_[2] ℚ_[2] :=
    (isUnramified_iff_normalizedValuation_algebraMap _ _).mpr fun _ ↦ by simp
  localRootOfUnityOrder_two_of_isUnramified ℚ_[2] two_ne_zero

/-- **`ℚ₂` lies in the odd dyadic case**: `q(ℚ₂) = 2`, and the degree `N = 1` is odd. -/
theorem isDyadicOddCase_ratPadic : IsDyadicOddCase ℚ_[2] :=
  .mk ℚ_[2] localRootOfUnityOrder_two_ratPadic (by simp)

/-- **`G_{ℚ₂}(2)` has Demushkin rank `3`**: for any witness `hG` that `G_{ℚ₂}(2)` is a Demushkin
group, the associated rank `demushkinRank hG` is `3`, the rank `N + 2` at `N = 1`. -/
@[simp]
theorem demushkinRank_absoluteGaloisGroupProP_two_ratPadic
    (hG : IsDemushkin 2 (absoluteGaloisGroupProP 2 ℚ_[2])) : demushkinRank hG = 3 := by
  rw [demushkinRank_absoluteGaloisGroupProP 2 ℚ_[2] ratPadicTwo_hasPrimitiveRoot,
    Module.finrank_self]

/-- **The marked presentation of `G_{ℚ₂}(2)`.** There is an isomorphism
`e : G_{ℚ₂}(2) ≃ D₀ = ⟨A, S, Y ∣ A²S⁴(S,Y)⟩` along which the standard orientation of `D₀` pulls
back to the cyclotomic orientation of `G_{ℚ₂}(2)`, and the cyclotomic orientation is surjective.

This is the odd-degree marked theorem `TauCeti.absoluteGaloisGroupProP_two_marked_of_degree_odd`
at `N = 1`, whose relator is that of `D₀`. Its values `-1`, `1`, `(-3)⁻¹` on the preimages of `A`,
`S`, `Y` are those that characterize the standard orientation. -/
theorem absoluteGaloisGroupProP_two_ratPadic_marked :
    ∃ e : absoluteGaloisGroupProP 2 ℚ_[2] ≃ₜ* demushkinD0,
      standardD0Orientation.comp (e : absoluteGaloisGroupProP 2 ℚ_[2] →ₜ* demushkinD0) =
          cyclotomicOrientation 2 ℚ_[2] ratPadicTwo_hasPrimitiveRoot ∧
        Function.Surjective (cyclotomicOrientation 2 ℚ_[2] ratPadicTwo_hasPrimitiveRoot) := by
  have h := absoluteGaloisGroupProP_two_marked_of_degree_odd ℚ_[2] ratPadicTwo_hasPrimitiveRoot
    isDyadicOddCase_ratPadic.odd_finrank
  -- At `N = 1` the relator of the marked theorem is that of `D₀`.
  have h3 : Module.finrank ℚ_[2] ℚ_[2] + 2 = 3 := by rw [Module.finrank_self]
  rw [h3, ← d0Relator_eq_demushkinWordTwoOdd] at h
  obtain ⟨e, hA, hY, hS⟩ := h
  set χ := cyclotomicOrientation 2 ℚ_[2] ratPadicTwo_hasPrimitiveRoot
  -- The `ℕ`-indexed generators of `D₀` are its marked generators.
  have h0 : presentedProPGen 2 3 {d0Relator} 0 = d0A := by simp [presentedProPGen_of_lt]
  have h1 : presentedProPGen 2 3 {d0Relator} 1 = d0S := by simp [presentedProPGen_of_lt]
  have h2 : presentedProPGen 2 3 {d0Relator} 2 = d0Y := by simp [presentedProPGen_of_lt]
  -- The marked values are those of the standard orientation, which they characterize.
  have hY' : χ (e.symm d0Y) = negThreeUnit⁻¹ := by
    refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
    rw [← h2, Units.val_mul, negThreeUnit_coe, Units.val_one, ← hY]
    norm_num
  have hψ : χ.comp (e.symm : demushkinD0 →ₜ* absoluteGaloisGroupProP 2 ℚ_[2]) =
      standardD0Orientation :=
    standardD0Orientation_unique _ (by simpa [h0] using hA)
      (by simpa [h1] using hS 1 one_ne_zero (by decide) (by decide)) (by simpa using hY')
  have hcomp : standardD0Orientation.comp (e : absoluteGaloisGroupProP 2 ℚ_[2] →ₜ* demushkinD0) =
      χ := by
    ext g
    simp [← hψ]
  refine ⟨e, hcomp, ?_⟩
  rw [← hcomp]
  exact standardD0Orientation_surjective.comp e.surjective

/-- **`G_{ℚ₂}(2) ≃ D₀`**: the unmarked form of the marked identification
`TauCeti.absoluteGaloisGroupProP_two_ratPadic_marked`. -/
theorem absoluteGaloisGroupProP_two_ratPadic :
    Nonempty (absoluteGaloisGroupProP 2 ℚ_[2] ≃ₜ* demushkinD0) :=
  let ⟨e, _⟩ := absoluteGaloisGroupProP_two_ratPadic_marked
  ⟨e⟩

end TauCeti
