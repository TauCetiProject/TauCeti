/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.OddDegree
public import TauCeti.NumberTheory.LocalField.ProP.Marked
public import TauCeti.NumberTheory.Padics.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.D0.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Orientation

/-!
# The pro-`2` Galois group of `ℚ₂`

The absolute Galois group of `ℚ₂` has maximal pro-`2` quotient isomorphic to the standard
dyadic Demushkin group `D₀`.

The field `ℚ₂` contains exactly two `2`-power roots of unity, `±1`, and has degree `N = 1` over
itself, so it lies in the odd dyadic case and `G_{ℚ₂}(2)` is a Demushkin group of rank
`N + 2 = 3`. This module identifies `G_{ℚ₂}(2)` with `D₀`, both as an unmarked group and with
the standard orientation of `D₀` corresponding to the cyclotomic orientation of `G_{ℚ₂}(2)`.

## Main results

* `TauCeti.localRootOfUnityOrder_two_ratPadic`: `q(ℚ₂) = 2`.
* `TauCeti.isDyadicOddCase_ratPadic`: `ℚ₂` lies in the odd dyadic case.
* `TauCeti.demushkinRank_absoluteGaloisGroupProP_two_ratPadic`: `G_{ℚ₂}(2)` has rank `3`.
* `TauCeti.absoluteGaloisGroupProP_two_ratPadic_marked`: **the marked identification
  `G_{ℚ₂}(2) ≃ D₀`**, carrying the standard orientation to the cyclotomic orientation, which is
  surjective.
* `TauCeti.absoluteGaloisGroupProP_two_ratPadic`: `G_{ℚ₂}(2) ≃ D₀`, its unmarked corollary.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter VII, §5.
* D. Roe, D. Turturean, *A Presentation of the Absolute Galois Group of ℚ₂*, manuscript (2026),
  §3.1, <https://roed314.github.io/gq2/>.
-/

public section

namespace TauCeti

/-- `ℚ₂` contains the primitive square root of unity `-1`. -/
theorem ratPadicTwo_hasPrimitiveRoot : ∃ ζ : ℚ_[2], IsPrimitiveRoot ζ 2 :=
  ⟨-1, IsPrimitiveRoot.neg_one 0 (by norm_num)⟩

/-- `ℚ₂` contains no primitive fourth root of unity, since its cyclotomic character is
surjective while a primitive fourth root would force its image into `1 + 4ℤ₂`. -/
theorem not_exists_isPrimitiveRoot_four_ratPadic :
    ¬ ∃ ζ : ℚ_[2], IsPrimitiveRoot ζ 4 := by
  intro hζ
  have hle : (localCyclotomicCharacter 2 ℚ_[2]).range ≤ unitsPrincipal 2 2 :=
    range_localCyclotomicCharacter_le_unitsPrincipal (by simpa using hζ)
  have htop : (-1 : ℤ_[2]ˣ) ∈ (localCyclotomicCharacter 2 ℚ_[2]).range := by
    rw [range_localCyclotomicCharacter_ratPadic 2]
    exact Subgroup.mem_top _
  have hneg := hle htop
  have hcontra : 2 ≤ 1 := neg_one_mem_unitsPrincipal_two_iff.mp hneg
  omega

/-- The group of `2`-power roots of unity in `ℚ₂` has order two. -/
theorem localRootOfUnityOrder_two_ratPadic :
    localRootOfUnityOrder 2 ℚ_[2]
      (finite_pPowerRootsOfUnity (p := 2) (K := ℚ_[2]) (by norm_num)) = 2 := by
  apply not_not.mp
  intro hne
  exact not_exists_isPrimitiveRoot_four_ratPadic
    ((localRootOfUnityOrder_ne_two_iff (by norm_num)).mp hne)

/-- `ℚ₂` is in the odd-degree dyadic case: its root-of-unity order is two and its degree is one. -/
theorem isDyadicOddCase_ratPadic : IsDyadicOddCase ℚ_[2] :=
  IsDyadicOddCase.mk ℚ_[2] localRootOfUnityOrder_two_ratPadic (by
    rw [Module.finrank_self]
    decide)

/-- **`G_{ℚ₂}(2)` has Demushkin rank `3`**: for any witness `hG` that `G_{ℚ₂}(2)` is a Demushkin
group, the associated rank `demushkinRank hG` is `3`, the rank `N + 2` at `N = 1`. -/
@[simp]
theorem demushkinRank_absoluteGaloisGroupProP_two_ratPadic
    (hG : IsDemushkin 2 (absoluteGaloisGroupProP 2 ℚ_[2])) : demushkinRank hG = 3 := by
  rw [demushkinRank_absoluteGaloisGroupProP 2 ℚ_[2] ratPadicTwo_hasPrimitiveRoot,
    Module.finrank_self]

/-- **The marked presentation of `G_{ℚ₂}(2)`.** There is an isomorphism
`e : G_{ℚ₂}(2) ≃ D₀ = ⟨A, S, Y ∣ A²S⁴(S,Y)⟩` along which the standard orientation of `D₀` pulls
back to the cyclotomic orientation of `G_{ℚ₂}(2)`, and the cyclotomic orientation is surjective. -/
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

/-- **The maximal pro-`2` quotient of `G_{ℚ₂}` is `D₀`.** -/
theorem absoluteGaloisGroupProP_two_ratPadic :
    Nonempty (absoluteGaloisGroupProP 2 ℚ_[2] ≃ₜ* demushkinD0) :=
  let ⟨e, _⟩ := absoluteGaloisGroupProP_two_ratPadic_marked
  ⟨e⟩

end TauCeti
