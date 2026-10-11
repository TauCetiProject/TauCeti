/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.FiniteExtension.Basic
public import TauCeti.NumberTheory.LocalField.ProP.Marked
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Orientation
import Mathlib.RingTheory.Prime
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.FiniteExtension
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Range
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Surjectivity
import TauCeti.FieldTheory.Kummer.Extension
import TauCeti.NumberTheory.Padics.Basic

/-!
# The marked pro-`2` Galois group of `ℚ₂(√-2)`

The field `ℚ₂(√-2)` has degree `2` over `ℚ₂` and exactly two `2`-power roots of unity, and the
image of its cyclotomic character is the twisted subgroup `U^[2] = closure⟨3⟩` of `ℤ₂ˣ`, which does
not contain `-1`. So it lies in the even-degree principal branch of the dyadic marked
classification, with `k = 2`, and

`G_{ℚ₂(√-2)}(2) ≃ ⟨x₁, x₂, x₃, x₄ ∣ x₁⁶ (x₁, x₂) x₃⁸ (x₃, x₄)⟩`,

under which the cyclotomic orientation satisfies `χ(x₂) · (1 + 4) = -1` and `χ(x₄) · (1 - 8) = 1`
and is trivial on `x₁` and `x₃`. This is
`TauCeti.absoluteGaloisGroupProP_two_marked_of_degree_even_principal` at `N = 2`, `k = 2`,
`α = 4`, `f = 3`. In this branch the level `f` is not an invariant: the general theorem applies
to every `f > k`, and `f = 3` is the least choice.

This example separates the two even-degree branches: `q = 2` and the rank `4` are those of the
plus-minus branch as well, and only the image of the orientation, through `-1 ∉ Im χ` and the
generator `3 = -1 + 2²`, selects the principal branch and its index `k = 2`.

The image is computed by Galois theory, without reciprocity. Every value of the character is `1`
or `3` modulo `8`, because `√-2 = ξ + ξ³` for a primitive eighth root of unity `ξ`
(`TauCeti.toZModPow_three_localCyclotomicCharacter_eq_one_or_eq_three`). This excludes `-1` and
every generator `-1 + 2^k` with `k ≥ 3` from the image, so the classification of the closed
subgroups of `ℤ₂ˣ` (`TauCeti.exists_range_localCyclotomicCharacter_eq_topologicalClosure_zpowers`)
leaves `closure⟨-1 + 2²⟩`. The same congruence excludes a primitive fourth root of unity: it would
put the image in `1 + 8ℤ₂`, of index `4` in `ℤ₂ˣ`, while the image has index dividing the degree
`2` (`TauCeti.relIndex_range_localCyclotomicCharacter_dvd_finrank`).

## Main definitions

* `TauCeti.RatPadicSqrtNegTwo`: the local field `ℚ₂(√-2)`, adjoining a root of `X² + 2` to `ℚ₂`.
* `TauCeti.RatPadicSqrtNegTwo.sqrtNegTwo`: its distinguished square root of `-2`.

## Main results

* `TauCeti.finrank_ratPadicSqrtNegTwo`: the degree is `2`.
* `TauCeti.localRootOfUnityOrder_two_ratPadicSqrtNegTwo`: `q(ℚ₂(√-2)) = 2`.
* `TauCeti.range_localCyclotomicCharacter_ratPadicSqrtNegTwo`: the cyclotomic image is
  `closure⟨-negThreeUnit⟩ = closure⟨3⟩`.
* `TauCeti.isDyadicEvenPrincipalCase_ratPadicSqrtNegTwo`: `ℚ₂(√-2)` is in the even principal
  branch.
* `TauCeti.absoluteGaloisGroupProP_two_ratPadicSqrtNegTwo_marked`: the marked presentation of
  `G_{ℚ₂(√-2)}(2)`, and its unmarked corollary
  `TauCeti.absoluteGaloisGroupProP_two_ratPadicSqrtNegTwo`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132,
  Theorems 8 and 9.
* J.-P. Serre, *Local Fields*, Chapter IV, §4.
-/

public section
noncomputable section

open Polynomial

namespace TauCeti

/-- The local field `ℚ₂(√-2)`, obtained by adjoining a root of `X² + 2` to `ℚ₂`. -/
def RatPadicSqrtNegTwo : Type := AdjoinRoot (X ^ 2 + C 2 : ℚ_[2][X])

namespace RatPadicSqrtNegTwo

/-- `X² + 2` is irreducible over `ℚ₂`: it is `X² - (-2)`, and `-2` is a uniformizer of `ℤ₂`. -/
local instance : Fact (Irreducible (X ^ 2 + C 2 : ℚ_[2][X])) :=
  ⟨by
    have h := X_pow_sub_C_irreducible_of_irreducible (R := ℤ_[2]) (K := ℚ_[2])
      (PadicInt.prime_p (p := 2)).neg.irreducible two_ne_zero
    rwa [map_neg, map_natCast, C_neg, sub_neg_eq_add, Nat.cast_ofNat] at h⟩

instance : Field RatPadicSqrtNegTwo :=
  inferInstanceAs (Field (AdjoinRoot (X ^ 2 + C 2 : ℚ_[2][X])))

instance : Algebra ℚ_[2] RatPadicSqrtNegTwo :=
  inferInstanceAs (Algebra ℚ_[2] (AdjoinRoot (X ^ 2 + C 2 : ℚ_[2][X])))

/-- The power basis `1, √-2` of `ℚ₂(√-2)` over `ℚ₂`. -/
private def powerBasis : PowerBasis ℚ_[2] RatPadicSqrtNegTwo :=
  AdjoinRoot.powerBasis (Fact.out : Irreducible (X ^ 2 + C 2 : ℚ_[2][X])).ne_zero

instance : FiniteDimensional ℚ_[2] RatPadicSqrtNegTwo := powerBasis.finite

instance : Algebra.IsSeparable ℚ_[2] RatPadicSqrtNegTwo :=
  Algebra.IsAlgebraic.isSeparable_of_perfectField

instance : CharZero RatPadicSqrtNegTwo :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[2] RatPadicSqrtNegTwo).injective

instance : ValuativeRel RatPadicSqrtNegTwo := finiteExtensionValuativeRel ℚ_[2] RatPadicSqrtNegTwo

instance : TopologicalSpace RatPadicSqrtNegTwo :=
  finiteExtensionNormedFieldTopology ℚ_[2] RatPadicSqrtNegTwo

instance : ValuativeExtension ℚ_[2] RatPadicSqrtNegTwo :=
  finiteExtension_valuativeExtension ℚ_[2] RatPadicSqrtNegTwo

instance : IsNonarchimedeanLocalField RatPadicSqrtNegTwo :=
  finiteExtension_isNonarchimedeanLocalField ℚ_[2] RatPadicSqrtNegTwo

/-- The square root `√-2` generating `ℚ₂(√-2)`, the class of `X`. -/
def sqrtNegTwo : RatPadicSqrtNegTwo := AdjoinRoot.root (X ^ 2 + C 2 : ℚ_[2][X])

/-- The defining equation of the generator `√-2`. -/
@[simp]
theorem sqrtNegTwo_sq : sqrtNegTwo ^ 2 = -2 := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 + C 2 : ℚ_[2][X])
  rwa [eval₂_add, eval₂_X_pow, eval₂_C, map_ofNat, ← eq_neg_iff_add_eq_zero] at h

end RatPadicSqrtNegTwo

open RatPadicSqrtNegTwo

/-- The degree of `ℚ₂(√-2)/ℚ₂` is `2`, so `N + 2 = 4`. -/
@[simp]
theorem finrank_ratPadicSqrtNegTwo : Module.finrank ℚ_[2] RatPadicSqrtNegTwo = 2 := by
  rw [powerBasis.finrank, powerBasis, AdjoinRoot.powerBasis_dim, natDegree_X_pow_add_C]

/-- `ℚ₂(√-2)` contains the primitive square root of unity `-1`. -/
theorem ratPadicSqrtNegTwo_hasPrimitiveRoot : ∃ ζ : RatPadicSqrtNegTwo, IsPrimitiveRoot ζ 2 :=
  ⟨-1, IsPrimitiveRoot.neg_one 0 (by norm_num)⟩

/-- Every value of the cyclotomic character of `ℚ₂(√-2)` is `1` or `3` modulo `8`. -/
private theorem toZModPow_three_eq_one_or_eq_three_of_mem_range {u : ℤ_[2]ˣ}
    (hu : u ∈ (localCyclotomicCharacter 2 RatPadicSqrtNegTwo).range) :
    PadicInt.toZModPow 3 (u : ℤ_[2]) = 1 ∨ PadicInt.toZModPow 3 (u : ℤ_[2]) = 3 := by
  obtain ⟨σ, rfl⟩ := hu
  exact toZModPow_three_localCyclotomicCharacter_eq_one_or_eq_three sqrtNegTwo_sq σ

/-- `ℚ₂(√-2)` contains no primitive fourth root of unity. Otherwise every value of its cyclotomic
character would be `1` modulo `4`, hence `1` modulo `8`, and the image would have index at least
`[ℤ₂ˣ : 1 + 8ℤ₂] = 4`, while its index divides `[ℚ₂(√-2) : ℚ₂] = 2`. -/
theorem not_exists_isPrimitiveRoot_four_ratPadicSqrtNegTwo :
    ¬ ∃ ζ : RatPadicSqrtNegTwo, IsPrimitiveRoot ζ 4 := by
  intro hmu
  have hle : (localCyclotomicCharacter 2 RatPadicSqrtNegTwo).range ≤ unitsPrincipal 2 3 := by
    intro u hu
    have h4 : u ∈ unitsPrincipal 2 2 :=
      range_localCyclotomicCharacter_le_unitsPrincipal (by simpa using hmu) hu
    rw [mem_unitsPrincipal_iff_toZModPow] at h4 ⊢
    refine (toZModPow_three_eq_one_or_eq_three_of_mem_range hu).resolve_right fun h3 ↦ ?_
    rw [← PadicInt.cast_toZModPow 2 3 (by norm_num), h3] at h4
    exact absurd h4 (by decide)
  have hdvd := relIndex_range_localCyclotomicCharacter_dvd_finrank 2 ℚ_[2] RatPadicSqrtNegTwo
  rw [range_localCyclotomicCharacter_ratPadic, Subgroup.relIndex_top_right,
    finrank_ratPadicSqrtNegTwo] at hdvd
  have h4 := (Subgroup.index_dvd_of_le hle).trans hdvd
  rw [index_unitsPrincipal_two] at h4
  norm_num at h4

/-- `q(ℚ₂(√-2)) = 2`: the only `2`-power roots of unity of `ℚ₂(√-2)` are `±1`. -/
theorem localRootOfUnityOrder_two_ratPadicSqrtNegTwo :
    localRootOfUnityOrder 2 RatPadicSqrtNegTwo
      (finite_pPowerRootsOfUnity (p := 2) (K := RatPadicSqrtNegTwo) (by norm_num)) = 2 :=
  not_not.mp fun h ↦ not_exists_isPrimitiveRoot_four_ratPadicSqrtNegTwo
    ((localRootOfUnityOrder_ne_two_iff (by norm_num)).mp h)

/-- `-1` is not a value of the cyclotomic character of `ℚ₂(√-2)`, since `-1 ≡ 7 mod 8`. -/
theorem neg_one_notMem_range_localCyclotomicCharacter_ratPadicSqrtNegTwo :
    (-1 : ℤ_[2]ˣ) ∉ (localCyclotomicCharacter 2 RatPadicSqrtNegTwo).range := fun h ↦ by
  have h8 := toZModPow_three_eq_one_or_eq_three_of_mem_range h
  rw [Units.val_neg, Units.val_one, map_neg, map_one] at h8
  rcases h8 with h8 | h8 <;> exact absurd h8 (by decide)

/-- **The cyclotomic image of `ℚ₂(√-2)` is `U^[2] = closure⟨3⟩`**, the closed subgroup of `ℤ₂ˣ`
topologically generated by `-negThreeUnit = 3 = -1 + 2²` (`negThreeUnit_neg_coe`). By the
classification of closed subgroups it is `closure⟨-1 + 2^k⟩` for some `k ≥ 2`, and `k = 2`
because `-1 + 2^k ≡ 7 mod 8` for `k ≥ 3`, while every value of the character is `1` or `3`
modulo `8`. -/
theorem range_localCyclotomicCharacter_ratPadicSqrtNegTwo :
    (localCyclotomicCharacter 2 RatPadicSqrtNegTwo).range =
      (Subgroup.zpowers (-negThreeUnit)).topologicalClosure := by
  obtain ⟨k, u, hk, hu, hrange⟩ :=
    exists_range_localCyclotomicCharacter_eq_topologicalClosure_zpowers RatPadicSqrtNegTwo
      not_exists_isPrimitiveRoot_four_ratPadicSqrtNegTwo
      neg_one_notMem_range_localCyclotomicCharacter_ratPadicSqrtNegTwo
  have hmem : u ∈ (localCyclotomicCharacter 2 RatPadicSqrtNegTwo).range :=
    hrange ▸ Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers u)
  -- For `k ≥ 3`, the generator `-1 + 2 ^ k` would be `7` modulo `8`.
  obtain rfl : k = 2 := by
    refine (hk.eq_or_lt.resolve_right fun h3 ↦ ?_).symm
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt h3)
    have h8 := toZModPow_three_eq_one_or_eq_three_of_mem_range hmem
    rw [hu] at h8
    have hpow : PadicInt.toZModPow 3 (2 : ℤ_[2]) ^ 3 = 0 := by
      rw [map_ofNat]
      decide
    simp only [Nat.reducePow, Nat.succ_eq_add_one, Nat.reduceAdd, pow_add, map_add, map_neg,
      map_one, map_mul, map_pow, hpow, zero_mul, add_zero] at h8
    rcases h8 with h8 | h8 <;> exact absurd h8 (by decide)
  rw [hrange, show u = -negThreeUnit from Units.ext (by rw [hu, negThreeUnit_neg_coe])]

/-- `ℚ₂(√-2)` lies in the even-degree principal branch: `q = 2`, the degree `2` is even, and `-1`
is not a value of the cyclotomic character. -/
theorem isDyadicEvenPrincipalCase_ratPadicSqrtNegTwo :
    IsDyadicEvenPrincipalCase RatPadicSqrtNegTwo :=
  isDyadicEvenPrincipalCase_iff.mpr ⟨localRootOfUnityOrder_two_ratPadicSqrtNegTwo, by simp,
    neg_one_notMem_range_localCyclotomicCharacter_ratPadicSqrtNegTwo⟩

/-- **The marked presentation of `G_{ℚ₂(√-2)}(2)`.** The maximal pro-`2` Galois group of
`ℚ₂(√-2)` is isomorphic to `⟨x₁, x₂, x₃, x₄ ∣ x₁⁶ (x₁, x₂) x₃⁸ (x₃, x₄)⟩`, the even dyadic
Demushkin group with `α = 4` and `f = 3`, and under this isomorphism the cyclotomic orientation
satisfies `χ(x₂) · (1 + 4) = -1` and `χ(x₄) · (1 - 8) = 1` and is trivial on `x₁` and `x₃`.

This is `absoluteGaloisGroupProP_two_marked_of_degree_even_principal` at `N = 2`, with `k = 2`
read off the cyclotomic image `closure⟨-1 + 2²⟩`
(`range_localCyclotomicCharacter_ratPadicSqrtNegTwo`). -/
theorem absoluteGaloisGroupProP_two_ratPadicSqrtNegTwo_marked :
    ∃ e : absoluteGaloisGroupProP 2 RatPadicSqrtNegTwo ≃ₜ*
        presentedProP 2 (Fin 4) {demushkinWordTwoEven 4 3 4 (freeProPGen 2 4)},
      ((cyclotomicOrientation 2 RatPadicSqrtNegTwo ratPadicSqrtNegTwo_hasPrimitiveRoot
          (e.symm (presentedProPGen 2 4 _ 1)) : ℤ_[2]) * (1 + 4) = -1) ∧
        ((cyclotomicOrientation 2 RatPadicSqrtNegTwo ratPadicSqrtNegTwo_hasPrimitiveRoot
            (e.symm (presentedProPGen 2 4 _ 3)) : ℤ_[2]) * (1 - 8) = 1) ∧
        cyclotomicOrientation 2 RatPadicSqrtNegTwo ratPadicSqrtNegTwo_hasPrimitiveRoot
            (e.symm (presentedProPGen 2 4 _ 0)) = 1 ∧
        cyclotomicOrientation 2 RatPadicSqrtNegTwo ratPadicSqrtNegTwo_hasPrimitiveRoot
            (e.symm (presentedProPGen 2 4 _ 2)) = 1 := by
  have hmarked := absoluteGaloisGroupProP_two_marked_of_degree_even_principal RatPadicSqrtNegTwo
    ratPadicSqrtNegTwo_hasPrimitiveRoot (by simp) (a := 4) (k := 2) (f := 3) le_rfl
    (by norm_num) (by norm_num) (by norm_num) negThreeUnit_neg_coe
    range_localCyclotomicCharacter_ratPadicSqrtNegTwo
  rw [finrank_ratPadicSqrtNegTwo] at hmarked
  obtain ⟨e, h1, h3, h⟩ := hmarked
  refine ⟨e, by simpa using h1, by norm_num at h3 ⊢; exact h3,
    h 0 (by norm_num) (by norm_num) (by norm_num), h 2 (by norm_num) (by norm_num) (by norm_num)⟩

/-- `G_{ℚ₂(√-2)}(2) ≃ ⟨x₁, x₂, x₃, x₄ ∣ x₁⁶ (x₁, x₂) x₃⁸ (x₃, x₄)⟩`, the unmarked form of
`absoluteGaloisGroupProP_two_ratPadicSqrtNegTwo_marked`. -/
theorem absoluteGaloisGroupProP_two_ratPadicSqrtNegTwo :
    Nonempty (absoluteGaloisGroupProP 2 RatPadicSqrtNegTwo ≃ₜ*
      presentedProP 2 (Fin 4) {demushkinWordTwoEven 4 3 4 (freeProPGen 2 4)}) :=
  let ⟨e, _⟩ := absoluteGaloisGroupProP_two_ratPadicSqrtNegTwo_marked
  ⟨e⟩

end TauCeti
