/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.ArakelovDivisor.Isometry
public import TauCeti.NumberTheory.NumberField.Quadratic.Model

/-!
# Checks for the hermitian lines of Arakelov divisors

* Over `ℚ`, the line `O((2))` of the principal divisor `(2) = [2] - log 2 · [∞]` is `½ ℤ` with
  the norm `2 |·|`. Its section `½` has norm one and trivializes it; the section `2` has norm `4`.
  Its class is zero, so `O((2))` is isometric to `O(0)`.
* Over `ℚ(i)`, the divisor `(2 𝓞 K, -log |2|_v)`, which forgets the multiplicity `2` of the complex
  place in the archimedean coefficient of `(2)`, has degree `log 4 - log 2 = log 2 ≠ 0`; so it is
  not principal, and `O` of it is not isometric to `O(0)`.
-/

public section

open NumberField NumberField.InfinitePlace TauCeti TauCeti.ArakelovDivisor FractionalIdeal
open scoped nonZeroDivisors

local instance TauCeti.ArakelovDivisorLineChecks.instFactNotIsSquareNegOne :
    Fact (¬ IsSquare (-1 : ℤ)) :=
  ⟨not_isSquare_of_neg (by norm_num)⟩

namespace TauCeti.ArakelovDivisorLineChecks

/-! ### The line `O((2))` over `ℚ` -/

/-- The unit `2` of `ℚ`. -/
noncomputable abbrev two : ℚˣ := Units.mk0 2 two_ne_zero

/-- The principal divisor `(2)` of `ℚ`. -/
noncomputable abbrev D₂ : ArakelovDivisor ℚ := principal ℚ (Additive.ofMul two)

/-- The infinite place of `ℚ` takes the value `2` at `2`. -/
theorem infinitePlace_two (v : InfinitePlace ℚ) : v (2 : ℚ) = 2 := by
  simp

/-- **`O((2))` has the norm `2 |·|`.** -/
theorem placeNorm_D₂ (v : InfinitePlace ℚ)
    (x : ((D₂.finitePart⁻¹ : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) : FractionalIdeal (𝓞 ℚ)⁰ ℚ)) :
    D₂.hermitianMetric.placeNorm v x = 2 * v x := by
  simp [placeNorm_hermitianMetric, Real.exp_log two_pos]

/-- The module of `O((2))` is `½ ℤ`. -/
theorem coe_finitePart_D₂_inv :
    ((D₂.finitePart⁻¹ : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) : FractionalIdeal (𝓞 ℚ)⁰ ℚ) =
      spanSingleton _ (2⁻¹ : ℚ) := by
  simp [finitePart_principal]

/-- `2 ∈ ½ ℤ`. -/
theorem two_mem : (2 : ℚ) ∈ ((D₂.finitePart⁻¹ : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) :
    FractionalIdeal (𝓞 ℚ)⁰ ℚ) := by
  rw [coe_finitePart_D₂_inv, mem_spanSingleton]
  exact ⟨4, by rw [Algebra.smul_def, map_ofNat]; norm_num⟩

/-- **The section `2` of `O((2))` has norm `4`**, while the section `½` has norm one
(`TauCeti.ArakelovDivisor.placeNorm_hermitianMetric_principal_inv`). -/
theorem placeNorm_D₂_two (v : InfinitePlace ℚ) :
    D₂.hermitianMetric.placeNorm v ⟨2, two_mem⟩ = 4 := by
  rw [placeNorm_D₂, infinitePlace_two]
  norm_num

/-- `O((2))` is isometric to the trivial line `O(0)`. -/
example : Nonempty (HermitianMetric.IsometryEquiv D₂.hermitianMetric
    (0 : ArakelovDivisor ℚ).hermitianMetric) :=
  ArakelovPicardGroup.mk_eq_mk_iff_nonempty_isometryEquiv.mp (by simp)

/-! ### Forgetting the multiplicity over `ℚ(i)` -/

/-- The Gaussian rationals `ℚ(i)`. -/
abbrev K := QuadraticAlgebra ℚ ((-1 : ℤ) : ℚ) 0

/-- The unit `2` of `ℚ(i)`. -/
noncomputable abbrev twoK : Kˣ := Units.mk0 2 two_ne_zero

/-- The divisor `(2 𝓞 K, v ↦ -log |2|_v)`: the principal divisor of `2` with the multiplicity
`mult(v) = 2` of the complex place left out of its archimedean coefficient. -/
noncomputable abbrev D : ArakelovDivisor K :=
  ⟨toPrincipalIdeal (𝓞 K) K twoK, fun v ↦ -Real.log (v (2 : K))⟩

/-- `ℚ(i)` has a single infinite place, a complex one. -/
theorem card_infinitePlace : Fintype.card (InfinitePlace K) = 1 := by
  have := QuadraticAlgebra.isTotallyComplex_iff.mpr (by norm_num : ((-1 : ℤ) : ℚ) < 0)
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    QuadraticAlgebra.nrComplexPlaces_eq_one (by norm_num), IsTotallyComplex.nrRealPlaces_eq_zero]

/-- **Forgetting the multiplicity breaks the degree**: the divisor `D` has degree
`log 4 - log 2 = log 2`. -/
theorem degree_D : degree K D = Real.log 4 - Real.log 2 := by
  have hv (v : InfinitePlace K) : v (2 : K) = 2 := by simpa using v.map_natCast 2
  have hnorm : Algebra.norm ℚ (2 : K) = 4 := by
    rw [← map_ofNat (algebraMap ℚ K) 2, Algebra.norm_algebraMap, QuadraticAlgebra.finrank_eq_two]
    norm_num
  rw [degree_apply]
  simp only [coe_toPrincipalIdeal, absNorm_span_singleton, Units.val_mk0, hnorm, hv,
    Finset.sum_const, Finset.card_univ, card_infinitePlace, one_smul]
  norm_num [sub_eq_add_neg]

/-- **`D` is not principal**: its degree `log 2` is not zero. -/
theorem mk_D_ne_zero : ArakelovPicardGroup.mk K D ≠ 0 := by
  intro h
  have h0 := congrArg (ArakelovPicardGroup.degree K) h
  rw [ArakelovPicardGroup.degree_mk, map_zero, degree_D, ← Real.log_div (by norm_num)
    (by norm_num)] at h0
  have : (0 : ℝ) < Real.log (4 / 2) := Real.log_pos (by norm_num)
  linarith

/-- `O(D)` is not isometric to the trivial line `O(0)`. -/
theorem not_nonempty_isometryEquiv_D :
    ¬ Nonempty (HermitianMetric.IsometryEquiv D.hermitianMetric
      (0 : ArakelovDivisor K).hermitianMetric) := by
  rw [← ArakelovPicardGroup.mk_eq_mk_iff_nonempty_isometryEquiv, map_zero]
  exact mk_D_ne_zero

end TauCeti.ArakelovDivisorLineChecks
