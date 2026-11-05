/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Degree
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Index
import TauCeti.NumberTheory.ModularForms.WithCenter

/-!
# The degree of the map from a modular curve to the level-one curve

A subgroup `H ≤ SL(2, ℤ)` acts on the upper half-plane through its image `H.map sl2zToPSL2R` in
`PSL(2, ℝ)`, a subgroup of the level-one group `PSL(2, ℤ)`. The inclusion induces the map
`X(H) → X(1)` of compactified quotients, whose degree is the index of the inclusion
(`Subgroup.degree_compactifiedQuotientMap`), and that index is `[SL(2, ℤ) : ±H]`
(`Subgroup.relIndex_map_sl2zToPSL2R`), equivalently the index in `PSL(2, ℤ)` of the image of
`H` in `PSL(2, ℤ)` (`Subgroup.index_map_mk'_eq_index_sup`). It is not `[SL(2, ℤ) : H]` in
general: the two differ by a factor `2` exactly when `-I ∉ H`.

* For `Γ₀(N)`, which always contains `-I`, the degree of `X₀(N) → X(1)` is
  `[SL(2, ℤ) : Γ₀(N)] = N ∏_{p ∣ N} (1 + 1/p)`.
* For `Γ₁(N)` and `Γ(N)`, `-I` belongs to the subgroup precisely when `N ∣ 2`: for `N ∈ {1, 2}`
  the degree of `X₁(N) → X(1)` (resp. `X(N) → X(1)`) is `[SL(2, ℤ) : Γ₁(N)]` (resp.
  `[SL(2, ℤ) : Γ(N)]`), while for `N ≥ 3` it is half that index, giving the cleared-denominator
  formulas `2 d · ∏_{p ∣ N} p² = N² · ∏_{p ∣ N} (p² - 1)` for `X₁(N)` and
  `2 d · ∏_{p ∣ N} p² = N³ · ∏_{p ∣ N} (p² - 1)` for `X(N)`.

This degree is the quantity `d` in the genus formula `g = 1 + d/12 - ε₂/4 - ε₃/3 - ε∞/2` for
`X(H)`.

## Main statements

* `Subgroup.degree_compactifiedQuotientMap_map_sl2zToPSL2R`: the map `X(H) → X(1)` has degree
  `[SL(2, ℤ) : ±H]`.
* `CongruenceSubgroup.degree_compactifiedQuotientMap_Gamma0` and
  `CongruenceSubgroup.degree_compactifiedQuotientMap_Gamma0_mul_prod_primeFactors`: the degree
  of `X₀(N) → X(1)` is `[SL(2, ℤ) : Γ₀(N)] = N ∏_{p ∣ N} (1 + 1/p)`.
* `CongruenceSubgroup.degree_compactifiedQuotientMap_Gamma1_of_dvd_two`,
  `CongruenceSubgroup.two_mul_degree_compactifiedQuotientMap_Gamma1`,
  `CongruenceSubgroup.degree_compactifiedQuotientMap_Gamma1_of_three_le`, and
  `CongruenceSubgroup.two_mul_degree_compactifiedQuotientMap_Gamma1_mul_prod_primeFactors`:
  the degree of `X₁(N) → X(1)` for `N ∣ 2` and for `N ≥ 3`.
* `CongruenceSubgroup.degree_compactifiedQuotientMap_Gamma_of_dvd_two`,
  `CongruenceSubgroup.two_mul_degree_compactifiedQuotientMap_Gamma`,
  `CongruenceSubgroup.degree_compactifiedQuotientMap_Gamma_of_three_le`, and
  `CongruenceSubgroup.two_mul_degree_compactifiedQuotientMap_Gamma_mul_prod_primeFactors`:
  the degree of `X(N) → X(1)` for `N ∣ 2` and for `N ≥ 3`.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Exercise 1.2.3 and §3.1.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971], §1.6.
-/

public noncomputable section

open TauCeti.RiemannSurface CongruenceSubgroup
open scoped MatrixGroups

namespace Subgroup

variable (H : Subgroup SL(2, ℤ))

/-- **The degree of `X(H) → X(1)`.** For a finite-index subgroup `H ≤ SL(2, ℤ)`, the map of
compactified modular curves induced by `H ≤ SL(2, ℤ)` has degree `[SL(2, ℤ) : ±H]`, which is the
index of the image of `H` in `PSL(2, ℤ)` (`Subgroup.index_map_mk'_eq_index_sup`). -/
theorem degree_compactifiedQuotientMap_map_sl2zToPSL2R [H.FiniteIndex] :
    degree (compactifiedQuotientMap H.map_sl2zToPSL2R_le_range_psl2zToPSL2R) =
      H.withCenter.index := by
  rw [degree_compactifiedQuotientMap, ← relIndex, relIndex_map_sl2zToPSL2R]

end Subgroup

namespace CongruenceSubgroup

variable (N : ℕ) [NeZero N]

/-! ### `X₀(N) → X(1)` -/

/-- **The degree of `X₀(N) → X(1)`** is `[SL(2, ℤ) : Γ₀(N)]`: as `-I ∈ Γ₀(N)`, no factor `2`
is lost on passing to `PSL(2, ℤ)`. -/
theorem degree_compactifiedQuotientMap_Gamma0 :
    degree (Subgroup.compactifiedQuotientMap
      (Gamma0 N).map_sl2zToPSL2R_le_range_psl2zToPSL2R) = (Gamma0 N).index := by
  rw [Subgroup.degree_compactifiedQuotientMap_map_sl2zToPSL2R, Gamma0_withCenter_index]

/-- **The degree of `X₀(N) → X(1)` is `N ∏_{p ∣ N} (1 + 1/p)`**, with the denominators
cleared. -/
theorem degree_compactifiedQuotientMap_Gamma0_mul_prod_primeFactors :
    degree (Subgroup.compactifiedQuotientMap
      (Gamma0 N).map_sl2zToPSL2R_le_range_psl2zToPSL2R) *
        ∏ p ∈ N.primeFactors, p = N * ∏ p ∈ N.primeFactors, (p + 1) := by
  rw [degree_compactifiedQuotientMap_Gamma0, Gamma0_index_mul_prod_primeFactors]

/-- At prime level `p`, the map `X₀(p) → X(1)` has degree `p + 1`. -/
theorem degree_compactifiedQuotientMap_Gamma0_prime (hp : N.Prime) :
    degree (Subgroup.compactifiedQuotientMap
      (Gamma0 N).map_sl2zToPSL2R_le_range_psl2zToPSL2R) = N + 1 := by
  rw [degree_compactifiedQuotientMap_Gamma0, Gamma0_prime_index N hp]

/-! ### `X₁(N) → X(1)` -/

/-- For `N ∣ 2` (`N ∈ {1, 2}`), `-I ∈ Γ₁(N)`, so the map `X₁(N) → X(1)` has degree
`[SL(2, ℤ) : Γ₁(N)]`. -/
theorem degree_compactifiedQuotientMap_Gamma1_of_dvd_two (hN : N ∣ 2) :
    degree (Subgroup.compactifiedQuotientMap
      (Gamma1 N).map_sl2zToPSL2R_le_range_psl2zToPSL2R) = (Gamma1 N).index := by
  rw [Subgroup.degree_compactifiedQuotientMap_map_sl2zToPSL2R,
    Gamma1_withCenter_index_of_dvd_two hN]

/-- **The degree of `X₁(N) → X(1)` for `N ≥ 3`** is half of `[SL(2, ℤ) : Γ₁(N)]`: there
`-I ∉ Γ₁(N)`, so each coset by the image of `Γ₁(N)` in `PSL(2, ℤ)` comes from two cosets of
`Γ₁(N)`. -/
theorem two_mul_degree_compactifiedQuotientMap_Gamma1 (hN : 3 ≤ N) :
    2 * degree (Subgroup.compactifiedQuotientMap
      (Gamma1 N).map_sl2zToPSL2R_le_range_psl2zToPSL2R) = (Gamma1 N).index := by
  rw [Subgroup.degree_compactifiedQuotientMap_map_sl2zToPSL2R,
    two_mul_Gamma1_withCenter_index hN]

/-- For `N ≥ 3`, the degree of `X₁(N) → X(1)` equals `[SL(2, ℤ) : Γ₁(N)] / 2`. -/
theorem degree_compactifiedQuotientMap_Gamma1_of_three_le (hN : 3 ≤ N) :
    degree (Subgroup.compactifiedQuotientMap
      (Gamma1 N).map_sl2zToPSL2R_le_range_psl2zToPSL2R) = (Gamma1 N).index / 2 := by
  rw [Subgroup.degree_compactifiedQuotientMap_map_sl2zToPSL2R,
    Gamma1_withCenter_index_of_three_le hN]

/-- **Closed-form degree of `X₁(N) → X(1)` for `N ≥ 3`**, with denominators cleared:
`2 · deg(X₁(N) → X(1)) · ∏_{p ∣ N} p² = N² · ∏_{p ∣ N} (p² - 1)`. -/
theorem two_mul_degree_compactifiedQuotientMap_Gamma1_mul_prod_primeFactors (hN : 3 ≤ N) :
    2 * degree (Subgroup.compactifiedQuotientMap
      (Gamma1 N).map_sl2zToPSL2R_le_range_psl2zToPSL2R) *
        ∏ p ∈ N.primeFactors, p ^ 2 =
      N ^ 2 * ∏ p ∈ N.primeFactors, (p ^ 2 - 1) := by
  rw [two_mul_degree_compactifiedQuotientMap_Gamma1 N hN, Gamma1_index_mul_prod_primeFactors]

/-- For an odd prime `N` (`N ≠ 2`), the map `X₁(N) → X(1)` has degree `(N² - 1) / 2`
(at `N = 2`, `degree_compactifiedQuotientMap_Gamma1_of_dvd_two` gives `2² - 1 = 3`). -/
theorem degree_compactifiedQuotientMap_Gamma1_prime (hp : N.Prime) (hN : N ≠ 2) :
    degree (Subgroup.compactifiedQuotientMap
      (Gamma1 N).map_sl2zToPSL2R_le_range_psl2zToPSL2R) = (N ^ 2 - 1) / 2 := by
  have h3 : 3 ≤ N := by have := hp.two_le; omega
  rw [degree_compactifiedQuotientMap_Gamma1_of_three_le N h3, Gamma1_prime_index N hp]

/-! ### `X(N) → X(1)` -/

/-- For `N ∣ 2` (`N ∈ {1, 2}`), `-I ∈ Γ(N)`, so the map `X(N) → X(1)` has degree
`[SL(2, ℤ) : Γ(N)]`. -/
theorem degree_compactifiedQuotientMap_Gamma_of_dvd_two (hN : N ∣ 2) :
    degree (Subgroup.compactifiedQuotientMap
      (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R) = (Gamma N).index := by
  rw [Subgroup.degree_compactifiedQuotientMap_map_sl2zToPSL2R,
    Gamma_withCenter_index_of_dvd_two hN]

/-- **The degree of `X(N) → X(1)` for `N ≥ 3`** is half of `[SL(2, ℤ) : Γ(N)]`: for `N ≥ 3`,
`-I ∉ Γ(N)`, so each projective coset comes from two cosets of `Γ(N)`. -/
theorem two_mul_degree_compactifiedQuotientMap_Gamma (hN : 3 ≤ N) :
    2 * degree (Subgroup.compactifiedQuotientMap
      (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R) = (Gamma N).index := by
  rw [Subgroup.degree_compactifiedQuotientMap_map_sl2zToPSL2R,
    two_mul_Gamma_withCenter_index hN]

/-- For `N ≥ 3`, the degree of `X(N) → X(1)` equals `[SL(2, ℤ) : Γ(N)] / 2`. -/
theorem degree_compactifiedQuotientMap_Gamma_of_three_le (hN : 3 ≤ N) :
    degree (Subgroup.compactifiedQuotientMap
      (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R) = (Gamma N).index / 2 := by
  rw [Subgroup.degree_compactifiedQuotientMap_map_sl2zToPSL2R,
    Gamma_withCenter_index_of_three_le hN]

/-- **Closed-form degree of `X(N) → X(1)` for `N ≥ 3`**, with denominators cleared:
`2 · deg(X(N) → X(1)) · ∏_{p ∣ N} p² = N³ · ∏_{p ∣ N} (p² - 1)`. -/
theorem two_mul_degree_compactifiedQuotientMap_Gamma_mul_prod_primeFactors (hN : 3 ≤ N) :
    2 * degree (Subgroup.compactifiedQuotientMap
      (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R) *
        ∏ p ∈ N.primeFactors, p ^ 2 =
      N ^ 3 * ∏ p ∈ N.primeFactors, (p ^ 2 - 1) := by
  rw [two_mul_degree_compactifiedQuotientMap_Gamma N hN, Gamma_index_mul_prod_primeFactors]

/-- For an odd prime `N` (`N ≠ 2`), the map `X(N) → X(1)` has degree `(N * (N² - 1)) / 2`
(at `N = 2`, `degree_compactifiedQuotientMap_Gamma_of_dvd_two` gives `2 * (2² - 1) = 6`). -/
theorem degree_compactifiedQuotientMap_Gamma_prime (hp : N.Prime) (hN : N ≠ 2) :
    degree (Subgroup.compactifiedQuotientMap
      (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R) = (N * (N ^ 2 - 1)) / 2 := by
  have h3 : 3 ≤ N := by have := hp.two_le; omega
  rw [degree_compactifiedQuotientMap_Gamma_of_three_le N h3, Gamma_prime_index N hp]

end CongruenceSubgroup
