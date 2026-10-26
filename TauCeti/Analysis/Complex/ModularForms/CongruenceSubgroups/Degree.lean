/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Degree
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

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

For `Γ₀(N)`, which contains `-I`, the degree is `[SL(2, ℤ) : Γ₀(N)] = N ∏_{p ∣ N} (1 + 1/p)`;
for `Γ₁(N)` with `N ≥ 3`, which does not, it is half of `[SL(2, ℤ) : Γ₁(N)]`. This degree is
the quantity `d` in the genus formula `g = 1 + d/12 - ε₂/4 - ε₃/3 - ε∞/2` for `X(H)`.

## Main statements

* `Subgroup.degree_compactifiedQuotientMap_map_sl2zToPSL2R`: the map `X(H) → X(1)` has degree
  `[SL(2, ℤ) : ±H]`.
* `CongruenceSubgroup.degree_compactifiedQuotientMap_Gamma0` and
  `CongruenceSubgroup.degree_compactifiedQuotientMap_Gamma0_mul_prod_primeFactors`: the degree
  of `X₀(N) → X(1)` is `[SL(2, ℤ) : Γ₀(N)] = N ∏_{p ∣ N} (1 + 1/p)`.
* `CongruenceSubgroup.two_mul_degree_compactifiedQuotientMap_Gamma1`: for `N ≥ 3` the degree of
  `X₁(N) → X(1)` is half of `[SL(2, ℤ) : Γ₁(N)]`.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Exercise 1.2.3 and §3.1.
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

/-- **The degree of `X₀(N) → X(1)`** is `[SL(2, ℤ) : Γ₀(N)]`: as `-I ∈ Γ₀(N)`, no factor `2`
is lost on passing to `PSL(2, ℤ)`. -/
theorem degree_compactifiedQuotientMap_Gamma0 :
    degree (Subgroup.compactifiedQuotientMap
      (Gamma0 N).map_sl2zToPSL2R_le_range_psl2zToPSL2R) = (Gamma0 N).index := by
  rw [Subgroup.degree_compactifiedQuotientMap_map_sl2zToPSL2R,
    le_antisymm (withCenter_le_Gamma0 le_rfl) (Gamma0 N).le_withCenter]

/-- **The degree of `X₀(N) → X(1)` is `N ∏_{p ∣ N} (1 + 1/p)`**, with the denominators
cleared. -/
theorem degree_compactifiedQuotientMap_Gamma0_mul_prod_primeFactors :
    degree (Subgroup.compactifiedQuotientMap
      (Gamma0 N).map_sl2zToPSL2R_le_range_psl2zToPSL2R) *
        ∏ p ∈ N.primeFactors, p = N * ∏ p ∈ N.primeFactors, (p + 1) := by
  rw [degree_compactifiedQuotientMap_Gamma0, Gamma0_index_mul_prod_primeFactors (NeZero.ne N)]

/-- **The degree of `X₁(N) → X(1)` for `N ≥ 3`** is half of `[SL(2, ℤ) : Γ₁(N)]`: there
`-I ∉ Γ₁(N)`, so each coset by the image of `Γ₁(N)` in `PSL(2, ℤ)` comes from two cosets of
`Γ₁(N)`. -/
theorem two_mul_degree_compactifiedQuotientMap_Gamma1 (hN : 3 ≤ N) :
    2 * degree (Subgroup.compactifiedQuotientMap
      (Gamma1 N).map_sl2zToPSL2R_le_range_psl2zToPSL2R) = (Gamma1 N).index := by
  have h : (-1 : SL(2, ℤ)) ∉ Gamma1 N := fun h ↦ by
    have := Nat.le_of_dvd two_pos (neg_one_mem_Gamma1_iff.mp h)
    omega
  rw [Subgroup.degree_compactifiedQuotientMap_map_sl2zToPSL2R,
    TauCeti.ModularForm.index_eq_two_mul_index_withCenter_of_neg_one_notMem h]

end CongruenceSubgroup
