/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Basic
public import TauCeti.NumberTheory.Padics.Measure.ExtendCoefficients.Basic

/-!
# Integral lattices of measures

For measures on a profinite space and a closed-unit-ball coefficient embedding into a complete
ultrametric normed field `K`, a single power of any nonzero `π : K` with `‖π‖ < 1` carries the
whole measure into the range of coefficient extension. This is
`AbstractMeasure.exists_inv_pow_smul_extendCoefficients_eq_of_norm_lt_one`.

For measures on a profinite space with coefficients in `ℚ_p`, the specialization
`AbstractMeasure.exists_inv_pow_smul_extendCoefficients_eq` uses powers of `p` and coefficient
extension from `ℤ_p`. After scaling, its values on all continuous `ℤ_p`-valued test functions
are integral.

## References

* J. Rodrigues Jacinto and C. Williams,
  [*An introduction to p-adic L-functions*](https://doi.org/10.2140/ent.2025.4.101),
  Remark 3.28(1).
-/

public section

open scoped AbstractMeasure

namespace AbstractMeasure

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

variable [T2Space X] [TotallyDisconnectedSpace X]

/-- On a profinite space, a single power of a nonzero scalar of norm less than `1` puts the
whole measure in the image of coefficient extension along a closed-unit-ball embedding. -/
theorem exists_inv_pow_smul_extendCoefficients_eq_of_norm_lt_one {K O : Type*}
    [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CommRing O]
    [TopologicalSpace O] [IsTopologicalRing O] (ν : D(X, K)) {j : O →+* K}
    (hj : ∀ a, ‖j a‖ ≤ 1) (hje : Topology.IsEmbedding j)
    (hjr : Metric.closedBall 0 1 ⊆ Set.range j) {π : K} (hπ : π ≠ 0) (hπnorm : ‖π‖ < 1) :
    ∃ (n : ℕ) (μ : D(X, O)), (π ^ n)⁻¹ • extendCoefficients j hj μ = ν := by
  let := NontriviallyNormedField.ofNormNeOne ⟨π, hπ, hπnorm.ne⟩
  have hpos : 0 < 1 + ‖toCLMEquiv ν‖ := by positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hpos) hπnorm
  have hnν : ‖π‖ ^ n * ‖toCLMEquiv ν‖ ≤ 1 := by
    calc
      _ ≤ (1 + ‖toCLMEquiv ν‖)⁻¹ * (1 + ‖toCLMEquiv ν‖) :=
        mul_le_mul hn.le (le_add_of_nonneg_left zero_le_one) (norm_nonneg _) (by positivity)
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  have hν : ‖toCLMEquiv (π ^ n • ν)‖ ≤ 1 := by
    simpa only [map_smul, norm_smul, norm_pow] using hnν
  obtain ⟨μ, hμ⟩ := (mem_range_extendCoefficients_iff hj hje hjr).2 hν
  exact ⟨n, μ, by rw [hμ, inv_smul_smul₀ (pow_ne_zero n hπ)]⟩

variable {p : ℕ} [Fact p.Prime]

/-- A single power of `p` puts the whole bounded rational p-adic measure in the image of
extension of coefficients from `ℤ_p`. After scaling, its values on all continuous `ℤ_p`-valued
test functions are integral. -/
theorem exists_inv_pow_smul_extendCoefficients_eq (ν : D(X, ℚ_[p])) :
    ∃ (n : ℕ) (μ : D(X, ℤ_[p])),
      ((p : ℚ_[p]) ^ n)⁻¹ •
        extendCoefficients PadicInt.Coe.ringHom PadicInt.norm_coe_ringHom_le_one μ = ν := by
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  exact exists_inv_pow_smul_extendCoefficients_eq_of_norm_lt_one ν
    PadicInt.norm_coe_ringHom_le_one PadicInt.isEmbedding_coe_ringHom
    TauCeti.range_padicInt_coe_ringHom.superset hp (Padic.norm_p_lt_one (p := p))

end AbstractMeasure
