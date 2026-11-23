/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.Convergence
public import Mathlib.Analysis.Meromorphic.Divisor

/-!
# Genus-one products with prescribed weighted zeros

Let `S ⊆ ℂ \ {0}` carry natural multiplicities `m : S → ℕ` with
`∑ ρ, m ρ / ‖ρ‖² < ∞`. The genus-one product

`P(z) = ∏' ρ : S, E₁(z / ρ) ^ m ρ`

converges locally uniformly on the plane, both as written and over the repeated index
`Σ ρ : S, Fin (m ρ)`, to an entire function with `P 0 = 1` whose analytic order is `m ρ` at each
`ρ ∈ S` and zero elsewhere (`Complex.analyticOrderAt_tprod_weierstrassFactor_one_inv_mul_pow`);
its native divisor has the same values. Zero multiplicities are allowed: such points contribute
the factor `1`. No enumeration of `S`, countability or compact finiteness is assumed; the
summability alone controls the product.

The divisor-input form `TauCeti.exists_entire_genusOne_product_of_divisor` takes a nonnegative
native divisor `D` on the plane with `D 0 = 0` and `∑ ρ, D ρ / ‖ρ‖² < ∞` and produces a
normalized entire function whose native divisor is exactly `D`. This realizes, for instance,
the divisor of any entire function nonzero at the origin whose zeros have convergent
inverse-square sum, without a growth hypothesis.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 14.3.
-/

public section

open Filter Set Topology

namespace Complex

variable {S : Set ℂ} (m : S → ℕ) (hsum : Summable (fun ρ : S ↦ (m ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2))

include hsum

open scoped Classical in
/-- The analytic order of the genus-one product over a weighted point set avoiding `0` is the
prescribed multiplicity on the set and zero off it. -/
theorem analyticOrderAt_tprod_weierstrassFactor_one_inv_mul_pow (hzero : (0 : ℂ) ∉ S) (z : ℂ) :
    analyticOrderAt (fun w ↦ ∏' ρ : S, weierstrassFactor 1 ((ρ : ℂ)⁻¹ * w) ^ m ρ) z =
      if hz : z ∈ S then (m ⟨z, hz⟩ : ℕ∞) else 0 := by
  have hsum' : Summable (fun ρ : S ↦ (m ρ : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2) := by
    simpa only [norm_inv, inv_pow, div_eq_mul_inv] using hsum
  split_ifs with hz
  · have hz0 : z ≠ 0 := fun h ↦ hzero (h ▸ hz)
    exact analyticOrderAt_tprod_weierstrassFactor_one_pow_of_injective _ m hsum'
      (i := ⟨z, hz⟩) (inv_injective.comp Subtype.val_injective) (inv_mul_cancel₀ hz0)
  · rw [((differentiable_tprod_weierstrassFactor_one_pow _ m hsum').analyticAt
      z).analyticOrderAt_eq_zero, ne_eq, tprod_weierstrassFactor_one_pow_eq_zero_iff _ m hsum']
    rintro ⟨ρ, -, hρ⟩
    have hρ0 : (ρ : ℂ) ≠ 0 := by
      rintro h
      simp [h] at hρ
    exact hz (((inv_mul_eq_one₀ hρ0).mp hρ) ▸ ρ.property)

open scoped Classical in
/-- The native divisor of the genus-one product over a weighted point set avoiding `0` is the
prescribed multiplicity on the set and zero off it. -/
theorem divisor_tprod_weierstrassFactor_one_inv_mul_pow (hzero : (0 : ℂ) ∉ S) (z : ℂ) :
    MeromorphicOn.divisor (fun w ↦ ∏' ρ : S, weierstrassFactor 1 ((ρ : ℂ)⁻¹ * w) ^ m ρ)
      Set.univ z = if hz : z ∈ S then (m ⟨z, hz⟩ : ℤ) else 0 := by
  have hF := differentiable_tprod_weierstrassFactor_one_pow (fun ρ : S ↦ (ρ : ℂ)⁻¹) m
    (by simpa only [norm_inv, inv_pow, div_eq_mul_inv] using hsum)
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (fun w _ ↦ hF.analyticAt w) (Set.mem_univ z),
    analyticOrderAt_tprod_weierstrassFactor_one_inv_mul_pow m hsum hzero z]
  split_ifs <;> simp

end Complex

namespace TauCeti

open Complex

open scoped Classical in
/-- **Genus-one product with prescribed weighted zeros.** For `S ⊆ ℂ \ {0}` with natural
multiplicities `m` satisfying `∑ ρ, m ρ / ‖ρ‖² < ∞`, the products `∏ E₁(z / ρ) ^ m ρ` over `S`
and `∏ E₁(z / ρ)` over the repeated index `Σ ρ : S, Fin (m ρ)` converge locally uniformly on the
plane to one entire function `F` with `F 0 = 1`, whose analytic order and native divisor are
`m ρ` at each `ρ ∈ S` and zero elsewhere. -/
theorem exists_entire_genusOne_product (S : Set ℂ) (m : S → ℕ) (hzero : (0 : ℂ) ∉ S)
    (hsum : Summable (fun ρ : S ↦ (m ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2)) :
    ∃ F : ℂ → ℂ,
      HasProdLocallyUniformlyOn
        (fun (ρ : S) z ↦ weierstrassFactor 1 ((ρ : ℂ)⁻¹ * z) ^ m ρ) F Set.univ ∧
      HasProdLocallyUniformlyOn
        (fun (i : Σ ρ : S, Fin (m ρ)) z ↦ weierstrassFactor 1 ((i.1 : ℂ)⁻¹ * z)) F Set.univ ∧
      Differentiable ℂ F ∧ F 0 = 1 ∧
      ∀ z, analyticOrderAt F z = (if hz : z ∈ S then (m ⟨z, hz⟩ : ℕ∞) else 0) ∧
        MeromorphicOn.divisor F Set.univ z = (if hz : z ∈ S then (m ⟨z, hz⟩ : ℤ) else 0) := by
  have hsum' : Summable (fun ρ : S ↦ (m ρ : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2) := by
    simpa only [norm_inv, inv_pow, div_eq_mul_inv] using hsum
  exact ⟨_, hasProdLocallyUniformlyOn_weierstrassFactor_one_pow _ m hsum',
    hasProdLocallyUniformlyOn_sigma_weierstrassFactor_one _ m hsum',
    differentiable_tprod_weierstrassFactor_one_pow _ m hsum', by simp,
    fun z ↦ ⟨analyticOrderAt_tprod_weierstrassFactor_one_inv_mul_pow m hsum hzero z,
      divisor_tprod_weierstrassFactor_one_inv_mul_pow m hsum hzero z⟩⟩

/-- **Divisor realization by a genus-one product.** A nonnegative native divisor `D` on the
plane with `D 0 = 0` and `∑ ρ, D ρ / ‖ρ‖² < ∞` is the native divisor of the normalized entire
function `∏ E₁(z / ρ) ^ D ρ`, the product over the support of `D` converging locally uniformly on
the plane. -/
theorem exists_entire_genusOne_product_of_divisor
    (D : Function.locallyFinsuppWithin (Set.univ : Set ℂ) ℤ) (hD : 0 ≤ D) (hDzero : D 0 = 0)
    (hsum : Summable (fun ρ : D.support ↦ (D ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2)) :
    ∃ F : ℂ → ℂ,
      HasProdLocallyUniformlyOn
        (fun (ρ : D.support) z ↦ weierstrassFactor 1 ((ρ : ℂ)⁻¹ * z) ^ (D ρ).toNat) F
        Set.univ ∧
      Differentiable ℂ F ∧ F 0 = 1 ∧ MeromorphicOn.divisor F Set.univ = D := by
  have hcast (ρ : ℂ) : ((D ρ).toNat : ℤ) = D ρ := Int.toNat_of_nonneg (hD ρ)
  have hsum' : Summable (fun ρ : D.support ↦ ((D ρ).toNat : ℝ) / ‖(ρ : ℂ)‖ ^ 2) := by
    refine hsum.congr fun ρ ↦ ?_
    congr 1
    exact_mod_cast (hcast ρ).symm
  have hzero : (0 : ℂ) ∉ D.support := by simpa using hDzero
  obtain ⟨F, hF, -, hdiff, hF0, hdiv⟩ := exists_entire_genusOne_product _ _ hzero hsum'
  refine ⟨F, hF, hdiff, hF0, ?_⟩
  ext z
  rw [(hdiv z).2]
  split_ifs with hz
  · exact hcast z
  · exact (by simpa using hz : D z = 0).symm

end TauCeti
