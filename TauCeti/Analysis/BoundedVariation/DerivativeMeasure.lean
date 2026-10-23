/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.TotalVariation
public import TauCeti.Analysis.Distribution.OrderZero
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv

/-!
# The directional derivatives of a function of locally bounded variation are measures

Let `Ω` be an open set of a finite-dimensional real inner product space `E` and let `u : E → ℝ`.
For locally integrable `u`, the pairing of the directional derivative `∂_v u` with a test
function `φ` is `-∫ ∂_v φ * u`, and `∂_v φ` is the divergence of the test vector field `φ v`.
Hence the variational total variation `|Du|(Ω)` bounds it:
`|∫ ∂_v φ * u| ≤ ‖v‖ ‖φ‖_∞ |Du|(Ω)`
(`TestFunction.ofReal_abs_integral_lineDeriv_mul_le_totalVariationOn`).

The distributional derivative is taken of `Distribution.ofFun Ω u μ ⊤`. When `u` is locally
integrable on `Ω` this is integration against `u`, so `∂_v u (φ) = -∫ ∂_v φ * u`; otherwise
`Distribution.ofFun` is zero by convention, and so is its derivative.

If `u` has **locally finite variation** on `Ω`, meaning that every compact `K ⊆ Ω` has an open
neighbourhood `U` with `|Du|(U) < ∞`, this makes each distributional derivative
`∂_v u ∈ 𝓓'(Ω, ℝ)` a distribution of order zero. It is therefore a signed Radon measure: there
are regular measures `ν₁` and `ν₂` on `Ω`, finite on compact sets, with
`∂_v u (φ) = ∫ φ dν₁ - ∫ φ dν₂` for every test function `φ`
(`TauCeti.exists_regular_lineDeriv_ofFun_apply_eq`). No global finiteness of the variation is
needed, so this covers functions of locally bounded variation on unbounded open sets.

## Main results

* `TestFunction.ofReal_abs_integral_lineDeriv_mul_le_totalVariationOn`: the directional derivative
  pairing is bounded by `‖v‖ ‖φ‖_∞ |Du|(Ω)`.
* `TauCeti.exists_regular_lineDeriv_ofFun_apply_eq`: the directional derivatives of a function of
  locally finite variation on `Ω` are differences of regular measures on `Ω`.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.1.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.1 (the structure theorem for functions of locally bounded variation).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace TestFunction LineDeriv TauCeti
open scoped ENNReal Distributions BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] {μ : Measure E} {Ω : Opens E} {u : E → ℝ}

namespace TestFunction

/-- **The directional derivative is bounded by the total variation.** For a test function `φ` on
`Ω` and a direction `v`, `|∫ ∂_v φ * u| ≤ ‖v‖ ‖φ‖_∞ |Du|(Ω)`. -/
theorem ofReal_abs_integral_lineDeriv_mul_le_totalVariationOn (φ : 𝓓(Ω, ℝ)) (v : E) :
    ENNReal.ofReal |∫ x, ∂_{v} φ x * u x ∂μ| ≤
      ‖v‖ₑ * ‖(φ : E →ᵇ ℝ)‖ₑ * totalVariationOn μ Ω u := by
  -- `∂_v φ` is the divergence of the vector field `φ v`, which is bounded by `‖v‖ ‖φ‖_∞`.
  have h := ofReal_abs_integral_le_ofReal_mul_totalVariationOn (μ := μ) (u := u)
    (postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ v) φ) (c := ‖v‖ * ‖(φ : E →ᵇ ℝ)‖)
    fun x => by
      simpa [norm_smul, mul_comm] using
        mul_le_mul_of_nonneg_left ((φ : E →ᵇ ℝ).norm_coe_le_norm x) (norm_nonneg v)
  rwa [divergenceCLM_postcompCLM_toSpanSingleton, ENNReal.ofReal_mul (norm_nonneg v), ofReal_norm,
    ofReal_norm] at h

end TestFunction

namespace TauCeti

/-- **The directional derivatives of a function of locally finite variation are signed Radon
measures.** If every compact `K ⊆ Ω` has an open neighbourhood `U` on which `u` has finite total
variation, then for every direction `v` there are regular measures `ν₁` and `ν₂` on `Ω` with
`∂_v u (φ) = ∫ φ dν₁ - ∫ φ dν₂` for every test function `φ`, where `∂_v u` is the derivative of
the distribution `Distribution.ofFun Ω u μ ⊤`. If `u` is locally integrable on `Ω`, this is the
distributional derivative of `u`, `∂_v u (φ) = -∫ ∂_v φ * u`; otherwise `Distribution.ofFun` is
zero by convention and the statement is trivial. The measures are finite on compact subsets of
`Ω` but need not be finite. -/
theorem exists_regular_lineDeriv_ofFun_apply_eq [BorelSpace E]
    (hu : ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞)
    (v : E) :
    ∃ ν₁ ν₂ : Measure Ω, ν₁.Regular ∧ ν₂.Regular ∧
      ∀ φ : 𝓓(Ω, ℝ), ∂_{v} (Distribution.ofFun Ω u μ ⊤) φ = ∫ x, φ x ∂ν₁ - ∫ x, φ x ∂ν₂ := by
  refine (Distribution.forall_exists_abs_le_iff_exists_regular _).1 fun K hK hKΩ => ?_
  obtain ⟨U, hKU, hU⟩ := hu K hK hKΩ
  refine ⟨‖v‖ * (totalVariationOn μ U u).toReal, fun φ hφ => ?_⟩
  have hC : 0 ≤ ‖v‖ * (totalVariationOn μ U u).toReal := by positivity
  rw [Distribution.lineDerivOp_apply_apply]
  by_cases hli : LocallyIntegrableOn u Ω μ
  · -- The same function, as a test function on `U`.
    let φ' : 𝓓(U, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφ.trans hKU⟩
    have hφ' (x : E) : ∂_{v} φ' x = ∂_{v} φ x := by simp [φ']
    have h := ofReal_abs_integral_lineDeriv_mul_le_totalVariationOn (μ := μ) (u := u) φ' v
    simp_rw [hφ'] at h
    rw [Distribution.ofFun_apply hli]
    simp only [neg_apply, smul_eq_mul, neg_mul, integral_neg, abs_neg]
    have hfin : ‖v‖ₑ * ‖(φ' : E →ᵇ ℝ)‖ₑ * totalVariationOn μ U u ≠ ∞ := by
      simp [ENNReal.mul_eq_top, hU]
    refine ((ENNReal.ofReal_le_iff_le_toReal hfin).1 h).trans_eq ?_
    have hnorm : ‖(φ' : E →ᵇ ℝ)‖ = ‖(φ : E →ᵇ ℝ)‖ :=
      congrArg norm (BoundedContinuousFunction.ext fun x => by simp [φ'])
    simp only [ENNReal.toReal_mul, toReal_enorm, hnorm]
    ring
  · rw [Distribution.ofFun_eq_zero hli]
    simpa using mul_nonneg hC (norm_nonneg _)

end TauCeti
