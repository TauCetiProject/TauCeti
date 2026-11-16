/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import TauCeti.Analysis.Convolution.Young

/-!
# Convolution with a continuous kernel on `Lᵖ` of a compact group

Let `G` be a compact additive group with a finite right-invariant measure `μ`, such as the Haar
probability measure of the torus. A continuous kernel `k : C(G, ℂ)` is integrable, so by Young's
inequality `‖k ⋆ f‖_p ≤ ‖k‖₁ ‖f‖_p` (`MeasureTheory.eLpNorm_convolution_le`) convolution with `k`
is a bounded operator on `Lᵖ(G, μ)` for every `1 ≤ p ≤ ∞`, of norm at most `‖k‖₁`.

The operator is defined through the pointwise convolution `(k ⋆ f)(x) = ∫ k(t) f(x - t) dμ(t)`,
which exists almost everywhere because `k` and `f ∈ Lᵖ ⊆ L¹` are integrable. Unlike the
`Lᵖ`-valued Bochner integral `MeasureTheory.Lp.convolutionL`, this covers `p = ∞` as well.

## Main declarations

* `ContinuousMap.memLp_convolution`, `ContinuousMap.eLpNorm_convolution_le`: convolution with `k`
  maps `Lᵖ` to itself, with `‖k ⋆ f‖_p ≤ ‖k‖₁ ‖f‖_p`.
* `ContinuousMap.convolutionLp`: convolution with `k` as a continuous linear operator on `Lᵖ`.
* `ContinuousMap.coeFn_convolutionLp`: the operator is represented by the pointwise convolution.
* `ContinuousMap.norm_convolutionLp_le`: its operator norm is at most `‖k‖₁`.
-/

public section

noncomputable section

open MeasureTheory ContinuousLinearMap
open scoped ENNReal Convolution

namespace ContinuousMap

variable {G : Type*} [AddGroup G] [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G]
  [OpensMeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
  (k : C(G, ℂ)) (μ : Measure G) [IsFiniteMeasure μ] [μ.IsAddRightInvariant]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Young's inequality for a continuous kernel on a compact group.** Convolution with `k`
satisfies `‖k ⋆ f‖_p ≤ ‖k‖₁ ‖f‖_p` on `Lᵖ(G, μ)`. -/
theorem eLpNorm_convolution_le (f : Lp ℂ p μ) :
    eLpNorm (⇑k ⋆[lsmul ℂ ℂ, μ] (f : G → ℂ)) p μ ≤
      ENNReal.ofReal (∫ z, ‖k z‖ ∂μ) * eLpNorm f p μ := by
  have hL : ‖lsmul ℂ ℂ (E := ℂ)‖ₑ ≤ 1 := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_one.2 opNorm_lsmul_le
  have hk : eLpNorm k 1 μ = ENNReal.ofReal (∫ z, ‖k z‖ ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_eNorm k.continuous.aestronglyMeasurable,
      ofReal_integral_norm_eq_lintegral_eNorm
      (k.continuous.integrable_of_hasCompactSupport (.of_compactSpace _))]
  calc _ ≤ ‖lsmul ℂ ℂ (E := ℂ)‖ₑ * eLpNorm k 1 μ * eLpNorm f p μ :=
        MeasureTheory.eLpNorm_convolution_le _ k.continuous.aestronglyMeasurable
          (Lp.aestronglyMeasurable f) Fact.out
    _ ≤ _ := by
        rw [hk, mul_assoc]
        exact mul_le_of_le_one_left zero_le hL

/-- Convolution with a continuous kernel `k` on a compact group maps `Lᵖ(G, μ)` to itself. -/
theorem memLp_convolution (f : Lp ℂ p μ) : MemLp (⇑k ⋆[lsmul ℂ ℂ, μ] (f : G → ℂ)) p μ :=
  (eLpNorm_convolution_le k μ f).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top f))

variable (p) in
/-- **Convolution with a continuous kernel on `Lᵖ(G, μ)`** of a compact group, `1 ≤ p ≤ ∞`, as a
bounded operator of norm at most `‖k‖₁` (`ContinuousMap.norm_convolutionLp_le`). -/
def convolutionLp : Lp ℂ p μ →L[ℂ] Lp ℂ p μ :=
  LinearMap.mkContinuous
    { toFun f := (memLp_convolution k μ f).toLp _
      map_add' f g := by
        have hk := k.continuous.integrable_of_hasCompactSupport (μ := μ) (.of_compactSpace _)
        have hex (h : Lp ℂ p μ) :=
          hk.ae_convolution_exists (lsmul ℂ ℂ) ((Lp.memLp h).integrable Fact.out)
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ ?_
        rw [convolution_congr _ (.rfl) (Lp.coeFn_add f g)]
        filter_upwards [hex f, hex g] with x hf hg using hf.distrib_add hg
      map_smul' c f := by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ (.of_eq ?_)
        rw [convolution_congr _ (.rfl) (Lp.coeFn_smul c f)]
        exact convolution_smul }
    (∫ z, ‖k z‖ ∂μ) fun f ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp]
      rw [Lp.norm_def, ← ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _),
        ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (by finiteness) (eLpNorm_convolution_le k μ f)

/-- The operator `k.convolutionLp μ p` is convolution with `k`. -/
theorem coeFn_convolutionLp (f : Lp ℂ p μ) :
    k.convolutionLp μ p f =ᵐ[μ] ⇑k ⋆[lsmul ℂ ℂ, μ] (f : G → ℂ) :=
  (memLp_convolution k μ f).coeFn_toLp

variable (p) in
/-- Convolution with `k` on `Lᵖ(G, μ)` has operator norm at most `‖k‖₁`. -/
theorem norm_convolutionLp_le : ‖k.convolutionLp μ p‖ ≤ ∫ z, ‖k z‖ ∂μ :=
  LinearMap.mkContinuous_norm_le _ (integral_nonneg fun _ ↦ norm_nonneg _) _

end ContinuousMap
