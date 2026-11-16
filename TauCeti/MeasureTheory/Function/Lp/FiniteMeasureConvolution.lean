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
# Convolution with an integrable kernel on `Lᵖ` of a finite measure

Let `G` be an additive group with a finite right-invariant measure `μ`, such as the Haar
probability measure of the torus. For an integrable kernel `k : G → ℂ`, Young's inequality
`‖k ⋆ f‖_p ≤ ‖k‖₁ ‖f‖_p` (`MeasureTheory.eLpNorm_convolution_le`) makes convolution with `k` a
bounded operator on `Lᵖ(G, μ)` for every `1 ≤ p ≤ ∞`, of norm at most `‖k‖₁`.

The operator is defined through the pointwise convolution `(k ⋆ f)(x) = ∫ k(t) f(x - t) dμ(t)`,
which exists almost everywhere because `k` and `f ∈ Lᵖ ⊆ L¹` are integrable. Unlike the
`Lᵖ`-valued Bochner integral `MeasureTheory.Lp.convolutionL`, this covers `p = ∞` as well.

## Main declarations

* `MeasureTheory.Integrable.memLp_convolution`, `MeasureTheory.Integrable.eLpNorm_convolution_le`:
  convolution with `k` maps `Lᵖ` to itself, with `‖k ⋆ f‖_p ≤ ‖k‖₁ ‖f‖_p`.
* `MeasureTheory.Integrable.convolutionLp`: convolution with `k` as a continuous linear operator
  on `Lᵖ`.
* `MeasureTheory.Integrable.coeFn_convolutionLp`: the operator is represented by the pointwise
  convolution.
* `MeasureTheory.Integrable.norm_convolutionLp_le`: its operator norm is at most `‖k‖₁`.
-/

public section

noncomputable section

open MeasureTheory ContinuousLinearMap
open scoped ENNReal Convolution

namespace MeasureTheory.Integrable

variable {G : Type*} [AddGroup G] [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
  {μ : Measure G} [μ.IsAddRightInvariant] {k : G → ℂ} (hk : Integrable k μ)
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

include hk

section SFinite

variable [SFinite μ]

/-- **Young's inequality for an integrable kernel.** Convolution with `k` satisfies
`‖k ⋆ f‖_p ≤ ‖k‖₁ ‖f‖_p` on `Lᵖ(G, μ)`. -/
theorem eLpNorm_convolution_le (f : Lp ℂ p μ) :
    eLpNorm (k ⋆[lsmul ℂ ℂ, μ] (f : G → ℂ)) p μ ≤
      ENNReal.ofReal (∫ z, ‖k z‖ ∂μ) * eLpNorm f p μ := by
  have hL : ‖lsmul ℂ ℂ (E := ℂ)‖ₑ ≤ 1 := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_one.2 opNorm_lsmul_le
  calc _ ≤ ‖lsmul ℂ ℂ (E := ℂ)‖ₑ * eLpNorm k 1 μ * eLpNorm f p μ :=
        _root_.MeasureTheory.eLpNorm_convolution_le _ hk.1 (Lp.aestronglyMeasurable f) Fact.out
    _ ≤ _ := by
        rw [eLpNorm_one_eq_lintegral_eNorm hk.1, ← ofReal_integral_norm_eq_lintegral_eNorm hk,
          mul_assoc]
        exact mul_le_of_le_one_left zero_le hL

/-- Convolution with an integrable kernel `k` maps `Lᵖ(G, μ)` to itself. -/
theorem memLp_convolution (f : Lp ℂ p μ) : MemLp (k ⋆[lsmul ℂ ℂ, μ] (f : G → ℂ)) p μ :=
  (hk.eLpNorm_convolution_le f).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top f))

end SFinite

variable [IsFiniteMeasure μ]

variable (p) in
/-- **Convolution with an integrable kernel on `Lᵖ(G, μ)`** of a finite measure, `1 ≤ p ≤ ∞`, as
a bounded operator of norm at most `‖k‖₁` (`MeasureTheory.Integrable.norm_convolutionLp_le`). -/
def convolutionLp : Lp ℂ p μ →L[ℂ] Lp ℂ p μ :=
  LinearMap.mkContinuous
    { toFun f := (hk.memLp_convolution f).toLp _
      map_add' f g := by
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
      exact ENNReal.toReal_mono (by finiteness) (hk.eLpNorm_convolution_le f)

/-- The operator `hk.convolutionLp p` is convolution with `k`. -/
theorem coeFn_convolutionLp (f : Lp ℂ p μ) :
    hk.convolutionLp p f =ᵐ[μ] k ⋆[lsmul ℂ ℂ, μ] (f : G → ℂ) :=
  (hk.memLp_convolution f).coeFn_toLp

variable (p) in
/-- Convolution with `k` on `Lᵖ(G, μ)` has operator norm at most `‖k‖₁`. -/
theorem norm_convolutionLp_le : ‖hk.convolutionLp p‖ ≤ ∫ z, ‖k z‖ ∂μ :=
  LinearMap.mkContinuous_norm_le _ (integral_nonneg fun _ ↦ norm_nonneg _) _

end MeasureTheory.Integrable
