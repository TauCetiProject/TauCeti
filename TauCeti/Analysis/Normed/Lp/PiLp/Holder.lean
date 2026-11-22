/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Basic.ENNReal.Holder
public import TauCeti.Analysis.Normed.Lp.PiLp.Basic
public import TauCeti.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.Analysis.Normed.Lp.LpEquiv
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Hölder inequalities for finite `Lᵖ` spaces

This file bridges the finite `Lᵖ` spaces `PiLp s (fun _ : ι ↦ ℝ)` to `MeasureTheory.eLpNorm` for
the counting measure (`PiLp.eNorm_toLp_eq_eLpNorm_count`) and deduces Hölder's inequality for
pointwise real products (`PiLp.norm_toLp_mul_le`), pointwise scalar products
(`PiLp.norm_toLp_smul_le`), and log-convex interpolation powers (`PiLp.norm_toLp_rpow_mul_rpow_le`).
-/

public section

open scoped ENNReal

namespace PiLp

variable {ι : Type*} [Fintype ι]

/-- For `1 ≤ s`, the `eNorm` of a vector in `PiLp s (fun _ : ι ↦ ℝ)` equals the `Lˢ` seminorm
of its coordinate function for the counting measure. -/
theorem eNorm_toLp_eq_eLpNorm_count {s : ℝ≥0∞} [Fact (1 ≤ s)] (f : ι → ℝ) :
    letI : MeasurableSpace ι := ⊤
    ‖WithLp.toLp s f‖ₑ = MeasureTheory.eLpNorm f s MeasureTheory.Measure.count := by
  let _ : MeasurableSpace ι := ⊤
  have _ : MeasurableSingletonClass ι := ⟨fun _ ↦ trivial⟩
  let F : lp (fun _ : ι ↦ ℝ) s := (lpPiLpₗᵢ (fun _ : ι ↦ ℝ) ℝ).symm (WithLp.toLp s f)
  have hnorm : ‖WithLp.toLp s f‖ₑ = ‖F‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, (lpPiLpₗᵢ (fun _ : ι ↦ ℝ) ℝ).symm.norm_map]
  exact hnorm.trans (lp.eLpNorm_count F).symm

/-- Hölder's inequality for finite `Lᵖ` norms of a pointwise real product over a Hölder triple
`p₀⁻¹ + p₁⁻¹ = r⁻¹`. -/
theorem norm_toLp_mul_le {p₀ p₁ r : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ r)]
    [ENNReal.HolderTriple p₀ p₁ r] (a b : ι → ℝ) :
    ‖WithLp.toLp r (fun i ↦ a i * b i)‖ ≤ ‖WithLp.toLp p₀ a‖ * ‖WithLp.toLp p₁ b‖ := by
  let _ : MeasurableSpace ι := ⊤
  have _ : MeasurableSingletonClass ι := ⟨fun _ ↦ trivial⟩
  have h : ‖WithLp.toLp r (fun i ↦ a i * b i)‖ₑ ≤
      ‖WithLp.toLp p₀ a‖ₑ * ‖WithLp.toLp p₁ b‖ₑ := by
    rw [eNorm_toLp_eq_eLpNorm_count, eNorm_toLp_eq_eLpNorm_count, eNorm_toLp_eq_eLpNorm_count]
    exact MeasureTheory.eLpNorm_smul_le_mul_eLpNorm (φ := a) (f := b)
      Measurable.of_discrete.aestronglyMeasurable Measurable.of_discrete.aestronglyMeasurable
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (norm_nonneg _) (norm_nonneg _))).1 h

/-- Hölder's inequality for finite `Lᵖ` norms of a pointwise scalar product over a Hölder triple
`p₀⁻¹ + p₁⁻¹ = r⁻¹`. -/
theorem norm_toLp_smul_le {p₀ p₁ r : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ r)]
    [ENNReal.HolderTriple p₀ p₁ r] {𝕜 : Type*} {β : ι → Type*} [NormedRing 𝕜]
    [∀ i, SeminormedAddCommGroup (β i)] [∀ i, Module 𝕜 (β i)] [∀ i, IsBoundedSMul 𝕜 (β i)]
    (a : ι → 𝕜) (x : ∀ i, β i) :
    ‖WithLp.toLp r (fun i ↦ a i • x i)‖ ≤ ‖WithLp.toLp p₀ a‖ * ‖WithLp.toLp p₁ x‖ := by
  refine (norm_mono (y := WithLp.toLp r fun i ↦ ‖a i‖ * ‖x i‖)
    fun i ↦ by simpa using norm_smul_le (a i) (x i)).trans ?_
  simpa only [norm_norm] using norm_toLp_mul_le (p₀ := p₀) (p₁ := p₁) (r := r)
    (fun i ↦ ‖a i‖) (fun i ↦ ‖x i‖)

private theorem inv_div_ofReal {s : ℝ≥0∞} {t : ℝ} (ht : 0 < t) :
    (s / ENNReal.ofReal t)⁻¹ = ENNReal.ofReal t * s⁻¹ := by
  rw [ENNReal.inv_div (.inl ENNReal.ofReal_ne_top) (.inl (ENNReal.ofReal_pos.2 ht).ne'),
    ENNReal.div_eq_inv_mul, mul_comm]

private theorem one_le_div_ofReal {s : ℝ≥0∞} (hs : 1 ≤ s) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    1 ≤ s / ENNReal.ofReal t := by
  rw [← ENNReal.inv_le_one, inv_div_ofReal ht0]
  exact mul_le_one' (ENNReal.ofReal_le_one.2 ht1) (ENNReal.inv_le_one.2 hs)

/-- Log-convex Hölder inequality for finite `Lᵖ` norms under the complex interpolation relation
`q⁻¹ = (1 - θ) / q₀ + θ / q₁` with `0 ≤ θ ≤ 1`. -/
theorem norm_toLp_rpow_mul_rpow_le {q₀ q₁ q : ℝ≥0∞} [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q)]
    {θ : ℝ} (hθ : θ ∈ Set.Icc 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) {a b : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ‖WithLp.toLp q (fun i ↦ a i ^ (1 - θ) * b i ^ θ)‖ ≤
      ‖WithLp.toLp q₀ a‖ ^ (1 - θ) * ‖WithLp.toLp q₁ b‖ ^ θ := by
  rcases eq_or_lt_of_le hθ.1 with rfl | hθ0
  · have hq_eq : q = q₀ := by
      simpa using congrArg Inv.inv hq
    subst hq_eq
    simp
  rcases eq_or_lt_of_le hθ.2 with rfl | hθ1
  · have hq_eq : q = q₁ := by
      simpa using congrArg Inv.inv hq
    subst hq_eq
    simp
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ1
  let p₀ := q₀ / ENNReal.ofReal (1 - θ)
  let p₁ := q₁ / ENNReal.ofReal θ
  have _ : Fact (1 ≤ p₀) := ⟨one_le_div_ofReal Fact.out h1θ (by linarith)⟩
  have _ : Fact (1 ≤ p₁) := ⟨one_le_div_ofReal Fact.out hθ0 hθ1.le⟩
  have _ : ENNReal.HolderTriple p₀ p₁ q := ⟨by rw [inv_div_ofReal h1θ, inv_div_ofReal hθ0, hq]⟩
  calc ‖WithLp.toLp q (fun i ↦ a i ^ (1 - θ) * b i ^ θ)‖
      ≤ ‖WithLp.toLp p₀ (fun i ↦ a i ^ (1 - θ))‖ * ‖WithLp.toLp p₁ (fun i ↦ b i ^ θ)‖ :=
        norm_toLp_mul_le (p₀ := p₀) (p₁ := p₁) (r := q) _ _
    _ = ‖WithLp.toLp q₀ a‖ ^ (1 - θ) * ‖WithLp.toLp q₁ b‖ ^ θ := by
        rw [norm_toLp_rpow_div_of_nonneg (zero_lt_one.trans_le Fact.out).ne' h1θ ha,
          norm_toLp_rpow_div_of_nonneg (zero_lt_one.trans_le Fact.out).ne' hθ0 hb]

end PiLp
