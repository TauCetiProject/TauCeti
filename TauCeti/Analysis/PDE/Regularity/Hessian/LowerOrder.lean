/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# The lower-order terms of a second-order operator in `Lᵖ`

For `u ∈ W^{2,p}(Ω)` on a finite-dimensional real inner product space and bounded measurable
coefficients `b` and `c`, the lower-order part `⟪b, ∇u⟫ + c u` of a second-order operator applied
to `u` lies in `Lᵖ`, with norm at most `β ‖∇u‖ + γ ‖u‖` when `‖b‖ ≤ β` and `|c| ≤ γ`
(`TauCeti.Wkp.memLp_inner_add_mul_and_lpNorm_le`). The `W^{2,p}` estimates for non-divergence-form
equations use it to move these terms to the right side of the equation.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open MeasureTheory TopologicalSpace
open scoped ENNReal InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The lower-order terms lie in `Lᵖ`.** On a set `S ⊆ Ω` where `‖b‖ ≤ β` and `|c| ≤ γ`
almost everywhere, the lower-order part `⟪b, ∇u⟫ + c u` of the operator applied to
`u ∈ W^{2,p}(Ω)` lies in `Lᵖ(S)`, with norm at most `β ‖∇u‖_{Lᵖ(S)} + γ ‖u‖_{Lᵖ(S)}`. -/
theorem memLp_inner_add_mul_and_lpNorm_le {S : Set E} (hS : S ⊆ Omega)
    (u : Wkp mu Omega p 2) {b : E → E} {c : E → ℝ} {β γ : ℝ}
    (hb : AEStronglyMeasurable b (mu.restrict S)) (hbβ : ∀ᵐ x ∂(mu.restrict S), ‖b x‖ ≤ β)
    (hc : AEStronglyMeasurable c (mu.restrict S)) (hcγ : ∀ᵐ x ∂(mu.restrict S), |c x| ≤ γ) :
    MemLp (fun x => ⟪b x, iteratedGradient 0 (lowerOrder 1 u) x⟫_ℝ + c x * value 2 u x) p
        (mu.restrict S) ∧
      lpNorm (fun x => ⟪b x, iteratedGradient 0 (lowerOrder 1 u) x⟫_ℝ + c x * value 2 u x) p
          (mu.restrict S) ≤
        β * lpNorm (iteratedGradient 0 (lowerOrder 1 u)) p (mu.restrict S) +
          γ * lpNorm (value 2 u) p (mu.restrict S) := by
  set G := iteratedGradient 0 (lowerOrder 1 u)
  set V := value 2 u
  have hG : MemLp G p (mu.restrict S) :=
    (Lp.memLp G).mono_measure (Measure.restrict_mono hS le_rfl)
  have hV : MemLp V p (mu.restrict S) :=
    (Lp.memLp V).mono_measure (Measure.restrict_mono hS le_rfl)
  have hdm : AEStronglyMeasurable (fun x => ⟪b x, G x⟫_ℝ) (mu.restrict S) :=
    hb.inner hG.aestronglyMeasurable
  have hzm : AEStronglyMeasurable (fun x => c x * V x) (mu.restrict S) :=
    hc.mul hV.aestronglyMeasurable
  have hdle : ∀ᵐ x ∂(mu.restrict S), ‖⟪b x, G x⟫_ℝ‖ ≤ β * ‖G x‖ := hbβ.mono fun x hx => by
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  have hzle : ∀ᵐ x ∂(mu.restrict S), ‖c x * V x‖ ≤ γ * ‖V x‖ := hcγ.mono fun x hx => by
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  have hd : MemLp (fun x => ⟪b x, G x⟫_ℝ) p (mu.restrict S) := hG.of_le_mul hdm hdle
  refine ⟨hd.add (hV.of_le_mul hzm hzle), (lpNorm_add_le hd Fact.out).trans ?_⟩
  exact add_le_add (lpNorm_le_mul_lpNorm_of_ae_le_mul hdm hG hdle)
    (lpNorm_le_mul_lpNorm_of_ae_le_mul hzm hV hzle)

end TauCeti.Wkp
