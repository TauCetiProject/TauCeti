/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Decision.Risk.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.Bind
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Real risk and garblings of statistical experiments

The risk of a randomized decision rule is the expected loss under the action distribution
induced by the sampling law. A garbling is a parameter-independent kernel applied to the
observation. A rule for the garbled experiment can be composed with that kernel to preserve its
action law and hence its risk at every parameter.

## References

* M. J. Schervish, *Theory of Statistics*, Springer (1995), §3.1.
* T. S. Ferguson, *Mathematical Statistics: A Decision Theoretic Approach*, Academic Press
  (1967), §1.5.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti

variable {Θ X Y Z A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z] [MeasurableSpace A]

/-- The expected real loss of a randomized rule at parameter `θ`, integrated against the
distribution of its action under the sampling law `P θ`. -/
noncomputable def risk (P : Θ → Measure X) (L : Θ → A → ℝ) (κ : Kernel X A) (θ : Θ) : ℝ :=
  ∫ a, L θ a ∂(κ ∘ₘ P θ)

/-- The integral defining the risk of a randomized rule. -/
theorem risk_def (P : Θ → Measure X) (L : Θ → A → ℝ) (κ : Kernel X A) (θ : Θ) :
    risk P L κ θ = ∫ a, L θ a ∂(κ ∘ₘ P θ) := (rfl)

variable {P : Θ → Measure X} {L : Θ → A → ℝ} {κ : Kernel X A} {θ : Θ}

/-- Risk is the expected conditional loss given the observation. -/
theorem risk_eq_integral_integral (hL : Integrable (L θ) (κ ∘ₘ P θ)) :
    risk P L κ θ = ∫ x, ∫ a, L θ a ∂κ x ∂P θ := by
  rw [risk_def]
  exact Measure.integral_bind κ.aemeasurable hL

/-- A bound on the absolute loss bounds the absolute risk under a probability law. -/
theorem abs_risk_le [IsProbabilityMeasure (κ ∘ₘ P θ)] {C : ℝ}
    (hL : ∀ᵐ a ∂(κ ∘ₘ P θ), |L θ a| ≤ C) : |risk P L κ θ| ≤ C := by
  simpa [risk_def, Real.norm_eq_abs] using norm_integral_le_of_norm_le_const
    (μ := κ ∘ₘ P θ) (f := L θ) (by simpa [Real.norm_eq_abs] using hL)

/-- Expected loss is measurable in the parameter for a measurable loss and a kernel model. -/
theorem measurable_risk [MeasurableSpace Θ] (P : Kernel Θ X)
    [IsSFiniteKernel (κ ∘ₖ P)] (hL : Measurable (Function.uncurry L)) :
    Measurable (risk P L κ) := by
  have heq : risk P L κ = fun θ ↦ ∫ a, L θ a ∂((κ ∘ₖ P) θ) := by
    funext θ
    rw [risk_def, Kernel.comp_apply]
  rw [heq]
  exact (hL.stronglyMeasurable.integral_kernel_prod_right (κ := κ ∘ₖ P)).measurable

/-- For an integrable nonnegative loss the real risk represents the corresponding Lebesgue
integral. -/
theorem ofReal_risk_eq_lintegral (hL : Integrable (L θ) (κ ∘ₘ P θ))
    (h₀ : 0 ≤ᵐ[κ ∘ₘ P θ] L θ) :
    ENNReal.ofReal (risk P L κ θ) = ∫⁻ a, ENNReal.ofReal (L θ a) ∂(κ ∘ₘ P θ) := by
  simpa only [risk_def] using ofReal_integral_eq_lintegral_ofReal hL h₀

/-- The average of real risks is Mathlib's average risk after conversion to `ℝ≥0∞` for a
nonnegative loss with integrable fibres and integrable real risk. -/
theorem ofReal_integral_risk_eq_avgRisk [MeasurableSpace Θ] (P : Kernel Θ X) (π : Measure Θ)
    (hr : Integrable (risk P L κ) π)
    (hL : ∀ᵐ θ ∂π, Integrable (L θ) ((κ ∘ₖ P) θ) ∧ 0 ≤ᵐ[(κ ∘ₖ P) θ] L θ) :
    ENNReal.ofReal (∫ θ, risk P L κ θ ∂π) =
      avgRisk (fun θ a ↦ ENNReal.ofReal (L θ a)) P κ π := by
  have h₀ : 0 ≤ᵐ[π] risk P L κ := by
    filter_upwards [hL] with θ hθ
    simpa only [Pi.zero_apply, risk_def, Kernel.comp_apply] using integral_nonneg_of_ae hθ.2
  rw [ofReal_integral_eq_lintegral_ofReal hr h₀, avgRisk]
  apply lintegral_congr_ae
  filter_upwards [hL] with θ hθ
  simp only [Kernel.comp_apply] at hθ ⊢
  exact ofReal_risk_eq_lintegral hθ.1 hθ.2

/-- `Q` is a garbling of `P` if one Markov kernel transforms every sampling law of `P` into the
corresponding sampling law of `Q`. -/
def IsGarbling (P : Θ → Measure X) (Q : Θ → Measure Y) : Prop :=
  ∃ K : Kernel X Y, IsMarkovKernel K ∧ ∀ θ, Q θ = K ∘ₘ P θ

/-- Characterization of garbling by a parameter-independent Markov kernel. -/
theorem isGarbling_iff (P : Θ → Measure X) (Q : Θ → Measure Y) :
    IsGarbling P Q ↔ ∃ K : Kernel X Y, IsMarkovKernel K ∧ ∀ θ, Q θ = K ∘ₘ P θ := (Iff.rfl)

/-- Applying a Markov kernel to the sampling laws gives a garbling. -/
theorem isGarbling_comp (P : Θ → Measure X) (K : Kernel X Y) [IsMarkovKernel K] :
    IsGarbling P (fun θ ↦ K ∘ₘ P θ) :=
  (isGarbling_iff ..).2 ⟨K, inferInstance, fun _ ↦ rfl⟩

/-- The identity kernel leaves the experiment unchanged. -/
@[refl]
theorem IsGarbling.refl (P : Θ → Measure X) : IsGarbling P P := by
  simpa using isGarbling_comp P Kernel.id

/-- Composing the two garbling kernels gives a garbling of the original experiment. -/
@[trans]
theorem IsGarbling.trans {Q : Θ → Measure Y} {R : Θ → Measure Z}
    (hPQ : IsGarbling P Q) (hQR : IsGarbling Q R) : IsGarbling P R := by
  obtain ⟨K, hK, hQ⟩ := (isGarbling_iff ..).1 hPQ
  obtain ⟨J, hJ, hR⟩ := (isGarbling_iff ..).1 hQR
  exact (isGarbling_iff ..).2 ⟨J ∘ₖ K, inferInstance, fun θ ↦ by
    rw [hR, hQ, Measure.comp_assoc]⟩

instance : Trans (α := Θ → Measure X) (β := Θ → Measure Y) (γ := Θ → Measure Z)
    IsGarbling IsGarbling IsGarbling :=
  ⟨IsGarbling.trans⟩

/-- A decision rule that first applies the garbling kernel has the same risk in the original
experiment as the given rule in the garbled experiment. -/
theorem risk_comp_garbling (K : Kernel X Y) (δ : Kernel Y A) :
    risk P L (δ ∘ₖ K) = risk (fun θ ↦ K ∘ₘ P θ) L δ := by
  funext θ
  simp only [risk_def, Measure.comp_assoc]

/-- Every randomized rule in a garbled experiment has a randomized rule of equal risk in the
original experiment. -/
theorem IsGarbling.exists_risk_eq {Q : Θ → Measure Y} (h : IsGarbling P Q)
    (δ : Kernel Y A) [IsMarkovKernel δ] (L : Θ → A → ℝ) :
    ∃ κ : Kernel X A, IsMarkovKernel κ ∧ risk P L κ = risk Q L δ := by
  obtain ⟨K, hK, hQ⟩ := (isGarbling_iff ..).1 h
  exact ⟨δ ∘ₖ K, inferInstance, by rw [risk_comp_garbling, ← funext hQ]⟩

end TauCeti
