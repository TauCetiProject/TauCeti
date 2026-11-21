/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.Basic
import TauCeti.Analysis.Sobolev.Leibniz
import TauCeti.MeasureTheory.Function.Lp.Multiplication
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn

/-!
# Multiplication of first-order Sobolev fields by smooth functions

Let `ψ` be a real function, smooth on an open set `Ω` of a finite-dimensional real normed space,
with `ψ` and its derivative bounded on `Ω`. Multiplication by `ψ` acts on the first-order
weak-derivative graph `W^{1,p}(Ω, F) = TauCeti.WeakDerivStep mu Ω p (id)` over `Lᵖ(Ω, F)`: by the
Leibniz rule for weak derivatives (`TauCeti.HasWeakFDerivOn.contDiffOn_smul`), the field `ψ u` has
weak derivative

`D(ψ u) = ψ Du + Dψ ⊗ u`, that is, `v ↦ ψ Du v + (Dψ v) u`.

This file packages it as a bounded linear map (`TauCeti.WeakDerivStep.smulLeftCLM`) and bounds
its norm by `√2 C₀ + C₁`, for bounds `C₀` on `|ψ|` and `C₁` on `‖Dψ‖`
(`TauCeti.WeakDerivStep.norm_smulLeftCLM_apply_le`). Multiplication by cutoff functions is how
operators are localized and spliced together, with the derivative of the cutoff measuring the
error.

## Main declarations

* `TauCeti.WeakDerivStep.smulLeftCLM`: multiplication by `ψ` on `W^{1,p}(Ω, F)`.
* `TauCeti.WeakDerivStep.prev_smulLeftCLM_ae`, `TauCeti.WeakDerivStep.weakFDeriv_smulLeftCLM_ae`:
  its field is `ψ u` and its weak derivative is `ψ Du + Dψ ⊗ u`.
* `TauCeti.WeakDerivStep.norm_smulLeftCLM_apply_le`: the bound `‖ψ u‖ ≤ (√2 C₀ + C₁) ‖u‖`.

## References

* L. C. Evans, *Partial Differential Equations*, §5.2.3, Theorem 1 (iv) (the product rule for
  weak derivatives).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal ContDiff

namespace TauCeti.WeakDerivStep

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {mu : Measure E} {Omega : Opens E}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {ψ : E → ℝ}

/-- The `L∞` class of `ψ` on `Ω`. -/
private def linftyClass (hψ : ContDiffOn ℝ ∞ ψ Omega) (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C) :
    Lp ℝ ∞ (mu.restrict Omega) :=
  (hψ.continuousOn.memLp_top_restrict_of_bound Omega.isOpen.measurableSet _
    h₀.choose_spec).toLp ψ

/-- Multiplication by the `L∞` class of `ψ` acts by `x ↦ ψ x • g x`. -/
private theorem multiplicationOperator_linftyClass_ae (G : Type*) [NormedAddCommGroup G]
    [NormedSpace ℝ G] (hψ : ContDiffOn ℝ ∞ ψ Omega) (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C)
    (g : Lp G p (mu.restrict Omega)) :
    ⇑(Lp.multiplicationOperator (linftyClass hψ h₀) g)
      =ᵐ[mu.restrict Omega] fun x ↦ ψ x • g x := by
  filter_upwards [Lp.multiplicationOperator_ae (linftyClass hψ h₀) g,
    (hψ.continuousOn.memLp_top_restrict_of_bound (μ := mu) Omega.isOpen.measurableSet _
      h₀.choose_spec).coeFn_toLp] with x hx hψx
  rw [hx, linftyClass, hψx]

variable [FiniteDimensional ℝ E]

/-- The rank-one correction `x ↦ Dψ x ⊗ u x` in `Lᵖ(Ω, E →L F)`, through the `L∞` class of
`Dψ`. -/
private def smulRightLp (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C) :
    Lp F p (mu.restrict Omega) →L[ℝ] Lp (E →L[ℝ] F) p (mu.restrict Omega) :=
  (ContinuousLinearMap.smulRightL ℝ E F).holderL (mu.restrict Omega) ∞ p p
    (((hψ.continuousOn_fderiv_of_isOpen Omega.isOpen (by simp)).memLp_top_restrict_of_bound
      Omega.isOpen.measurableSet _ h₁.choose_spec).toLp (fderiv ℝ ψ))

private theorem smulRightLp_ae (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C) (g : Lp F p (mu.restrict Omega)) :
    ⇑(smulRightLp hψ h₁ g) =ᵐ[mu.restrict Omega] fun x ↦ (fderiv ℝ ψ x).smulRight (g x) := by
  filter_upwards [(ContinuousLinearMap.smulRightL ℝ E F).coeFn_holder (r := p)
    (((hψ.continuousOn_fderiv_of_isOpen Omega.isOpen (by simp)).memLp_top_restrict_of_bound
      Omega.isOpen.measurableSet _ h₁.choose_spec).toLp (fderiv ℝ ψ)) g,
    ((hψ.continuousOn_fderiv_of_isOpen Omega.isOpen (by simp)).memLp_top_restrict_of_bound
      (μ := mu) Omega.isOpen.measurableSet _ h₁.choose_spec).coeFn_toLp] with x hx hψx
  rw [smulRightLp, ContinuousLinearMap.holderL_apply_apply, hx, hψx]
  rfl

variable [CompleteSpace F] [IsFiniteMeasureOnCompacts mu]

/-- **Multiplication by a smooth function on `W^{1,p}(Ω, F)`.** For `ψ` smooth on `Ω` with `ψ` and
`Dψ` bounded on `Ω`, the map `u ↦ ψ u`; its weak derivative is `ψ Du + Dψ ⊗ u`
(`TauCeti.WeakDerivStep.weakFDeriv_smulLeftCLM_ae`). -/
def smulLeftCLM (ψ : E → ℝ) (hψ : ContDiffOn ℝ ∞ ψ Omega) (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C)
    (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C) :
    WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) →L[ℝ]
      WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) :=
  ContinuousLinearMap.codRestrict
    ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
      (((Lp.multiplicationOperator (E := F) (p := p) (linftyClass hψ h₀)).comp (prevL _)).prod
        ((Lp.multiplicationOperator (E := E →L[ℝ] F) (p := p) (linftyClass hψ h₀)).comp
            (weakFDerivL _) +
          (smulRightLp hψ h₁).comp (prevL _))))
    _ fun u ↦ (mem_weakDerivStepSubmodule_iff_hasWeakFDerivOn _ _).mpr <| by
      have h := (hasWeakFDerivOn_base_prev _ u).contDiffOn_smul hψ
      refine (h.congr_ae ?_).congr_ae_deriv ?_
      · simpa using (multiplicationOperator_linftyClass_ae F hψ h₀ (prev _ u)).symm
      · simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
          Function.comp_apply, ContinuousLinearMap.prod_apply, prevL_apply, weakFDerivL_apply,
          add_apply, WithLp.prodContinuousLinearEquiv_symm_apply,
          WithLp.toLp_snd]
        filter_upwards [Lp.coeFn_add
            (Lp.multiplicationOperator (linftyClass hψ h₀) (weakFDeriv _ u))
            (smulRightLp hψ h₁ (prev _ u)),
          multiplicationOperator_linftyClass_ae (E →L[ℝ] F) hψ h₀ (weakFDeriv _ u),
          smulRightLp_ae hψ h₁ (prev _ u)]
          with x hx h₂ h₃
        rw [hx, Pi.add_apply, h₂, h₃, ContinuousLinearMap.id_apply]

private theorem prev_smulLeftCLM (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C) (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    prev _ (smulLeftCLM ψ hψ h₀ h₁ u) =
      Lp.multiplicationOperator (linftyClass hψ h₀) (prev _ u) := by
  simp [prev_coe, smulLeftCLM]

private theorem weakFDeriv_smulLeftCLM (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C) (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    weakFDeriv _ (smulLeftCLM ψ hψ h₀ h₁ u) =
      Lp.multiplicationOperator (linftyClass hψ h₀) (weakFDeriv _ u) +
        smulRightLp hψ h₁ (prev _ u) := by
  simp [weakFDeriv_coe, smulLeftCLM]

/-- The field of `ψ u` is represented almost everywhere by `x ↦ ψ x • u x`. -/
theorem prev_smulLeftCLM_ae (hψ : ContDiffOn ℝ ∞ ψ Omega) (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C)
    (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    ⇑(prev _ (smulLeftCLM ψ hψ h₀ h₁ u)) =ᵐ[mu.restrict Omega] fun x ↦ ψ x • prev _ u x := by
  rw [prev_smulLeftCLM]
  exact multiplicationOperator_linftyClass_ae F hψ h₀ (prev _ u)

/-- **The Leibniz rule.** The weak derivative of `ψ u` is represented almost everywhere by
`x ↦ ψ x • Du x + Dψ x ⊗ u x`. -/
theorem weakFDeriv_smulLeftCLM_ae (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C) (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    ⇑(weakFDeriv _ (smulLeftCLM ψ hψ h₀ h₁ u)) =ᵐ[mu.restrict Omega]
      fun x ↦ ψ x • weakFDeriv _ u x + (fderiv ℝ ψ x).smulRight (prev _ u x) := by
  rw [weakFDeriv_smulLeftCLM]
  filter_upwards [Lp.coeFn_add (Lp.multiplicationOperator (linftyClass hψ h₀) (weakFDeriv _ u))
      (smulRightLp hψ h₁ (prev _ u)),
    multiplicationOperator_linftyClass_ae (E →L[ℝ] F) hψ h₀ (weakFDeriv _ u),
    smulRightLp_ae hψ h₁ (prev _ u)]
    with x hx h₂ h₃
  rw [hx, Pi.add_apply, h₂, h₃]

private theorem norm_prev_smulLeftCLM_le (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C) (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C) {C₀ : ℝ}
    (hC₀ : ∀ x ∈ Omega, ‖ψ x‖ ≤ C₀)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    ‖prev _ (smulLeftCLM ψ hψ h₀ h₁ u)‖ ≤ C₀ * ‖prev _ u‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [prev_smulLeftCLM_ae hψ h₀ h₁ u, ae_restrict_mem Omega.isOpen.measurableSet]
    with x hx hxΩ
  rw [hx, norm_smul]
  exact mul_le_mul_of_nonneg_right (hC₀ x hxΩ) (norm_nonneg _)

private theorem norm_weakFDeriv_smulLeftCLM_le (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C) (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C) {C₀ C₁ : ℝ}
    (hC₀ : ∀ x ∈ Omega, ‖ψ x‖ ≤ C₀) (hC₁ : ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C₁)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    ‖weakFDeriv _ (smulLeftCLM ψ hψ h₀ h₁ u)‖ ≤ C₀ * ‖weakFDeriv _ u‖ + C₁ * ‖prev _ u‖ := by
  have hΩ := Omega.isOpen.measurableSet
  rw [weakFDeriv_smulLeftCLM]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [multiplicationOperator_linftyClass_ae (E →L[ℝ] F) hψ h₀ (weakFDeriv _ u),
      ae_restrict_mem hΩ]
      with x hx hxΩ
    rw [hx, norm_smul]
    exact mul_le_mul_of_nonneg_right (hC₀ x hxΩ) (norm_nonneg _)
  · refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [smulRightLp_ae hψ h₁ (prev _ u), ae_restrict_mem hΩ] with x hx hxΩ
    rw [hx, ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul_of_nonneg_right (hC₁ x hxΩ) (norm_nonneg _)

omit [FiniteDimensional ℝ E] in
/-- On an empty domain every field of `W^{1,p}(Ω, F)` has norm zero. -/
private theorem norm_weakDerivStep_eq_zero_of_coe_eq_empty (hΩ : (Omega : Set E) = ∅)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    ‖u‖ = 0 := by
  have h := norm_le_norm_prev_add_norm_weakFDeriv
    (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u
  have h0 : mu.restrict (Omega : Set E) = 0 := by rw [hΩ, Measure.restrict_empty]
  simp only [Lp.norm_def, h0, eLpNorm_measure_zero, ENNReal.toReal_zero, add_zero] at h
  exact le_antisymm h (norm_nonneg u)

/-- **The norm of multiplication by a smooth function.** If `|ψ| ≤ C₀` and `‖Dψ‖ ≤ C₁` on `Ω`,
then `‖ψ u‖ ≤ (√2 C₀ + C₁) ‖u‖` in the graph norm. -/
theorem norm_smulLeftCLM_apply_le (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C) (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C) {C₀ C₁ : ℝ}
    (hC₀ : ∀ x ∈ Omega, ‖ψ x‖ ≤ C₀) (hC₁ : ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C₁)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    ‖smulLeftCLM ψ hψ h₀ h₁ u‖ ≤ (√2 * C₀ + C₁) * ‖u‖ := by
  rcases (Omega : Set E).eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
  · rw [norm_weakDerivStep_eq_zero_of_coe_eq_empty hempty,
      norm_weakDerivStep_eq_zero_of_coe_eq_empty hempty u, mul_zero]
  have hC₀' : 0 ≤ C₀ := (norm_nonneg _).trans (hC₀ x₀ hx₀)
  have hC₁' : 0 ≤ C₁ := (norm_nonneg _).trans (hC₁ x₀ hx₀)
  calc ‖smulLeftCLM ψ hψ h₀ h₁ u‖
      ≤ ‖prev _ (smulLeftCLM ψ hψ h₀ h₁ u)‖ + ‖weakFDeriv _ (smulLeftCLM ψ hψ h₀ h₁ u)‖ :=
        norm_le_norm_prev_add_norm_weakFDeriv _ _
    _ ≤ C₀ * (‖prev _ u‖ + ‖weakFDeriv _ u‖) + C₁ * ‖prev _ u‖ := by
        linarith [norm_prev_smulLeftCLM_le hψ h₀ h₁ hC₀ u,
          norm_weakFDeriv_smulLeftCLM_le hψ h₀ h₁ hC₀ hC₁ u]
    _ ≤ C₀ * (√2 * ‖u‖) + C₁ * ‖u‖ := by
        gcongr
        · exact norm_prev_add_norm_weakFDeriv_le _ u
        · exact norm_prev_le _ u
    _ = (√2 * C₀ + C₁) * ‖u‖ := by ring

end TauCeti.WeakDerivStep
