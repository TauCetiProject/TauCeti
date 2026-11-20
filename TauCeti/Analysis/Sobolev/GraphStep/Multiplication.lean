/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.Basic
import TauCeti.Analysis.Sobolev.Leibniz

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

private theorem memLp_top_of_contDiffOn (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C) : MemLp ψ ∞ (mu.restrict Omega) := by
  obtain ⟨C, hC⟩ := h₀
  exact memLp_top_of_bound
    (hψ.continuousOn.aestronglyMeasurable Omega.isOpen.measurableSet) C
    ((ae_restrict_iff' Omega.isOpen.measurableSet).2 (Filter.Eventually.of_forall hC))

/-- Multiplication by `ψ` on `Lᵖ(Ω, G)`, through the `L∞` class of `ψ`. -/
private def smulLp (G : Type*) [NormedAddCommGroup G] [NormedSpace ℝ G]
    (hψ : ContDiffOn ℝ ∞ ψ Omega) (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C) :
    Lp G p (mu.restrict Omega) →L[ℝ] Lp G p (mu.restrict Omega) :=
  (ContinuousLinearMap.lsmul ℝ ℝ).holderL (mu.restrict Omega) ∞ p p
    ((memLp_top_of_contDiffOn hψ h₀).toLp ψ)

private theorem smulLp_ae (G : Type*) [NormedAddCommGroup G] [NormedSpace ℝ G]
    (hψ : ContDiffOn ℝ ∞ ψ Omega) (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C)
    (g : Lp G p (mu.restrict Omega)) :
    ⇑(smulLp G hψ h₀ g) =ᵐ[mu.restrict Omega] fun x ↦ ψ x • g x := by
  filter_upwards [(ContinuousLinearMap.lsmul ℝ ℝ).coeFn_holder (r := p)
    ((memLp_top_of_contDiffOn hψ h₀).toLp ψ) g,
    (memLp_top_of_contDiffOn (mu := mu) hψ h₀).coeFn_toLp] with x hx hψx
  rw [smulLp, ContinuousLinearMap.holderL_apply_apply, hx, hψx,
    ContinuousLinearMap.lsmul_apply]

variable [FiniteDimensional ℝ E]

private theorem memLp_top_fderiv_of_contDiffOn (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C) : MemLp (fderiv ℝ ψ) ∞ (mu.restrict Omega) := by
  obtain ⟨C, hC⟩ := h₁
  exact memLp_top_of_bound
    ((hψ.continuousOn_fderiv_of_isOpen Omega.isOpen (by simp)).aestronglyMeasurable
      Omega.isOpen.measurableSet) C
    ((ae_restrict_iff' Omega.isOpen.measurableSet).2 (Filter.Eventually.of_forall hC))

/-- The rank-one correction `x ↦ Dψ x ⊗ u x` in `Lᵖ(Ω, E →L F)`, through the `L∞` class of
`Dψ`. -/
private def smulRightLp (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C) :
    Lp F p (mu.restrict Omega) →L[ℝ] Lp (E →L[ℝ] F) p (mu.restrict Omega) :=
  (ContinuousLinearMap.smulRightL ℝ E F).holderL (mu.restrict Omega) ∞ p p
    ((memLp_top_fderiv_of_contDiffOn hψ h₁).toLp (fderiv ℝ ψ))

private theorem smulRightLp_ae (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C) (g : Lp F p (mu.restrict Omega)) :
    ⇑(smulRightLp hψ h₁ g) =ᵐ[mu.restrict Omega] fun x ↦ (fderiv ℝ ψ x).smulRight (g x) := by
  filter_upwards [(ContinuousLinearMap.smulRightL ℝ E F).coeFn_holder (r := p)
    ((memLp_top_fderiv_of_contDiffOn hψ h₁).toLp (fderiv ℝ ψ)) g,
    (memLp_top_fderiv_of_contDiffOn (mu := mu) hψ h₁).coeFn_toLp] with x hx hψx
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
      (((smulLp F hψ h₀).comp (prevL _)).prod
        ((smulLp (E →L[ℝ] F) hψ h₀).comp (weakFDerivL _) +
          (smulRightLp hψ h₁).comp (prevL _))))
    _ fun u ↦ (mem_weakDerivStepSubmodule_iff_hasWeakFDerivOn _ _).mpr <| by
      have h := (hasWeakFDerivOn_base_prev _ u).contDiffOn_smul hψ
      refine (h.congr_ae ?_).congr_ae_deriv ?_
      · simpa using (smulLp_ae F hψ h₀ (prev _ u)).symm
      · simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
          Function.comp_apply, ContinuousLinearMap.prod_apply, prevL_apply, weakFDerivL_apply,
          add_apply, WithLp.prodContinuousLinearEquiv_symm_apply,
          WithLp.toLp_snd]
        filter_upwards [Lp.coeFn_add ((smulLp (E →L[ℝ] F) hψ h₀) (weakFDeriv _ u))
            ((smulRightLp hψ h₁) (prev _ u)),
          smulLp_ae (E →L[ℝ] F) hψ h₀ (weakFDeriv _ u), smulRightLp_ae hψ h₁ (prev _ u)]
          with x hx h₂ h₃
        rw [hx, Pi.add_apply, h₂, h₃, ContinuousLinearMap.id_apply]

/-- The field of `ψ u` is represented almost everywhere by `x ↦ ψ x • u x`. -/
theorem prev_smulLeftCLM_ae (hψ : ContDiffOn ℝ ∞ ψ Omega) (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C)
    (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    ⇑(prev _ (smulLeftCLM ψ hψ h₀ h₁ u)) =ᵐ[mu.restrict Omega] fun x ↦ ψ x • prev _ u x := by
  have : prev _ (smulLeftCLM ψ hψ h₀ h₁ u) = smulLp F hψ h₀ (prev _ u) := by
    simp [prev_coe, smulLeftCLM]
  rw [this]
  exact smulLp_ae F hψ h₀ (prev _ u)

/-- **The Leibniz rule.** The weak derivative of `ψ u` is represented almost everywhere by
`x ↦ ψ x • Du x + Dψ x ⊗ u x`. -/
theorem weakFDeriv_smulLeftCLM_ae (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C) (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    ⇑(weakFDeriv _ (smulLeftCLM ψ hψ h₀ h₁ u)) =ᵐ[mu.restrict Omega]
      fun x ↦ ψ x • weakFDeriv _ u x + (fderiv ℝ ψ x).smulRight (prev _ u x) := by
  have : weakFDeriv _ (smulLeftCLM ψ hψ h₀ h₁ u) =
      smulLp (E →L[ℝ] F) hψ h₀ (weakFDeriv _ u) + smulRightLp hψ h₁ (prev _ u) := by
    simp [weakFDeriv_coe, smulLeftCLM]
  rw [this]
  filter_upwards [Lp.coeFn_add ((smulLp (E →L[ℝ] F) hψ h₀) (weakFDeriv _ u))
      ((smulRightLp hψ h₁) (prev _ u)),
    smulLp_ae (E →L[ℝ] F) hψ h₀ (weakFDeriv _ u), smulRightLp_ae hψ h₁ (prev _ u)]
    with x hx h₂ h₃
  rw [hx, Pi.add_apply, h₂, h₃]

/-- **The norm of multiplication by a smooth function.** If `|ψ| ≤ C₀` and `‖Dψ‖ ≤ C₁` on `Ω`,
then `‖ψ u‖ ≤ (√2 C₀ + C₁) ‖u‖` in the graph norm. -/
theorem norm_smulLeftCLM_apply_le (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C) (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C) {C₀ C₁ : ℝ}
    (hC₀ : ∀ x ∈ Omega, ‖ψ x‖ ≤ C₀) (hC₁ : ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C₁)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    ‖smulLeftCLM ψ hψ h₀ h₁ u‖ ≤ (√2 * C₀ + C₁) * ‖u‖ := by
  have hΩ := Omega.isOpen.measurableSet
  have hprev : ‖prev _ (smulLeftCLM ψ hψ h₀ h₁ u)‖ ≤ C₀ * ‖prev _ u‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [prev_smulLeftCLM_ae hψ h₀ h₁ u, ae_restrict_mem hΩ] with x hx hxΩ
    rw [hx, norm_smul]
    exact mul_le_mul_of_nonneg_right (hC₀ x hxΩ) (norm_nonneg _)
  have hD : ‖weakFDeriv _ (smulLeftCLM ψ hψ h₀ h₁ u)‖ ≤
      C₀ * ‖weakFDeriv _ u‖ + C₁ * ‖prev _ u‖ := by
    have : weakFDeriv _ (smulLeftCLM ψ hψ h₀ h₁ u) =
        smulLp (E →L[ℝ] F) hψ h₀ (weakFDeriv _ u) + smulRightLp hψ h₁ (prev _ u) := by
      simp [weakFDeriv_coe, smulLeftCLM]
    rw [this]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [smulLp_ae (E →L[ℝ] F) hψ h₀ (weakFDeriv _ u), ae_restrict_mem hΩ]
        with x hx hxΩ
      rw [hx, norm_smul]
      exact mul_le_mul_of_nonneg_right (hC₀ x hxΩ) (norm_nonneg _)
    · refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [smulRightLp_ae hψ h₁ (prev _ u), ae_restrict_mem hΩ] with x hx hxΩ
      rw [hx, ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul_of_nonneg_right (hC₁ x hxΩ) (norm_nonneg _)
  have hle : ‖smulLeftCLM ψ hψ h₀ h₁ u‖ ≤
      C₀ * (‖prev _ u‖ + ‖weakFDeriv _ u‖) + C₁ * ‖prev _ u‖ := by
    refine (norm_le_norm_prev_add_norm_weakFDeriv
      (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) (smulLeftCLM ψ hψ h₀ h₁ u)).trans ?_
    rw [mul_add, add_assoc]
    exact add_le_add hprev hD
  rcases (Omega : Set E).eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
  · -- On an empty domain every `Lᵖ` class vanishes, so both sides are zero.
    have hnull : ∀ᵐ _ ∂(mu.restrict Omega), False := by
      rw [hempty, Measure.restrict_empty]
      simp
    have h₁ : ‖prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u‖ = 0 := by
      have hf := Lp.norm_le_mul_norm_of_ae_le_mul (c := 0)
        (f := prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u)
        (g := prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u)
        (hnull.mono fun _ h ↦ h.elim)
      rw [zero_mul] at hf
      exact le_antisymm hf (norm_nonneg _)
    have h₂ : ‖weakFDeriv (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u‖ = 0 := by
      have hf := Lp.norm_le_mul_norm_of_ae_le_mul (c := 0)
        (f := weakFDeriv (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u)
        (g := weakFDeriv (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u)
        (hnull.mono fun _ h ↦ h.elim)
      rw [zero_mul] at hf
      exact le_antisymm hf (norm_nonneg _)
    have hu : ‖u‖ = 0 := by
      refine le_antisymm ?_ (norm_nonneg u)
      have := norm_le_norm_prev_add_norm_weakFDeriv
        (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u
      rwa [h₁, h₂, add_zero] at this
    rw [h₁, h₂] at hle
    rw [hu, mul_zero]
    simpa using hle
  · have hC₀' : 0 ≤ C₀ := (norm_nonneg _).trans (hC₀ x₀ hx₀)
    have hC₁' : 0 ≤ C₁ := (norm_nonneg _).trans (hC₁ x₀ hx₀)
    calc ‖smulLeftCLM ψ hψ h₀ h₁ u‖
        ≤ C₀ * (‖prev _ u‖ + ‖weakFDeriv _ u‖) + C₁ * ‖prev _ u‖ := hle
      _ ≤ C₀ * (√2 * ‖u‖) + C₁ * ‖u‖ := by
          gcongr
          · exact norm_prev_add_norm_weakFDeriv_le
              (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u
          · exact norm_prev_le (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u
      _ = (√2 * C₀ + C₁) * ‖u‖ := by ring

end TauCeti.WeakDerivStep
