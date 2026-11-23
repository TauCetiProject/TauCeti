/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.Basic
public import TauCeti.MeasureTheory.Function.Lp.Multiplication
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

The multiplication is defined more generally on the graph `TauCeti.WeakDerivStep mu Ω p T` of any
base `T : Lᵖ(Ω, D) →L Lᵖ(Ω, F)` commuting with multiplication by `L∞` functions, such as the
composition `ι.compLpL p (mu.restrict Ω)` with a continuous linear map `ι : D →L F`
(`ContinuousLinearMap.compLpL_multiplicationOperator`). There the weak derivative of `T (ψ u)` is
`ψ Du + Dψ ⊗ T u`.

## Main declarations

* `TauCeti.WeakDerivStep.smulLeftCLM`: multiplication by `ψ` on the graph of a base `T`, in
  particular on `W^{1,p}(Ω, F)`.
* `TauCeti.WeakDerivStep.prev_smulLeftCLM_ae`, `TauCeti.WeakDerivStep.weakFDeriv_smulLeftCLM_ae`:
  its field is `ψ u` and its weak derivative is `ψ Du + Dψ ⊗ T u`.
* `TauCeti.WeakDerivStep.norm_smulLeftCLM_apply_le`: the bound `‖ψ u‖ ≤ (√2 C₀ + C₁) ‖u‖`, and
  `TauCeti.WeakDerivStep.norm_smulLeftCLM_apply_le_mul_opNorm`, `‖ψ u‖ ≤ (√2 C₀ + C₁ ‖T‖) ‖u‖`
  over a base `T`.
* `TauCeti.WeakDerivStep.sum_smulLeftCLM`: if `∑ᵢ ψᵢ = 1` on `Ω`, then `∑ᵢ ψᵢ u = u`.

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

variable [FiniteDimensional ℝ E]

/-- The rank-one correction `x ↦ Dψ x ⊗ u x` in `Lᵖ(Ω, E →L F)`, through the `L∞` class of
`Dψ`. -/
private def smulRightLp (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C) :
    Lp F p (mu.restrict Omega) →L[ℝ] Lp (E →L[ℝ] F) p (mu.restrict Omega) :=
  (ContinuousLinearMap.smulRightL ℝ ℝ ℝ E F).holderL (mu.restrict Omega) ∞ p p
    (linftyOfContinuousOn mu (hψ.continuousOn_fderiv_of_isOpen Omega.isOpen (by simp))
      Omega.isOpen.measurableSet h₁)

private theorem smulRightLp_ae (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C) (g : Lp F p (mu.restrict Omega)) :
    ⇑(smulRightLp hψ h₁ g) =ᵐ[mu.restrict Omega] fun x ↦ (fderiv ℝ ψ x).smulRight (g x) := by
  filter_upwards [(ContinuousLinearMap.smulRightL ℝ ℝ ℝ E F).coeFn_holder (r := p)
    (linftyOfContinuousOn mu (hψ.continuousOn_fderiv_of_isOpen Omega.isOpen (by simp))
      Omega.isOpen.measurableSet h₁) g,
    coeFn_linftyOfContinuousOn (μ := mu) (hψ.continuousOn_fderiv_of_isOpen Omega.isOpen (by simp))
      Omega.isOpen.measurableSet h₁] with x hx hψx
  rw [smulRightLp, ContinuousLinearMap.holderL_apply_apply, hx, hψx,
    ContinuousLinearMap.smulRightL_apply_apply]

/-- The Leibniz combination `ψ W + Dψ ⊗ g` is represented almost everywhere by
`x ↦ ψ x • W x + Dψ x ⊗ g x`. -/
private theorem multiplicationOperator_add_smulRightLp_ae (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C) (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C)
    (W : Lp (E →L[ℝ] F) p (mu.restrict Omega)) (g : Lp F p (mu.restrict Omega)) :
    ⇑(Lp.multiplicationOperator
        (linftyOfContinuousOn mu hψ.continuousOn Omega.isOpen.measurableSet h₀) W +
      smulRightLp hψ h₁ g)
      =ᵐ[mu.restrict Omega] fun x ↦ ψ x • W x + (fderiv ℝ ψ x).smulRight (g x) := by
  filter_upwards [Lp.coeFn_add (Lp.multiplicationOperator
        (linftyOfContinuousOn mu hψ.continuousOn Omega.isOpen.measurableSet h₀) W)
      (smulRightLp hψ h₁ g),
    Lp.multiplicationOperator_linftyOfContinuousOn_ae hψ.continuousOn Omega.isOpen.measurableSet
      h₀ W, smulRightLp_ae hψ h₁ g]
    with x hx h₂ h₃
  rw [hx, Pi.add_apply, h₂, h₃]

variable [CompleteSpace F] [IsFiniteMeasureOnCompacts mu] {D : Type*} [NormedAddCommGroup D]
  [NormedSpace ℝ D] {T : Lp D p (mu.restrict Omega) →L[ℝ] Lp F p (mu.restrict Omega)}

/-- **Multiplication by a smooth function on a first-order graph space.** For `ψ` smooth on `Ω` with
`ψ` and `Dψ` bounded on `Ω`, and a base `T` commuting with multiplication by `L∞` functions, the
map `u ↦ ψ u`; the weak derivative of `T (ψ u)` is `ψ Du + Dψ ⊗ T u`
(`TauCeti.WeakDerivStep.weakFDeriv_smulLeftCLM_ae`). The commutation hypothesis `hT` holds by
`rfl` for the identity base of `W^{1,p}(Ω, F)`, and by
`ContinuousLinearMap.compLpL_multiplicationOperator` for a base `ι.compLpL p (mu.restrict Ω)`. -/
def smulLeftCLM (ψ : E → ℝ) (hψ : ContDiffOn ℝ ∞ ψ Omega) (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C)
    (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C)
    (hT : ∀ (a : Lp ℝ ∞ (mu.restrict Omega)) g,
      T (Lp.multiplicationOperator a g) = Lp.multiplicationOperator a (T g)) :
    WeakDerivStep mu Omega p T →L[ℝ] WeakDerivStep mu Omega p T :=
  ContinuousLinearMap.codRestrict
    ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
      (((Lp.multiplicationOperator (E := D) (p := p)
          (linftyOfContinuousOn mu hψ.continuousOn Omega.isOpen.measurableSet h₀)).comp
          (prevL _)).prod
        ((Lp.multiplicationOperator (E := E →L[ℝ] F) (p := p)
          (linftyOfContinuousOn mu hψ.continuousOn Omega.isOpen.measurableSet h₀)).comp
            (weakFDerivL _) +
          (smulRightLp hψ h₁).comp (T.comp (prevL _)))))
    _ fun u ↦ (mem_weakDerivStepSubmodule_iff_hasWeakFDerivOn _ _).mpr <| by
      have h := (hasWeakFDerivOn_base_prev _ u).contDiffOn_smul hψ
      refine (h.congr_ae ?_).congr_ae_deriv ?_
      · simpa [hT] using (Lp.multiplicationOperator_linftyOfContinuousOn_ae hψ.continuousOn
          Omega.isOpen.measurableSet h₀ (T (prev _ u))).symm
      · simpa using
          (multiplicationOperator_add_smulRightLp_ae hψ h₀ h₁ (weakFDeriv _ u) (T (prev _ u))).symm

private theorem prev_smulLeftCLM (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C) (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C)
    (hT : ∀ (a : Lp ℝ ∞ (mu.restrict Omega)) g,
      T (Lp.multiplicationOperator a g) = Lp.multiplicationOperator a (T g))
    (u : WeakDerivStep mu Omega p T) :
    prev _ (smulLeftCLM ψ hψ h₀ h₁ hT u) = Lp.multiplicationOperator
      (linftyOfContinuousOn mu hψ.continuousOn Omega.isOpen.measurableSet h₀) (prev _ u) := by
  simp [prev_coe, smulLeftCLM]

private theorem weakFDeriv_smulLeftCLM (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C) (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C)
    (hT : ∀ (a : Lp ℝ ∞ (mu.restrict Omega)) g,
      T (Lp.multiplicationOperator a g) = Lp.multiplicationOperator a (T g))
    (u : WeakDerivStep mu Omega p T) :
    weakFDeriv _ (smulLeftCLM ψ hψ h₀ h₁ hT u) = Lp.multiplicationOperator
        (linftyOfContinuousOn mu hψ.continuousOn Omega.isOpen.measurableSet h₀) (weakFDeriv _ u) +
      smulRightLp hψ h₁ (T (prev _ u)) := by
  simp [weakFDeriv_coe, smulLeftCLM]

/-- The field of `ψ u` is represented almost everywhere by `x ↦ ψ x • u x`. -/
theorem prev_smulLeftCLM_ae (hψ : ContDiffOn ℝ ∞ ψ Omega) (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C)
    (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C) (hT : ∀ (a : Lp ℝ ∞ (mu.restrict Omega)) g,
      T (Lp.multiplicationOperator a g) = Lp.multiplicationOperator a (T g))
    (u : WeakDerivStep mu Omega p T) :
    ⇑(prev _ (smulLeftCLM ψ hψ h₀ h₁ hT u)) =ᵐ[mu.restrict Omega] fun x ↦ ψ x • prev _ u x := by
  rw [prev_smulLeftCLM hψ h₀ h₁ hT]
  exact Lp.multiplicationOperator_linftyOfContinuousOn_ae hψ.continuousOn
    Omega.isOpen.measurableSet h₀ (prev _ u)

/-- If `ψ` vanishes on a set `Z`, then so does the field of `ψ u`, almost everywhere. -/
theorem ae_prev_smulLeftCLM_eq_zero (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C) (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C)
    (hT : ∀ (a : Lp ℝ ∞ (mu.restrict Omega)) g,
      T (Lp.multiplicationOperator a g) = Lp.multiplicationOperator a (T g))
    {Z : Set E} (hZ : ∀ x ∈ Z, ψ x = 0) (u : WeakDerivStep mu Omega p T) :
    ∀ᵐ x ∂mu.restrict Omega, x ∈ Z → prev _ (smulLeftCLM ψ hψ h₀ h₁ hT u) x = 0 := by
  filter_upwards [prev_smulLeftCLM_ae hψ h₀ h₁ hT u] with x hx hxZ
  rw [hx, hZ x hxZ, zero_smul]

/-- **The Leibniz rule.** The weak derivative of `T (ψ u)` is represented almost everywhere by
`x ↦ ψ x • Du x + Dψ x ⊗ T u x`. -/
theorem weakFDeriv_smulLeftCLM_ae (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C) (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C)
    (hT : ∀ (a : Lp ℝ ∞ (mu.restrict Omega)) g,
      T (Lp.multiplicationOperator a g) = Lp.multiplicationOperator a (T g))
    (u : WeakDerivStep mu Omega p T) :
    ⇑(weakFDeriv _ (smulLeftCLM ψ hψ h₀ h₁ hT u)) =ᵐ[mu.restrict Omega]
      fun x ↦ ψ x • weakFDeriv _ u x + (fderiv ℝ ψ x).smulRight (T (prev _ u) x) := by
  rw [weakFDeriv_smulLeftCLM hψ h₀ h₁ hT]
  exact multiplicationOperator_add_smulRightLp_ae hψ h₀ h₁ (weakFDeriv _ u) (T (prev _ u))

private theorem norm_prev_smulLeftCLM_le (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C) (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C)
    (hT : ∀ (a : Lp ℝ ∞ (mu.restrict Omega)) g,
      T (Lp.multiplicationOperator a g) = Lp.multiplicationOperator a (T g))
    {C₀ : ℝ} (hC₀ : ∀ x ∈ Omega, ‖ψ x‖ ≤ C₀) (u : WeakDerivStep mu Omega p T) :
    ‖prev _ (smulLeftCLM ψ hψ h₀ h₁ hT u)‖ ≤ C₀ * ‖prev _ u‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [prev_smulLeftCLM_ae hψ h₀ h₁ hT u, ae_restrict_mem Omega.isOpen.measurableSet]
    with x hx hxΩ
  rw [hx, norm_smul]
  exact mul_le_mul_of_nonneg_right (hC₀ x hxΩ) (norm_nonneg _)

private theorem norm_weakFDeriv_smulLeftCLM_le (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C) (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C)
    (hT : ∀ (a : Lp ℝ ∞ (mu.restrict Omega)) g,
      T (Lp.multiplicationOperator a g) = Lp.multiplicationOperator a (T g))
    {C₀ C₁ : ℝ} (hC₀ : ∀ x ∈ Omega, ‖ψ x‖ ≤ C₀) (hC₁ : ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C₁)
    (u : WeakDerivStep mu Omega p T) :
    ‖weakFDeriv _ (smulLeftCLM ψ hψ h₀ h₁ hT u)‖ ≤
      C₀ * ‖weakFDeriv _ u‖ + C₁ * ‖T (prev _ u)‖ := by
  have hΩ := Omega.isOpen.measurableSet
  rw [weakFDeriv_smulLeftCLM hψ h₀ h₁ hT]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [Lp.multiplicationOperator_linftyOfContinuousOn_ae hψ.continuousOn hΩ h₀
      (weakFDeriv _ u), ae_restrict_mem hΩ]
      with x hx hxΩ
    rw [hx, norm_smul]
    exact mul_le_mul_of_nonneg_right (hC₀ x hxΩ) (norm_nonneg _)
  · refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [smulRightLp_ae hψ h₁ (T (prev _ u)), ae_restrict_mem hΩ] with x hx hxΩ
    rw [hx, ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul_of_nonneg_right (hC₁ x hxΩ) (norm_nonneg _)

omit [FiniteDimensional ℝ E] in
/-- On an empty domain every field of a weak-derivative graph has norm zero. -/
private theorem norm_weakDerivStep_eq_zero_of_coe_eq_empty (hΩ : (Omega : Set E) = ∅)
    (u : WeakDerivStep mu Omega p T) : ‖u‖ = 0 := by
  have h := norm_le_norm_prev_add_norm_weakFDeriv T u
  have h0 : mu.restrict (Omega : Set E) = 0 := by rw [hΩ, Measure.restrict_empty]
  simp only [Lp.norm_def, h0, eLpNorm_measure_zero, ENNReal.toReal_zero, add_zero] at h
  exact le_antisymm h (norm_nonneg u)

/-- **The norm of multiplication by a smooth function over a base `T`.** If `|ψ| ≤ C₀` and
`‖Dψ‖ ≤ C₁` on `Ω`, then `‖ψ u‖ ≤ (√2 C₀ + C₁ ‖T‖) ‖u‖` in the graph norm. -/
theorem norm_smulLeftCLM_apply_le_mul_opNorm (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C) (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C)
    (hT : ∀ (a : Lp ℝ ∞ (mu.restrict Omega)) g,
      T (Lp.multiplicationOperator a g) = Lp.multiplicationOperator a (T g))
    {C₀ C₁ : ℝ} (hC₀ : ∀ x ∈ Omega, ‖ψ x‖ ≤ C₀) (hC₁ : ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C₁)
    (u : WeakDerivStep mu Omega p T) :
    ‖smulLeftCLM ψ hψ h₀ h₁ hT u‖ ≤ (√2 * C₀ + C₁ * ‖T‖) * ‖u‖ := by
  rcases (Omega : Set E).eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
  · rw [norm_weakDerivStep_eq_zero_of_coe_eq_empty hempty,
      norm_weakDerivStep_eq_zero_of_coe_eq_empty hempty u, mul_zero]
  have hC₀' : 0 ≤ C₀ := (norm_nonneg _).trans (hC₀ x₀ hx₀)
  have hC₁' : 0 ≤ C₁ := (norm_nonneg _).trans (hC₁ x₀ hx₀)
  calc ‖smulLeftCLM ψ hψ h₀ h₁ hT u‖
      ≤ ‖prev _ (smulLeftCLM ψ hψ h₀ h₁ hT u)‖ + ‖weakFDeriv _ (smulLeftCLM ψ hψ h₀ h₁ hT u)‖ :=
        norm_le_norm_prev_add_norm_weakFDeriv _ _
    _ ≤ C₀ * (‖prev _ u‖ + ‖weakFDeriv _ u‖) + C₁ * (‖T‖ * ‖prev _ u‖) := by
        linarith [norm_prev_smulLeftCLM_le hψ h₀ h₁ hT hC₀ u,
          norm_weakFDeriv_smulLeftCLM_le hψ h₀ h₁ hT hC₀ hC₁ u,
          mul_le_mul_of_nonneg_left (T.le_opNorm (prev _ u)) hC₁']
    _ ≤ C₀ * (√2 * ‖u‖) + C₁ * (‖T‖ * ‖u‖) := by
        gcongr
        · exact norm_prev_add_norm_weakFDeriv_le _ u
        · exact norm_prev_le _ u
    _ = (√2 * C₀ + C₁ * ‖T‖) * ‖u‖ := by ring

/-- **The norm of multiplication by a smooth function.** If `|ψ| ≤ C₀` and `‖Dψ‖ ≤ C₁` on `Ω`,
then `‖ψ u‖ ≤ (√2 C₀ + C₁) ‖u‖` in the graph norm. -/
theorem norm_smulLeftCLM_apply_le (hψ : ContDiffOn ℝ ∞ ψ Omega)
    (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C) (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C) {C₀ C₁ : ℝ}
    (hC₀ : ∀ x ∈ Omega, ‖ψ x‖ ≤ C₀) (hC₁ : ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C₁)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    ‖smulLeftCLM ψ hψ h₀ h₁ (fun _ _ ↦ rfl) u‖ ≤ (√2 * C₀ + C₁) * ‖u‖ := by
  refine (norm_smulLeftCLM_apply_le_mul_opNorm hψ h₀ h₁ _ hC₀ hC₁ u).trans ?_
  rcases (Omega : Set E).eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
  · rw [norm_weakDerivStep_eq_zero_of_coe_eq_empty hempty u, mul_zero, mul_zero]
  have hC₁' : 0 ≤ C₁ := (norm_nonneg _).trans (hC₁ x₀ hx₀)
  gcongr
  exact mul_le_of_le_one_right hC₁' (ContinuousLinearMap.norm_id_le)

/-- **Multiplication by a partition of unity.** If the smooth functions `ψᵢ` add up to one on `Ω`,
then the fields `ψᵢ u` add up to `u`. -/
theorem sum_smulLeftCLM {κ : Type*} (t : Finset κ) (ψ : κ → E → ℝ)
    (hψ : ∀ i, ContDiffOn ℝ ∞ (ψ i) Omega) (h₀ : ∀ i, ∃ C, ∀ x ∈ Omega, ‖ψ i x‖ ≤ C)
    (h₁ : ∀ i, ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ (ψ i) x‖ ≤ C)
    (hT : ∀ (a : Lp ℝ ∞ (mu.restrict Omega)) g,
      T (Lp.multiplicationOperator a g) = Lp.multiplicationOperator a (T g))
    (hsum : ∀ x ∈ Omega, ∑ i ∈ t, ψ i x = 1) (u : WeakDerivStep mu Omega p T) :
    ∑ i ∈ t, smulLeftCLM (ψ i) (hψ i) (h₀ i) (h₁ i) hT u = u := by
  classical
  -- The field of a partial sum is the partial sum of the `ψᵢ` times the field of `u`.
  have key : ∀ t' : Finset κ, ⇑(prev _ (∑ i ∈ t', smulLeftCLM (ψ i) (hψ i) (h₀ i) (h₁ i) hT u))
      =ᵐ[mu.restrict Omega] fun x ↦ (∑ i ∈ t', ψ i x) • prev _ u x := by
    intro t'
    induction t' using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, prev_zero, zero_smul]
      exact Lp.coeFn_zero D p _
    | insert j t' hj ih =>
      simp only [Finset.sum_insert hj, prev_add]
      filter_upwards [Lp.coeFn_add (prev _ (smulLeftCLM (ψ j) (hψ j) (h₀ j) (h₁ j) hT u))
          (prev _ (∑ i ∈ t', smulLeftCLM (ψ i) (hψ i) (h₀ i) (h₁ i) hT u)),
        prev_smulLeftCLM_ae (hψ j) (h₀ j) (h₁ j) hT u, ih] with x hx hj' ht'
      rw [hx, Pi.add_apply, hj', ht', add_smul]
  refine ext (Lp.ext ?_)
  filter_upwards [key t, ae_restrict_mem Omega.isOpen.measurableSet] with x hx hxΩ
  rw [hx, hsum x hxΩ, one_smul]

end TauCeti.WeakDerivStep
