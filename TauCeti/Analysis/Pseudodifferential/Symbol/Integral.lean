/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ParametricIntegral
public import TauCeti.Analysis.Pseudodifferential.Symbol.Topology

/-!
# Integrals of compact parameter families of symbols

For a finite measure `μ` on a compact parameter space `Y`, `TauCeti.Symbol.integral` integrates
the coefficients of a family of symbols of the same real order `m`. Every spatial jet must be
jointly continuous in the parameter and the position-frequency variables. The symbol estimates
on each compact set of positions must have constants independent of the parameter.

Mixed coordinate derivatives commute with this coefficient integral
(`TauCeti.Symbol.mixedDeriv_integral_of_continuous_jets`). If the seminorm `p_{K,α,β}` of every
member of the family is at most `C ≥ 0`, the integral has that seminorm at most
`μ.real Set.univ * C` (`TauCeti.Symbol.seminorm_integral_le`). For a probability measure, this
is an average with seminorm at most `C` (`TauCeti.Symbol.seminorm_integral_le_of_probability`).

Integration takes place in the coefficient operator space `V →L[ℂ] W`, with no
finite-dimensionality assumption on `V` or `W`. The parameter space needs only a topology.
The position estimates remain local on compact sets, with the native weight
`⟨ξ⟩^(m - |β|) = (1 + ‖ξ‖²)^((m - |β|)/2)`.

## References

* Lean-Atiyah-Singer, `AtiyahSinger/Analysis/CompactSymbolIntegral.lean`:
  the source formalization of compact-parameter symbol integration.
  <https://github.com/alpha-squared-labs/Lean-Atiyah-Singer>.
* H. B. Lawson, Jr. and M.-L. Michelsohn, *Spin Geometry*, Chapter III,
  proof of Theorem 9.7, p. 214: compact-group averaging of operator homotopies.
  The coefficient differentiation and seminorm estimates are supplementary
  analytic inputs in the source formalization.
  <https://doi.org/10.1515/9781400883912>.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace TauCeti.Symbol

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [OpensMeasurableSpace Y]
  (μ : Measure Y) [IsFiniteMeasure μ]
  {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}
  (a : Y → Symbol n V W m)
  (hjets : ∀ k : ℕ, Continuous
    (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
      iteratedFDeriv ℝ k (a p.1).coefficient p.2))

include hjets

private theorem contDiff_coefficient_integral :
    ContDiff ℝ ∞ (fun p ↦ ∫ y, (a y).coefficient p ∂μ) := by
  apply contDiff_of_differentiable_iteratedFDeriv
  intro k _
  have heq : iteratedFDeriv ℝ k (fun p ↦ ∫ y, (a y).coefficient p ∂μ) =
      fun p ↦ ∫ y, iteratedFDeriv ℝ k (a y).coefficient p ∂μ :=
    funext fun p ↦ iteratedFDeriv_integral_of_continuous_jets (μ := μ) isOpen_univ
      (fun y ↦ (a y).contDiff_coefficient.contDiffOn) (fun k ↦ (hjets k).continuousOn)
      k (mem_univ p)
  rw [heq]
  intro p
  have hnext := (continuousMultilinearCurryLeftEquiv ℝ
    (fun _ : Fin (k + 1) ↦ CoordinateSpace n × CoordinateSpace n) (V →L[ℂ] W)).continuous.comp
      ((hjets (k + 1)).comp continuous_swap)
  change Continuous (fun q : (CoordinateSpace n × CoordinateSpace n) × Y ↦
    fderiv ℝ (iteratedFDeriv ℝ k (a q.2).coefficient) q.1) at hnext
  have hD := hasFDerivAt_integral_of_continuousOn_fderiv (𝕜 := ℝ) (μ := μ) (x₀ := p)
    (F := fun p y ↦ iteratedFDeriv ℝ k (a y).coefficient p)
    Filter.univ_mem isCompact_univ MeasurableSet.univ (measure_ne_top _ _) Subset.rfl
    ((hjets k).comp continuous_swap).continuousOn
    (fun y _ ↦ ((a y).contDiff_coefficient.differentiable_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)).differentiableOn) hnext.continuousOn
  simpa only [setIntegral_univ] using hD.differentiableAt

/-- Mixed coordinate derivatives commute with the coefficient integral of a compact family
whose spatial jets are jointly continuous. -/
theorem mixedDeriv_integral_of_continuous_jets (α β : List (Fin n))
    (x ξ : CoordinateSpace n) :
    mixedDeriv α β (fun p ↦ ∫ y, (a y).coefficient p ∂μ) x ξ =
      ∫ y, mixedDeriv α β (a y).coefficient x ξ ∂μ := by
  rw [mixedDeriv_eq_iteratedFDeriv α β
    ((contDiff_coefficient_integral μ a hjets).of_le (by simp)),
    iteratedFDeriv_integral_of_continuous_jets (μ := μ) isOpen_univ
      (fun y ↦ (a y).contDiff_coefficient.contDiffOn) (fun k ↦ (hjets k).continuousOn)
      _ (mem_univ (x, ξ))]
  have hi : Integrable
      (fun y ↦ iteratedFDeriv ℝ (mixedDirections α β).length (a y).coefficient (x, ξ)) μ :=
    ((hjets (mixedDirections α β).length).comp
      (continuous_id.prodMk (continuous_const (y := (x, ξ))))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [ContinuousMultilinearMap.integral_apply hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y ↦
    (mixedDeriv_eq_iteratedFDeriv α β ((a y).contDiff_coefficient.of_le (by simp)) x ξ).symm

private theorem norm_mixedDeriv_integral_le (α β : List (Fin n)) (x ξ : CoordinateSpace n)
    {C : ℝ} (hC : ∀ y, ‖mixedDeriv α β (a y).coefficient x ξ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)) :
    ‖mixedDeriv α β (fun p ↦ ∫ y, (a y).coefficient p ∂μ) x ξ‖ ≤
      (μ.real univ * C) * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  rw [mixedDeriv_integral_of_continuous_jets μ a hjets]
  exact (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hC)).trans_eq (by ring)

variable (hbound : ∀ K : Set (CoordinateSpace n), IsCompact K → ∀ α β : List (Fin n),
  ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Y, ∀ x ∈ K, ∀ ξ,
    ‖mixedDeriv α β (a y).coefficient x ξ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2))

/-- The coefficient integral of a compact family with jointly continuous spatial jets and
parameter-uniform symbol estimates is a symbol of the same order. -/
def integral : Symbol n V W m where
  coefficient p := ∫ y, (a y).coefficient p ∂μ
  contDiff_coefficient := contDiff_coefficient_integral μ a hjets
  exists_bound K hK α β := by
    obtain ⟨C, hC, h⟩ := hbound K hK α β
    exact ⟨μ.real univ * C, mul_nonneg measureReal_nonneg hC,
      fun x hx ξ ↦ norm_mixedDeriv_integral_le μ a hjets α β x ξ (fun y ↦ h y x hx ξ)⟩

/-- The coefficient of the symbol integral is the pointwise integral of the coefficients. -/
@[simp]
theorem coefficient_integral (p : CoordinateSpace n × CoordinateSpace n) :
    (integral μ a hjets hbound).coefficient p = ∫ y, (a y).coefficient p ∂μ :=
  (rfl)

/-- A parameter-uniform seminorm bound `C ≥ 0` becomes `μ.real univ * C` after integration. -/
theorem seminorm_integral_le (K : TopologicalSpace.Compacts (CoordinateSpace n))
    (α β : List (Fin n)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ y, Symbol.seminorm K α β (a y) ≤ C) :
    Symbol.seminorm K α β (integral μ a hjets hbound) ≤ μ.real univ * C := by
  refine seminorm_le_bound K α β _ (mul_nonneg measureReal_nonneg hC) fun x hx ξ ↦ ?_
  exact norm_mixedDeriv_integral_le μ a hjets α β x ξ fun y ↦
    (le_seminorm K α β (a y) hx ξ).trans
      (mul_le_mul_of_nonneg_right (h y) (rpow_weight_pos ξ _).le)

/-- Averaging with a probability measure preserves every parameter-uniform seminorm bound. -/
theorem seminorm_integral_le_of_probability [IsProbabilityMeasure μ]
    (K : TopologicalSpace.Compacts (CoordinateSpace n)) (α β : List (Fin n))
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ y, Symbol.seminorm K α β (a y) ≤ C) :
    Symbol.seminorm K α β (integral μ a hjets hbound) ≤ C := by
  simpa using seminorm_integral_le μ a hjets hbound K α β hC h

end TauCeti.Symbol
