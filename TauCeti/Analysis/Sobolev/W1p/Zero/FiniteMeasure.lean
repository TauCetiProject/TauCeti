/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.FiniteMeasure

/-!
# `W^{1,p}_0(Ω)` on sets of finite measure

Two facts about the zero-boundary Sobolev spaces of an open set `Ω` of finite measure, which let
solutions of the Dirichlet problem found in `H¹₀(Ω) = W^{1,2}_0(Ω)` be compared, as elements of
`W^{1,p}_0(Ω)` with `p < 2`, in the `W^{1,p}` norm.

* **Lowering the exponent.** `W^{1,q}(Ω) ⊆ W^{1,p}(Ω)` for `p ≤ q` (`TauCeti.W1p.ofExponentLEL`),
  and this inclusion respects the homogeneous Dirichlet condition: it maps `W^{1,q}_0(Ω)` into
  `W^{1,p}_0(Ω)`. A test function's jet in `W^{1,q}(Ω)` is sent to its jet in `W^{1,p}(Ω)`, and
  `W^{1,p}_0(Ω)` is closed, so the closure of the test functions in the stronger norm lands in their
  closure in the weaker one.
* **The Poincaré inequality for the full norm.** In dimension `n ≥ 1` and for `p < ∞`, the
  `W^{1,p}` norm of `u ∈ W^{1,p}_0(Ω)` is at most a constant times `‖∇u‖_{Lᵖ}`. This is the case
  `q = p` of the Sobolev inequality on sets of finite measure,
  `TauCeti.W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt`.

## Main declarations

* `TauCeti.W1p.ofExponentLE_mem_w1p0Submodule`: the inclusion maps `W^{1,q}_0(Ω)` into
  `W^{1,p}_0(Ω)`.
* `TauCeti.W1p0.ofExponentLEL`: the continuous linear inclusion `W^{1,q}_0(Ω) → W^{1,p}_0(Ω)`;
  its underlying `W^{1,p}(Ω)` function is `TauCeti.W1p.ofExponentLE` of the original one
  (`TauCeti.W1p0.coe_ofExponentLEL`), so it changes neither the value nor the weak gradient.
* `TauCeti.W1p.exists_forall_enorm_le_mul_enorm_gradient_of_measure_ne_top`: the Poincaré
  inequality `‖u‖_{W^{1,p}} ≤ C ‖∇u‖_{Lᵖ}` on `W^{1,p}_0(Ω)`.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Module TopologicalSpace
open scoped Distributions ENNReal NNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p q : ENNReal} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [IsFiniteMeasure (mu.restrict (Omega : Set E))]

section Exponent

/-- Lowering the exponent sends the jet of a test function in `W^{1,q}(Ω)` to its jet in
`W^{1,p}(Ω)`. -/
@[simp]
theorem W1p.ofExponentLE_ofTestFunctionₗ (hpq : p ≤ q) (phi : 𝓓(Omega, ℝ)) :
    W1p.ofExponentLE hpq (W1p.ofTestFunctionₗ mu Omega q phi) =
      W1p.ofTestFunctionₗ mu Omega p phi := by
  refine W1p.ext (Lp.ext ?_) (Lp.ext ?_)
  · rw [W1p.coeFn_value_ofExponentLE]
    exact (W1p.value_ofTestFunctionₗ_ae (mu := mu) (p := q) phi).trans
      (W1p.value_ofTestFunctionₗ_ae phi).symm
  · rw [W1p.coeFn_gradient_ofExponentLE, W1p.gradient_ofTestFunctionₗ,
      W1p.gradient_ofTestFunctionₗ]
    filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) q phi,
      gradientTestFunctionLp_apply_ae (mu := mu) p phi] with x hq hp
    rw [hq, hp]

/-- On a set of finite measure, lowering the exponent maps `W^{1,q}_0(Ω)` into `W^{1,p}_0(Ω)`. -/
theorem W1p.ofExponentLE_mem_w1p0Submodule (hpq : p ≤ q) {u : W1p mu Omega q}
    (hu : u ∈ w1p0Submodule mu Omega q) :
    W1p.ofExponentLE hpq u ∈ w1p0Submodule mu Omega p := by
  have hclosed : IsClosed {v : W1p mu Omega q |
      W1p.ofExponentLEL hpq v ∈ w1p0Submodule mu Omega p} :=
    (w1p0Submodule mu Omega p).isClosed.preimage (W1p.ofExponentLEL hpq).continuous
  have h := w1p0Submodule_subset_of_isClosed hclosed (fun phi => by
    simpa only [Set.mem_ofPred_eq, W1p.ofExponentLEL_apply, W1p.ofExponentLE_ofTestFunctionₗ]
      using W1p.ofTestFunctionₗ_mem_w1p0Submodule phi) hu
  rwa [Set.mem_ofPred_eq, W1p.ofExponentLEL_apply] at h

/-- **The inclusion `W^{1,q}_0(Ω) → W^{1,p}_0(Ω)`** for `p ≤ q` on a set of finite measure: the
restriction of `TauCeti.W1p.ofExponentLEL` to the zero-boundary spaces. -/
def W1p0.ofExponentLEL (hpq : p ≤ q) : W1p0 mu Omega q →L[ℝ] W1p0 mu Omega p :=
  ContinuousLinearMap.codRestrict
    ((W1p.ofExponentLEL hpq).comp (w1p0Submodule mu Omega q).toSubmodule.subtypeL)
    (w1p0Submodule mu Omega p).toSubmodule
    fun u => by
      rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, W1p.ofExponentLEL_apply]
      exact W1p.ofExponentLE_mem_w1p0Submodule hpq u.property

/-- The underlying `W^{1,p}(Ω)` function of the inclusion is the exponent-lowered function. -/
@[simp]
theorem W1p0.coe_ofExponentLEL (hpq : p ≤ q) (u : W1p0 mu Omega q) :
    (W1p0.ofExponentLEL hpq u : W1p mu Omega p) = W1p.ofExponentLE hpq (u : W1p mu Omega q) := by
  rw [W1p0.ofExponentLEL, ContinuousLinearMap.coe_codRestrict_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, W1p.ofExponentLEL_apply]

end Exponent

omit [Fact (1 ≤ q)] [IsFiniteMeasure (mu.restrict (Omega : Set E))] in
/-- **The Poincaré inequality on `W^{1,p}_0(Ω)` for `Ω` of finite measure.** In dimension
`n ≥ 1` and for `p < ∞`, there is a constant `C` with `‖u‖_{W^{1,p}} ≤ C ‖∇u‖_{Lᵖ}` for every
`u ∈ W^{1,p}_0(Ω)`. No regularity of `Ω` is assumed. -/
theorem W1p.exists_forall_enorm_le_mul_enorm_gradient_of_measure_ne_top [Nontrivial E]
    (hp : p ≠ ∞) (hOmega : mu Omega ≠ ∞) :
    ∃ C : ℝ≥0, ∀ u ∈ w1p0Submodule mu Omega p, ‖u‖ₑ ≤ C * ‖W1p.gradient u‖ₑ := by
  set n : ℝ := (finrank ℝ E : ℝ)
  have hn : 0 < n⁻¹ := inv_pos.2 (Nat.cast_pos.2 finrank_pos)
  have hpp : p = (p.toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal hp).symm
  -- The Sobolev inequality at `q = p`, that is `δ = 0`, bounds the value.
  set S : ℝ≥0∞ := ENNReal.ofReal (n⁻¹ * mu.real (Metric.ball 0 1) ^ (-n⁻¹) *
    ((1 - 0) / (n⁻¹ - 0)) ^ ((1 : ℝ) - 0)) * mu Omega ^ (n⁻¹ - 0)
  have hS : S ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by linarith) hOmega)
  refine ⟨(S + 1).toNNReal, fun u hu => ?_⟩
  have hval := W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt (q := p.toNNReal)
    hOmega hpp.le (sub_self _) hn hu
  rw [← hpp] at hval
  rw [ENNReal.coe_toNNReal (ENNReal.add_ne_top.2 ⟨hS, ENNReal.one_ne_top⟩), add_mul, one_mul]
  refine (W1p.enorm_le_enorm_value_add_enorm_gradient _).trans (add_le_add ?_ le_rfl)
  rwa [Lp.eNorm_def]

end TauCeti
