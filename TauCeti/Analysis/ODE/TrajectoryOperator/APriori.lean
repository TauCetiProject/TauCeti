/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import TauCeti.Analysis.ODE.TrajectoryOperator
public import TauCeti.Analysis.Sobolev.GraphStep.Density

/-!
# A priori estimates and surjectivity of the trajectory operator from smooth paths

Let `D_A u = u' + A u` be the trajectory operator from `W^{1,p}(ℝ, E)` to `Lᵖ(ℝ, E)`
(`TauCeti.WeakDerivStep.trajectoryOperator`), for an essentially bounded coefficient `A` and
`1 ≤ p < ∞`. Its basic estimates and its surjectivity reduce to statements about smooth compactly
supported paths, where `D_A` acts classically:

* an estimate `‖φ‖_{Lᵖ} ≤ C ‖φ' + A φ‖_{Lᵖ}` for every smooth compactly supported `φ` extends to
  all of `W^{1,p}(ℝ, E)` when `E` is finite-dimensional, since such paths are dense there and
  both sides are continuous
  (`TauCeti.WeakDerivStep.norm_prev_le_mul_norm_trajectoryOperator_of_forall_contDiff`);
* such an estimate on the value of `u` controls its whole graph norm, because `u' = D_A u - A u`
  (`TauCeti.WeakDerivStep.norm_le_mul_norm_trajectoryOperator_of_norm_prev_le`);
* a graph-norm estimate makes the range of `D_A` closed, so `D_A` is onto as soon as its range
  contains every smooth compactly supported path, these being dense in `Lᵖ`
  (`TauCeti.WeakDerivStep.surjective_trajectoryOperator_of_forall_norm_le`).

These are the steps by which an explicit solution formula for `u' + A u = f`, valid for smooth
compactly supported `f`, shows that `D_A` is invertible; they are used for constant hyperbolic
coefficients (`TauCeti.Analysis.ODE.TrajectoryOperator.Hyperbolic`) and for expanding scalar
coefficients (`TauCeti.Analysis.ODE.TrajectoryOperator.ScalarGreen`).

## References

* K. J. Palmer, *Exponential dichotomies and transversal homoclinic points*, J. Differential
  Equations **55** (1984), 225--256 (the operator `u ↦ u' - A(t) u` and its a priori estimates).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace TauCeti.WeakDerivStep

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}

/-- **An estimate on the value controls the graph norm.** If `u ∈ W^{1,p}(ℝ, E)` satisfies
`‖u‖_{Lᵖ} ≤ C ‖D_A u‖_{Lᵖ}`, then its graph norm satisfies
`‖u‖ ≤ (1 + (1 + ‖A‖) C) ‖D_A u‖_{Lᵖ}`, since its weak derivative is `D_A u - A u`. -/
theorem norm_le_mul_norm_trajectoryOperator_of_norm_prev_le {C : ℝ}
    (u : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp E p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))))
    (h : ‖prev _ u‖ ≤ C * ‖trajectoryOperator AL u‖) :
    ‖u‖ ≤ (1 + (1 + ‖AL‖) * C) * ‖trajectoryOperator AL u‖ := by
  have hweak := norm_weakFDeriv_le_norm_trajectoryOperator_add AL u
  have hsum : ‖u‖ ≤ ‖prev _ u‖ + ‖weakFDeriv _ u‖ := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg u) (by positivity) two_ne_zero).mp ?_
    rw [norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq]
    nlinarith [norm_nonneg (prev _ u), norm_nonneg (weakFDeriv _ u)]
  calc ‖u‖ ≤ ‖trajectoryOperator AL u‖ + (1 + ‖AL‖) * ‖prev _ u‖ := by linarith
    _ ≤ ‖trajectoryOperator AL u‖ + (1 + ‖AL‖) * (C * ‖trajectoryOperator AL u‖) := by gcongr
    _ = (1 + (1 + ‖AL‖) * C) * ‖trajectoryOperator AL u‖ := by ring

/-- **A priori estimates extend from smooth compactly supported paths.** Let `E` be
finite-dimensional, `1 ≤ p < ∞`, `C ≥ 0`, and `AL` the `L∞` class of a coefficient `A`. If
`‖φ‖_{Lᵖ} ≤ C ‖φ' + A φ‖_{Lᵖ}` for every smooth compactly supported `φ`, then
`‖u‖_{Lᵖ} ≤ C ‖D_A u‖_{Lᵖ}` for every `u ∈ W^{1,p}(ℝ, E)`. -/
theorem norm_prev_le_mul_norm_trajectoryOperator_of_forall_contDiff [FiniteDimensional ℝ E]
    (hp : p ≠ ∞) {A : ℝ → E →L[ℝ] E}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ φ : ℝ → E, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      eLpNorm φ p volume ≤ ENNReal.ofReal C * eLpNorm (fun s ↦ deriv φ s + A s (φ s)) p volume)
    (u : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp E p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    ‖prev _ u‖ ≤ C * ‖trajectoryOperator AL u‖ := by
  -- Abstract the base map before introducing `u`, so that the closed set below and the density
  -- statement are stated over the same graph space.
  revert u
  set base := ContinuousLinearMap.id ℝ (Lp E p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
  intro u
  -- The estimate is a closed condition, so it suffices to prove it on smooth compactly supported
  -- paths, where `D_A` acts classically.
  have hclosed : IsClosed {u : WeakDerivStep volume ⊤ p base |
      ‖prev base u‖ ≤ C * ‖trajectoryOperator AL u‖} :=
    isClosed_le ((prevL base).continuous.congr fun u ↦ prevL_apply base u).norm
      (continuous_const.mul (trajectoryOperator AL).continuous.norm)
  refine hclosed.closure_subset_iff.mpr ?_ (dense_setOf_exists_contDiff_hasCompactSupport hp u)
  rintro u ⟨φ, hφ, hφc, huφ⟩
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hTu : trajectoryOperator AL u =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ deriv φ s + A s (φ s) := by
    filter_upwards [trajectoryOperator_apply_ae_eq_deriv_add AL u huφ
      ((hφ1.continuous_fderiv one_ne_zero).locallyIntegrable.locallyIntegrableOn _)
      (fun s _ ↦ hφ1.differentiable one_ne_zero s), hAL] with s hs' hAs
    rw [hs', hAs]
  have hfin : eLpNorm (fun s ↦ deriv φ s + A s (φ s)) p volume ≠ ∞ := by
    have h' := Lp.eLpNorm_ne_top (trajectoryOperator AL u)
    rwa [eLpNorm_congr_ae hTu, Opens.coe_top, Measure.restrict_univ] at h'
  rw [Set.mem_ofPred_eq, Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae huφ, eLpNorm_congr_ae hTu]
  simp only [Opens.coe_top, Measure.restrict_univ]
  calc (eLpNorm φ p volume).toReal
      ≤ (ENNReal.ofReal C * eLpNorm (fun s ↦ deriv φ s + A s (φ s)) p volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) (h φ hφ hφc)
    _ = C * (eLpNorm (fun s ↦ deriv φ s + A s (φ s)) p volume).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC]

/-- **Surjectivity from an a priori estimate and smooth solutions.** For `1 ≤ p < ∞`, if
`‖u‖ ≤ C ‖D_A u‖_{Lᵖ}` on `W^{1,p}(ℝ, E)` and every smooth compactly supported `f` is `D_A u`
for some `u`, then `D_A` maps `W^{1,p}(ℝ, E)` onto `Lᵖ(ℝ, E)`: the estimate makes its range
closed, and the range is dense. -/
theorem surjective_trajectoryOperator_of_forall_norm_le (hp : p ≠ ∞) {C : ℝ}
    (hC : ∀ u, ‖u‖ ≤ C * ‖trajectoryOperator (p := p) AL u‖)
    (h : ∀ f : ℝ → E, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      ∃ u : WeakDerivStep volume ⊤ p
          (ContinuousLinearMap.id ℝ (Lp E p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))),
        ⇑(trajectoryOperator AL u) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] f) :
    Function.Surjective (trajectoryOperator (p := p) AL) := by
  have hanti : AntilipschitzWith C.toNNReal (trajectoryOperator (p := p) AL) :=
    (trajectoryOperator (p := p) AL).antilipschitz_of_bound fun u ↦
      (hC u).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C) (norm_nonneg _))
  have hclosed : IsClosed (range (trajectoryOperator (p := p) AL)) :=
    hanti.isClosed_range (trajectoryOperator (p := p) AL).uniformContinuous
  -- The range contains every smooth compactly supported path, and these are dense in `Lᵖ`.
  have hdense : Dense (range (trajectoryOperator (p := p) AL)) := by
    refine (Lp.dense_hasCompactSupport_contDiff hp).mono ?_
    rintro f ⟨g, hfg, hgc, hg⟩
    obtain ⟨u, hTu⟩ := h g hg hgc
    exact ⟨u, Lp.ext (hTu.trans hfg.symm)⟩
  exact range_eq_univ.mp (hclosed.closure_eq.symm.trans hdense.closure_eq)

end TauCeti.WeakDerivStep
