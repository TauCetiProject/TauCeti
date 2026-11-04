/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compact.Estimate
public import TauCeti.Analysis.ODE.EnergyEstimate.Global
public import TauCeti.Analysis.ODE.TrajectoryOperator
public import TauCeti.Analysis.Sobolev.GraphStep.Density
public import TauCeti.Analysis.Sobolev.GraphStep.LocalCompactness
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Estimates for the trajectory operator on Sobolev paths

The trajectory operator

`D_A u = u' + A u : W^{1,2}(ℝ, E) → L²(ℝ, E)`

(`TauCeti.WeakDerivStep.trajectoryOperator`, for an `L∞` class of `A`) is controlled on Sobolev
paths by any estimate it satisfies on compactly supported `C¹` paths. An estimate

`a ∫ ‖u'‖² + b ∫ ‖u‖² ≤ c ∫ ‖u' + A u‖² + d ∫_{[-R, R]} ‖u‖²`

on such paths extends to `W^{1,2}(ℝ, E)`, with the last term replaced by the squared norm of the
restriction to a slightly larger interval, because those paths are dense
(`TauCeti.WeakDerivStep.dense_setOf_exists_contDiff_hasCompactSupport`) and both sides are
continuous. Restriction from `W^{1,2}(ℝ, E)` to `L²(-R, R)` is compact (Rellich), so an estimate
with `a, b > 0` is an estimate with a compact error term, the input of Peetre's lemma. This is how
the Fredholm property of `D_A` is proved in `TauCeti.Analysis.ODE.EnergyEstimate.Lyapunov`.

When `A` is a `C¹` family of symmetric operators with a spectral gap and a small derivative on the
whole line, rather than only near its limits, the coercive estimate for test paths
`TauCeti.integral_norm_deriv_sq_add_mul_integral_norm_sq_le` has no error term, so `D_A` is
injective. This applies in particular to a constant invertible symmetric coefficient.

## Main declarations

* `TauCeti.WeakDerivStep.mul_norm_weakFDeriv_sq_add_mul_norm_prev_sq_le_of_forall_contDiff`: an
  estimate on compactly supported `C¹` paths extends to `W^{1,2}(ℝ, E)`.
* `TauCeti.WeakDerivStep.isCompactOperator_smul_restrictBaseL`: restriction to a bounded interval
  is compact.
* `TauCeti.WeakDerivStep.norm_weakFDeriv_sq_add_mul_norm_prev_sq_le_norm_trajectoryOperator_sq`:
  for a family with a uniform spectral gap `α` and `⟪v, A' v⟫ ≤ β ‖v‖²`, the estimate
  `‖u'‖² + (α² - β) ‖u‖² ≤ ‖D_A u‖²` without compact error.
* `TauCeti.WeakDerivStep.ker_trajectoryOperator_eq_bot`: for such a family with `β < α²`, `D_A` is
  injective.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix A.1 (estimates with a compact error and the Fredholm criterion).
* M. Schwarz, *Morse Homology*, Chapter 2 (the Fredholm property of linearized trajectory
  operators).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter
open scoped ENNReal Topology

namespace TauCeti.WeakDerivStep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {A : ℝ → E →L[ℝ] E}

/-! ### Norms of a path with a smooth compactly supported representative -/

section Smooth

variable {u : WeakDerivStep volume ⊤ 2
  (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))} {φ : ℝ → E}

/-- The squared `L²` norm of a path is the integral of the squared norm of a representative. -/
private theorem norm_prev_sq_eq_integral
    (hu : ⇑(prev _ u) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] φ) :
    ‖prev _ u‖ ^ 2 = ∫ s, ‖φ s‖ ^ 2 := by
  rw [← Lp.integral_norm_sq_eq_norm_sq,
    integral_congr_ae (g := fun s ↦ ‖φ s‖ ^ 2) (hu.mono fun s hs ↦ by rw [hs])]
  simp

/-- The squared `L²` norm of the weak derivative is that of the classical derivative of a `C¹`
representative. -/
private theorem norm_weakFDeriv_sq_eq_integral (hφ : ContDiff ℝ 1 φ)
    (hu : ⇑(prev _ u) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] φ) :
    ‖weakFDeriv _ u‖ ^ 2 = ∫ s, ‖deriv φ s‖ ^ 2 := by
  have hw := ((hasWeakFDerivOn_base_prev _ u).congr_ae hu).ae_eq_fderiv
    ((hφ.continuous_fderiv one_ne_zero).locallyIntegrable.locallyIntegrableOn _)
    fun s _ ↦ hφ.differentiable one_ne_zero s
  rw [← Lp.integral_norm_sq_eq_norm_sq,
    integral_congr_ae (g := fun s ↦ ‖fderiv ℝ φ s‖ ^ 2) (hw.mono fun s hs ↦ by rw [hs])]
  simp [← toSpanSingleton_deriv]

/-- On a path with a `C¹` representative `φ`, the squared norm of `D_A` is
`∫ ‖φ' + A φ‖²`. -/
private theorem norm_trajectoryOperator_sq_eq_integral (hφ : ContDiff ℝ 1 φ)
    (hu : ⇑(prev _ u) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] φ)
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    ‖trajectoryOperator AL u‖ ^ 2 = ∫ s, ‖deriv φ s + A s (φ s)‖ ^ 2 := by
  have hTu := trajectoryOperator_apply_ae_eq_deriv_add AL u hu
    ((hφ.continuous_fderiv one_ne_zero).locallyIntegrable.locallyIntegrableOn _)
    fun s _ ↦ hφ.differentiable one_ne_zero s
  rw [← Lp.integral_norm_sq_eq_norm_sq,
    integral_congr_ae (g := fun s ↦ ‖deriv φ s + A s (φ s)‖ ^ 2) (by
      filter_upwards [hTu, hAL] with s hs hAs
      rw [hs, hAs])]
  simp

/-- Restriction to `(-R', R')` controls the `L²` norm of a representative on `[-R, R]`. -/
private theorem integral_Icc_le_norm_restrictBaseL_sq (hφ : Continuous φ)
    (hφc : HasCompactSupport φ)
    (hu : ⇑(prev _ u) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] φ) {R R' : ℝ} (hR : R < R') :
    ∫ s in Icc (-R) R, ‖φ s‖ ^ 2 ≤
      ‖restrictBaseL _ (V := ⟨Ioo (-R') R', isOpen_Ioo⟩) le_top u‖ ^ 2 := by
  have hKu : restrictBaseL _ (V := ⟨Ioo (-R') R', isOpen_Ioo⟩) le_top u
      =ᵐ[volume.restrict ((⟨Ioo (-R') R', isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)] φ :=
    (restrictBaseL_apply_ae _ le_top u).trans
      (ae_restrict_of_ae_restrict_of_subset (by simp) hu)
  rw [← Lp.integral_norm_sq_eq_norm_sq,
    integral_congr_ae (g := fun s ↦ ‖φ s‖ ^ 2) (hKu.mono fun s hs ↦ by rw [hs])]
  have hcs : HasCompactSupport (fun s ↦ ‖φ s‖ ^ 2) :=
    hφc.norm.comp_left (g := fun x : ℝ ↦ x ^ 2) (by norm_num)
  have hint : Integrable (fun s ↦ ‖φ s‖ ^ 2) volume :=
    (hφ.norm.pow 2).integrable_of_hasCompactSupport hcs
  exact setIntegral_mono_set hint.integrableOn (Eventually.of_forall fun _ ↦ by positivity)
    (Eventually.of_forall (Icc_subset_Ioo (by linarith) hR))

end Smooth

/-- **Extending a test-path estimate to Sobolev paths.** If every compactly supported `C¹` path `φ`
satisfies `a ∫ ‖φ'‖² + b ∫ ‖φ‖² ≤ c ∫ ‖φ' + A φ‖² + d ∫_{[-R, R]} ‖φ‖²` with `d ≥ 0`, then
`a ‖u'‖² + b ‖u‖² ≤ c ‖D_A u‖² + d ‖u‖²_{L²(-R', R')}` for every `u ∈ W^{1,2}(ℝ, E)` and every
`R' > R`. The coefficient of the operator is any `L∞` class `AL` of `A`. -/
theorem mul_norm_weakFDeriv_sq_add_mul_norm_prev_sq_le_of_forall_contDiff
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) {a b c d R R' : ℝ} (hd : 0 ≤ d)
    (hR : R < R')
    (hest : ∀ φ : ℝ → E, ContDiff ℝ 1 φ → HasCompactSupport φ →
      a * (∫ s, ‖deriv φ s‖ ^ 2) + b * (∫ s, ‖φ s‖ ^ 2) ≤
        c * (∫ s, ‖deriv φ s + A s (φ s)‖ ^ 2) + d * ∫ s in Icc (-R) R, ‖φ s‖ ^ 2)
    (u : WeakDerivStep volume ⊤ 2
      (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    a * ‖weakFDeriv _ u‖ ^ 2 + b * ‖prev _ u‖ ^ 2 ≤ c * ‖trajectoryOperator AL u‖ ^ 2 +
      d * ‖restrictBaseL _ (V := ⟨Ioo (-R') R', isOpen_Ioo⟩) le_top u‖ ^ 2 := by
  revert u
  set base := ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
  set V : Opens ℝ := ⟨Ioo (-R') R', isOpen_Ioo⟩
  intro u
  -- The estimate is a closed condition, so it suffices to prove it on smooth compactly supported
  -- paths, where it is the estimate for test paths.
  have hclosed : IsClosed {u : WeakDerivStep volume ⊤ 2 base |
      a * ‖weakFDeriv base u‖ ^ 2 + b * ‖prev base u‖ ^ 2 ≤
        c * ‖trajectoryOperator AL u‖ ^ 2 + d * ‖restrictBaseL base (V := V) le_top u‖ ^ 2} :=
    isClosed_le ((continuous_const.mul
        (((weakFDerivL base).continuous.congr fun u ↦ weakFDerivL_apply base u).norm.pow 2)).add
      (continuous_const.mul
        (((prevL base).continuous.congr fun u ↦ prevL_apply base u).norm.pow 2)))
      ((continuous_const.mul ((trajectoryOperator AL).continuous.norm.pow 2)).add
        (continuous_const.mul ((restrictBaseL base le_top).continuous.norm.pow 2)))
  refine hclosed.closure_subset_iff.mpr ?_
    (dense_setOf_exists_contDiff_hasCompactSupport (by norm_num) u)
  rintro u ⟨φ, hφ, hφc, hu⟩
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hK := mul_le_mul_of_nonneg_left
    (integral_Icc_le_norm_restrictBaseL_sq hφ1.continuous hφc hu hR) hd
  have := hest φ hφ1 hφc
  rw [← norm_prev_sq_eq_integral hu, ← norm_weakFDeriv_sq_eq_integral hφ1 hu,
    ← norm_trajectoryOperator_sq_eq_integral hφ1 hu AL hAL] at this
  rw [Set.mem_ofPred_eq]
  linarith

open scoped InnerProductSpace in
/-- **The coercive trajectory estimate on Sobolev paths.** If a `C¹` family of symmetric operators
satisfies `α ‖v‖ ≤ ‖A s v‖` and `⟪v, A' s v⟫ ≤ β ‖v‖²` everywhere, then
`‖u'‖² + (α² - β) ‖u‖² ≤ ‖D_A u‖²` for every `u ∈ W^{1,2}(ℝ, E)`, with no compact error term. The
coefficient of the operator is any `L∞` class `AL` of `A`. -/
theorem norm_weakFDeriv_sq_add_mul_norm_prev_sq_le_norm_trajectoryOperator_sq
    (hA : ContDiff ℝ 1 A) (hsym : ∀ s, (A s).toLinearMap.IsSymmetric) {α β : ℝ} (hα : 0 ≤ α)
    (hgap : ∀ s v, α * ‖v‖ ≤ ‖A s v‖) (hsmall : ∀ s v, ⟪v, deriv A s v⟫_ℝ ≤ β * ‖v‖ ^ 2)
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A)
    (u : WeakDerivStep volume ⊤ 2
      (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    ‖weakFDeriv _ u‖ ^ 2 + (α ^ 2 - β) * ‖prev _ u‖ ^ 2 ≤ ‖trajectoryOperator AL u‖ ^ 2 := by
  simpa using mul_norm_weakFDeriv_sq_add_mul_norm_prev_sq_le_of_forall_contDiff AL hAL (a := 1)
    (c := 1) le_rfl zero_lt_one (fun φ hφ hφc ↦ by
      simpa using integral_norm_deriv_sq_add_mul_integral_norm_sq_le hA (fun s _ ↦ hsym s) hφ hφc
        hα (fun s _ ↦ hgap s _) (fun s _ ↦ hsmall s _)) u

open scoped InnerProductSpace in
/-- **The trajectory operator of a coercive family is injective.** If a `C¹` family of symmetric
operators satisfies `α ‖v‖ ≤ ‖A s v‖` and `⟪v, A' s v⟫ ≤ β ‖v‖²` everywhere with `β < α²`, then
`u' + A u = 0` has no nonzero solution in `W^{1,2}(ℝ, E)`. -/
theorem ker_trajectoryOperator_eq_bot
    (hA : ContDiff ℝ 1 A) (hsym : ∀ s, (A s).toLinearMap.IsSymmetric) {α β : ℝ} (hα : 0 ≤ α)
    (hgap : ∀ s v, α * ‖v‖ ≤ ‖A s v‖) (hsmall : ∀ s v, ⟪v, deriv A s v⟫_ℝ ≤ β * ‖v‖ ^ 2)
    (hβ : β < α ^ 2) (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    (trajectoryOperator (p := 2) AL).ker = ⊥ := by
  refine LinearMap.ker_eq_bot'.mpr fun u hu ↦ ?_
  have hest := norm_weakFDeriv_sq_add_mul_norm_prev_sq_le_norm_trajectoryOperator_sq hA hsym hα
    hgap hsmall AL hAL u
  have hu' : trajectoryOperator AL u = 0 := by simpa only [ContinuousLinearMap.coe_coe] using hu
  rw [hu', norm_zero, zero_pow two_ne_zero] at hest
  have hprev : ‖prev _ u‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖weakFDeriv _ u‖, sq_nonneg ‖prev _ u‖]
  have hweak : ‖weakFDeriv _ u‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖weakFDeriv _ u‖, sq_nonneg ‖prev _ u‖]
  rw [← norm_le_zero_iff, ← sq_le_sq₀ (norm_nonneg u) le_rfl,
    norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq, hprev, hweak]
  simp

/-- Restriction of `W^{1,2}(ℝ, E)` paths to a bounded interval, scaled by a constant, is
compact. -/
theorem isCompactOperator_smul_restrictBaseL (K R : ℝ) :
    IsCompactOperator (K • restrictBaseL
      (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))
      (V := ⟨Ioo (-R) R, isOpen_Ioo⟩) le_top) := by
  rw [FunLike.coe_smul]
  exact (isCompactOperator_restrictBaseL _ (by norm_num)
    (Metric.isBounded_Ioo (-R) R).isCompact_closure (by simp)).smul K

end TauCeti.WeakDerivStep
