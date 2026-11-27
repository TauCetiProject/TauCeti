/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ACL.Basic

import TauCeti.Analysis.Calculus.ACL.Measurable
import TauCeti.Analysis.Calculus.ACL.Puncture
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Check: `|x|^{1/2}` on `ℝ²` is `ACL^p` exactly for `p < 4`

The map `u(x) = |x|^{1/2}` on `ℝ² = EuclideanSpace ℝ (Fin 2)` is continuous and smooth off the
origin, so it is `ACL` (`TauCeti.ACLChecks.isACLOn_sqrtNorm`, through
`TauCeti.isACLOn_of_contDiffOn_diff_singleton`), although it is not Lipschitz near `0`. Off the
origin its formal derivative is its derivative, of norm `|∇u| = |x|^{-1/2} / 2`
(`TauCeti.ACLChecks.norm_formalDeriv_sqrtNorm`). Since `∫_{|x|<1} |x|^{-p/2} dx` is finite exactly
when `p < 4`, `u` is `ACL^p` on `ℝ²` exactly for `p < 4`
(`TauCeti.ACLChecks.isACLpOn_sqrtNorm_iff`); in particular it is not `ACL^∞`.
-/

public section

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

noncomputable section

namespace TauCeti.ACLChecks

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The map `x ↦ |x|^{1/2}` on `ℝ²`. -/
def sqrtNorm (x : ℝ²) : ℝ := ‖x‖ ^ (1 / 2 : ℝ)

theorem sqrtNorm_apply (x : ℝ²) : sqrtNorm x = ‖x‖ ^ (1 / 2 : ℝ) := (rfl)

/-- `|x|^{1/2}` is `ACL` on `ℝ²`: it is continuous, and smooth off the origin. -/
theorem isACLOn_sqrtNorm : IsACLOn sqrtNorm univ := by
  have hfun : sqrtNorm = fun x : ℝ² ↦ ‖x‖ ^ (1 / 2 : ℝ) := funext sqrtNorm_apply
  rw [hfun]
  refine isACLOn_of_contDiffOn_diff_singleton le_rfl isOpen_univ ?_ fun x hx ↦ ?_
  · exact (continuous_norm.rpow_const fun _ ↦ Or.inr (by norm_num)).continuousOn
  · exact (contDiffAt_norm_rpow_of_ne _ hx.2).contDiffWithinAt

/-- Off the origin, the formal derivative of `|x|^{1/2}` has norm `|x|^{-1/2} / 2`. -/
theorem norm_formalDeriv_sqrtNorm {x : ℝ²} (hx : x ≠ 0) :
    ‖formalDeriv sqrtNorm x‖ = 1 / 2 * ‖x‖ ^ (-(1 / 2) : ℝ) := by
  have hfun : sqrtNorm = fun x : ℝ² ↦ ‖x‖ ^ (1 / 2 : ℝ) := funext sqrtNorm_apply
  rw [hfun, formalDeriv_eq_fderiv (hasFDerivAt_norm_rpow_of_ne _ hx).differentiableAt,
    norm_fderiv_norm_rpow_of_ne _ hx]
  norm_num

/-- Almost everywhere, the `q`-th power of the norm of the formal derivative of `|x|^{1/2}` is
`(1/2)^q |x|^{-q/2}`. -/
private theorem ae_norm_formalDeriv_sqrtNorm_rpow (q : ℝ) :
    ∀ᵐ x : ℝ², ‖formalDeriv sqrtNorm x‖ ^ q = (1 / 2) ^ q * ‖x‖ ^ (-(q / 2)) := by
  have h0 : ∀ᵐ x : ℝ², x ∉ ({0} : Set ℝ²) :=
    measure_eq_zero_iff_ae_notMem.1 (measure_singleton 0)
  filter_upwards [h0] with x hx
  rw [norm_formalDeriv_sqrtNorm hx, Real.mul_rpow (by norm_num) (by positivity),
    ← Real.rpow_mul (norm_nonneg _)]
  ring_nf

/-- **`|x|^{1/2}` is `ACL^p` on `ℝ²` exactly when `p < 4`.** Its gradient `|x|^{-1/2} / 2` is
`p`-th power integrable near the origin exactly when `∫₀¹ r^{1 - p/2} dr < ∞`. -/
theorem isACLpOn_sqrtNorm_iff {p : ℝ≥0∞} : IsACLpOn sqrtNorm p univ ↔ p < 4 := by
  have hm : AEStronglyMeasurable (formalDeriv sqrtNorm) volume := by
    simpa using isACLOn_sqrtNorm.aestronglyMeasurable_formalDeriv (μ := volume) isOpen_univ
  have hdim : (Module.finrank ℝ ℝ² : ℝ) = 2 := by simp
  constructor
  · intro h
    by_contra hp
    push Not at hp
    have hK : IsCompact (closedBall (0 : ℝ²) 1) := isCompact_closedBall 0 1
    have : IsFiniteMeasure (volume.restrict (closedBall (0 : ℝ²) 1)) :=
      isFiniteMeasure_restrict.2 hK.measure_ne_top
    have h4 : MemLp (formalDeriv sqrtNorm) 4 (volume.restrict (closedBall (0 : ℝ²) 1)) :=
      (h.memLp_formalDeriv _ (subset_univ _) hK).mono_exponent hp
    have hint := (integrable_norm_rpow_iff hm.restrict (by norm_num) (by simp)).2 h4
    have hint' : IntegrableOn (fun x : ℝ² ↦ (1 / 2 : ℝ) ^ (4 : ℝ) * ‖x‖ ^ (-(4 / 2 : ℝ)))
        (closedBall 0 1) := by
      refine hint.congr ?_
      filter_upwards [ae_restrict_of_ae (ae_norm_formalDeriv_sqrtNorm_rpow 4)] with x hx
      simpa using hx
    have hball : IntegrableOn (fun x : ℝ² ↦ ‖x‖ ^ (-(4 / 2 : ℝ))) (ball 0 1) :=
      IntegrableOn.congr_fun
        ((hint'.mono_set ball_subset_closedBall).const_mul ((1 / 2 : ℝ) ^ (4 : ℝ))⁻¹)
        (fun x _ ↦ by field_simp) measurableSet_ball
    rw [integrableOn_norm_rpow_ball_iff one_pos, hdim] at hball
    norm_num at hball
  · intro hp
    refine ⟨isACLOn_sqrtNorm, fun K _ hK ↦ ?_⟩
    rcases eq_or_ne p 0 with rfl | hp0
    · exact memLp_zero_iff_aestronglyMeasurable.2 hm.restrict
    have hptop : p ≠ ∞ := hp.ne_top
    refine (integrable_norm_rpow_iff hm.restrict hp0 hptop).1 ?_
    obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : ℝ²)
    have hq : p.toReal < 4 := by
      have := (ENNReal.toReal_lt_toReal hptop (by simp)).2 hp
      simpa using this
    have hball : IntegrableOn (fun x : ℝ² ↦ ‖x‖ ^ (-(p.toReal / 2))) (ball 0 R) :=
      integrableOn_norm_rpow_ball (by rw [hdim]; linarith)
    refine ((hball.mono_set hR).const_mul ((1 / 2 : ℝ) ^ p.toReal)).congr ?_
    filter_upwards [ae_restrict_of_ae (ae_norm_formalDeriv_sqrtNorm_rpow p.toReal)] with x hx
    exact hx.symm

end TauCeti.ACLChecks
