/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.Representative
public import TauCeti.Analysis.Sobolev.W1p.Zero
import TauCeti.Analysis.Calculus.Gradient

/-!
# Endpoint obstruction to approximation in `W^{1,∞}_0`

The full `W^{1,∞}` norm detects boundary values of a continuous weak derivative, not just
boundary values of the function. If the weak derivative of `u` has a continuous representative
`g` on `[a,b]`, then the distance from `u` to any element of the closure-defined
`W^{1,∞}_0(a,b)` is at least `max (|g a|) (|g b|)`. In particular, membership in that closure
forces both endpoint derivatives to vanish.

The polynomial `x(1-x)` on `(0,1)` has zero endpoint trace but is at distance at least one
from `W^{1,∞}_0(0,1)`. Thus the kernel of the endpoint trace is not contained in the
full-norm closure of the test functions at the infinite exponent.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., §3, for the distinction between
  zero trace and approximation by test functions at the infinite exponent.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Gradient Distributions

namespace TauCeti.W1p

/-- A continuous representative of the weak derivative gives an endpoint lower bound on the
`W^{1,∞}` distance to the closure of the test functions. -/
theorem max_abs_gradient_endpoints_le_dist {a b : ℝ} (hab : a < b)
    {u v : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ ⊤} {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b))
    (hu : gradient u =ᵐ[volume.restrict (Ioo a b)] g)
    (hv : v ∈ w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ ⊤) :
    max |g a| |g b| ≤ dist u v := by
  -- The distance bound is closed in `v`, so it suffices to test it on test functions.
  refine w1p0Submodule_subset_of_isClosed
    (isClosed_le continuous_const (continuous_const.dist continuous_id)) ?_ hv
  intro φ
  let w := ofTestFunctionₗ volume ⟨Ioo a b, isOpen_Ioo⟩ ⊤ φ
  have hG : ∀ᵐ t ∂volume.restrict (Ioo a b),
      ‖g t - ∇ (φ : ℝ → ℝ) t‖ ≤ dist u w := by
    have hw : gradient w =ᵐ[volume.restrict (Ioo a b)] ∇ (φ : ℝ → ℝ) := by
      rw [gradient_ofTestFunctionₗ]
      exact gradientTestFunctionLp_apply_ae ⊤ φ
    filter_upwards [ae_norm_gradient_sub_le_dist u w, hu, hw] with t ht hut hwt
    simpa only [hut, hwt] using ht
  -- Express the bound as an equality of continuous functions to recover endpoint values.
  have hc : ContinuousOn (fun t ↦ max ‖g t - ∇ (φ : ℝ → ℝ) t‖ (dist u w)) (Icc a b) :=
    (hg.sub (φ.contDiff.continuous_gradient (by simp)).continuousOn).norm.sup
      continuousOn_const
  have heq := Measure.eqOn_Icc_of_ae_eq volume hab.ne
    (by
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact hG.mono fun t ht ↦ max_eq_right ht) hc continuousOn_const
  have hzero (x : ℝ) (hx : x ∉ Ioo a b) : ∇ (φ : ℝ → ℝ) x = 0 :=
    gradient_of_notMem_tsupport (fun h ↦ hx (φ.tsupport_subset h))
  have ha := heq (left_mem_Icc.2 hab.le)
  have hb := heq (right_mem_Icc.2 hab.le)
  simp only [hzero a (by simp), sub_zero, Real.norm_eq_abs] at ha
  simp only [hzero b (by simp), sub_zero, Real.norm_eq_abs] at hb
  exact max_le (max_eq_right_iff.1 ha) (max_eq_right_iff.1 hb)

/-- A continuous weak derivative of an element of `W^{1,∞}_0(a,b)` vanishes at both
endpoints. This is an additional boundary condition beyond zero trace of the function. -/
theorem gradient_endpoints_eq_zero_of_mem_w1p0Submodule {a b : ℝ} (hab : a < b)
    {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ ⊤} {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b))
    (hu : gradient u =ᵐ[volume.restrict (Ioo a b)] g)
    (hu0 : u ∈ w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ ⊤) :
    g a = 0 ∧ g b = 0 := by
  have h := max_abs_gradient_endpoints_le_dist hab hg hu hu0
  simp only [dist_self, max_le_iff, abs_nonpos_iff] at h
  exact h

/-- The polynomial `x(1-x)` has zero endpoint trace on `(0,1)`, but its `W^{1,∞}` distance
from every zero-boundary element is at least one. In particular, zero trace does not imply
membership in the full-norm closure of test functions. -/
theorem exists_intervalTraceL_eq_zero_notMem_w1p0Submodule_top :
    ∃ u : W1p volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ ⊤,
      (value u =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun x ↦ x * (1 - x)) ∧
      intervalTraceL (by norm_num : (0 : ℝ) < 1) u = 0 ∧
      (∀ v ∈ w1p0Submodule volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ ⊤, 1 ≤ dist u v) ∧
      u ∉ w1p0Submodule volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ ⊤ := by
  have hf : ContDiff ℝ 1 (fun x : ℝ ↦ x * (1 - x)) := by fun_prop
  obtain ⟨u, huv, hug⟩ := exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact
    (mu := volume) (Omega := ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩) (p := ⊤)
    isOpen_univ hf.contDiffOn isCompact_Icc Ioo_subset_Icc_self (subset_univ _)
  have hderiv (x : ℝ) : ∇ (fun x : ℝ ↦ x * (1 - x)) x = 1 - 2 * x := by
    rw [gradient_eq_deriv']
    have hd : HasDerivAt (fun x : ℝ ↦ x * (1 - x)) (1 * (1 - x) + x * (0 - 1)) x :=
      (hasDerivAt_id x).mul ((hasDerivAt_const x 1).sub (hasDerivAt_id x))
    rw [hd.deriv]
    ring
  have hug' : gradient u =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun x ↦ 1 - 2 * x := by
    filter_upwards [hug] with x hx using hx.trans (hderiv x)
  have hdist : ∀ v ∈ w1p0Submodule volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ ⊤,
      1 ≤ dist u v := by
    intro v hv
    have h := max_abs_gradient_endpoints_le_dist (by norm_num : (0 : ℝ) < 1)
      (g := fun x ↦ 1 - 2 * x) (by fun_prop) hug' hv
    norm_num at h ⊢
    exact h
  refine ⟨u, huv, ?_, hdist, fun h ↦ ?_⟩
  · have hrep : intervalRepresentativeL (by norm_num : (0 : ℝ) < 1) u =
        (⟨fun x ↦ x.val * (1 - x.val), by fun_prop⟩ : C(Icc (0 : ℝ) 1, ℝ)) := by
      apply (intervalRepresentativeL_eq_iff _ _ _).2
      filter_upwards [huv, ae_restrict_mem measurableSet_Ioo] with x hx hmem
      simpa only [projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) (Ioo_subset_Icc_self hmem),
        ContinuousMap.coe_mk] using hx
    simp [intervalTraceL_apply, hrep]
  · exact (not_le_of_gt zero_lt_one) (by simpa only [dist_self] using hdist u h)

end TauCeti.W1p
