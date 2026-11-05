/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Carlson.RJ
public import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Carlson.Basic

/-!
# Holomorphy of Carlson's third integral in its fourth argument

For fixed nodes `x ∈ slitPlane ∪ {0}` and `y, z ∈ slitPlane`, Carlson's integral
`R_J(x, y, z, p)` is holomorphic for `p ∈ slitPlane`. Its derivative is obtained by
replacing the last factor `(t + p)⁻¹` by `-(t + p)⁻²` in the defining integral.
The derivative integral converges absolutely, including when the first node is zero.
Symmetry in the first three nodes allows the zero node to occur in any position.

This is the parameter dependence needed when using the third symmetric integral in
elliptic integral identities. The already integrable first-kind kernel dominates both
the integral and its derivative locally uniformly in the fourth argument.

## References

* NIST *Digital Library of Mathematical Functions*, §19.16(ii),
  <https://dlmf.nist.gov/19.16>.
* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Chapter 9.

Bastiaan J Braams' `lean-codes`, `Carlson/Elliptic/Standard.lean` at commit `2b8cba1`,
develops the symmetric integrals through the general Carlson R-function. The results here
instead use the direct improper integral; no proof is ported from that development.
-/

public section

open MeasureTheory Set Filter Topology

namespace Complex

/-- The integral obtained by differentiating the fourth-argument kernel of `R_J`
converges absolutely on its slit-plane domain. -/
theorem integrableOn_carlsonRJ_fourth_deriv_integrand {x y z p : ℂ}
    (hx : x ∈ slitPlane ∪ {0}) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane)
    (hp : p ∈ slitPlane) :
    IntegrableOn (fun t : ℝ =>
      ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) * (((t : ℂ) + p)⁻¹) ^ 2) (Ioi 0) := by
  obtain ⟨c, hc, hbound⟩ := TauCeti.exists_pos_forall_mem_ball_mul_one_add_le_norm_add hp
  have hmeas : Measurable (fun t : ℝ => (((t : ℂ) + p)⁻¹) ^ 2) :=
    (continuous_ofReal.measurable.add measurable_const).inv.pow_const 2
  refine (integrableOn_carlsonRF_integrand hx hy hz).mul_bdd (c := (c⁻¹) ^ 2)
    hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have h : c * (1 + t) ≤ ‖p + (t : ℂ)‖ :=
    hbound p (Metric.mem_ball_self hc) ⟨t, ht.le⟩
  have hlower : c ≤ ‖(t : ℂ) + p‖ := by
    rw [add_comm p] at h
    nlinarith [mul_nonneg hc.le ht.le]
  rw [norm_pow, norm_inv]
  exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hc hlower) 2

/-- Differentiating `R_J` in its fourth argument replaces `(t + p)⁻¹` by
`-(t + p)⁻²` under the integral sign. The other nodes may include one zero. -/
theorem hasDerivAt_carlsonRJ_fourth {x y z p : ℂ}
    (hx : x ∈ slitPlane ∪ {0}) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane)
    (hp : p ∈ slitPlane) :
    HasDerivAt (carlsonRJ x y z)
      (-(3 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ),
        ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
          ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) * (((t : ℂ) + p)⁻¹) ^ 2) p := by
  rw [funext (carlsonRJ_def x y z)]
  let f : ℝ → ℂ := fun t =>
    ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
      ((t : ℂ) + z) ^ (-(1 / 2) : ℂ)
  have hf : IntegrableOn f (Ioi 0) := integrableOn_carlsonRF_integrand hx hy hz
  obtain ⟨c, hc, hbound⟩ := TauCeti.exists_pos_forall_mem_ball_mul_one_add_le_norm_add hp
  let s := Metric.ball p c ∩ slitPlane
  have hs : s ∈ 𝓝 p := inter_mem (Metric.ball_mem_nhds p hc) (isOpen_slitPlane.mem_nhds hp)
  have hbound' {q : ℂ} (hq : q ∈ s) {t : ℝ} (ht : t ∈ Ioi 0) :
      ‖((t : ℂ) + q)⁻¹‖ ≤ c⁻¹ := by
    have h : c * (1 + t) ≤ ‖q + (t : ℂ)‖ := hbound q hq.1 ⟨t, ht.le⟩
    have hlower : c ≤ ‖(t : ℂ) + q‖ := by
      rw [add_comm q] at h
      nlinarith [mul_nonneg hc.le ht.le]
    rw [norm_inv]
    exact inv_anti₀ hc hlower
  have hmeas (q : ℂ) :
      AEStronglyMeasurable (fun t : ℝ => ((t : ℂ) + q)⁻¹) (volume.restrict (Ioi 0)) :=
    (continuous_ofReal.measurable.add measurable_const).inv.aestronglyMeasurable
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun q t => f t * ((t : ℂ) + q)⁻¹)
    (F' := fun q t => -(f t * (((t : ℂ) + q)⁻¹) ^ 2))
    (bound := fun t => ‖f t‖ * (c⁻¹) ^ 2) hs
    (Eventually.of_forall fun q => hf.aestronglyMeasurable.mul (hmeas q))
    (integrableOn_carlsonRJ_integrand hx hy hz hp)
    ((integrableOn_carlsonRJ_fourth_deriv_integrand hx hy hz hp).neg.aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro q hq
      simp only [norm_neg, norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hbound' hq ht) 2) (norm_nonneg _))
    (hf.norm.mul_const _) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro q hq
      have hne := slitPlane_ne_zero (TauCeti.ofReal_add_mem_slitPlane hq.2 ht.le)
      convert (((hasDerivAt_id q).const_add (t : ℂ)).inv hne).const_mul (f t) using 1 <;>
        simp [pow_two, div_eq_mul_inv, mul_comm, mul_assoc])
  rw [integral_neg] at hderiv
  simpa only [f, mul_neg, neg_mul] using hderiv.2.const_mul (3 / 2 : ℂ)

/-- For fixed admissible nodes, `R_J` is complex differentiable in its fourth
argument throughout the slit plane. -/
theorem differentiableOn_carlsonRJ_fourth {x y z : ℂ}
    (hx : x ∈ slitPlane ∪ {0}) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    DifferentiableOn ℂ (carlsonRJ x y z) slitPlane := fun _ hp =>
  (hasDerivAt_carlsonRJ_fourth hx hy hz hp).differentiableAt.differentiableWithinAt

/-- For fixed admissible nodes, `R_J` is holomorphic in its fourth argument
on the slit plane. -/
theorem analyticOnNhd_carlsonRJ_fourth {x y z : ℂ}
    (hx : x ∈ slitPlane ∪ {0}) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    AnalyticOnNhd ℂ (carlsonRJ x y z) slitPlane :=
  (differentiableOn_carlsonRJ_fourth hx hy hz).analyticOnNhd isOpen_slitPlane

end Complex
