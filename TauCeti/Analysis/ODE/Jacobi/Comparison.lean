/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.ODE.Jacobi.Determinant
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Curvature.Sturm

/-!
# Ricci comparison for Jacobi determinant roots

A lower bound on the curvature trace bounds the determinant root of a Jacobi operator above
by the constant-curvature model sine, provided the operator starts at zero with identity
velocity and is nonsingular on the open comparison interval. The estimate includes the right
endpoint. Positive curvature also bounds the interval length by `π / √κ`
(`TauCeti.le_pi_div_sqrt_of_jacobi`). The initial right derivative is established in
`TauCeti.Analysis.Calculus.FDeriv.Det.NormDet`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 11.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section

open Filter Set
open scoped Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- A lower curvature-trace bound gives upper comparison for the genuine Jacobi determinant
root. Endpoint jets are taken within the interval, and symmetry and nonsingularity are
only needed in the open comparison interval. -/
private theorem normDet_rpow_le_curvatureSine_of_jacobi_of_le_pi
    {J V K : ℝ → F →L[ℝ] F} {b t κ : ℝ}
    (hm : 0 < Module.finrank ℝ F)
    (hJ : ∀ r ∈ Icc 0 b, HasDerivWithinAt J (V r) (Icc 0 b) r)
    (hVc : ContinuousOn V (Icc 0 b))
    (hV : ∀ r ∈ Ioo 0 b, HasDerivWithinAt V (-((K r).comp (J r))) (Icc 0 b) r)
    (hK : ∀ r ∈ Ioo 0 b, LinearMap.IsSymmetric (K r).toLinearMap)
    (hzero : J 0 = 0) (hvel : V 0 = ContinuousLinearMap.id ℝ F)
    (hi : ∀ r ∈ Ioo 0 b, (J r).IsInvertible)
    (hRic : ∀ r ∈ Ioo 0 b,
      (Module.finrank ℝ F : ℝ) * κ ≤ LinearMap.trace ℝ F (K r).toLinearMap)
    (hb : 0 < κ → b ≤ Real.pi / Real.sqrt κ) (ht : t ∈ Icc 0 b) :
    (J t).toLinearMap.normDet ^ (1 / (Module.finrank ℝ F : ℝ)) ≤ curvatureSine κ t := by
  by_cases hb0 : 0 < b
  swap
  · have ht0 : t = 0 := by linarith [ht.1, ht.2]
    simp only [ht0, hzero, ContinuousLinearMap.toLinearMap_zero, LinearMap.normDet_zero,
      zero_pow hm.ne', Real.zero_rpow (by positivity : (1 / (Module.finrank ℝ F : ℝ)) ≠ 0),
      curvatureSine_zero_right, le_refl]
  let f := fun r ↦ (J r).toLinearMap.normDet ^ (1 / (Module.finrank ℝ F : ℝ))
  have h0 : 0 ∈ Icc 0 b := ⟨le_rfl, ht.1.trans ht.2⟩
  have hJa (r : ℝ) (hr : r ∈ Ioo 0 b) : HasDerivAt J (V r) r :=
    (hJ r (Ioo_subset_Icc_self hr)).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
  have hc : ContinuousOn f (Icc 0 b) := fun r hr ↦
    (ContinuousLinearMap.continuous_normDet.continuousAt.comp_continuousWithinAt
      (hJ r hr).continuousWithinAt).rpow_const (Or.inr (by positivity))
  have hf0 : f 0 = 0 := by simp [f, hzero, LinearMap.normDet_zero, hm.ne']
  have hfa := hasDerivWithinAt_normDet_rpow_zero hm hzero (by
    simpa only [hvel] using (hJ 0 h0).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hb0))
  have hd (r : ℝ) (hr : r ∈ Ioo 0 b) : DifferentiableAt ℝ f r :=
    (hJa r hr).differentiableAt.normDet_rpow (hi r hr)
  have hdd (r : ℝ) (hr : r ∈ Ioo 0 b) : DifferentiableAt ℝ (deriv f) r :=
    differentiableAt_deriv_normDet_rpow
      (by filter_upwards [Ioo_mem_nhds hr.1 hr.2] with q hq using
        hJa q hq)
      ((hV r hr).hasDerivAt (Icc_mem_nhds hr.1 hr.2)).differentiableAt (hi r hr)
  have hbound (r : ℝ) (hr : r ∈ Ioo 0 b) : deriv (deriv f) r ≤ -κ * f r :=
    deriv2_normDet_rpow_le_of_jacobi hm hJ hVc (by simpa only [interior_Icc] using hV)
      (by simpa only [interior_Icc] using hK)
      (convex_Icc 0 b) h0 (by simp [hzero])
      (by simpa only [interior_Icc] using hr) (hi r hr)
      (by simpa only [mul_neg, neg_mul, neg_neg] using hRic r hr)
  have hcomp := mul_curvatureSine_le_of_hasDerivAt (f := fun r ↦ -f r)
    (f' := fun r ↦ -deriv f r) (f'' := fun r ↦ -deriv (deriv f) r)
    hb hc.neg (by simp only [hf0, neg_zero])
    (hfa.mono Icc_subset_Ici_self).neg
    (fun r hr ↦ (hd r hr).hasDerivAt.neg)
    (fun r hr ↦ (hdd r hr).hasDerivAt.neg)
    (fun r hr ↦ by have := hbound r hr; nlinarith) ht
  simpa only [neg_mul, one_mul, neg_le_neg_iff] using hcomp

/-- A positive lower curvature-trace bound forces a nonsingular Jacobi interval to end no
later than the first model zero. Positive dimension is necessary for this conjugate-radius bound. -/
theorem le_pi_div_sqrt_of_jacobi
    {J V K : ℝ → F →L[ℝ] F} {b κ : ℝ}
    (hm : 0 < Module.finrank ℝ F)
    (hJ : ∀ r ∈ Icc 0 b, HasDerivWithinAt J (V r) (Icc 0 b) r)
    (hVc : ContinuousOn V (Icc 0 b))
    (hV : ∀ r ∈ Ioo 0 b, HasDerivWithinAt V (-((K r).comp (J r))) (Icc 0 b) r)
    (hK : ∀ r ∈ Ioo 0 b, LinearMap.IsSymmetric (K r).toLinearMap)
    (hzero : J 0 = 0) (hvel : V 0 = ContinuousLinearMap.id ℝ F)
    (hi : ∀ r ∈ Ioo 0 b, (J r).IsInvertible)
    (hRic : ∀ r ∈ Ioo 0 b,
      (Module.finrank ℝ F : ℝ) * κ ≤ LinearMap.trace ℝ F (K r).toLinearMap)
    (hκ : 0 < κ) : b ≤ Real.pi / Real.sqrt κ := by
  by_contra! hb
  have hc : 0 < Real.pi / Real.sqrt κ := div_pos Real.pi_pos (Real.sqrt_pos.mpr hκ)
  have hcomp := normDet_rpow_le_curvatureSine_of_jacobi_of_le_pi hm
    (fun r hr ↦ (hJ r ⟨hr.1, hr.2.trans hb.le⟩).mono (Icc_subset_Icc_right hb.le))
    (hVc.mono (Icc_subset_Icc_right hb.le))
    (fun r hr ↦ (hV r ⟨hr.1, hr.2.trans hb⟩).mono (Icc_subset_Icc_right hb.le))
    (fun r hr ↦ hK r ⟨hr.1, hr.2.trans hb⟩) hzero hvel
    (fun r hr ↦ hi r ⟨hr.1, hr.2.trans hb⟩)
    (fun r hr ↦ hRic r ⟨hr.1, hr.2.trans hb⟩)
    (fun _ ↦ le_rfl) (right_mem_Icc.mpr hc.le)
  rw [curvatureSine_pi_div_sqrt] at hcomp
  exact (not_le_of_gt (Real.rpow_pos_of_pos (hi _ ⟨hc, hb⟩).normDet_pos _)) hcomp

/-- A lower curvature-trace bound gives upper comparison for the genuine Jacobi determinant
root. Nonsingularity implies the model radius restriction rather than requiring it as input. -/
theorem normDet_rpow_le_curvatureSine_of_jacobi
    {J V K : ℝ → F →L[ℝ] F} {b t κ : ℝ}
    (hm : 0 < Module.finrank ℝ F)
    (hJ : ∀ r ∈ Icc 0 b, HasDerivWithinAt J (V r) (Icc 0 b) r)
    (hVc : ContinuousOn V (Icc 0 b))
    (hV : ∀ r ∈ Ioo 0 b, HasDerivWithinAt V (-((K r).comp (J r))) (Icc 0 b) r)
    (hK : ∀ r ∈ Ioo 0 b, LinearMap.IsSymmetric (K r).toLinearMap)
    (hzero : J 0 = 0) (hvel : V 0 = ContinuousLinearMap.id ℝ F)
    (hi : ∀ r ∈ Ioo 0 b, (J r).IsInvertible)
    (hRic : ∀ r ∈ Ioo 0 b,
      (Module.finrank ℝ F : ℝ) * κ ≤ LinearMap.trace ℝ F (K r).toLinearMap)
    (ht : t ∈ Icc 0 b) :
    (J t).toLinearMap.normDet ^ (1 / (Module.finrank ℝ F : ℝ)) ≤ curvatureSine κ t :=
  normDet_rpow_le_curvatureSine_of_jacobi_of_le_pi hm hJ hVc hV hK hzero hvel hi hRic
    (le_pi_div_sqrt_of_jacobi hm hJ hVc hV hK hzero hvel hi hRic) ht

/-- The Jacobi determinant is bounded by the model polar density. This also includes
zero-dimensional operators, whose norm determinant and model density are both one. -/
theorem normDet_le_curvatureSine_pow_of_jacobi
    {J V K : ℝ → F →L[ℝ] F} {b t κ : ℝ}
    (hJ : ∀ r ∈ Icc 0 b, HasDerivWithinAt J (V r) (Icc 0 b) r)
    (hVc : ContinuousOn V (Icc 0 b))
    (hV : ∀ r ∈ Ioo 0 b, HasDerivWithinAt V (-((K r).comp (J r))) (Icc 0 b) r)
    (hK : ∀ r ∈ Ioo 0 b, LinearMap.IsSymmetric (K r).toLinearMap)
    (hzero : J 0 = 0) (hvel : V 0 = ContinuousLinearMap.id ℝ F)
    (hi : ∀ r ∈ Ioo 0 b, (J r).IsInvertible)
    (hRic : ∀ r ∈ Ioo 0 b,
      (Module.finrank ℝ F : ℝ) * κ ≤ LinearMap.trace ℝ F (K r).toLinearMap)
    (ht : t ∈ Icc 0 b) :
    (J t).toLinearMap.normDet ≤ curvatureSine κ t ^ Module.finrank ℝ F := by
  by_cases hm : 0 < Module.finrank ℝ F
  · have hroot := normDet_rpow_le_curvatureSine_of_jacobi
      hm hJ hVc hV hK hzero hvel hi hRic ht
    have hpow := pow_le_pow_left₀
      (Real.rpow_nonneg (J t).toLinearMap.normDet_nonneg _) hroot (Module.finrank ℝ F)
    rwa [one_div, Real.rpow_inv_natCast_pow (J t).toLinearMap.normDet_nonneg hm.ne'] at hpow
  · have hdim : Module.finrank ℝ F = 0 := Nat.eq_zero_of_not_pos hm
    have : Subsingleton F := Module.finrank_zero_iff.mp hdim
    simp only [LinearMap.normDet_of_subsingleton, hdim, pow_zero, le_refl]

end TauCeti
