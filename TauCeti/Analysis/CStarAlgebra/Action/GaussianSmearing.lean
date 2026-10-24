/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Analytic
import TauCeti.Analysis.SpecialFunctions.Gaussian.Concentration
import TauCeti.Analysis.PDE.HeatKernel.ApproximateIdentity

/-!
# Gaussian smearing and density of entire analytic elements

For a point-norm continuous real action `α` on a possibly nonunital C⋆-algebra `A`, the
*Gaussian smearing* of `a : A` with parameter `c` is the average of the orbit of `a` against the
Gaussian density of width `c⁻¹`,

`α.gaussianSmear c a = ∫ t, (c / √π) exp (-(c t)²) • α_t a`.

The smeared element is entire analytic: its complex-time extension is obtained by translating the
Gaussian kernel into the complex plane,

`α_z (α.gaussianSmear c a) = ∫ t, (c / √π) exp (-(c (t - z))²) • α_t a`,

which is entire by differentiation under the integral sign. Smearing commutes with the action
and does not increase norms. As `c → ∞` the Gaussian densities concentrate at `0`,
so `α.gaussianSmear c a → a`. Hence the entire analytic elements form a dense star subalgebra,
invariant under the action. This is the density statement used to reduce identities such as the
KMS condition to entire analytic elements.

Neither unitality of `A` nor any countability assumption is needed. For each `c`, smearing is
complex linear and commutes with `star`.

## Main definitions

* `TauCeti.CStarAction.gaussianSmear`: the Gaussian smearing of an element.

## Main statements

* `TauCeti.CStarAction.entireExtension_gaussianSmear`: the complex-time extension of a Gaussian
  smearing.
* `TauCeti.CStarAction.isEntireAnalytic_gaussianSmear`: Gaussian smearings are entire analytic.
* `TauCeti.CStarAction.gaussianSmear_add`, `TauCeti.CStarAction.gaussianSmear_smul`: smearing is
  complex linear.
* `TauCeti.CStarAction.gaussianSmear_star`: smearing commutes with `star`.
* `TauCeti.CStarAction.apply_gaussianSmear`, `TauCeti.CStarAction.norm_gaussianSmear_le`:
  smearing commutes with the action and is contractive.
* `TauCeti.CStarAction.tendsto_gaussianSmear`: `α.gaussianSmear c a → a` as `c → ∞`.
* `TauCeti.CStarAction.dense_entireAnalytic`: the entire analytic elements are dense.

## References

Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 1*, second edition,
Section 2.5.3, for the density of entire analytic elements by Gaussian smearing.
-/

public section

noncomputable section

open Complex MeasureTheory Filter Topology Real
open scoped Convolution

namespace TauCeti.CStarAction

variable {A : Type*} [NonUnitalCStarAlgebra A] (α : CStarAction (Multiplicative ℝ) A)

/-- The *Gaussian smearing* `∫ t, (c / √π) exp (-(c t)²) • α_t a` of `a`. For `c > 0` it is the
average of the orbit of `a` against the Gaussian probability density of width `c⁻¹`. -/
def gaussianSmear (c : ℝ) (a : A) : A :=
  ∫ t : ℝ, ((c : ℂ) / √π * cexp (-(c * t) ^ 2)) • α (Multiplicative.ofAdd t) a

/-- The defining formula of the Gaussian smearing. -/
theorem gaussianSmear_def (c : ℝ) (a : A) :
    α.gaussianSmear c a =
      ∫ t : ℝ, ((c : ℂ) / √π * cexp (-(c * t) ^ 2)) • α (Multiplicative.ofAdd t) a := by
  rw [gaussianSmear]

/-- The integrand of the Gaussian smearing is integrable. -/
private theorem integrable_gaussianIntegrand (c : ℝ) (a : A) :
    Integrable fun t : ℝ =>
      ((c : ℂ) / √π * cexp (-(c * t) ^ 2)) • α (Multiplicative.ofAdd t) a := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hk : Integrable fun t : ℝ => (c : ℂ) / √π * cexp (-(c * t) ^ 2) := by
    refine ((integrable_cexp_neg_mul_sq (b := (c : ℂ) ^ 2) ?_).const_mul ((c : ℂ) / √π)).congr
      (ae_of_all _ fun t => ?_)
    · rw [← ofReal_pow, ofReal_re]
      positivity
    · simp only [mul_pow, neg_mul]
  exact hk.smul_bdd ‖a‖ (α.continuous_apply continuous_ofAdd continuous_const).aestronglyMeasurable
    (ae_of_all _ fun t => (StarAlgEquiv.norm_map _ _).le)

/-- The Gaussian smearing of `0` is `0`. -/
@[simp]
theorem gaussianSmear_zero (c : ℝ) : α.gaussianSmear c 0 = 0 := by
  simp [gaussianSmear_def]

/-- The Gaussian smearing with parameter `0` vanishes. -/
@[simp]
theorem gaussianSmear_zero_param (a : A) : α.gaussianSmear 0 a = 0 := by
  simp [gaussianSmear_def]

/-- The Gaussian smearing is additive. -/
@[simp]
theorem gaussianSmear_add (c : ℝ) (a b : A) :
    α.gaussianSmear c (a + b) = α.gaussianSmear c a + α.gaussianSmear c b := by
  simp only [gaussianSmear_def, map_add, smul_add]
  exact integral_add (α.integrable_gaussianIntegrand c a) (α.integrable_gaussianIntegrand c b)

/-- The Gaussian smearing commutes with complex scalars. -/
@[simp]
theorem gaussianSmear_smul (c : ℝ) (r : ℂ) (a : A) :
    α.gaussianSmear c (r • a) = r • α.gaussianSmear c a := by
  simp only [gaussianSmear_def, map_smul, smul_comm _ r, integral_smul]

/-! ### The complex-time extension -/

/-- The translated Gaussian integrand is continuous in the time variable. -/
private theorem continuous_gaussianIntegrand (c : ℝ) (a : A) (z : ℂ) :
    Continuous fun t : ℝ =>
      ((c : ℂ) / √π * cexp (-(c * (t - z)) ^ 2)) • α (Multiplicative.ofAdd t) a := by
  refine Continuous.smul ?_ (α.continuous_apply continuous_ofAdd continuous_const)
  fun_prop

/-- The function `z ↦ ∫ t, (c / √π) exp (-(c (t - z))²) • α_t a` is entire. -/
private theorem differentiable_gaussianExtension (c : ℝ) (a : A) :
    Differentiable ℂ fun z : ℂ =>
      ∫ t : ℝ, ((c : ℂ) / √π * cexp (-(c * (t - z)) ^ 2)) • α (Multiplicative.ofAdd t) a := by
  intro z₀
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hb : 0 < c ^ 2 / 2 := by positivity
  set D := ‖z₀‖ + 1
  have hD (z : ℂ) (hz : z ∈ Metric.ball z₀ 1) : ‖z‖ ≤ D := (norm_lt_of_mem_ball hz).le
  -- dominate the kernel and its derivative on the unit ball about `z₀` by Gaussians in `t`
  have hG := integrable_exp_neg_mul_sq hb
  have hG' : Integrable fun t : ℝ => (|t| + D) * rexp (-(c ^ 2 / 2) * t ^ 2) := by
    refine ((integrable_mul_exp_neg_mul_sq hb).norm.add (hG.const_mul D)).congr
      (ae_of_all _ fun t => ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    ring
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z₀ one_pos)
    (F' := fun z t => ((c : ℂ) / √π * cexp (-(c * (t - z)) ^ 2) * (2 * c ^ 2 * (t - z))) •
      α (Multiplicative.ofAdd t) a)
    (bound := fun t => ‖(c : ℂ) / √π‖ * rexp (c ^ 2 * D ^ 2) * (2 * c ^ 2) * ‖a‖ *
      ((|t| + D) * rexp (-(c ^ 2 / 2) * t ^ 2)))
    (.of_forall fun z => (α.continuous_gaussianIntegrand c a z).aestronglyMeasurable) ?_
    ?_ (ae_of_all _ fun t z hz => ?_) (hG'.const_mul _)
    (ae_of_all _ fun t z _ => by
      simpa only [mul_assoc] using ((Complex.hasDerivAt_cexp_neg_mul_sub_sq c t z).const_mul
        ((c : ℂ) / √π)).smul_const (α (Multiplicative.ofAdd t) a))).2.differentiableAt
  · refine Integrable.mono' ((hG.const_mul (‖(c : ℂ) / √π‖ * rexp (c ^ 2 * D ^ 2) * ‖a‖)))
      (α.continuous_gaussianIntegrand c a z₀).aestronglyMeasurable (ae_of_all _ fun t => ?_)
    rw [norm_smul, norm_mul, StarAlgEquiv.norm_map]
    calc _ ≤ ‖(c : ℂ) / √π‖ * (rexp (c ^ 2 * D ^ 2) * rexp (-(c ^ 2 / 2) * t ^ 2)) * ‖a‖ := by
          gcongr
          exact Complex.norm_cexp_neg_mul_sub_sq_le c t (hD z₀ (Metric.mem_ball_self one_pos))
      _ = _ := by ring
  · exact (Continuous.smul (by fun_prop)
      (α.continuous_apply continuous_ofAdd continuous_const)).aestronglyMeasurable
  · have h₁ : ‖2 * (c : ℂ) ^ 2 * (t - z)‖ ≤ 2 * c ^ 2 * (|t| + D) := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        Complex.norm_two]
      gcongr
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      gcongr
      exact hD z hz
    rw [norm_smul, norm_mul, norm_mul, StarAlgEquiv.norm_map]
    calc _ ≤ ‖(c : ℂ) / √π‖ * (rexp (c ^ 2 * D ^ 2) * rexp (-(c ^ 2 / 2) * t ^ 2)) *
          (2 * c ^ 2 * (|t| + D)) * ‖a‖ := by
          gcongr
          exact Complex.norm_cexp_neg_mul_sub_sq_le c t (hD z hz)
      _ = _ := by ring

/-- On the real line, the translated Gaussian integral is the orbit of the Gaussian smearing. -/
private theorem gaussianExtension_ofReal (c : ℝ) (a : A) (s : ℝ) :
    ∫ t : ℝ, ((c : ℂ) / √π * cexp (-(c * (t - s)) ^ 2)) • α (Multiplicative.ofAdd t) a =
      α (Multiplicative.ofAdd s) (α.gaussianSmear c a) := by
  -- substitute `t = u + s` and pull `α_s` out of the integral
  rw [gaussianSmear, ← integral_comp_comm, ← integral_add_right_eq_self _ s]
  congr 1 with u
  rw [map_smul, ← mul_apply, ← ofAdd_add, add_comm s u]
  push_cast
  ring_nf

/-- The complex-time extension of a Gaussian smearing is obtained by translating the Gaussian
kernel: `α_z (α.gaussianSmear c a) = ∫ t, (c / √π) exp (-(c (t - z))²) • α_t a`. -/
theorem entireExtension_gaussianSmear (c : ℝ) (a : A) (z : ℂ) :
    α.entireExtension (α.gaussianSmear c a) z =
      ∫ t : ℝ, ((c : ℂ) / √π * cexp (-(c * (t - z)) ^ 2)) • α (Multiplicative.ofAdd t) a :=
  congrFun (entireExtension_eq_of_differentiable (α.differentiable_gaussianExtension c a)
    (α.gaussianExtension_ofReal c a)) z

/-- **Gaussian smearings are entire analytic.** -/
theorem isEntireAnalytic_gaussianSmear (c : ℝ) (a : A) :
    α.IsEntireAnalytic (α.gaussianSmear c a) := by
  refine isEntireAnalytic_iff.mpr ⟨?_, fun t => ?_⟩
  · simpa only [funext (α.entireExtension_gaussianSmear c a)] using
      α.differentiable_gaussianExtension c a
  · rw [entireExtension_gaussianSmear, gaussianExtension_ofReal]

/-- The Gaussian smearing is odd in the parameter `c`. -/
@[simp]
theorem gaussianSmear_neg (c : ℝ) (a : A) : α.gaussianSmear (-c) a = -α.gaussianSmear c a := by
  simp [gaussianSmear_def, neg_div, ← integral_neg]

/-- Gaussian smearing commutes with the action: `α_s (α.gaussianSmear c a) =
α.gaussianSmear c (α_s a)`. -/
theorem apply_gaussianSmear (c s : ℝ) (a : A) :
    α (Multiplicative.ofAdd s) (α.gaussianSmear c a) =
      α.gaussianSmear c (α (Multiplicative.ofAdd s) a) := by
  rw [← gaussianExtension_ofReal, gaussianSmear, ← integral_add_right_eq_self _ s]
  congr 1 with t
  rw [← mul_apply, ← ofAdd_add]
  push_cast
  ring_nf

/-! ### Convergence as the width tends to zero -/

/-- The Gaussian smearing as an integral against the real Gaussian density. -/
private theorem gaussianSmear_eq_integral_gaussianDensity_smul (c : ℝ) (a : A) :
    α.gaussianSmear c a = ∫ t : ℝ, gaussianDensity c t • α (Multiplicative.ofAdd t) a := by
  rw [gaussianSmear]
  congr 1 with t
  rw [gaussianDensity_def, ← Complex.coe_smul]
  push_cast
  ring_nf

/-- The Gaussian smearing commutes with the star operation, since the Gaussian density is real
and the action preserves `star`. -/
@[simp]
theorem gaussianSmear_star (c : ℝ) (a : A) :
    α.gaussianSmear c (star a) = star (α.gaussianSmear c a) := by
  simpa [gaussianSmear_eq_integral_gaussianDensity_smul, map_star] using
    ((starL' ℝ : A ≃L[ℝ] A).integral_comp_comm (μ := volume)
      fun t : ℝ => gaussianDensity c t • α (Multiplicative.ofAdd t) a)

/-- The Gaussian smearing is a contraction: `‖α.gaussianSmear c a‖ ≤ ‖a‖`. -/
theorem norm_gaussianSmear_le (c : ℝ) (a : A) : ‖α.gaussianSmear c a‖ ≤ ‖a‖ := by
  -- for `c > 0` integrate against the Gaussian probability density; `c ≤ 0` follows by oddness
  have key {c : ℝ} (hc : 0 < c) : ‖α.gaussianSmear c a‖ ≤ ‖a‖ := by
    have hψ₁ := integral_gaussianDensity hc
    rw [gaussianSmear_eq_integral_gaussianDensity_smul]
    refine (norm_integral_le_of_norm_le ((integrable_of_integral_eq_one hψ₁).mul_const ‖a‖)
      (ae_of_all _ fun t => ?_)).trans_eq (by rw [integral_mul_const, hψ₁, one_mul])
    rw [norm_smul, Real.norm_of_nonneg (gaussianDensity_nonneg hc.le t), StarAlgEquiv.norm_map]
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · simpa using key (neg_pos.mpr hc)
  · simp
  · exact key hc

/-- At positive width, Gaussian smearing is heat-kernel convolution of the reversed orbit. -/
private theorem gaussianSmear_eq_heatKernel_convolution {c : ℝ} (hc : 0 < c) (a : A) :
    α.gaussianSmear c a =
      (heatKernel (1 / (4 * c ^ 2)) ⋆ fun u : ℝ => α (Multiplicative.ofAdd (-u)) a) 0 := by
  have hvariance : 4 * π * (1 / (4 * c ^ 2)) = π / c ^ 2 := by field_simp
  have hexponent (t : ℝ) : -t ^ 2 / (4 * (1 / (4 * c ^ 2))) = -(c * t) ^ 2 := by
    field_simp
  have hkernel (t : ℝ) : heatKernel (1 / (4 * c ^ 2)) t = gaussianDensity c t := by
    rw [heatKernel_apply]
    simp only [Module.finrank_self, Nat.cast_one, Real.norm_eq_abs, sq_abs]
    rw [neg_div, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, hvariance,
      Real.sqrt_div' _ (sq_nonneg c), Real.sqrt_sq hc.le, hexponent, gaussianDensity_def]
    simp only [inv_div]
    ring
  rw [gaussianSmear_eq_integral_gaussianDensity_smul, convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, zero_sub, neg_neg, hkernel]

/-- **Convergence of Gaussian smearings.** As the width `c⁻¹` of the Gaussian tends to zero, the
Gaussian smearing of `a` tends to `a`. -/
theorem tendsto_gaussianSmear (a : A) :
    Tendsto (fun c : ℝ => α.gaussianSmear c a) atTop (𝓝 a) := by
  let g : ℝ → A := fun u => α (Multiplicative.ofAdd (-u)) a
  have hg : Continuous g := α.continuous_apply (continuous_ofAdd.comp continuous_neg)
    continuous_const
  have hpow : Tendsto (fun c : ℝ => c ^ 2) atTop atTop :=
    tendsto_pow_atTop (by decide : 2 ≠ 0)
  have htime : Tendsto (fun c : ℝ => 4 * c ^ 2) atTop atTop :=
    hpow.const_mul_atTop (by norm_num : 0 < (4 : ℝ))
  have ht₀ : Tendsto (fun c : ℝ => 1 / (4 * c ^ 2)) atTop (𝓝 0) := by
    simpa only [one_div] using! htime.inv_tendsto_atTop
  have ht : Tendsto (fun c : ℝ => 1 / (4 * c ^ 2)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht₀, (eventually_gt_atTop 0).mono fun c hc =>
      Set.mem_Ioi.mpr (by positivity)⟩
  have h := (tendsto_heatKernel_convolution hg.aestronglyMeasurable
    (ae_of_all _ fun u => (StarAlgEquiv.norm_map _ a).le) (x₀ := 0) hg.continuousAt).comp
      (ht.prodMk tendsto_const_nhds)
  have hg₀ : g 0 = a := by simp [g]
  rw [hg₀] at h
  exact h.congr' ((eventually_gt_atTop 0).mono fun c hc =>
    (α.gaussianSmear_eq_heatKernel_convolution hc a).symm)

/-! ### Density -/

/-- **Density of entire analytic elements.** The entire analytic elements of a point-norm
continuous real action are dense, since every element is a limit of its Gaussian smearings. -/
theorem dense_entireAnalytic : Dense (α.entireAnalytic : Set A) := fun a =>
  mem_closure_of_tendsto (α.tendsto_gaussianSmear a)
    (.of_forall fun c => mem_entireAnalytic.mpr (α.isEntireAnalytic_gaussianSmear c a))

end TauCeti.CStarAction
