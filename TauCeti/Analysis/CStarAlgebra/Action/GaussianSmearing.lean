/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Analytic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import TauCeti.Analysis.SpecialFunctions.Gaussian.Concentration

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

open Complex MeasureTheory Filter Topology Real TauCeti.Real

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

/-- Up to `‖a‖` times the Gaussian mass of the complement of `[-1, 1]`, the Gaussian smearing of
`a` is the Gaussian average of the orbit of `a` truncated to `[-1, 1]`. -/
private theorem norm_gaussianSmear_sub_le {c : ℝ} (hc : 0 < c) (a : A) :
    ‖α.gaussianSmear c a -
        ∫ t, gaussianDensity c t • (Set.Icc (-1) 1).indicator
          (fun t : ℝ => α (Multiplicative.ofAdd t) a) t‖ ≤
      ‖a‖ * (1 - ∫ t, gaussianDensity c t • (Set.Icc (-1) 1).indicator (fun _ => (1 : ℝ)) t) := by
  have hg : Continuous fun t : ℝ => α (Multiplicative.ofAdd t) a :=
    α.continuous_apply continuous_ofAdd continuous_const
  have hψ₁ := integral_gaussianDensity hc
  have hψ : Integrable (gaussianDensity c) := integrable_of_integral_eq_one hψ₁
  have hψs : Integrable fun t =>
      gaussianDensity c t • (Set.Icc (-1) 1).indicator (fun _ => (1 : ℝ)) t :=
    hψ.smul_bdd 1 (aestronglyMeasurable_const.indicator measurableSet_Icc)
      (ae_of_all _ fun t => by by_cases ht : t ∈ Set.Icc (-1 : ℝ) 1 <;> simp [ht])
  have hint₁ : Integrable fun t => gaussianDensity c t • α (Multiplicative.ofAdd t) a :=
    hψ.smul_bdd ‖a‖ hg.aestronglyMeasurable (ae_of_all _ fun t => (StarAlgEquiv.norm_map _ _).le)
  have hint₂ : Integrable fun t => gaussianDensity c t • (Set.Icc (-1) 1).indicator
      (fun t : ℝ => α (Multiplicative.ofAdd t) a) t :=
    hψ.smul_bdd ‖a‖ (hg.aestronglyMeasurable.indicator measurableSet_Icc) (ae_of_all _ fun t => by
      by_cases ht : t ∈ Set.Icc (-1 : ℝ) 1 <;> simp [ht, StarAlgEquiv.norm_map])
  have hmass : ‖a‖ * (1 - ∫ t, gaussianDensity c t •
      (Set.Icc (-1) 1).indicator (fun _ => (1 : ℝ)) t) = ∫ t, ‖a‖ * (gaussianDensity c t -
        gaussianDensity c t • (Set.Icc (-1) 1).indicator (fun _ => (1 : ℝ)) t) := by
    rw [integral_const_mul, integral_sub hψ hψs, hψ₁]
  rw [gaussianSmear_eq_integral_gaussianDensity_smul, ← integral_sub hint₁ hint₂, hmass]
  -- outside `[-1, 1]` the orbit has norm `‖a‖`
  refine norm_integral_le_of_norm_le ((hψ.sub hψs).const_mul _) (ae_of_all _ fun t => ?_)
  by_cases ht : t ∈ Set.Icc (-1 : ℝ) 1
  · simp [ht]
  · simp [ht, norm_smul, abs_of_nonneg (gaussianDensity_nonneg hc.le t), StarAlgEquiv.norm_map,
      mul_comm]

/-- **Convergence of Gaussian smearings.** As the width `c⁻¹` of the Gaussian tends to zero, the
Gaussian smearing of `a` tends to `a`. -/
theorem tendsto_gaussianSmear (a : A) :
    Tendsto (fun c : ℝ => α.gaussianSmear c a) atTop (𝓝 a) := by
  have hg : Continuous fun t : ℝ => α (Multiplicative.ofAdd t) a :=
    α.continuous_apply continuous_ofAdd continuous_const
  have hs : Set.Icc (-1 : ℝ) 1 ∈ 𝓝 0 := Icc_mem_nhds (by norm_num) (by norm_num)
  -- the orbit truncated to `[-1, 1]` and the Gaussian mass of `[-1, 1]` converge by
  -- concentration of the Gaussian densities at `0`
  have h₁ := tendsto_integral_gaussianDensity_smul
    ((hg.integrableOn_Icc (a := -1) (b := 1)).integrable_indicator measurableSet_Icc)
    (hg.continuousAt.congr (Filter.mem_of_superset hs fun t ht =>
      (Set.indicator_of_mem ht fun t : ℝ => α (Multiplicative.ofAdd t) a).symm))
  have h₂ := tendsto_integral_gaussianDensity_smul
    ((continuous_const.integrableOn_Icc (a := -1) (b := 1)).integrable_indicator
      measurableSet_Icc)
    (continuous_const.continuousAt.congr (Filter.mem_of_superset hs fun t ht =>
      (Set.indicator_of_mem ht fun _ => (1 : ℝ)).symm))
  rw [Set.indicator_of_mem (mem_of_mem_nhds hs)] at h₁ h₂
  have h₃ := squeeze_zero_norm' ((eventually_gt_atTop 0).mono fun c hc =>
    α.norm_gaussianSmear_sub_le hc a) (by simpa using (h₂.const_sub 1).const_mul ‖a‖)
  simpa using h₃.add h₁

/-! ### Density -/

/-- **Density of entire analytic elements.** The entire analytic elements of a point-norm
continuous real action are dense, since every element is a limit of its Gaussian smearings. -/
theorem dense_entireAnalytic : Dense (α.entireAnalytic : Set A) := fun a =>
  mem_closure_of_tendsto (α.tendsto_gaussianSmear a)
    (.of_forall fun c => mem_entireAnalytic.mpr (α.isEntireAnalytic_gaussianSmear c a))

end TauCeti.CStarAction
