/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Analytic
import TauCeti.Analysis.SpecialFunctions.Gaussian.Concentration
import TauCeti.Analysis.SpecialFunctions.Gaussian.Basic

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
* `TauCeti.CStarAction.gaussianSmearCLM`: Gaussian smearing as a continuous linear map.

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
open scoped NNReal

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

/-- The function `z ↦ ∫ t, (c / √π) exp (-(c (t - z))²) • α_t a` is entire. -/
private theorem differentiable_gaussianExtension (c : ℝ) (a : A) :
    Differentiable ℂ fun z : ℂ =>
      ∫ t : ℝ, ((c : ℂ) / √π * cexp (-(c * (t - z)) ^ 2)) • α (Multiplicative.ofAdd t) a := by
  simpa only [Complex.gaussianKernel_def] using
    Complex.differentiable_integral_gaussianKernel_smul
      (α.continuous_apply continuous_ofAdd continuous_const)
      (fun t => (StarAlgEquiv.norm_map _ _).le) c

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
  refine (isEntireAnalytic_iff α _).mpr fun t => ?_
  rw [entireExtension_gaussianSmear, gaussianExtension_ofReal]

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

/-- Gaussian smearing as a continuous complex-linear map. -/
def gaussianSmearCLM (c : ℝ) : A →L[ℂ] A :=
  ({ toFun := α.gaussianSmear c
     map_add' := α.gaussianSmear_add c
     map_smul' := α.gaussianSmear_smul c } : A →ₗ[ℂ] A).mkContinuous 1
    (fun a => by simpa using α.norm_gaussianSmear_le c a)

/-- Applying the continuous linear Gaussian smearing map gives the Gaussian smearing. -/
@[simp]
theorem gaussianSmearCLM_apply (c : ℝ) (a : A) :
    α.gaussianSmearCLM c a = α.gaussianSmear c a := by
  rfl

/-- Gaussian smearing commutes with the associated strongly continuous semigroup. -/
theorem toSemigroup_gaussianSmearCLM (c : ℝ) (t : ℝ≥0) (a : A) :
    α.toStronglyContinuousGroup.toSemigroup t (α.gaussianSmearCLM c a) =
      α.gaussianSmearCLM c (α.toStronglyContinuousGroup.toSemigroup t a) := by
  simpa only [Semigroups.StronglyContinuousGroup.toSemigroup_apply,
    toStronglyContinuousGroup_apply, gaussianSmearCLM_apply] using α.apply_gaussianSmear c t a

/-- **Convergence of Gaussian smearings.** As the width `c⁻¹` of the Gaussian tends to zero, the
Gaussian smearing of `a` tends to `a`. -/
theorem tendsto_gaussianSmear (a : A) :
    Tendsto (fun c : ℝ => α.gaussianSmear c a) atTop (𝓝 a) := by
  have h := Complex.tendsto_integral_gaussianKernel_smul
    (α.continuous_apply continuous_ofAdd continuous_const)
    (fun t => (StarAlgEquiv.norm_map _ a).le)
  simpa [gaussianSmear_def, Complex.gaussianKernel_def] using h

/-! ### Density -/

/-- **Density of entire analytic elements.** The entire analytic elements of a point-norm
continuous real action are dense, since every element is a limit of its Gaussian smearings. -/
theorem dense_entireAnalytic : Dense (α.entireAnalytic : Set A) := fun a =>
  mem_closure_of_tendsto (α.tendsto_gaussianSmear a)
    (.of_forall fun c => mem_entireAnalytic.mpr (α.isEntireAnalytic_gaussianSmear c a))

end TauCeti.CStarAction
