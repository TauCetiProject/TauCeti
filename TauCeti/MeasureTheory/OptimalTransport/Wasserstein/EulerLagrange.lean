/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.PotentialEnergy
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Pushforward

/-!
# The Euler–Lagrange equation of the Jordan–Kinderlehrer–Otto step

Let `E` be a separable Hilbert space, `φ` an energy on the quadratic Wasserstein space `P₂(E)` and
`τ > 0` a time step. A step of the *Jordan–Kinderlehrer–Otto scheme* (JKO scheme) from a law `μ`
is a law `ν` minimizing

`ρ ↦ φ ρ + W₂ (μ, ρ) ^ 2 / (2τ)`,

that is, a point of the resolvent `TauCeti.moreauYosidaResolvent φ τ μ`. This file derives the
first-order condition satisfied by such a minimizer, by perturbing `ν` along vector fields.

For a vector field `ξ ∈ L²(ν; E)` and `h : ℝ`, the law `ν_h` of `x + h • ξ x` under `ν` lies in
`P₂(E)` (`TauCeti.exists_coe_eq_map_add_smul`). If `γ` is a coupling of `ν` and `μ`, then
`(x, y) ↦ (x + h • ξ x, y)` carries it to a coupling of `ν_h` and `μ`, whence

`W₂ (ν_h, μ) ^ 2 ≤ ∫ ‖x - y‖² dγ + 2h ∫ ⟪x - y, ξ x⟫ dγ + h² ∫ ‖ξ‖² dν`

(`TauCeti.wassersteinEDist_map_add_smul_sq_le`). When `γ` is an optimal coupling, the first
integral is `W₂ (ν, μ) ^ 2`, and comparing the minimizer `ν` with `ν_h` gives the variational
inequality

`φ ν ≤ φ ν_h + (h ∫ ⟪x - y, ξ x⟫ dγ + (h² / 2) ∫ ‖ξ‖² dν) / τ`

for every `h` (`TauCeti.apply_le_apply_add_of_mem_moreauYosidaResolvent`). If the energy has a
derivative `D` along the perturbation, that is `φ ν_h = f h` near `h = 0` for a function `f`
differentiable at `0` with `f' 0 = D`, then the right side minus the left has a local minimum at
`h = 0`, and its derivative there vanishes. This is the *Euler–Lagrange equation* of the JKO step:

`∫ ⟪x - y, ξ x⟫ dγ(x, y) = -τ D`

(`TauCeti.integral_inner_eq_neg_mul_of_mem_moreauYosidaResolvent`). Heuristically
`D = ∫ ⟪∇ (δφ/δν), ξ⟫ dν` for the first variation `δφ/δν` of the energy, and the equation is the
weak form of `(x - y) / τ = -∇ (δφ/δν)(x)`, the displacement of the step being averaged over the
conditional law of `y` given `x` under `γ`.

For the potential energy `ρ ↦ ∫ V dρ` of a differentiable potential whose gradient grows at most
linearly, `‖∇V x‖ ≤ C (1 + ‖x‖)`, the potential is integrable against every law of finite second
moment (`TauCeti.integrable_comp_of_norm_gradient_le`), and differentiating under the integral sign
gives the derivative `∫ ⟪∇V x, ξ x⟫ dν` along the perturbation
(`TauCeti.hasDerivAt_integral_comp_add_smul`). The Euler–Lagrange equation then reads

`∫ ⟪x - y, ξ x⟫ dγ(x, y) = -τ ∫ ⟪∇V x, ξ x⟫ dν(x)`

(`TauCeti.integral_inner_eq_neg_mul_integral_inner_gradient_of_mem_moreauYosidaResolvent`). This is
the drift part of the discrete Euler–Lagrange equation of Jordan, Kinderlehrer and Otto for the
Fokker–Planck equation.

## Main results

* `TauCeti.exists_coe_eq_map_add_smul`: the perturbation of a law of `P₂(E)` along a vector field
  of `L²` lies in `P₂(E)`.
* `TauCeti.wassersteinEDist_map_add_smul_sq_le`: the expansion of the squared Wasserstein distance
  along such a perturbation, against an arbitrary coupling.
* `TauCeti.apply_le_apply_add_of_mem_moreauYosidaResolvent`: the variational inequality of the
  JKO step.
* `TauCeti.integral_inner_eq_neg_mul_of_mem_moreauYosidaResolvent`: the Euler–Lagrange equation
  of the JKO step for an energy differentiable along the perturbation.
* `TauCeti.hasDerivAt_integral_comp_add_smul`: the first variation of the potential energy along
  a perturbation.
* `TauCeti.integral_inner_eq_neg_mul_integral_inner_gradient_of_mem_moreauYosidaResolvent`: the
  Euler–Lagrange equation of the JKO step for the potential energy.

## References

* R. Jordan, D. Kinderlehrer and F. Otto, *The variational formulation of the Fokker–Planck
  equation*, SIAM J. Math. Anal. 29 (1998), 1–17, for the variation of the discrete scheme along
  the flow of a vector field.
* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Section 10.1, for the first-order condition of
  the minimizing movement step in `P₂`.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, Section 8.3.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {ξ : E → E}

section Perturbation

/-- **Perturbing a law of `P₂(E)` along a vector field of `L²`.** For `ξ ∈ L²(ν; E)` and `h : ℝ`,
the law of `x + h • ξ x` under `ν` is again a law of `P₂(E)`. -/
theorem exists_coe_eq_map_add_smul [NormedSpace ℝ E] {ν : WassersteinSpace 2 E}
    (hξ : MemLp ξ 2 ((ν : ProbabilityMeasure E) : Measure E)) (h : ℝ) :
    ∃ ν' : WassersteinSpace 2 E, ((ν' : ProbabilityMeasure E) : Measure E) =
      ((ν : ProbabilityMeasure E) : Measure E).map (fun x ↦ x + h • ξ x) := by
  set ρ := ((ν : ProbabilityMeasure E) : Measure E)
  have hT : AEMeasurable (fun x ↦ x + h • ξ x) ρ :=
    aemeasurable_id.add (hξ.aestronglyMeasurable.aemeasurable.const_smul h)
  have hm : HasFiniteMoment 2 (ρ.map fun x ↦ x + h • ξ x) := by
    rw [hasFiniteMoment_map_iff_memLp_edist hT 0]
    have hL := ν.hasFiniteMoment.memLp_id.add (hξ.const_smul h)
    exact (memLp_congr_enorm hL.aestronglyMeasurable
      ((by fun_prop : Measurable fun y : E ↦ edist y 0).comp_aemeasurable hT).aestronglyMeasurable
      (.of_forall fun x ↦ by simp [edist_eq_enorm_sub])).1 hL
  let P : ProbabilityMeasure E :=
    ⟨ρ.map fun x ↦ x + h • ξ x, (Measure.isProbabilityMeasure_map_iff hT).2 inferInstance⟩
  have hP : (P : Measure E) = ρ.map fun x ↦ x + h • ξ x := ProbabilityMeasure.coe_mk _ _
  exact ⟨WassersteinSpace.mk P (hP ▸ hm), by rw [WassersteinSpace.coe_mk, hP]⟩

variable [InnerProductSpace ℝ E] {ν μ : Measure E} {γ : Measure (E × E)}

/-- The pairing `⟪x - y, ξ x⟫` of the displacement of a coupling of finite quadratic cost with a
vector field of `L²(ν)` is integrable. -/
theorem IsCoupling.integrable_inner_sub_comp_fst (hγ : IsCoupling γ ν μ)
    (hγ₂ : Integrable (fun z : E × E ↦ ‖z.1 - z.2‖ ^ 2) γ) (hξ : MemLp ξ 2 ν) :
    Integrable (fun z : E × E ↦ ⟪z.1 - z.2, ξ z.1⟫) γ := by
  have hξγ := hξ.comp_measurePreserving hγ.measurePreserving_fst
  have hξ₂ := (memLp_two_iff_integrable_sq_norm hξγ.aestronglyMeasurable).1 hξγ
  have hd : MemLp (fun z : E × E ↦ z.1 - z.2) 2 γ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).2 hγ₂
  refine (hγ₂.add hξ₂).mono' (hd.aestronglyMeasurable.inner
    hξγ.aestronglyMeasurable) (.of_forall fun z ↦ ?_)
  simp only [Function.comp_apply, Pi.add_apply, Real.norm_eq_abs]
  have h₁ := abs_real_inner_le_norm (z.1 - z.2) (ξ z.1)
  nlinarith [sq_nonneg (‖z.1 - z.2‖ - ‖ξ z.1‖)]

/-- The quadratic cost of the perturbation `(x, y) ↦ (x + h • ξ x, y)` of a coupling `γ` of `ν`
and `μ`, expanded in `h`: `∫ ‖x - y + h • ξ x‖² dγ` is
`∫ ‖x - y‖² dγ + 2h ∫ ⟪x - y, ξ x⟫ dγ + h² ∫ ‖ξ‖² dν`. -/
private theorem IsCoupling.integral_norm_sub_add_smul_sq (hγ : IsCoupling γ ν μ)
    (hγ₂ : Integrable (fun z : E × E ↦ ‖z.1 - z.2‖ ^ 2) γ) (hξ : MemLp ξ 2 ν) (h : ℝ) :
    ∫ z, ‖z.1 - z.2 + h • ξ z.1‖ ^ 2 ∂γ = ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ +
      2 * h * ∫ z, ⟪z.1 - z.2, ξ z.1⟫ ∂γ + h ^ 2 * ∫ x, ‖ξ x‖ ^ 2 ∂ν := by
  have hξγ := hξ.comp_measurePreserving hγ.measurePreserving_fst
  have hξ₂ : Integrable (fun z : E × E ↦ ‖ξ z.1‖ ^ 2) γ :=
    (memLp_two_iff_integrable_sq_norm hξγ.aestronglyMeasurable).1 hξγ
  have hinner := hγ.integrable_inner_sub_comp_fst hγ₂ hξ
  have hpt : (fun z : E × E ↦ ‖z.1 - z.2 + h • ξ z.1‖ ^ 2) = fun z ↦
      ‖z.1 - z.2‖ ^ 2 + 2 * h * ⟪z.1 - z.2, ξ z.1⟫ + h ^ 2 * ‖ξ z.1‖ ^ 2 := by
    ext z
    rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have h₁ : Integrable (fun z : E × E ↦ ‖z.1 - z.2‖ ^ 2 + 2 * h * ⟪z.1 - z.2, ξ z.1⟫) γ :=
    hγ₂.add (hinner.const_mul _)
  rw [hpt, integral_add h₁ (hξ₂.const_mul _), integral_add hγ₂ (hinner.const_mul _),
    integral_const_mul, integral_const_mul,
    hγ.integral_comp_fst (f := fun x ↦ ‖ξ x‖ ^ 2) (hξ.aestronglyMeasurable.norm.pow 2)]

/-- **The squared Wasserstein distance along a perturbation.** Let `γ` couple `ν` and `μ` with
finite quadratic cost and let `ξ ∈ L²(ν; E)`. The law `ν_h` of `x + h • ξ x` under `ν` satisfies
`W₂ (ν_h, μ) ^ 2 ≤ ∫ ‖x - y‖² dγ + 2h ∫ ⟪x - y, ξ x⟫ dγ + h² ∫ ‖ξ‖² dν`, the right side being the
quadratic cost of the coupling `(x, y) ↦ (x + h • ξ x, y)` of `ν_h` and `μ` carried by `γ`. -/
theorem wassersteinEDist_map_add_smul_sq_le (hγ : IsCoupling γ ν μ)
    (hγ₂ : Integrable (fun z : E × E ↦ ‖z.1 - z.2‖ ^ 2) γ) (hξ : MemLp ξ 2 ν) (h : ℝ) :
    wassersteinEDist 2 (ν.map fun x ↦ x + h • ξ x) μ ^ 2 ≤
      ENNReal.ofReal (∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ + 2 * h * ∫ z, ⟪z.1 - z.2, ξ z.1⟫ ∂γ +
        h ^ 2 * ∫ x, ‖ξ x‖ ^ 2 ∂ν) := by
  have hfst := hγ.measurePreserving_fst
  have hξγ := hξ.comp_measurePreserving hfst
  have hξ₂ : Integrable (fun z : E × E ↦ ‖ξ z.1‖ ^ 2) γ :=
    (memLp_two_iff_integrable_sq_norm hξγ.aestronglyMeasurable).1 hξγ
  have hT : AEMeasurable (fun x ↦ x + h • ξ x) ν :=
    aemeasurable_id.add (hξ.aestronglyMeasurable.aemeasurable.const_smul h)
  have hTγ : AEMeasurable (fun z : E × E ↦ z.1 + h • ξ z.1) γ :=
    measurable_fst.aemeasurable.add (hξγ.aestronglyMeasurable.aemeasurable.const_smul h)
  have hF : AEMeasurable (fun z : E × E ↦ (z.1 + h • ξ z.1, z.2)) γ :=
    hTγ.prodMk measurable_snd.aemeasurable
  -- The perturbation of `γ` couples the perturbed law with `μ`.
  have hcoup : IsCoupling (γ.map fun z ↦ (z.1 + h • ξ z.1, z.2)) (ν.map fun x ↦ x + h • ξ x) μ := by
    refine ⟨?_, ?_⟩
    · rw [Measure.fst, AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hF,
        ← hfst.map_eq, AEMeasurable.map_map_of_aemeasurable (hfst.map_eq ▸ hT)
          measurable_fst.aemeasurable]
      rfl
    · rw [Measure.snd, AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hF]
      exact hγ.snd_eq
  -- Its quadratic cost is the integral of `‖(x - y) + h • ξ x‖²`.
  have hd : MemLp (fun z : E × E ↦ z.1 - z.2) 2 γ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).2 hγ₂
  have hm₂ : MemLp (fun z : E × E ↦ z.1 - z.2 + h • ξ z.1) 2 γ := hd.add (hξγ.const_smul h)
  have hint : Integrable (fun z : E × E ↦ ‖z.1 - z.2 + h • ξ z.1‖ ^ 2) γ :=
    (memLp_two_iff_integrable_sq_norm hm₂.aestronglyMeasurable).1 hm₂
  have hcost : ∫⁻ z, edist z.1 z.2 ^ 2 ∂(γ.map fun z ↦ (z.1 + h • ξ z.1, z.2)) =
      ENNReal.ofReal (∫ z, ‖z.1 - z.2 + h • ξ z.1‖ ^ 2 ∂γ) := by
    rw [lintegral_map' (by fun_prop) hF, ofReal_integral_eq_lintegral_ofReal hint
      (.of_forall fun _ ↦ by positivity)]
    refine lintegral_congr fun z ↦ ?_
    rw [edist_dist, dist_eq_norm, ENNReal.ofReal_pow (norm_nonneg _), add_sub_right_comm]
  calc wassersteinEDist 2 (ν.map fun x ↦ x + h • ξ x) μ ^ 2
      ≤ ∫⁻ z, edist z.1 z.2 ^ 2 ∂(γ.map fun z ↦ (z.1 + h • ξ z.1, z.2)) := by
        simpa using wassersteinEDist_rpow_le_lintegral measurable_edist two_ne_zero
          ENNReal.ofNat_ne_top hcoup
    _ = _ := by rw [hcost, hγ.integral_norm_sub_add_smul_sq hγ₂ hξ h]

end Perturbation

section Resolvent

variable [CompleteSpace E] {φ : WassersteinSpace 2 E → EReal} {τ : ℝ≥0}
  {μ ν : WassersteinSpace 2 E} {γ : Measure (E × E)}

/-- An optimal coupling of two laws of `P₂(E)` realizes the squared Wasserstein distance as its
quadratic cost. -/
private theorem dist_sq_eq_integral (hγ : IsCoupling γ ((ν : ProbabilityMeasure E) : Measure E)
      ((μ : ProbabilityMeasure E) : Measure E))
    (hγW : eLpNorm (fun z : E × E ↦ edist z.1 z.2) 2 γ =
      wassersteinEDist 2 ((ν : ProbabilityMeasure E) : Measure E)
        ((μ : ProbabilityMeasure E) : Measure E)) :
    Integrable (fun z : E × E ↦ ‖z.1 - z.2‖ ^ 2) γ ∧
      dist ν μ ^ 2 = ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ := by
  have : IsProbabilityMeasure γ := hγ.isProbabilityMeasure
  have hγ₂ := integrable_norm_sub_sq_of_hasFiniteMoment (hγ.fst_eq ▸ ν.hasFiniteMoment)
    (hγ.snd_eq ▸ μ.hasFiniteMoment)
  refine ⟨hγ₂, ?_⟩
  have hL : eLpNorm (fun z : E × E ↦ edist z.1 z.2) 2 γ ^ 2 = ∫⁻ z, edist z.1 z.2 ^ 2 ∂γ := by
    simpa using eLpNorm_rpow_eq_lintegral two_ne_zero ENNReal.ofNat_ne_top
      (measurable_edist (α := E)).aemeasurable (μ := γ)
  rw [hγW, lintegral_edist_sq_eq_ofReal_integral hγ₂, ← WassersteinSpace.edist_def,
    edist_dist, ← ENNReal.ofReal_pow dist_nonneg,
    ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (integral_nonneg fun _ ↦ by positivity)] at hL
  exact hL

variable [InnerProductSpace ℝ E]

/-- **The variational inequality of the JKO step.** Let `ν` be a JKO step of time step `τ > 0`
from `μ` for the energy `φ`, let `γ` be an optimal coupling of `ν` and `μ`, and let
`ξ ∈ L²(ν; E)`. For every `h : ℝ`, the law `ν'` of `x + h • ξ x` under `ν` satisfies
`φ ν ≤ φ ν' + (h ∫ ⟪x - y, ξ x⟫ dγ + (h² / 2) ∫ ‖ξ‖² dν) / τ`. -/
theorem apply_le_apply_add_of_mem_moreauYosidaResolvent (hτ : 0 < τ)
    (hν : ν ∈ moreauYosidaResolvent φ τ μ)
    (hγ : IsCoupling γ ((ν : ProbabilityMeasure E) : Measure E)
      ((μ : ProbabilityMeasure E) : Measure E))
    (hγW : eLpNorm (fun z : E × E ↦ edist z.1 z.2) 2 γ =
      wassersteinEDist 2 ((ν : ProbabilityMeasure E) : Measure E)
        ((μ : ProbabilityMeasure E) : Measure E))
    (hξ : MemLp ξ 2 ((ν : ProbabilityMeasure E) : Measure E)) (h : ℝ) {ν' : WassersteinSpace 2 E}
    (hν' : ((ν' : ProbabilityMeasure E) : Measure E) =
      ((ν : ProbabilityMeasure E) : Measure E).map fun x ↦ x + h • ξ x) :
    φ ν ≤ φ ν' + (((h * ∫ z, ⟪z.1 - z.2, ξ z.1⟫ ∂γ +
      h ^ 2 / 2 * ∫ x, ‖ξ x‖ ^ 2 ∂((ν : ProbabilityMeasure E) : Measure E)) / τ : ℝ) : EReal) := by
  obtain ⟨hγ₂, hd⟩ := dist_sq_eq_integral hγ hγW
  set A := ∫ z, ⟪z.1 - z.2, ξ z.1⟫ ∂γ
  set B := ∫ x, ‖ξ x‖ ^ 2 ∂((ν : ProbabilityMeasure E) : Measure E)
  -- The perturbed law is at squared distance at most `W₂ (ν, μ) ^ 2 + 2hA + h²B` from `μ`.
  have hdist : dist μ ν' ^ 2 ≤ dist μ ν ^ 2 + 2 * h * A + h ^ 2 * B := by
    have hW := wassersteinEDist_map_add_smul_sq_le hγ hγ₂ hξ h
    rw [← hν', ← WassersteinSpace.edist_def, edist_dist, ← ENNReal.ofReal_pow dist_nonneg,
      ← hd, ENNReal.ofReal_le_ofReal_iff (by
        rw [hd, ← hγ.integral_norm_sub_add_smul_sq hγ₂ hξ h]
        exact integral_nonneg fun _ ↦ by positivity)] at hW
    rwa [dist_comm μ ν', dist_comm μ ν]
  -- Minimality of `ν` against `ν'`.
  have hmin := (mem_moreauYosidaResolvent_iff_isMinOn.1 hν) (mem_univ ν')
  simp only [coe_edist_sq_div_eq_coe_dist_sq_div hτ] at hmin
  have hτ' : (0 : ℝ) < τ := hτ
  have hpen : dist μ ν' ^ 2 / (2 * τ) ≤
      dist μ ν ^ 2 / (2 * τ) + (h * A + h ^ 2 / 2 * B) / τ := by
    calc dist μ ν' ^ 2 / (2 * τ) ≤ (dist μ ν ^ 2 + 2 * h * A + h ^ 2 * B) / (2 * τ) := by
          gcongr
      _ = _ := by field_simp; ring
  calc φ ν = φ ν + ((dist μ ν ^ 2 / (2 * τ) : ℝ) : EReal) -
        ((dist μ ν ^ 2 / (2 * τ) : ℝ) : EReal) := EReal.add_sub_cancel_right.symm
    _ ≤ φ ν' + ((dist μ ν' ^ 2 / (2 * τ) : ℝ) : EReal) -
        ((dist μ ν ^ 2 / (2 * τ) : ℝ) : EReal) := EReal.sub_le_sub hmin le_rfl
    _ ≤ φ ν' + ((dist μ ν ^ 2 / (2 * τ) + (h * A + h ^ 2 / 2 * B) / τ : ℝ) : EReal) -
        ((dist μ ν ^ 2 / (2 * τ) : ℝ) : EReal) :=
      EReal.sub_le_sub (add_le_add le_rfl (EReal.coe_le_coe_iff.2 hpen)) le_rfl
    _ = φ ν' + (((h * A + h ^ 2 / 2 * B) / τ : ℝ) : EReal) := by
      rw [EReal.coe_add, add_comm ((dist μ ν ^ 2 / (2 * τ) : ℝ) : EReal), ← add_assoc,
        EReal.add_sub_cancel_right]

/-- **The Euler–Lagrange equation of the JKO step.** Let `ν` be a JKO step of time step `τ > 0`
from `μ` for the energy `φ`, let `γ` be an optimal coupling of `ν` and `μ`, and let
`ξ ∈ L²(ν; E)`. Suppose that the energy is differentiable along the perturbation of `ν` by `ξ`:
for `h` near `0`, the law of `x + h • ξ x` under `ν` has energy `f h`, where `f` has derivative
`D` at `0`. Then `∫ ⟪x - y, ξ x⟫ dγ(x, y) = -τ D`. -/
theorem integral_inner_eq_neg_mul_of_mem_moreauYosidaResolvent (hτ : 0 < τ)
    (hν : ν ∈ moreauYosidaResolvent φ τ μ)
    (hγ : IsCoupling γ ((ν : ProbabilityMeasure E) : Measure E)
      ((μ : ProbabilityMeasure E) : Measure E))
    (hγW : eLpNorm (fun z : E × E ↦ edist z.1 z.2) 2 γ =
      wassersteinEDist 2 ((ν : ProbabilityMeasure E) : Measure E)
        ((μ : ProbabilityMeasure E) : Measure E))
    (hξ : MemLp ξ 2 ((ν : ProbabilityMeasure E) : Measure E)) {f : ℝ → ℝ} {D : ℝ}
    (hf : ∀ᶠ h in 𝓝 0, ∀ ν' : WassersteinSpace 2 E, ((ν' : ProbabilityMeasure E) : Measure E) =
      ((ν : ProbabilityMeasure E) : Measure E).map (fun x ↦ x + h • ξ x) → φ ν' = f h)
    (hD : HasDerivAt f D 0) :
    ∫ z, ⟪z.1 - z.2, ξ z.1⟫ ∂γ = -(τ * D) := by
  set A := ∫ z, ⟪z.1 - z.2, ξ z.1⟫ ∂γ
  set B := ∫ x, ‖ξ x‖ ^ 2 ∂((ν : ProbabilityMeasure E) : Measure E)
  have hτ' : (0 : ℝ) < τ := hτ
  -- At `h = 0` the perturbation is the identity, so `φ ν = f 0`.
  have h₀ : φ ν = f 0 := hf.self_of_nhds ν (by simp)
  -- The penalized energy `g h = f h + (h A + h² B / 2) / τ` has a local minimum at `0`.
  set g : ℝ → ℝ := fun h ↦ f h + (h * A + h ^ 2 / 2 * B) / τ
  have hmin : IsLocalMin g 0 := by
    filter_upwards [hf] with h hfh
    obtain ⟨ν', hν'⟩ := exists_coe_eq_map_add_smul hξ h
    have hle := apply_le_apply_add_of_mem_moreauYosidaResolvent hτ hν hγ hγW hξ h hν'
    rw [hfh ν' hν', h₀, ← EReal.coe_add, EReal.coe_le_coe_iff] at hle
    simpa [g] using hle
  have hg : HasDerivAt g (D + A / τ) 0 := by
    have hq : HasDerivAt (fun h : ℝ ↦ (h * A + h ^ 2 / 2 * B) / τ) (A / τ) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).mul_const A).add
        (((hasDerivAt_pow 2 (0 : ℝ)).div_const 2).mul_const B)).div_const (τ : ℝ)
      simpa using this
    exact hD.add hq
  have h0 := IsLocalMin.hasDerivAt_eq_zero hmin hg
  field_simp at h0
  linarith

end Resolvent

section PotentialEnergy

variable [InnerProductSpace ℝ E] [CompleteSpace E] {V : E → ℝ} {C : ℝ}

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- A differentiable potential whose gradient grows at most linearly, `‖∇V x‖ ≤ C (1 + ‖x‖)`, is
integrable against the law of every square-integrable random vector: for a finite measure `ρ` and
`T ∈ L²(ρ; E)`, the function `V ∘ T` is integrable. -/
theorem integrable_comp_of_norm_gradient_le {α : Type*} [MeasurableSpace α] {ρ : Measure α}
    [IsFiniteMeasure ρ] {T : α → E} (hV : Differentiable ℝ V)
    (hV' : ∀ x, ‖gradient V x‖ ≤ C * (1 + ‖x‖)) (hT : MemLp T 2 ρ) :
    Integrable (fun a ↦ V (T a)) ρ := by
  -- By the mean value inequality, `V` grows at most quadratically.
  have hgrowth (x : E) : |V x - V 0| ≤ C * (1 + ‖x‖) * ‖x‖ := by
    have hb : ∀ y ∈ Metric.closedBall (0 : E) ‖x‖, ‖fderiv ℝ V y‖ ≤ C * (1 + ‖x‖) := by
      intro y hy
      rw [← toDual_gradient, LinearIsometryEquiv.norm_map]
      exact (hV' y).trans (mul_le_mul_of_nonneg_left (by simpa using hy)
        (by simpa using (norm_nonneg _).trans (hV' 0)))
    have := (convex_closedBall (0 : E) ‖x‖).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (fun y _ ↦ hV y) hb (Metric.mem_closedBall_self (norm_nonneg x) : (0 : E) ∈ _)
      (by simp : x ∈ Metric.closedBall (0 : E) ‖x‖)
    simpa [← Real.norm_eq_abs] using this
  have hT₂ : Integrable (fun a ↦ ‖T a‖ ^ 2) ρ :=
    (memLp_two_iff_integrable_sq_norm hT.aestronglyMeasurable).1 hT
  have hT₁ : Integrable (fun a ↦ ‖T a‖) ρ := (hT.integrable one_le_two).norm
  refine ((integrable_const |V 0|).add ((hT₁.add hT₂).const_mul C)).mono'
    (hV.continuous.comp_aestronglyMeasurable hT.aestronglyMeasurable) (.of_forall fun a ↦ ?_)
  have := hgrowth (T a)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_le] at this ⊢
  constructor <;> nlinarith [neg_abs_le (V 0), le_abs_self (V 0)]

/-- **The first variation of the potential energy.** Let `V` be a differentiable potential whose
gradient grows at most linearly, `‖∇V x‖ ≤ C (1 + ‖x‖)`, and let `ρ` be a finite measure with
finite second moment. For every vector field `ξ ∈ L²(ρ; E)`, the potential energy
`h ↦ ∫ V (x + h • ξ x) dρ` of the perturbation of `ρ` along `ξ` has derivative
`∫ ⟪∇V x, ξ x⟫ dρ` at `h = 0`. -/
theorem hasDerivAt_integral_comp_add_smul {ρ : Measure E} [IsFiniteMeasure ρ]
    (hV : Differentiable ℝ V) (hV' : ∀ x, ‖gradient V x‖ ≤ C * (1 + ‖x‖)) (hρ : MemLp id 2 ρ)
    (hξ : MemLp ξ 2 ρ) :
    HasDerivAt (fun h : ℝ ↦ ∫ x, V (x + h • ξ x) ∂ρ) (∫ x, ⟪gradient V x, ξ x⟫ ∂ρ) 0 := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (hV' 0)
  have hξm := hξ.aestronglyMeasurable
  have hVint (h : ℝ) : Integrable (fun x ↦ V (x + h • ξ x)) ρ :=
    integrable_comp_of_norm_gradient_le hV hV' (hρ.add (hξ.const_smul h))
  have hpt (x : E) (h : ℝ) : HasDerivAt (fun h ↦ V (x + h • ξ x))
      ⟪gradient V (x + h • ξ x), ξ x⟫ h := by
    have hl : HasDerivAt (fun h : ℝ ↦ x + h • ξ x) (ξ x) h := by
      simpa using ((hasDerivAt_id h).smul_const (ξ x)).const_add x
    have := (hV (x + h • ξ x)).hasFDerivAt.comp_hasDerivAt h hl
    rwa [← toDual_gradient, InnerProductSpace.toDual_apply_apply] at this
  have hgm : AEStronglyMeasurable (fun x ↦ ⟪gradient V x, ξ x⟫) ρ := by
    have : Measurable (gradient V) :=
      (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp (measurable_fderiv ℝ V)
    exact this.aestronglyMeasurable.inner hξm
  -- For `|h| < 1` the derivative is dominated by `C (1 + ‖x‖ + ‖ξ x‖) ‖ξ x‖`, which is
  -- integrable because `x` and `ξ x` are square integrable.
  have hx₂ : Integrable (fun x : E ↦ ‖x‖ ^ 2) ρ :=
    (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).1 hρ
  have hξ₂ : Integrable (fun x ↦ ‖ξ x‖ ^ 2) ρ := (memLp_two_iff_integrable_sq_norm hξm).1 hξ
  have hbd : Integrable (fun x ↦ C * (‖ξ x‖ + (‖x‖ ^ 2 + ‖ξ x‖ ^ 2) / 2 + ‖ξ x‖ ^ 2)) ρ :=
    (((hξ.integrable one_le_two).norm.add ((hx₂.add hξ₂).div_const 2)).add hξ₂).const_mul C
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun h x ↦ ⟪gradient V (x + h • ξ x), ξ x⟫) (Metric.ball_mem_nhds 0 one_pos)
    (.of_forall fun h ↦ (hVint h).aestronglyMeasurable)
    (by simpa only [zero_smul, add_zero] using hVint 0)
    (by simpa only [zero_smul, add_zero] using hgm) ?_ hbd
    (.of_forall fun x h _ ↦ hpt x h)).2.congr_deriv (by simp only [zero_smul, add_zero])
  refine .of_forall fun x h hh ↦ ?_
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
  have hs : ‖x + h • ξ x‖ ≤ ‖x‖ + ‖ξ x‖ := by
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) hh.le
  calc ‖⟪gradient V (x + h • ξ x), ξ x⟫‖
      ≤ ‖gradient V (x + h • ξ x)‖ * ‖ξ x‖ := norm_inner_le_norm _ _
    _ ≤ C * (1 + (‖x‖ + ‖ξ x‖)) * ‖ξ x‖ :=
      mul_le_mul_of_nonneg_right ((hV' _).trans
        (mul_le_mul_of_nonneg_left (by linarith) hC)) (norm_nonneg _)
    _ ≤ C * (‖ξ x‖ + (‖x‖ ^ 2 + ‖ξ x‖ ^ 2) / 2 + ‖ξ x‖ ^ 2) := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hC
      nlinarith [sq_nonneg (‖x‖ - ‖ξ x‖)]

variable {τ : ℝ≥0} {μ ν : WassersteinSpace 2 E} {γ : Measure (E × E)}

/-- **The Euler–Lagrange equation of the JKO step for the potential energy.** Let `V` be a
differentiable potential whose gradient grows at most linearly, `‖∇V x‖ ≤ C (1 + ‖x‖)`. Let `ν`
be a JKO step of time step `τ > 0` from `μ` for the potential energy `ρ ↦ ∫ V dρ`, and `γ` an
optimal coupling of `ν` and `μ`. Then for every vector field `ξ ∈ L²(ν; E)`,
`∫ ⟪x - y, ξ x⟫ dγ(x, y) = -τ ∫ ⟪∇V x, ξ x⟫ dν(x)`. -/
theorem integral_inner_eq_neg_mul_integral_inner_gradient_of_mem_moreauYosidaResolvent
    (hV : Differentiable ℝ V) (hV' : ∀ x, ‖gradient V x‖ ≤ C * (1 + ‖x‖)) (hτ : 0 < τ)
    (hν : ν ∈ moreauYosidaResolvent
      (fun ρ : WassersteinSpace 2 E ↦ potentialEnergy V ((ρ : ProbabilityMeasure E) : Measure E))
      τ μ)
    (hγ : IsCoupling γ ((ν : ProbabilityMeasure E) : Measure E)
      ((μ : ProbabilityMeasure E) : Measure E))
    (hγW : eLpNorm (fun z : E × E ↦ edist z.1 z.2) 2 γ =
      wassersteinEDist 2 ((ν : ProbabilityMeasure E) : Measure E)
        ((μ : ProbabilityMeasure E) : Measure E))
    (hξ : MemLp ξ 2 ((ν : ProbabilityMeasure E) : Measure E)) :
    ∫ z, ⟪z.1 - z.2, ξ z.1⟫ ∂γ =
      -(τ * ∫ x, ⟪gradient V x, ξ x⟫ ∂((ν : ProbabilityMeasure E) : Measure E)) := by
  set ρ := ((ν : ProbabilityMeasure E) : Measure E)
  have hρ : MemLp id 2 ρ := ν.hasFiniteMoment.memLp_id
  -- The potential energy of the perturbed law is the integral of `V (x + h • ξ x)` against `ν`.
  have hf : ∀ᶠ h in 𝓝 (0 : ℝ), ∀ ν' : WassersteinSpace 2 E,
      ((ν' : ProbabilityMeasure E) : Measure E) = ρ.map (fun x ↦ x + h • ξ x) →
      potentialEnergy V ((ν' : ProbabilityMeasure E) : Measure E) =
        ((∫ x, V (x + h • ξ x) ∂ρ : ℝ) : EReal) := by
    refine .of_forall fun h ν' hν' ↦ ?_
    have hT : AEMeasurable (fun x ↦ x + h • ξ x) ρ :=
      aemeasurable_id.add (hξ.aestronglyMeasurable.aemeasurable.const_smul h)
    rw [hν', potentialEnergy_of_integrable ((integrable_map_measure
      hV.continuous.aestronglyMeasurable hT).2
        (integrable_comp_of_norm_gradient_le (V := V) hV hV' (hρ.add (hξ.const_smul h)))),
      integral_map hT hV.continuous.aestronglyMeasurable]
  exact integral_inner_eq_neg_mul_of_mem_moreauYosidaResolvent hτ hν hγ hγW hξ hf
    (hasDerivAt_integral_comp_add_smul hV hV' hρ hξ)

end PotentialEnergy

end TauCeti
