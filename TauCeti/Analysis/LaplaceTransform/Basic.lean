/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.MeasureTheory.Integral.Exp.Complex
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# The one-sided Laplace transform

This file defines the one-sided Laplace transform with a complex parameter as a convergence-carrying
predicate `TauCeti.HasLaplace` and develops its algebraic, analytic, and differential calculus.

Because the Bochner integral of a non-integrable function is zero by convention, the bare equation
`∫ t in Ioi 0, exp (-s * t) • f t = z` cannot distinguish genuine convergence from divergence.
`HasLaplace f s z μ` therefore bundles Bochner integrability of `t ↦ exp (-s * t) • f t` with
respect to `μ` (defaulting to Lebesgue measure restricted to `(0, ∞)`) together with equality of
the integral to `z`.

## Main definitions and results

* `TauCeti.HasLaplace`: `HasLaplace f s z μ` asserts that `t ↦ exp (-s * t) • f t` is integrable
  with respect to `μ` and has integral `z`.
* Congruence, uniqueness, and linearity: `HasLaplace.unique`, `HasLaplace.congr_ae`,
  `hasLaplace_congr_Ioi`, `hasLaplace_restrict_Ici_iff`, `hasLaplace_zero`, `HasLaplace.add`,
  `HasLaplace.neg`, `HasLaplace.sub`, `hasLaplace_sum`, `HasLaplace.const_smul`,
  `ContinuousLinearMap.hasLaplace`, `HasLaplace.conj` (complex conjugation), and
  `HasLaplace.ofReal_re_of_conj` (real-part averaging).
* Scaling, shifts, and half-plane convergence: `hasLaplace_cexp_mul_smul_iff` (frequency shift),
  `HasLaplace.comp_mul_left` and `hasLaplace_comp_mul_left_iff` (positive time dilation),
  `HasLaplace.indicator_Ici_comp_sub_right` (right-shift on `[a, ∞)` for `0 ≤ a`),
  `HasLaplace.integrableOn_of_re_le` (monotonicity of convergence in `Re s`), and
  `exists_hasLaplace_neg_smul_and_hasDerivAt`, `hasDerivAt_of_hasLaplace`,
  `differentiableOn_of_hasLaplace`, and `differentiableOn_of_hasLaplace_re_gt` (holomorphic
  differentiation under the integral sign with respect to `s`, producing the transform of
  `t ↦ -(t : ℂ) • f t`); `hasLaplace_neg_smul_deriv` and `hasLaplace_neg_smul_deriv_of_re_gt`
  state that `F'(s)` is that transform.
* Higher derivatives: `hasLaplace_neg_pow_smul_iteratedDeriv` (the `n`-th derivative is the
  transform of `t ↦ (-t) ^ n • f t`) and `hasLaplace_pow_div_factorial_smul_iteratedDeriv` (the
  normalised coefficient `(-1) ^ n / n ! • F⁽ⁿ⁾` is the transform of `t ↦ (t ^ n / n !) • f t`).
  For a real input and a real centre `b`, `integrable_and_taylor_term_eq_integral` writes the
  Taylor term of the transform at `b - t` as the real integral of
  `u ↦ (t * u) ^ n / n ! * (exp (-b * u) * f u)`.
* Transform of a derivative: `intervalIntegral_cexp_neg_mul_smul_of_eq_add_intervalIntegral`
  establishes the finite-cutoff identity on `[0, T]`; `TauCeti.hasLaplace_deriv_of_primitive` proves
  `HasLaplace g s (s • z - f 0)` for a primitive `f(t) = f(0) + ∫₀ᵗ g(u) du` on `[0, ∞)` assuming
  only `HasLaplace f s z` and integrability of `exp (-s * t) • g t` on `(0, ∞)`, with no growth
  bound and no sign condition on `Re s`; `TauCeti.hasLaplace_deriv` deduces the rule for functions
  continuous at `0` from the right and differentiable on `(0, ∞)`.

## References

* Dennj Osele, *The Laplace transform* (2026), declarations `LaplaceConvergent`, `laplace`, and
  `HasLaplace` at commit `90482cd37e85e423459de2ed103cea2f4d98cb20`, for the argument order,
  default measure, and scalar-action hypotheses of `HasLaplace`.
* Hubert Delange, *Généralisation du théorème de Ikehara*, Ann. Sci. École Norm. Sup. (3) **71**
  (1954), 213–242, for the ordinary Laplace-integral formulation and parameter differentiation on
  open half-planes.
* Jiří Lebl, *Notes on Diffy Qs: Differential Equations for Engineers*, version 6.11 (2026),
  §6.2.1, for the Laplace transform of a derivative.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval

namespace TauCeti

/-! ### Definition and basic properties -/

section Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SMul ℂ E]

/-- `HasLaplace f s z μ` asserts that `t ↦ Complex.exp (-s * t) • f t` is Bochner-integrable with
respect to `μ` and has integral `z`. With the default measure `volume.restrict (Ioi 0)`, this is
the one-sided Laplace transform `∫₀^∞ exp (-s t) • f t dt = z` at complex parameter `s`, following
the predicate `HasLaplace` in Osele, *The Laplace transform*. -/
def HasLaplace (f : ℝ → E) (s : ℂ) (z : E) (μ : Measure ℝ := volume.restrict (Ioi 0)) : Prop :=
  Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ ∧
    ∫ t : ℝ, Complex.exp (-s * t) • f t ∂μ = z

/-- `HasLaplace f s z μ` unfolds to integrability of `t ↦ exp (-s * t) • f t` and equality of its
integral to `z`. -/
theorem hasLaplace_iff {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ} :
    HasLaplace f s z μ ↔
      Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ ∧
        ∫ t : ℝ, Complex.exp (-s * t) • f t ∂μ = z :=
  Iff.rfl

/-- Construct a `HasLaplace` witness from integrability and the value of the integral. -/
theorem HasLaplace.intro {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (hint : Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ)
    (heq : ∫ t : ℝ, Complex.exp (-s * t) • f t ∂μ = z) :
    HasLaplace f s z μ :=
  ⟨hint, heq⟩

/-- An integrable Laplace integrand has, as its transform, its integral. -/
theorem _root_.MeasureTheory.Integrable.hasLaplace {f : ℝ → E} {s : ℂ} {μ : Measure ℝ}
    (hf : Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ) :
    HasLaplace f s (∫ t : ℝ, Complex.exp (-s * t) • f t ∂μ) μ :=
  ⟨hf, rfl⟩

/-- A convergent Laplace transform has an integrable integrand. -/
@[grind →]
theorem HasLaplace.integrable {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) :
    Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ :=
  hf.1

/-- `HasLaplace` with respect to a restricted measure `μ.restrict A` gives `IntegrableOn` on `A`. -/
@[grind →]
theorem HasLaplace.integrableOn {f : ℝ → E} {s : ℂ} {z : E} {A : Set ℝ} {μ : Measure ℝ}
    (hf : HasLaplace f s z (μ.restrict A)) :
    IntegrableOn (fun t : ℝ ↦ Complex.exp (-s * t) • f t) A μ :=
  hf.1

/-- The Laplace integral equals the target value `z`. -/
@[grind →]
theorem HasLaplace.integral_eq {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) :
    ∫ t : ℝ, Complex.exp (-s * t) • f t ∂μ = z :=
  hf.2

/-- The Laplace transform of `f` at `s` with respect to `μ` is unique. -/
@[grind →]
theorem HasLaplace.unique {f : ℝ → E} {s : ℂ} {z z' : E} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) (hf' : HasLaplace f s z' μ) : z = z' :=
  hf.2.symm.trans hf'.2

/-- Functions equal `μ`-almost everywhere have the same Laplace transform. -/
theorem HasLaplace.congr_ae {f g : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) (hfg : f =ᵐ[μ] g) : HasLaplace g s z μ := by
  have hsmul :
      (fun t : ℝ ↦ Complex.exp (-s * t) • f t) =ᵐ[μ] fun t : ℝ ↦ Complex.exp (-s * t) • g t :=
    hfg.mono fun t ht ↦ by simp only [ht]
  exact ⟨hf.1.congr hsmul, (integral_congr_ae hsmul).symm.trans hf.2⟩

/-- Almost-everywhere congruence of `HasLaplace`. -/
theorem hasLaplace_congr_ae {f g : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (hfg : f =ᵐ[μ] g) : HasLaplace f s z μ ↔ HasLaplace g s z μ :=
  ⟨fun h ↦ h.congr_ae hfg, fun h ↦ h.congr_ae hfg.symm⟩

/-- Pointwise agreement on a measurable set `A` preserves `HasLaplace` for `μ.restrict A`. -/
theorem hasLaplace_congr {f g : ℝ → E} {s : ℂ} {z : E} {A : Set ℝ} {μ : Measure ℝ}
    (hA : MeasurableSet A) (hfg : EqOn f g A) :
    HasLaplace f s z (μ.restrict A) ↔ HasLaplace g s z (μ.restrict A) :=
  hasLaplace_congr_ae ((ae_restrict_iff' hA).mpr (.of_forall hfg))

/-- The default one-sided Laplace transform depends only on the values of `f` on `(0, ∞)`. -/
theorem hasLaplace_congr_Ioi {f g : ℝ → E} {s : ℂ} {z : E} (hfg : EqOn f g (Ioi 0)) :
    HasLaplace f s z ↔ HasLaplace g s z :=
  hasLaplace_congr measurableSet_Ioi hfg

/-- Because `{0}` has Lebesgue measure zero, integrating over `[0, ∞)` gives the same `HasLaplace`
predicate as the default domain `(0, ∞)`. -/
@[simp, grind =]
theorem hasLaplace_restrict_Ici_iff {f : ℝ → E} {s : ℂ} {z : E} :
    HasLaplace f s z (volume.restrict (Ici 0)) ↔ HasLaplace f s z := by
  rw [hasLaplace_iff, hasLaplace_iff, ← IntegrableOn, ← IntegrableOn,
    integrableOn_Ici_iff_integrableOn_Ioi, integral_Ici_eq_integral_Ioi]

/-- Every function has Laplace transform `0` with respect to the zero measure. -/
@[simp, grind .]
theorem hasLaplace_zero_measure (f : ℝ → E) (s : ℂ) : HasLaplace f s 0 (0 : Measure ℝ) :=
  ⟨integrable_zero_measure, integral_zero_measure _⟩

end Basic

/-! ### Linearity, shifts, and dilation -/

section Algebra

/-- The zero function has Laplace transform `0` at every complex parameter and for every measure. -/
@[simp, grind .]
theorem hasLaplace_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SMulZeroClass ℂ E]
    (s : ℂ) (μ : Measure ℝ := volume.restrict (Ioi 0)) :
    HasLaplace (0 : ℝ → E) s 0 μ := by
  simp [HasLaplace]

/-- Functional form of `hasLaplace_zero`: the constant zero function has Laplace transform `0`. -/
@[simp, grind .]
theorem hasLaplace_fun_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SMulZeroClass ℂ E]
    (s : ℂ) (μ : Measure ℝ := volume.restrict (Ioi 0)) :
    HasLaplace (fun _ : ℝ ↦ (0 : E)) s 0 μ :=
  hasLaplace_zero s μ

section DistribSMul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DistribSMul ℂ E]

/-- Addition of functions adds their Laplace transforms. -/
@[to_fun]
theorem HasLaplace.add {f g : ℝ → E} {s : ℂ} {z w : E} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) (hg : HasLaplace g s w μ) :
    HasLaplace (f + g) s (z + w) μ := by
  refine ⟨?_, ?_⟩
  · simpa only [Pi.add_def, Pi.add_apply, smul_add] using hf.1.add hg.1
  · simpa only [Pi.add_apply, smul_add, ← hf.2, ← hg.2] using integral_add hf.1 hg.1

/-- Negating a function negates its Laplace transform. -/
@[to_fun]
theorem HasLaplace.neg {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) :
    HasLaplace (-f) s (-z) μ := by
  refine ⟨?_, ?_⟩
  · simpa only [Pi.neg_def, Pi.neg_apply, smul_neg] using hf.1.neg
  · simpa only [Pi.neg_apply, smul_neg, ← hf.2] using integral_neg _

/-- Subtraction of functions subtracts their Laplace transforms. -/
@[to_fun]
theorem HasLaplace.sub {f g : ℝ → E} {s : ℂ} {z w : E} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) (hg : HasLaplace g s w μ) :
    HasLaplace (f - g) s (z - w) μ := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- A finite sum of functions with convergent Laplace transforms has the sum of their transforms. -/
theorem hasLaplace_sum {ι : Type*} {u : Finset ι} {F : ι → ℝ → E} {s : ℂ} {z : ι → E}
    {μ : Measure ℝ} (h : ∀ i ∈ u, HasLaplace (F i) s (z i) μ) :
    HasLaplace (fun t : ℝ ↦ ∑ i ∈ u, F i t) s (∑ i ∈ u, z i) μ := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert a u ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a u)).fun_add
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

end DistribSMul

/-- Scalar multiplication by a normed ring commuting with the `ℝ`- and `ℂ`-actions scales the
Laplace transform. -/
@[to_fun]
theorem HasLaplace.const_smul {R E : Type*} [NormedRing R] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [SMul ℂ E] [Module R E] [IsBoundedSMul R E]
    [SMulCommClass ℝ R E] [SMulCommClass ℂ R E]
    {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) (c : R) :
    HasLaplace (c • f) s (c • z) μ := by
  refine ⟨?_, ?_⟩
  · simpa only [Pi.smul_def, Pi.smul_apply, smul_comm _ c] using hf.1.smul c
  · simpa only [Pi.smul_apply, smul_comm _ c, ← hf.2] using hf.1.integral_smul c

/-- Continuous `ℂ`-linear maps commute with `HasLaplace`. -/
theorem _root_.ContinuousLinearMap.hasLaplace {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (L : E →L[ℂ] F) {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) :
    HasLaplace (fun t : ℝ ↦ L (f t)) s (L z) μ := by
  have hL : (fun t : ℝ ↦ (L.restrictScalars ℝ) (Complex.exp (-s * t) • f t)) =
      fun t : ℝ ↦ Complex.exp (-s * t) • L (f t) := by
    ext t
    simp
  refine ⟨?_, ?_⟩
  · simpa only [hL] using (L.restrictScalars ℝ).integrable_comp hf.1
  · rw [← hL, (L.restrictScalars ℝ).integral_comp_comm hf.1, hf.2,
      ContinuousLinearMap.coe_restrictScalars']

open scoped ComplexConjugate in
/-- Complex conjugation of a scalar Laplace integral conjugates its input and parameter. -/
theorem HasLaplace.conj {f : ℝ → ℂ} {s z : ℂ} {μ : Measure ℝ}
    (h : HasLaplace f s z μ) : HasLaplace (fun u ↦ conj (f u)) (conj s) (conj z) μ := by
  have hconj (u : ℝ) :
      Complex.exp (-conj s * u) • conj (f u) = conj (Complex.exp (-s * u) • f u) := by
    simp only [smul_eq_mul, map_mul, ← Complex.exp_conj, map_neg, Complex.conj_ofReal]
  rw [hasLaplace_iff]
  simp only [hconj]
  refine ⟨?_, ?_⟩
  · exact Complex.conjCLE.toContinuousLinearEquiv.integrable_comp_iff.mpr h.integrable
  · rw [integral_conj, h.integral_eq]

open scoped ComplexConjugate in
/-- If a complex input and its conjugate have Laplace transforms at the same parameter,
then the real part of the input has transform equal to the average of those values. -/
theorem HasLaplace.ofReal_re_of_conj {f : ℝ → ℂ} {s z z' : ℂ} {μ : Measure ℝ}
    (h : HasLaplace f s z μ) (h' : HasLaplace (fun u ↦ conj (f u)) s z' μ) :
    HasLaplace (fun u ↦ ((f u).re : ℂ)) s ((z + z') / 2) μ := by
  have heq (u : ℝ) : (2 : ℂ)⁻¹ * (f u + conj (f u)) = ((f u).re : ℂ) := by
    simpa only [div_eq_inv_mul] using (Complex.re_eq_add_conj (f u)).symm
  simpa only [Pi.smul_apply, smul_eq_mul, heq, div_eq_inv_mul] using
    (h.fun_add h').fun_const_smul (2 : ℂ)⁻¹

/-- Multiplying `f(t)` by `exp (w * t)` shifts the Laplace parameter from `s` to `s - w`. -/
theorem hasLaplace_cexp_mul_smul_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MulAction ℂ E] {f : ℝ → E} {s w : ℂ} {z : E} {μ : Measure ℝ} :
    HasLaplace (fun t : ℝ ↦ Complex.exp (w * t) • f t) s z μ ↔ HasLaplace f (s - w) z μ := by
  have heq : (fun t : ℝ ↦ Complex.exp (-s * t) • (Complex.exp (w * t) • f t)) =
      fun t : ℝ ↦ Complex.exp (-(s - w) * t) • f t := by
    ext t
    rw [← mul_smul, ← Complex.exp_add]
    congr 2
    ring
  simp only [HasLaplace, heq]

/-- Multiplying `f(t)` by `exp (w * t)` transforms `HasLaplace f (s - w) z μ` into
`HasLaplace (fun t ↦ exp (w * t) • f t) s z μ`. -/
theorem HasLaplace.cexp_mul_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MulAction ℂ E] {f : ℝ → E} {s w : ℂ} {z : E} {μ : Measure ℝ}
    (hf : HasLaplace f (s - w) z μ) :
    HasLaplace (fun t : ℝ ↦ Complex.exp (w * t) • f t) s z μ :=
  hasLaplace_cexp_mul_smul_iff.mpr hf

/-- Positive time dilation for the one-sided Laplace transform: for `0 < c`,
`HasLaplace f (s / c) z` gives `HasLaplace (fun t ↦ f (c * t)) s (c⁻¹ • z)`. The value is the real
scalar `c⁻¹ • z`, so no compatibility of the real and complex actions on `E` is needed; for `E = ℂ`
it is `(c : ℂ)⁻¹ * z`, by `Complex.real_smul`. -/
theorem HasLaplace.comp_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SMul ℂ E]
    {f : ℝ → E} {s : ℂ} {z : E} {c : ℝ} (hc : 0 < c)
    (hf : HasLaplace f (s / c) z) :
    HasLaplace (fun t : ℝ ↦ f (c * t)) s (c⁻¹ • z) := by
  let g : ℝ → E := fun u ↦ Complex.exp (-(s / c) * u) • f u
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hfun : (fun t : ℝ ↦ Complex.exp (-s * t) • f (c * t)) = fun t : ℝ ↦ g (c * t) := by
    ext t
    simp only [g, Complex.ofReal_mul]
    have hexp : -(s / (c : ℂ)) * ((c : ℂ) * t) = -s * t := by
      field_simp [hc0]
    rw [hexp]
  refine ⟨?_, ?_⟩
  · rw [hfun, ← IntegrableOn, integrableOn_Ioi_comp_mul_left_iff g 0 hc, mul_zero]
    exact hf.1
  · rw [hfun, integral_comp_mul_left_Ioi g 0 hc, mul_zero, hf.2]

/-- Equivalence form of positive time dilation for the one-sided Laplace transform. -/
theorem hasLaplace_comp_mul_left_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SMul ℂ E] {f : ℝ → E} {s : ℂ} {z : E} {c : ℝ} (hc : 0 < c) :
    HasLaplace (fun t : ℝ ↦ f (c * t)) s (c⁻¹ • z) ↔ HasLaplace f (s / c) z := by
  refine ⟨fun h ↦ ?_, HasLaplace.comp_mul_left hc⟩
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hs : s / c / (c⁻¹ : ℝ) = s := by
    rw [Complex.ofReal_inv, div_inv_eq_mul, div_mul_cancel₀ _ hc0]
  have h1 := HasLaplace.comp_mul_left (inv_pos.mpr hc) (s := s / c) (by rwa [hs])
  rw [inv_inv, smul_inv_smul₀ hc.ne'] at h1
  exact h1.congr_ae (.of_forall fun t ↦ by simp [mul_inv_cancel_left₀ hc.ne'])

/-- Right-translation (Heaviside delay) of a one-sided Laplace transform: for `0 ≤ a`, shifting `f`
by `a` and extending by `0` on `(-∞, a)` multiplies the Laplace transform by `exp (-s * a)`. -/
theorem HasLaplace.indicator_Ici_comp_sub_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℝ → E} {s : ℂ} {z : E} {a : ℝ} (ha : 0 ≤ a)
    (hf : HasLaplace f s z) :
    HasLaplace ((Ici a).indicator fun t ↦ f (t - a)) s (Complex.exp (-s * a) • z) := by
  let g : ℝ → E := (Ioi 0).indicator fun u ↦ Complex.exp (-s * u) • f u
  have hg : Integrable g volume := (integrable_indicator_iff measurableSet_Ioi).mpr hf.1
  have hae : (fun t : ℝ ↦ Complex.exp (-s * t) • (Ici a).indicator (fun u ↦ f (u - a)) t)
      =ᵐ[volume.restrict (Ioi 0)] fun t : ℝ ↦ Complex.exp (-s * a) • g (t - a) := by
    have hnull : ({a} : Set ℝ)ᶜ ∈ ae (volume.restrict (Ioi 0)) :=
      mem_ae_iff.mpr (by simp)
    filter_upwards [ae_restrict_mem measurableSet_Ioi, hnull] with t _ hta
    by_cases h : a < t
    · have hsub : t - a ∈ Ioi (0 : ℝ) := mem_Ioi.mpr (sub_pos.mpr h)
      dsimp only [g]
      rw [indicator_of_mem (mem_Ici.mpr h.le), indicator_of_mem hsub, smul_smul, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    · have hlt : t < a := lt_of_le_of_ne (not_lt.mp h) hta
      have hsub : t - a ∉ Ioi (0 : ℝ) := not_lt.mpr (sub_nonpos.mpr hlt.le)
      dsimp only [g]
      rw [indicator_of_notMem (not_le.mpr hlt), indicator_of_notMem hsub, smul_zero, smul_zero]
  have hsupp : ∀ t ∉ Ioi (0 : ℝ), Complex.exp (-s * a) • g (t - a) = 0 := by
    intro t ht
    have hsub : t - a ∉ Ioi (0 : ℝ) := by
      simp only [mem_Ioi, not_lt] at ht ⊢
      linarith
    dsimp only [g]
    rw [indicator_of_notMem hsub, smul_zero]
  have hint_Ioi : IntegrableOn (fun t : ℝ ↦ Complex.exp (-s * a) • g (t - a)) (Ioi 0) volume :=
    ((hg.comp_sub_right a).smul (Complex.exp (-s * a))).integrableOn
  refine ⟨hint_Ioi.congr_fun_ae hae.symm, ?_⟩
  rw [integral_congr_ae hae, ← integral_indicator measurableSet_Ioi]
  have hind : (Ioi (0 : ℝ)).indicator (fun t : ℝ ↦ Complex.exp (-s * a) • g (t - a)) =
      fun t : ℝ ↦ Complex.exp (-s * a) • g (t - a) := by
    ext t
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · exact indicator_of_mem ht _
    · exact (indicator_of_notMem ht _).trans (hsupp t ht).symm
  rw [hind, (hg.comp_sub_right a).integral_smul, integral_sub_right_eq_self g a,
    integral_indicator measurableSet_Ioi, hf.2]

end Algebra

/-! ### Half-plane convergence and parameter differentiation -/

section HalfPlane

/-- If the one-sided Laplace integral of `f` converges at `s₀`, then it converges at every `s` with
`s₀.re ≤ s.re`. -/
theorem HasLaplace.integrableOn_of_re_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℝ → E} {s₀ s : ℂ} {z₀ : E}
    (hf : HasLaplace f s₀ z₀) (hs : s₀.re ≤ s.re) :
    IntegrableOn (fun t : ℝ ↦ Complex.exp (-s * t) • f t) (Ioi 0) :=
  integrable_cexp_neg_mul_smul_of_re_le hf.1
    ((ae_restrict_mem measurableSet_Ioi).mono fun _ ht ↦ ht.le) hs

/-- Pointwise domination of `exp (-w * t) • (-(t : ℂ) • v)` by `δ⁻¹ * ‖exp (-s₀ * t) • v‖`
whenever `0 < t`, `0 < δ`, and `s₀.re + δ ≤ w.re`. -/
private theorem norm_cexp_neg_mul_smul_neg_smul_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : E) {s₀ w : ℂ} {δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t) (hw : s₀.re + δ ≤ w.re) :
    ‖Complex.exp (-w * t) • (-(t : ℂ) • v)‖ ≤ δ⁻¹ * ‖Complex.exp (-s₀ * t) • v‖ := by
  simp only [norm_smul, norm_neg, Complex.norm_exp, Complex.norm_real,
    Real.norm_of_nonneg ht.le, Complex.re_mul_ofReal, Complex.neg_re]
  have hexp : -(w.re - (s₀.re + δ)) * t + -(δ * t) + -s₀.re * t = -w.re * t := by ring
  have hsplit : Real.exp (-w.re * t) * (t * ‖v‖) =
      δ⁻¹ * (Real.exp (-(w.re - (s₀.re + δ)) * t) * (δ * t * Real.exp (-(δ * t))) *
        (Real.exp (-s₀.re * t) * ‖v‖)) := by
    calc Real.exp (-w.re * t) * (t * ‖v‖)
        = (Real.exp (-(w.re - (s₀.re + δ)) * t) * Real.exp (-(δ * t)) *
            Real.exp (-s₀.re * t)) * (δ⁻¹ * (δ * t)) * ‖v‖ := by
          rw [← Real.exp_add, ← Real.exp_add, hexp, inv_mul_cancel_left₀ hδ.ne', mul_assoc]
      _ = _ := by ring
  rw [hsplit]
  have hexp1 : Real.exp (-(w.re - (s₀.re + δ)) * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) ht.le)
  have hdt : δ * t * Real.exp (-(δ * t)) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one (δ * t)).trans (Real.exp_le_one_iff.mpr (by norm_num))
  calc δ⁻¹ * (Real.exp (-(w.re - (s₀.re + δ)) * t) * (δ * t * Real.exp (-(δ * t))) *
          (Real.exp (-s₀.re * t) * ‖v‖))
      ≤ δ⁻¹ * (1 * 1 * (Real.exp (-s₀.re * t) * ‖v‖)) := by gcongr
    _ = δ⁻¹ * (Real.exp (-s₀.re * t) * ‖v‖) := by ring

/-- **Differentiating a Laplace transform with respect to its parameter.** If `F w` is the
one-sided Laplace transform of `f` for all `w` in a neighborhood of `s`, then
`t ↦ -(t : ℂ) • f t` has a convergent Laplace transform at `s` and `F` has complex derivative equal
to that transform at `s`. -/
theorem exists_hasLaplace_neg_smul_and_hasDerivAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℝ → E} {F : ℂ → E} {s : ℂ}
    (hF : ∀ᶠ w in 𝓝 s, HasLaplace f w (F w)) :
    ∃ z' : E, HasLaplace (fun t : ℝ ↦ -(t : ℂ) • f t) s z' ∧ HasDerivAt F z' s := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hF
  set s₀ : ℂ := s - ((r / 2 : ℝ) : ℂ)
  set δ : ℝ := r / 4
  have hδ : 0 < δ := by positivity
  have hs₀_mem : dist s₀ s < r := by
    rw [dist_eq_norm]
    have hsub : s₀ - s = -((r / 2 : ℝ) : ℂ) := by dsimp [s₀]; ring
    rw [hsub, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    linarith
  have hf₀ : HasLaplace f s₀ (F s₀) := hball hs₀_mem
  have hFs : HasLaplace f s (F s) := hball (by simpa using hr)
  have hball_sub : ∀ w ∈ Metric.ball s δ, dist w s < r := fun w hw ↦
    (Metric.mem_ball.mp hw).trans (by dsimp [δ]; linarith)
  have hball_re : ∀ w ∈ Metric.ball s δ, s₀.re + δ < w.re := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have h1 := (Complex.abs_re_le_norm (w - s)).trans_lt hw
    rw [Complex.sub_re, abs_lt] at h1
    have hs₀_re : s₀.re = s.re - r / 2 := by simp [s₀]
    dsimp [δ] at h1 ⊢
    linarith
  let μ := volume.restrict (Ioi (0 : ℝ))
  let F' : ℂ → ℝ → E := fun w t ↦ Complex.exp (-w * t) • (-(t : ℂ) • f t)
  have hmeas_F : ∀ᶠ w in 𝓝 s, AEStronglyMeasurable (fun t : ℝ ↦ Complex.exp (-w * t) • f t) μ := by
    filter_upwards [Metric.ball_mem_nhds s hδ] with w hw
    exact (hball (hball_sub w hw)).1.aestronglyMeasurable
  have hmeas_F' : AEStronglyMeasurable (F' s) μ := by
    have hcomm : F' s = fun t : ℝ ↦ (-(t : ℂ)) • (Complex.exp (-s * t) • f t) :=
      funext fun _ ↦ smul_comm _ _ _
    rw [hcomm]
    exact (Measurable.aestronglyMeasurable (by fun_prop)).smul hFs.1.aestronglyMeasurable
  have hbound : ∀ᵐ (t : ℝ) ∂μ, ∀ w ∈ Metric.ball s δ,
      ‖F' w t‖ ≤ δ⁻¹ * ‖Complex.exp (-s₀ * t) • f t‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t) w hw
    exact norm_cexp_neg_mul_smul_neg_smul_le (f t) hδ ht (hball_re w hw).le
  have hderiv : ∀ᵐ (t : ℝ) ∂μ, ∀ w ∈ Metric.ball s δ,
      HasDerivAt (fun z : ℂ ↦ Complex.exp (-z * t) • f t) (F' w t) w := by
    refine .of_forall fun t w _ ↦ ?_
    simpa only [F', Pi.neg_apply, id_eq, neg_one_mul, one_mul, mul_smul, neg_mul, smul_neg] using
      (((hasDerivAt_id w).neg.mul_const (t : ℂ)).cexp).smul_const (f t)
  obtain ⟨hint_F', hder_int⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s hδ) hmeas_F hFs.1 hmeas_F' hbound (hf₀.1.norm.const_mul δ⁻¹) hderiv
  refine ⟨∫ t : ℝ, F' s t ∂μ, ⟨hint_F', rfl⟩, ?_⟩
  refine hder_int.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds s hδ] with w hw
  exact (hball (hball_sub w hw)).2.symm

/-- If `F` represents the one-sided Laplace transform of `f` in a neighborhood of `s` and
`t ↦ -(t : ℂ) • f t` has Laplace transform `z'` at `s`, then `HasDerivAt F z' s`. -/
theorem hasDerivAt_of_hasLaplace {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℝ → E} {F : ℂ → E} {s : ℂ} {z' : E}
    (hF : ∀ᶠ w in 𝓝 s, HasLaplace f w (F w))
    (hf' : HasLaplace (fun t : ℝ ↦ -(t : ℂ) • f t) s z') :
    HasDerivAt F z' s := by
  obtain ⟨w', hw', hder⟩ := exists_hasLaplace_neg_smul_and_hasDerivAt hF
  exact hw'.unique hf' ▸ hder

/-- A function representing a convergent one-sided Laplace transform on an open set `U ⊆ ℂ` is
complex-differentiable on `U`. -/
theorem differentiableOn_of_hasLaplace {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℝ → E} {F : ℂ → E} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ s ∈ U, HasLaplace f s (F s)) :
    DifferentiableOn ℂ F U := by
  intro s hs
  obtain ⟨_, -, hder⟩ := exists_hasLaplace_neg_smul_and_hasDerivAt
    (Filter.eventually_of_mem (hU.mem_nhds hs) hF)
  exact hder.differentiableAt.differentiableWithinAt

/-- A function representing a convergent one-sided Laplace transform on an open right half-plane
`{s : ℂ | a < s.re}` is complex-differentiable there. -/
theorem differentiableOn_of_hasLaplace_re_gt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℝ → E} {F : ℂ → E} {a : ℝ}
    (hF : ∀ s : ℂ, a < s.re → HasLaplace f s (F s)) :
    DifferentiableOn ℂ F {s : ℂ | a < s.re} :=
  differentiableOn_of_hasLaplace (isOpen_lt continuous_const Complex.continuous_re) hF

/-- **The derivative of a Laplace transform.** If `F` is the one-sided Laplace transform of `f`
near `s`, then `F'(s)` is the Laplace transform of `t ↦ -(t : ℂ) • f t` at `s`. -/
theorem hasLaplace_neg_smul_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℝ → E} {F : ℂ → E} {s : ℂ} (hF : ∀ᶠ w in 𝓝 s, HasLaplace f w (F w)) :
    HasLaplace (fun t : ℝ ↦ -(t : ℂ) • f t) s (deriv F s) := by
  obtain ⟨_, hz', hder⟩ := exists_hasLaplace_neg_smul_and_hasDerivAt hF
  rwa [hder.deriv]

/-- **The derivative of a Laplace transform on a half-plane.** If `F` is the one-sided Laplace
transform of `f` on the open half-plane `Re s > a`, then at every point of that half-plane `F'(s)`
is the Laplace transform of `t ↦ -(t : ℂ) • f t`. -/
theorem hasLaplace_neg_smul_deriv_of_re_gt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℝ → E} {F : ℂ → E} {a : ℝ} (hF : ∀ s : ℂ, a < s.re → HasLaplace f s (F s)) {s : ℂ}
    (hs : a < s.re) :
    HasLaplace (fun t : ℝ ↦ -(t : ℂ) • f t) s (deriv F s) :=
  hasLaplace_neg_smul_deriv
    (((isOpen_lt continuous_const Complex.continuous_re).eventually_mem hs).mono hF)

/-- **Derivatives of a Laplace transform.** If `F` is the one-sided Laplace transform of `f` near
`s`, then the `n`-th derivative of `F` at `s` is the Laplace transform of `u ↦ (-u) ^ n • f u`. -/
theorem hasLaplace_neg_pow_smul_iteratedDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℝ → E} {F : ℂ → E} {s : ℂ} (hF : ∀ᶠ w in 𝓝 s, HasLaplace f w (F w)) (n : ℕ) :
    HasLaplace (fun u : ℝ ↦ (-(u : ℂ)) ^ n • f u) s (iteratedDeriv n F s) := by
  induction n generalizing s with
  | zero => simpa only [pow_zero, one_smul, iteratedDeriv_zero] using hF.self_of_nhds
  | succ n ih =>
    obtain ⟨z', hz', hder⟩ := exists_hasLaplace_neg_smul_and_hasDerivAt
      (hF.eventually_nhds.mono fun w hw ↦ ih hw)
    rw [iteratedDeriv_succ, hder.deriv]
    simpa only [pow_succ', mul_smul] using hz'

open scoped Nat in
/-- **Taylor coefficients of a Laplace transform.** If `F` is the one-sided Laplace transform of
`f` near `s`, then `(-1) ^ n / n !` times the `n`-th derivative of `F` at `s`, the `n`-th Taylor
coefficient of `F` at `s` up to the sign `(-1) ^ n`, is the Laplace transform of
`u ↦ (u ^ n / n !) • f u`. -/
theorem hasLaplace_pow_div_factorial_smul_iteratedDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℝ → E} {F : ℂ → E} {s : ℂ} (hF : ∀ᶠ w in 𝓝 s, HasLaplace f w (F w))
    (n : ℕ) :
    HasLaplace (fun u : ℝ ↦ ((u : ℂ) ^ n / n !) • f u) s
      (((-1) ^ n / n ! : ℂ) • iteratedDeriv n F s) := by
  have hc : ∀ u : ℝ, ((-1) ^ n / n ! : ℂ) * (-(u : ℂ)) ^ n = (u : ℂ) ^ n / n ! := fun u ↦ by
    rw [div_mul_eq_mul_div, ← mul_pow, neg_one_mul, neg_neg]
  simpa only [Pi.smul_def, smul_smul, hc] using
    (hasLaplace_neg_pow_smul_iteratedDeriv hF n).const_smul ((-1) ^ n / n ! : ℂ)

open scoped Nat in
/-- **Real Taylor terms of a real Laplace transform.** Let `F` be the Laplace transform of a real
function `f` near a real point `b`. For real `t`, the function
`u ↦ (t * u) ^ n / n ! * (exp (-b * u) * f u)` is integrable on `(0, ∞)`, and its integral is the
`n`-th term of the Taylor expansion of `F` about `b`, evaluated at `b - t`. -/
theorem integrable_and_taylor_term_eq_integral {f : ℝ → ℝ} {F : ℂ → ℂ} {b : ℝ}
    (hF : ∀ᶠ w in 𝓝 (b : ℂ), HasLaplace (fun u ↦ (f u : ℂ)) w (F w)) (t : ℝ) (n : ℕ) :
    Integrable (fun u ↦ (t * u) ^ n / (n ! : ℝ) * (Real.exp (-b * u) * f u))
        (volume.restrict (Ioi 0)) ∧
      (n ! : ℂ)⁻¹ • (-(t : ℂ)) ^ n • iteratedDeriv n F b =
        ((∫ u in Ioi 0, (t * u) ^ n / (n ! : ℝ) * (Real.exp (-b * u) * f u) : ℝ) : ℂ) := by
  have hL := (hasLaplace_pow_div_factorial_smul_iteratedDeriv hF n).const_smul ((t : ℂ) ^ n)
  have key : ∀ u : ℝ, Complex.exp (-(b : ℂ) * u) • ((t : ℂ) ^ n • ((u : ℂ) ^ n / n !) • (f u : ℂ)) =
      (((t * u) ^ n / (n ! : ℝ) * (Real.exp (-b * u) * f u) : ℝ) : ℂ) := fun u ↦ by
    simp only [smul_eq_mul]
    push_cast
    ring
  have hc := hL.integrable.congr (.of_forall key)
  refine ⟨hc.re.congr (.of_forall fun u ↦ by
    simp only [RCLike.re_to_complex, Complex.ofReal_re]), ?_⟩
  have hI : ∫ u : ℝ in Ioi 0,
      Complex.exp (-(b : ℂ) * u) • ((t : ℂ) ^ n • ((u : ℂ) ^ n / n !) • (f u : ℂ)) =
        (t : ℂ) ^ n • ((-1) ^ n / n ! : ℂ) • iteratedDeriv n F b := hL.integral_eq
  rw [← integral_complex_ofReal, ← integral_congr_ae (.of_forall key), hI]
  simp only [smul_eq_mul, neg_pow (t : ℂ)]
  ring

end HalfPlane

/-! ### The Laplace transform of a derivative -/

section LaplaceDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **Finite-cutoff Laplace identity for a primitive.** If `g` is integrable on `[0, T]` (`0 ≤ T`)
and `f(t) = f(0) + ∫₀ᵗ g(u) du` on `[0, T]`, then for every `s : ℂ`,
`∫₀ᵀ exp (-s t) • g t dt = exp (-s T) • f T - f 0 + s • ∫₀ᵀ exp (-s t) • f t dt`. -/
theorem intervalIntegral_cexp_neg_mul_smul_of_eq_add_intervalIntegral {f g : ℝ → E} (s : ℂ) {T : ℝ}
    (hT : 0 ≤ T) (hg : IntervalIntegrable g volume 0 T)
    (hfg : ∀ t ∈ Icc 0 T, f t = f 0 + ∫ u in (0 : ℝ)..t, g u) :
    ∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • g t =
      Complex.exp (-s * T) • f T - f 0 + s • ∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • f t := by
  let φ : ℝ → ℂ := fun t ↦ Complex.exp (-s * t)
  have hφ : ContDiff ℝ 1 φ := (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  have hderiv : ∀ t : ℝ, deriv φ t = -s * Complex.exp (-s * t) := fun t ↦ by
    simpa [φ, mul_comm] using (((hasDerivAt_id t).ofReal_comp.const_mul (-s)).cexp).deriv
  have hf_cont : ContinuousOn f (Icc 0 T) := by
    refine (continuousOn_const.add ?_).congr fun t ht ↦ hfg t ht
    simpa only [uIcc_of_le hT] using
      intervalIntegral.continuousOn_primitive_interval' hg left_mem_uIcc
  have hf_int : IntervalIntegrable f volume 0 T := hf_cont.intervalIntegrable_of_Icc hT
  have hibp := TauCeti.intervalIntegral.integral_deriv_smul_primitive_eq_sub_of_le hT hφ hg
  have hcongr : EqOn (fun t : ℝ ↦ deriv φ t • ∫ u in (0 : ℝ)..t, g u)
      (fun t : ℝ ↦ (-s) • (Complex.exp (-s * t) • f t) + (s * Complex.exp (-s * t)) • f 0)
      (uIcc 0 T) := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    dsimp only
    rw [hderiv t, eq_sub_iff_add_eq'.mpr (hfg t ht).symm]
    simp only [smul_sub, neg_mul, neg_smul, sub_neg_eq_add, mul_smul]
  have h1 : IntervalIntegrable (fun t : ℝ ↦ (-s) • (Complex.exp (-s * t) • f t)) volume 0 T :=
    ((intervalIntegrable_cexp_neg_mul_smul_iff s).mpr hf_int).smul (-s)
  have h2 : IntervalIntegrable (fun t : ℝ ↦ (s * Complex.exp (-s * t)) • f 0) volume 0 T :=
    (by fun_prop : Continuous fun t : ℝ ↦ (s * Complex.exp (-s * t)) • f 0).intervalIntegrable 0 T
  have hconst : ∫ t in (0 : ℝ)..T, (s * Complex.exp (-s * t)) • f 0 =
      (1 - Complex.exp (-s * T)) • f 0 := by
    rw [intervalIntegral.integral_smul_const, intervalIntegral_const_mul_cexp_neg_mul]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_smul, hconst,
    eq_sub_iff_add_eq'.mpr (hfg T ⟨hT, le_rfl⟩).symm] at hibp
  have heq : ∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • g t =
      Complex.exp (-s * T) • (f T - f 0) -
        ((-s) • (∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • f t) +
          (1 - Complex.exp (-s * T)) • f 0) :=
    eq_sub_of_add_eq' (add_eq_of_eq_sub hibp)
  rw [heq, smul_sub, sub_smul, one_smul, neg_smul]
  abel

/-- **The Laplace transform of a derivative, primitive form.** If `f(t) = f(0) + ∫₀ᵗ g(u) du` for
every `t ≥ 0`, `HasLaplace f s z`, and `t ↦ exp (-s * t) • g t` is integrable on `(0, ∞)`, then
`HasLaplace g s (s • z - f 0)`. Neither a sign condition on `Re s` nor an exponential growth bound
on `f` is assumed: `exp (-s * T) • f T → 0` follows from the two integrabilities (compare Lebl,
*Notes on Diffy Qs*, version 6.11, §6.2.1, under exponential order). -/
theorem hasLaplace_deriv_of_primitive {f g : ℝ → E} {s : ℂ} {z : E}
    (hfg : ∀ t ∈ Ici (0 : ℝ), f t = f 0 + ∫ u in (0 : ℝ)..t, g u)
    (hf : HasLaplace f s z)
    (hg : Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • g t) (volume.restrict (Ioi 0))) :
    HasLaplace g s (s • z - f 0) := by
  set w : E := ∫ t in Ioi (0 : ℝ), Complex.exp (-s * t) • g t
  have hg_tend :
      Tendsto (fun T : ℝ ↦ ∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • g t) atTop (𝓝 w) :=
    intervalIntegral_tendsto_integral_Ioi 0 hg tendsto_id
  have hf_tend :
      Tendsto (fun T : ℝ ↦ ∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • f t) atTop (𝓝 z) :=
    hf.2 ▸ intervalIntegral_tendsto_integral_Ioi 0 hf.1 tendsto_id
  have hbd_tend :
      Tendsto (fun T : ℝ ↦ Complex.exp (-s * T) • f T) atTop (𝓝 (w - s • z + f 0)) := by
    refine (hg_tend.sub (hf_tend.const_smul s) |>.add_const (f 0)).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    have hid := intervalIntegral_cexp_neg_mul_smul_of_eq_add_intervalIntegral s hT
      (intervalIntegrable_of_integrableOn_cexp_neg_mul_smul_Ioi hg hT)
      (fun t ht ↦ hfg t ht.1)
    rw [hid]
    abel
  have hiat : IntegrableAtFilter (fun t : ℝ ↦ Complex.exp (-s * t) • f t) atTop volume :=
    ⟨Ioi 0, Ioi_mem_atTop 0, hf.1⟩
  have hinf : ∀ U ∈ (atTop : Filter ℝ), volume U = ⊤ := by
    intro U hU
    obtain ⟨b, hb⟩ := mem_atTop_sets.mp hU
    exact top_unique (Real.volume_Ici (a := b) ▸ measure_mono hb)
  have hzero : w - s • z + f 0 = 0 := hiat.eq_zero_of_tendsto hinf hbd_tend
  refine ⟨hg, ?_⟩
  rw [← sub_eq_zero]
  calc w - (s • z - f 0) = w - s • z + f 0 := by abel
    _ = 0 := hzero

/-- **The Laplace transform of a derivative.** If `f` is continuous at `0` from the right, has
derivative `f' t` at every `t > 0`, satisfies `HasLaplace f s z`, and `t ↦ exp (-s * t) • f' t`
is integrable on `(0, ∞)`, then `HasLaplace f' s (s • z - f 0)` (compare Lebl, *Notes on Diffy Qs*,
version 6.11, §6.2.1, under exponential order). -/
theorem hasLaplace_deriv {f f' : ℝ → E} {s : ℂ} {z : E}
    (hf0 : ContinuousWithinAt f (Ici 0) 0)
    (hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t)
    (hf : HasLaplace f s z)
    (hf' : Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f' t) (volume.restrict (Ioi 0))) :
    HasLaplace f' s (s • z - f 0) := by
  have hf_cont : ContinuousOn f (Ici 0) := by
    intro t ht
    rcases ht.out.eq_or_lt with rfl | hpos
    · exact hf0
    · exact (hderiv t hpos).continuousAt.continuousWithinAt
  refine hasLaplace_deriv_of_primitive (fun t (ht : 0 ≤ t) ↦ ?_) hf hf'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
    (hf_cont.mono Icc_subset_Ici_self) (fun u hu ↦ hderiv u hu.1)
    (intervalIntegrable_of_integrableOn_cexp_neg_mul_smul_Ioi hf' ht), add_sub_cancel]

end LaplaceDeriv

end TauCeti
