/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Integral.Exp.Decay

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
  `HasLaplace.neg`, `HasLaplace.sub`, `hasLaplace_sum`, `HasLaplace.const_smul`, and
  `ContinuousLinearMap.comp_hasLaplace`.
* Scaling, shifts, and half-plane convergence: `hasLaplace_cexp_mul_smul_iff` (frequency shift),
  `HasLaplace.comp_mul_left` and `hasLaplace_comp_mul_left_iff` (positive time dilation),
  `HasLaplace.indicator_Ici_sub` (right-shift on `[a, ∞)` for `0 ≤ a`),
  `HasLaplace.integrableOn_of_re_le` (monotonicity of convergence in `Re s`), and
  `HasLaplace.exists_hasLaplace_neg_mul_and_hasDerivAt`, `HasLaplace.hasDerivAt_of_re_lt`, and
  `differentiableOn_of_hasLaplace_re_gt` (holomorphic differentiation under the integral sign with
  respect to `s`, producing the transform of `t ↦ -(t : ℂ) • f t`).
* Transform of a derivative: `TauCeti.hasLaplace_deriv_of_primitive` proves
  `HasLaplace g s (s • z - f 0)` for a primitive `f(t) = f(0) + ∫₀ᵗ g(u) du` on `[0, ∞)` assuming
  only `HasLaplace f s z` and integrability of `exp (-s * t) • g t` on `(0, ∞)`, with no growth
  bound and no sign condition on `Re s`; `TauCeti.hasLaplace_deriv` deduces the rule for functions
  continuous at `0` from the right and differentiable on `(0, ∞)`.
* Elementary transforms: `hasLaplace_const`, `hasLaplace_one`, `not_hasLaplace_one_of_re_nonpos`,
  `hasLaplace_indicator_Ici_one`, `hasLaplace_cexp_mul`, `hasLaplace_pow`,
  `hasLaplace_cexp_mul_pow`, and `hasLaplace_exp_mul_pow`.

## References

* Dennj Osele, *The Laplace transform* (2026), declarations `LaplaceConvergent`, `laplace`, and
  `HasLaplace` at commit `90482cd37e85e423459de2ed103cea2f4d98cb20`, for the argument order,
  default measure, and scalar-action hypotheses of `HasLaplace`.
* Hubert Delange, *Généralisation du théorème de Ikehara*, Ann. Sci. École Norm. Sup. (3) **71**
  (1954), 213–242, for the ordinary Laplace-integral formulation and parameter differentiation on
  open half-planes.
* Jiří Lebl, *Notes on Diffy Qs: Differential Equations for Engineers*, version 6.11 (2026),
  §6.2.1 and Table 6.2, for the Laplace transform of a derivative and elementary transforms.
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
@[expose]
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

/-- A convergent Laplace transform has an integrable integrand. -/
theorem HasLaplace.integrable {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) :
    Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ :=
  hf.1

/-- `HasLaplace` with respect to a restricted measure `μ.restrict A` gives `IntegrableOn` on `A`. -/
theorem HasLaplace.integrableOn {f : ℝ → E} {s : ℂ} {z : E} {A : Set ℝ} {μ : Measure ℝ}
    (hf : HasLaplace f s z (μ.restrict A)) :
    IntegrableOn (fun t : ℝ ↦ Complex.exp (-s * t) • f t) A μ :=
  hf.1

/-- The Laplace integral equals the target value `z`. -/
theorem HasLaplace.integral_eq {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) :
    ∫ t : ℝ, Complex.exp (-s * t) • f t ∂μ = z :=
  hf.2

/-- The Laplace transform of `f` at `s` with respect to `μ` is unique. -/
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
@[simp]
theorem hasLaplace_restrict_Ici_iff {f : ℝ → E} {s : ℂ} {z : E} :
    HasLaplace f s z (volume.restrict (Ici 0)) ↔ HasLaplace f s z := by
  rw [hasLaplace_iff, hasLaplace_iff, ← IntegrableOn, ← IntegrableOn,
    integrableOn_Ici_iff_integrableOn_Ioi, integral_Ici_eq_integral_Ioi]

/-- Every function has Laplace transform `0` with respect to the zero measure. -/
@[simp]
theorem hasLaplace_zero_measure (f : ℝ → E) (s : ℂ) : HasLaplace f s 0 (0 : Measure ℝ) :=
  ⟨integrable_zero_measure, integral_zero_measure _⟩

end Basic

/-! ### Linearity, shifts, and dilation -/

section Algebra

/-- The zero function has Laplace transform `0` at every complex parameter and for every measure. -/
@[simp]
theorem hasLaplace_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SMulZeroClass ℂ E]
    (s : ℂ) (μ : Measure ℝ := volume.restrict (Ioi 0)) :
    HasLaplace (0 : ℝ → E) s 0 μ := by
  simp [HasLaplace]

@[simp]
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
theorem _root_.ContinuousLinearMap.comp_hasLaplace {E F : Type*}
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
  · rw [← hL, (L.restrictScalars ℝ).integral_comp_comm hf.1, hf.2]
    rfl

/-- Multiplying `f(t)` by `exp (w * t)` shifts the Laplace parameter from `s` to `s - w`. -/
theorem hasLaplace_cexp_mul_smul_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MulAction ℂ E] {f : ℝ → E} {s w : ℂ} {z : E} {μ : Measure ℝ} :
    HasLaplace (fun t : ℝ ↦ Complex.exp (w * t) • f t) s z μ ↔ HasLaplace f (s - w) z μ := by
  have heq : (fun t : ℝ ↦ Complex.exp (-s * t) • (Complex.exp (w * t) • f t)) =
      fun t : ℝ ↦ Complex.exp (-(s - w) * t) • f t := by
    ext t
    rw [← mul_smul, ← Complex.exp_add]
    ring_nf
  simp only [HasLaplace, heq]

/-- Multiplying `f(t)` by `exp (w * t)` transforms `HasLaplace f (s - w) z μ` into
`HasLaplace (fun t ↦ exp (w * t) • f t) s z μ`. -/
theorem HasLaplace.cexp_mul_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MulAction ℂ E] {f : ℝ → E} {s w : ℂ} {z : E} {μ : Measure ℝ}
    (hf : HasLaplace f (s - w) z μ) :
    HasLaplace (fun t : ℝ ↦ Complex.exp (w * t) • f t) s z μ :=
  hasLaplace_cexp_mul_smul_iff.mpr hf

/-- Positive time dilation for the one-sided Laplace transform: for `0 < c`,
`HasLaplace f (s / c) z` gives `HasLaplace (fun t ↦ f (c * t)) s ((c : ℂ)⁻¹ • z)`. -/
theorem HasLaplace.comp_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MulAction ℂ E] [IsScalarTower ℝ ℂ E]
    {f : ℝ → E} {s : ℂ} {z : E} {c : ℝ} (hc : 0 < c)
    (hf : HasLaplace f (s / c) z) :
    HasLaplace (fun t : ℝ ↦ f (c * t)) s ((c : ℂ)⁻¹ • z) := by
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
  · rw [hfun, integral_comp_mul_left_Ioi g 0 hc, mul_zero, hf.2, ← Complex.ofReal_inv]
    conv_lhs => rw [← one_smul ℂ z, ← smul_assoc, Complex.real_smul, mul_one]

/-- Equivalence form of positive time dilation for the one-sided Laplace transform. -/
theorem hasLaplace_comp_mul_left_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MulAction ℂ E] [IsScalarTower ℝ ℂ E]
    {f : ℝ → E} {s : ℂ} {z : E} {c : ℝ} (hc : 0 < c) :
    HasLaplace (fun t : ℝ ↦ f (c * t)) s ((c : ℂ)⁻¹ • z) ↔ HasLaplace f (s / c) z := by
  refine ⟨fun h ↦ ?_, HasLaplace.comp_mul_left hc⟩
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hs : s / c / (c⁻¹ : ℝ) = s := by
    rw [Complex.ofReal_inv, div_inv_eq_mul, div_mul_cancel₀ _ hc0]
  have h1 := HasLaplace.comp_mul_left (inv_pos.mpr hc) (s := s / c) (by rwa [hs])
  have htarget : ((c⁻¹ : ℝ) : ℂ)⁻¹ • (c : ℂ)⁻¹ • z = z := by
    rw [Complex.ofReal_inv, inv_inv, ← mul_smul, mul_inv_cancel₀ hc0, one_smul]
  rw [htarget] at h1
  exact h1.congr_ae (.of_forall fun t ↦ by simp [mul_inv_cancel_left₀ hc.ne'])

/-- Right-translation (Heaviside delay) of a one-sided Laplace transform: for `0 ≤ a`, shifting `f`
by `a` and extending by `0` on `(-∞, a)` multiplies the Laplace transform by `exp (-s * a)`. -/
theorem HasLaplace.indicator_Ici_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
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
    IntegrableOn (fun t : ℝ ↦ Complex.exp (-s * t) • f t) (Ioi 0) := by
  have heq : (fun t : ℝ ↦ Complex.exp (-s * t) • f t) =
      fun t : ℝ ↦ Complex.exp (-(s - s₀) * t) • (Complex.exp (-s₀ * t) • f t) := by
    ext t
    rw [smul_smul, ← Complex.exp_add]
    ring_nf
  rw [heq]
  refine hf.1.bdd_smul 1 (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  rw [Complex.norm_exp, Complex.re_mul_ofReal, Complex.neg_re, Complex.sub_re]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) ht.le)

/-- Elementary uniform bound `t * exp (-δ * t) ≤ δ⁻¹` for `0 < δ` and `0 ≤ t`, used to dominate
parameter derivatives of Laplace integrands on half-planes. -/
private theorem mul_exp_neg_mul_le_inv {δ t : ℝ} (hδ : 0 < δ) :
    t * Real.exp (-δ * t) ≤ δ⁻¹ := by
  have h1 : δ * t ≤ Real.exp (δ * t) :=
    (lt_add_one (δ * t)).le.trans (by simpa [add_comm] using Real.add_one_le_exp (δ * t))
  have hneg : -δ * t = -(δ * t) := by ring
  rw [hneg, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  calc t = δ⁻¹ * (δ * t) := by field_simp [hδ.ne']
    _ ≤ δ⁻¹ * Real.exp (δ * t) := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hδ.le)

/-- Pointwise domination of `exp (-w * t) • (-(t : ℂ) • f t)` by `δ⁻¹ * ‖exp (-s₀ * t) • f t‖`
whenever `0 < t`, `0 < δ`, and `s₀.re + δ ≤ w.re`. -/
private theorem norm_cexp_neg_mul_smul_neg_mul_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : E) {s₀ w : ℂ} {δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t) (hw : s₀.re + δ ≤ w.re) :
    ‖Complex.exp (-w * t) • (-(t : ℂ) • v)‖ ≤ δ⁻¹ * ‖Complex.exp (-s₀ * t) • v‖ := by
  rw [norm_smul, norm_smul, norm_neg, norm_smul, Complex.norm_exp, Complex.norm_exp,
    Complex.norm_real, Real.norm_of_nonneg ht.le, Complex.re_mul_ofReal, Complex.re_mul_ofReal,
    Complex.neg_re, Complex.neg_re]
  have hsplit : Real.exp (-w.re * t) * (t * ‖v‖) =
      Real.exp (-(w.re - (s₀.re + δ)) * t) * (t * Real.exp (-δ * t)) *
        (Real.exp (-s₀.re * t) * ‖v‖) := by
    calc Real.exp (-w.re * t) * (t * ‖v‖)
        = (Real.exp (-(w.re - (s₀.re + δ)) * t) * Real.exp (-δ * t) *
            Real.exp (-s₀.re * t)) * t * ‖v‖ := by
          rw [← Real.exp_add, ← Real.exp_add]
          ring_nf
      _ = _ := by ring
  rw [hsplit]
  have hexp1 : Real.exp (-(w.re - (s₀.re + δ)) * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) ht.le)
  calc Real.exp (-(w.re - (s₀.re + δ)) * t) * (t * Real.exp (-δ * t)) *
          (Real.exp (-s₀.re * t) * ‖v‖)
      ≤ 1 * δ⁻¹ * (Real.exp (-s₀.re * t) * ‖v‖) := by
        gcongr
        exact mul_exp_neg_mul_le_inv hδ
    _ = δ⁻¹ * (Real.exp (-s₀.re * t) * ‖v‖) := by ring

/-- **Differentiating a Laplace transform with respect to its parameter.** If `f` has a convergent
Laplace transform at `s₀` and `F w` is its Laplace transform on the open half-plane `s₀.re < w.re`,
then at every `s` with `s₀.re < s.re`, `t ↦ -(t : ℂ) • f t` has a convergent Laplace transform and
`F` has complex derivative equal to that transform at `s`. -/
theorem HasLaplace.exists_hasLaplace_neg_mul_and_hasDerivAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℝ → E} {F : ℂ → E} {s₀ s : ℂ} {z₀ : E}
    (hf₀ : HasLaplace f s₀ z₀) (hs : s₀.re < s.re)
    (hF : ∀ w : ℂ, s₀.re < w.re → HasLaplace f w (F w)) :
    ∃ z' : E, HasLaplace (fun t : ℝ ↦ -(t : ℂ) • f t) s z' ∧ HasDerivAt F z' s := by
  set δ : ℝ := (s.re - s₀.re) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hball_re : ∀ w ∈ Metric.ball s δ, s₀.re + δ < w.re := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have h1 := (Complex.abs_re_le_norm (w - s)).trans_lt hw
    rw [Complex.sub_re, abs_lt] at h1
    dsimp [δ] at h1 ⊢
    linarith
  let μ := volume.restrict (Ioi (0 : ℝ))
  let F' : ℂ → ℝ → E := fun w t ↦ Complex.exp (-w * t) • (-(t : ℂ) • f t)
  have hmeas_F : ∀ᶠ w in 𝓝 s, AEStronglyMeasurable (fun t : ℝ ↦ Complex.exp (-w * t) • f t) μ := by
    filter_upwards [Metric.ball_mem_nhds s hδ] with w hw
    exact (hF w (by linarith [hball_re w hw])).1.aestronglyMeasurable
  have hmeas_F' : AEStronglyMeasurable (F' s) μ := by
    have hcomm : F' s = fun t : ℝ ↦ (-(t : ℂ)) • (Complex.exp (-s * t) • f t) :=
      funext fun _ ↦ smul_comm _ _ _
    rw [hcomm]
    exact (Measurable.aestronglyMeasurable (by fun_prop)).smul (hF s hs).1.aestronglyMeasurable
  have hbound : ∀ᵐ (t : ℝ) ∂μ, ∀ w ∈ Metric.ball s δ,
      ‖F' w t‖ ≤ δ⁻¹ * ‖Complex.exp (-s₀ * t) • f t‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t) w hw
    exact norm_cexp_neg_mul_smul_neg_mul_le (f t) hδ ht (hball_re w hw).le
  have hderiv : ∀ᵐ (t : ℝ) ∂μ, ∀ w ∈ Metric.ball s δ,
      HasDerivAt (fun z : ℂ ↦ Complex.exp (-z * t) • f t) (F' w t) w := by
    refine .of_forall fun t w _ ↦ ?_
    simpa only [F', Pi.neg_apply, id_eq, neg_one_mul, one_mul, mul_smul, neg_mul, smul_neg] using
      (((hasDerivAt_id w).neg.mul_const (t : ℂ)).cexp).smul_const (f t)
  obtain ⟨hint_F', hder_int⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s hδ) hmeas_F (hF s hs).1 hmeas_F' hbound (hf₀.1.norm.const_mul δ⁻¹)
    hderiv
  refine ⟨∫ t : ℝ, F' s t ∂μ, ⟨hint_F', rfl⟩, ?_⟩
  refine hder_int.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds s hδ] with w hw
  exact (hF w (by linarith [hball_re w hw])).2.symm

/-- If `F` represents the Laplace transform of `f` on `s₀.re < w.re` (witnessed by convergence at
`s₀`) and `t ↦ -(t : ℂ) • f t` has Laplace transform `z'` at `s` with `s₀.re < s.re`, then
`HasDerivAt F z' s`. -/
theorem HasLaplace.hasDerivAt_of_re_lt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℝ → E} {F : ℂ → E} {s₀ s : ℂ} {z₀ z' : E}
    (hf₀ : HasLaplace f s₀ z₀) (hs : s₀.re < s.re)
    (hF : ∀ w : ℂ, s₀.re < w.re → HasLaplace f w (F w))
    (hf' : HasLaplace (fun t : ℝ ↦ -(t : ℂ) • f t) s z') :
    HasDerivAt F z' s := by
  obtain ⟨w', hw', hder⟩ := hf₀.exists_hasLaplace_neg_mul_and_hasDerivAt hs hF
  exact hw'.unique hf' ▸ hder

/-- A function representing a convergent one-sided Laplace transform on an open right half-plane
`{s : ℂ | a < s.re}` is complex-differentiable there. -/
theorem differentiableOn_of_hasLaplace_re_gt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℝ → E} {F : ℂ → E} {a : ℝ}
    (hF : ∀ s : ℂ, a < s.re → HasLaplace f s (F s)) :
    DifferentiableOn ℂ F {s : ℂ | a < s.re} := by
  intro s (hs : a < s.re)
  let s₀ : ℂ := ((a + s.re) / 2 : ℝ)
  have ha₀ : a < s₀.re := by simp [s₀]; linarith
  have hs₀ : s₀.re < s.re := by simp [s₀]; linarith
  obtain ⟨z', -, hder⟩ := (hF s₀ ha₀).exists_hasLaplace_neg_mul_and_hasDerivAt hs₀
    fun w hw ↦ hF w (ha₀.trans hw)
  exact hder.differentiableAt.differentiableWithinAt

end HalfPlane

/-! ### The Laplace transform of a derivative -/

section LaplaceDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Multiplying by the scalar exponential `t ↦ exp (-s * t)` preserves `IntervalIntegrable` for
vector-valued functions (compare `TauCeti.intervalIntegrable_mul_cexp_neg_mul_iff` for `E = ℂ`). -/
theorem intervalIntegrable_cexp_neg_mul_smul_iff {g : ℝ → E} {a b : ℝ} (s : ℂ) :
    IntervalIntegrable (fun t : ℝ ↦ Complex.exp (-s * t) • g t) volume a b ↔
      IntervalIntegrable g volume a b := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.continuousOn_smul (by fun_prop)⟩
  have h' := h.continuousOn_smul (f := fun t : ℝ ↦ Complex.exp (s * t)) (by fun_prop)
  simpa only [smul_smul, ← Complex.exp_add, neg_mul, add_neg_cancel, Complex.exp_zero, one_smul]
    using h'

/-- Product integrability of the upper-triangle kernel `(t, r) ↦ 1_{t < r} (s exp (-s r)) • g t`
on `(0, T] × (0, T]`. -/
private theorem integrable_prod_triangle_cexp_smul {g : ℝ → E} (s : ℂ) {T : ℝ}
    (hT : 0 ≤ T) (hg : IntegrableOn g (Ioc 0 T)) :
    Integrable
      (Function.uncurry fun t r : ℝ ↦
        if t < r then (s * Complex.exp (-s * r)) • g t else 0)
      ((volume.restrict (Ioc 0 T)).prod (volume.restrict (Ioc 0 T))) := by
  have hexp : IntegrableOn (fun r : ℝ ↦ s * Complex.exp (-s * r)) (Ioc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp
      ((by fun_prop : Continuous _).intervalIntegrable 0 T)
  have heq : (Function.uncurry fun t r : ℝ ↦
        if t < r then (s * Complex.exp (-s * r)) • g t else 0) =
      {p : ℝ × ℝ | p.1 < p.2}.indicator
        ((fun z : ℝ × ℝ ↦ (s * Complex.exp (-s * z.1)) • g z.2) ∘ Prod.swap) := by
    ext ⟨t, r⟩
    simp [Set.indicator_apply]
  rw [heq]
  exact (hexp.smul_prod hg).swap.indicator (measurableSet_lt measurable_fst measurable_snd)

/-- Evaluation of `∫ r in Ioc a T, s * exp (-s * r)` for `a ≤ T`. -/
private theorem setIntegral_Ioc_mul_cexp_neg_mul (s : ℂ) {a T : ℝ} (ha : a ≤ T) :
    ∫ r in Ioc a T, s * Complex.exp (-s * r) =
      Complex.exp (-s * a) - Complex.exp (-s * T) := by
  have hneg : (fun r : ℝ ↦ s * Complex.exp (-s * r)) =
      fun r : ℝ ↦ -(-s * Complex.exp (-s * r)) := funext fun _ ↦ by ring
  rw [← intervalIntegral.integral_of_le ha, hneg, intervalIntegral.integral_neg]
  have hd : ∀ r ∈ Ioo a T,
      HasDerivAt (fun x : ℝ ↦ Complex.exp (-s * x)) (-s * Complex.exp (-s * r)) r := by
    intro r _
    simpa [mul_comm] using ((hasDerivAt_id r).ofReal_comp.const_mul (-s)).cexp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha (by fun_prop) hd
    ((by fun_prop : Continuous _).intervalIntegrable _ _)]
  ring

variable [CompleteSpace E]

/-- **Finite-cutoff Laplace identity for a primitive.** If `g` is integrable on `[0, T]` (`0 ≤ T`)
and `f(t) = f(0) + ∫₀ᵗ g(u) du` on `[0, T]`, then for every `s : ℂ`,
`∫₀ᵀ exp (-s t) • g t dt = exp (-s T) • f T - f 0 + s • ∫₀ᵀ exp (-s t) • f t dt`. -/
theorem intervalIntegral_cexp_neg_mul_smul_of_primitive {f g : ℝ → E} (s : ℂ) {T : ℝ}
    (hT : 0 ≤ T) (hg : IntervalIntegrable g volume 0 T)
    (hfg : ∀ t ∈ Icc 0 T, f t = f 0 + ∫ u in (0 : ℝ)..t, g u) :
    ∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • g t =
      Complex.exp (-s * T) • f T - f 0 + s • ∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • f t := by
  have hf_cont : ContinuousOn f (Icc 0 T) := by
    refine (continuousOn_const.add ?_).congr fun t ht ↦ hfg t ht
    simpa only [uIcc_of_le hT] using
      intervalIntegral.continuousOn_primitive_interval' hg left_mem_uIcc
  have hf_int : IntervalIntegrable f volume 0 T := hf_cont.intervalIntegrable_of_Icc hT
  have hg_Ioc : IntegrableOn g (Ioc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hg
  let μT := volume.restrict (Ioc 0 T)
  let K : ℝ → ℝ → E := fun t r ↦ if t < r then (s * Complex.exp (-s * r)) • g t else 0
  have hiter_left :
      ∫ t, (∫ r, K t r ∂μT) ∂μT =
        (∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • g t) -
          Complex.exp (-s * T) • (f T - f 0) := by
    have hinner : ∀ t ∈ Ioc 0 T,
        ∫ r, K t r ∂μT = (Complex.exp (-s * t) - Complex.exp (-s * T)) • g t := by
      intro t ht
      have hsec : EqOn (K t) ((Ioi t).indicator fun r ↦ (s * Complex.exp (-s * r)) • g t)
          (Ioc 0 T) := fun r _ ↦ by simp [K, Set.indicator_apply]
      rw [setIntegral_congr_fun measurableSet_Ioc hsec, setIntegral_indicator measurableSet_Ioi,
        Ioc_inter_Ioi, max_eq_right ht.1.le, integral_smul_const,
        setIntegral_Ioc_mul_cexp_neg_mul s ht.2]
    rw [setIntegral_congr_fun measurableSet_Ioc hinner]
    simp_rw [sub_smul]
    have h1 : IntegrableOn (fun t : ℝ ↦ Complex.exp (-s * t) • g t) (Ioc 0 T) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp
        ((intervalIntegrable_cexp_neg_mul_smul_iff s).mpr hg)
    have h2 : IntegrableOn (fun t : ℝ ↦ Complex.exp (-s * T) • g t) (Ioc 0 T) :=
      hg_Ioc.smul (Complex.exp (-s * T))
    rw [integral_sub h1 h2, ← intervalIntegral.integral_of_le hT, integral_smul,
      ← intervalIntegral.integral_of_le hT, eq_sub_iff_add_eq'.mpr (hfg T ⟨hT, le_rfl⟩).symm]
  have hiter_right :
      ∫ r, (∫ t, K t r ∂μT) ∂μT =
        s • (∫ r in (0 : ℝ)..T, Complex.exp (-s * r) • f r) -
          (1 - Complex.exp (-s * T)) • f 0 := by
    have hinner : ∀ r ∈ Ioc 0 T,
        ∫ t, K t r ∂μT = s • (Complex.exp (-s * r) • f r) -
          (s * Complex.exp (-s * r)) • f 0 := by
      intro r hr
      have hsec : EqOn (fun t ↦ K t r)
          ((Iio r).indicator fun t ↦ (s * Complex.exp (-s * r)) • g t) (Ioc 0 T) :=
        fun t _ ↦ by simp [K, Set.indicator_apply]
      have hsub : Ioc 0 T ∩ Iio r = Ioo 0 r := by
        ext t; simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
        exact ⟨fun ⟨⟨h0, _⟩, htr⟩ ↦ ⟨h0, htr⟩, fun ⟨h0, htr⟩ ↦ ⟨⟨h0, htr.le.trans hr.2⟩, htr⟩⟩
      rw [setIntegral_congr_fun measurableSet_Ioc hsec, setIntegral_indicator measurableSet_Iio,
        hsub, integral_smul, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le hr.1.le,
        eq_sub_iff_add_eq'.mpr (hfg r (Ioc_subset_Icc_self hr)).symm, smul_sub, mul_smul]
    rw [setIntegral_congr_fun measurableSet_Ioc hinner]
    have h1 : IntegrableOn (fun r : ℝ ↦ s • (Complex.exp (-s * r) • f r)) (Ioc 0 T) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp
        ((intervalIntegrable_cexp_neg_mul_smul_iff s).mpr hf_int)).smul s
    have h2 : IntegrableOn (fun r : ℝ ↦ (s * Complex.exp (-s * r)) • f 0) (Ioc 0 T) :=
      ((by fun_prop : Continuous fun r : ℝ ↦ (s * Complex.exp (-s * r)) • f 0).intervalIntegrable
        0 T |> (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp)
    rw [integral_sub h1 h2, integral_smul, ← intervalIntegral.integral_of_le hT,
      integral_smul_const, setIntegral_Ioc_mul_cexp_neg_mul s hT, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero]
  have hswap := integral_integral_swap (integrable_prod_triangle_cexp_smul s hT hg_Ioc)
  rw [hiter_left, hiter_right, sub_eq_iff_eq_add] at hswap
  rw [hswap, smul_sub, sub_smul, one_smul]
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
  have hg_on : IntegrableOn (fun t : ℝ ↦ Complex.exp (-s * t) • g t) (Ioi 0) := hg
  have hbd_tend :
      Tendsto (fun T : ℝ ↦ Complex.exp (-s * T) • f T) atTop (𝓝 (w - s • z + f 0)) := by
    refine (hg_tend.sub (hf_tend.const_smul s) |>.add_const (f 0)).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    have hgT : IntervalIntegrable g volume 0 T :=
      (intervalIntegrable_cexp_neg_mul_smul_iff s).mp
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
          (hg_on.mono_set Ioc_subset_Ioi_self))
    have hid := intervalIntegral_cexp_neg_mul_smul_of_primitive s hT hgT
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
  have hf'_on : IntegrableOn (fun t : ℝ ↦ Complex.exp (-s * t) • f' t) (Ioi 0) := hf'
  refine hasLaplace_deriv_of_primitive (fun t (ht : 0 ≤ t) ↦ ?_) hf hf'
  have hf't : IntervalIntegrable f' volume 0 t :=
    (intervalIntegrable_cexp_neg_mul_smul_iff s).mp
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr
        (hf'_on.mono_set Ioc_subset_Ioi_self))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
    (hf_cont.mono Icc_subset_Ici_self) (fun u hu ↦ hderiv u hu.1) hf't, add_sub_cancel]

end LaplaceDeriv

/-! ### Elementary Laplace transforms -/

section Elementary

/-- For `0 < s.re`, the constant function `v` in a complex Banach space has Laplace transform
`s⁻¹ • v`. -/
theorem hasLaplace_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (v : E) {s : ℂ} (hs : 0 < s.re) :
    HasLaplace (fun _ : ℝ ↦ v) s (s⁻¹ • v) := by
  have hsneg : (-s).re < 0 := by simpa using hs
  refine ⟨(integrableOn_exp_mul_complex_Ioi hsneg 0).smul_const v, ?_⟩
  rw [integral_smul_const, integral_exp_mul_complex_Ioi hsneg 0, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, neg_div_neg_eq, one_div]

/-- For `0 < s.re`, the constant function `1 : ℝ → ℂ` has Laplace transform `s⁻¹ = 1 / s`. -/
theorem hasLaplace_one {s : ℂ} (hs : 0 < s.re) :
    HasLaplace (fun _ : ℝ ↦ (1 : ℂ)) s s⁻¹ := by
  simpa using hasLaplace_const (1 : ℂ) hs

/-- For `s.re ≤ 0`, the constant function `1 : ℝ → ℂ` has no convergent one-sided Laplace
transform, even though the totalized Bochner integral at `s = 0` equals `0`. -/
theorem not_hasLaplace_one_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) (z : ℂ) :
    ¬ HasLaplace (fun _ : ℝ ↦ (1 : ℂ)) s z := by
  rintro ⟨hint, -⟩
  have hnorm : IntegrableOn (fun t : ℝ ↦ Real.exp (-s.re * t)) (Ioi 0) :=
    hint.norm.congr (.of_forall fun t ↦ by simp [Complex.norm_exp, neg_mul])
  have hlt : -s.re < 0 := integrableOn_exp_mul_Ioi_iff.mp hnorm
  linarith

/-- At `s = 0`, `HasLaplace (fun _ ↦ 1) 0 0` is false. -/
theorem not_hasLaplace_one_zero : ¬ HasLaplace (fun _ : ℝ ↦ (1 : ℂ)) 0 0 :=
  not_hasLaplace_one_of_re_nonpos (by simp) 0

/-- For `0 ≤ a` and `0 < s.re`, the indicator of `[a, ∞)` has Laplace transform
`exp (-s * a) / s`. -/
theorem hasLaplace_indicator_Ici_one {a : ℝ} (ha : 0 ≤ a) {s : ℂ} (hs : 0 < s.re) :
    HasLaplace ((Ici a).indicator fun _ ↦ (1 : ℂ)) s (Complex.exp (-s * a) / s) := by
  simpa [div_eq_mul_inv] using (hasLaplace_one hs).indicator_Ici_sub ha

/-- For `w.re < s.re`, `t ↦ exp (w * t)` has Laplace transform `(s - w)⁻¹`. -/
theorem hasLaplace_cexp_mul {w s : ℂ} (hws : w.re < s.re) :
    HasLaplace (fun t : ℝ ↦ Complex.exp (w * t)) s (s - w)⁻¹ := by
  have hs : 0 < (s - w).re := by
    rw [Complex.sub_re]
    linarith
  simpa using (hasLaplace_one hs).cexp_mul_smul

/-- For `0 < s.re` and `k : ℕ`, `t ↦ (t : ℂ) ^ k` has Laplace transform `k! / s ^ (k + 1)`. -/
theorem hasLaplace_pow (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasLaplace (fun t : ℝ ↦ (t : ℂ) ^ k) s ((k.factorial : ℂ) / s ^ (k + 1)) := by
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs
  induction k with
  | zero =>
    simpa [Nat.factorial_zero, pow_zero, pow_one, one_div] using hasLaplace_one hs
  | succ k ih =>
    let f : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (k + 1)
    let f' : ℝ → ℂ := fun t ↦ ((k + 1 : ℕ) : ℂ) * (t : ℂ) ^ k
    have hint : Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) (volume.restrict (Ioi 0)) := by
      refine (integrableOn_pow_mul_exp_neg_mul_Ioi (k + 1) hs).mono'
        (Measurable.aestronglyMeasurable (by fun_prop)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
      rw [norm_smul, Complex.norm_exp, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le,
        Complex.re_mul_ofReal, Complex.neg_re, neg_mul, mul_comm]
    set z' : ℂ := ∫ t in Ioi (0 : ℝ), Complex.exp (-s * t) • f t
    have hz' : HasLaplace f s z' := ⟨hint, rfl⟩
    have ih' : HasLaplace f' s (((k + 1 : ℕ) : ℂ) * ((k.factorial : ℂ) / s ^ (k + 1))) :=
      ih.fun_const_smul ((k + 1 : ℕ) : ℂ)
    have hder : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t := by
      intro t _
      simpa [f, f', add_sub_cancel_right] using (hasDerivAt_pow (k + 1) t).ofReal_comp
    have hstep := hasLaplace_deriv (by fun_prop : Continuous f).continuousWithinAt hder hz' ih'.1
    have heq : s * z' - f 0 = ((k + 1 : ℕ) : ℂ) * ((k.factorial : ℂ) / s ^ (k + 1)) :=
      hstep.unique ih'
    have hf0 : f 0 = 0 := by simp [f]
    have hz'_eq : z' = (((k + 1).factorial : ℂ) / s ^ (k + 2)) := by
      rw [hf0, sub_zero] at heq
      rw [Nat.factorial_succ, Nat.cast_mul, eq_div_iff (pow_ne_zero (k + 2) hs0)]
      have hmul : s * z' * s ^ (k + 1) = ((k + 1 : ℕ) : ℂ) * (k.factorial : ℂ) := by
        rw [heq, mul_assoc, div_mul_cancel₀ _ (pow_ne_zero (k + 1) hs0)]
      linear_combination hmul
    exact hz'_eq ▸ hz'

/-- For `w.re < s.re` and `k : ℕ`, `t ↦ exp (w * t) * (t : ℂ) ^ k` has Laplace transform
`k! / (s - w) ^ (k + 1)`. -/
theorem hasLaplace_cexp_mul_pow (k : ℕ) {w s : ℂ} (hws : w.re < s.re) :
    HasLaplace (fun t : ℝ ↦ Complex.exp (w * t) * (t : ℂ) ^ k) s
      ((k.factorial : ℂ) / (s - w) ^ (k + 1)) := by
  have hs : 0 < (s - w).re := by
    rw [Complex.sub_re]
    linarith
  exact (hasLaplace_pow k hs).cexp_mul_smul

/-- For `a < s.re` and `k : ℕ`, the real damped monomial `t ↦ exp (a * t) * t ^ k` (cast to `ℂ`)
has Laplace transform `k! / (s - a) ^ (k + 1)`. -/
theorem hasLaplace_exp_mul_pow (k : ℕ) {a : ℝ} {s : ℂ} (has : a < s.re) :
    HasLaplace (fun t : ℝ ↦ ((Real.exp (a * t) * t ^ k : ℝ) : ℂ)) s
      ((k.factorial : ℂ) / (s - a) ^ (k + 1)) := by
  refine (hasLaplace_cexp_mul_pow k (w := (a : ℂ)) (by simpa using has)).congr_ae ?_
  exact .of_forall fun t ↦ by simp [Complex.ofReal_exp]

end Elementary

end TauCeti
