/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.ExpDecay
import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate
import TauCeti.MeasureTheory.Integral.Exp.Decay
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# The one-sided Laplace transform

This file defines the ordinary one-sided Laplace transform of a vector-valued function on `ℝ` at a
complex parameter `s : ℂ`, bundling Bochner integrability with the value of the integral so that
totalised junk values cannot satisfy the transform predicate:

* `TauCeti.LaplaceConvergent f s μ`: `t ↦ exp (-s * t) • f t` is integrable with respect to `μ`
  (defaulting to Lebesgue measure restricted to `(0, ∞)`);
* `TauCeti.laplace f s μ`: the Bochner integral `∫ t, exp (-s * t) • f t ∂μ`;
* `TauCeti.HasLaplace f s z μ`: `LaplaceConvergent f s μ` holds and `laplace f s μ = z`.

Because `{0}` has Lebesgue measure zero, restricting to `[0, ∞)` produces the same convergence
predicate and transform as `(0, ∞)` (`laplaceConvergent_restrict_Ici_iff`, `laplace_restrict_Ici`,
`hasLaplace_restrict_Ici_iff`).

## Main results

* Algebraic and geometric calculus: uniqueness (`HasLaplace.unique`), almost-everywhere and
  `(0, ∞)` congruence (`HasLaplace.congr_ae`, `hasLaplace_congr`), linearity (`hasLaplace_zero`,
  `HasLaplace.add`, `HasLaplace.neg`, `HasLaplace.sub`, `HasLaplace.const_smul`), frequency
  translation (`hasLaplace_cexp_smul`, `laplaceConvergent_exp_smul`, `laplace_exp_smul`,
  `hasLaplace_exp_smul`), and positive time dilation (`HasLaplace.comp_mul_left`).
* Half-plane convergence and parameter differentiation: convergence at `s₀` propagates to every `s`
  with `s₀.re ≤ s.re` (`LaplaceConvergent.of_re_le_re`), exponential growth `O(exp (a * t))` gives
  convergence on `a < s.re` (`laplaceConvergent_of_isBigO_exp`), on the open half-plane
  `s₀.re < s.re` the transform is complex-differentiable with derivative equal to the transform of
  `t ↦ -(t : ℂ) • f t` (`LaplaceConvergent.hasDerivAt_laplace`,
  `LaplaceConvergent.differentiableOn_laplace`), and locally around any `s` where `F` represents
  the Laplace transform of `f`, `t ↦ -(t : ℂ) • f t` has Laplace transform `deriv F s`
  (`hasLaplace_neg_smul_deriv`).
* Transform of a derivative (`hasLaplace_deriv_of_primitive`, `hasLaplace_deriv`): in a complex
  Banach space, if `f` is a primitive of `g` on `[0, ∞)` (or right-continuous at `0` with derivative
  `f'` on `(0, ∞)`), `HasLaplace f s z`, and `t ↦ exp (-s * t) • g t` is integrable on `(0, ∞)`,
  then `HasLaplace g s (s • z - f 0)` with no restriction on `s.re` and no auxiliary growth bound;
  vanishing of the boundary term `exp (-s * T) • f T` at `+∞` is derived from integrability
  (`tendsto_cexp_neg_mul_smul_atTop_zero_of_primitive`).
* Explicit transforms: constants (`laplaceConvergent_const_iff`, `hasLaplace_const`,
  `hasLaplace_one`, and non-convergence on `s.re ≤ 0` via `not_hasLaplace_const_of_re_nonpos`),
  exponentials (`hasLaplace_cexp`), and monomials and exponentially weighted monomials
  (`hasLaplace_pow`, `hasLaplace_cexp_mul_pow`, `hasLaplace_exp_mul_pow`).

## References

* D. Osele, `Mathlib/Analysis/LaplaceTransform.lean` in
  [dennj/mathlib4](https://github.com/dennj/mathlib4/blob/90482cd37e85e423459de2ed103cea2f4d98cb20/Mathlib/Analysis/LaplaceTransform.lean)
  ([mathlib4#40582](https://github.com/leanprover-community/mathlib4/pull/40582)) at commit
  `90482cd37e85e423459de2ed103cea2f4d98cb20`, declarations `LaplaceConvergent`, `laplace`, and
  `HasLaplace`, for the argument order, default measure, and scalar-action hypotheses of the
  transform predicate.
* H. Delange, *Généralisation du théorème de Ikehara*, Ann. Sci. École Norm. Sup. (3) **71**
  (1954), 213–242, p. 213 and §3.3.1, pp. 221–222, for the ordinary one-sided Laplace integral
  formulation.
* J. Lebl, *Notes on Diffy Qs*, version 6.11 (2026), §6.2.1, p. 300 and Table 6.2, for the rule
  `ℒ{g'}(s) = s ℒ{g}(s) - g(0)` under exponential order (generalized here to complex Banach spaces
  under integrability of the two transforms alone).
-/

public section

noncomputable section

open Filter MeasureTheory Set Asymptotics Metric
open scoped Topology Interval

namespace TauCeti

/-! ### Definitions and characteristic API -/

section Defs

/-- `LaplaceConvergent f s μ`: the Laplace integrand `t ↦ exp (-s * t) • f t` is Bochner integrable
with respect to `μ`. With the default measure `volume.restrict (Ioi 0)`, this asserts absolute
convergence of the one-sided Laplace integral `∫₀^∞ exp (-s * t) • f t dt`, following D. Osele,
`Mathlib/Analysis/LaplaceTransform.lean` in `dennj/mathlib4` (`mathlib4#40582`),
`LaplaceConvergent`. -/
def LaplaceConvergent {E : Type*} [NormedAddCommGroup E] [SMul ℂ E]
    (f : ℝ → E) (s : ℂ) (μ : Measure ℝ := volume.restrict (Ioi 0)) : Prop :=
  Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ

/-- Unfolding characterization of `LaplaceConvergent`. -/
theorem laplaceConvergent_def {E : Type*} [NormedAddCommGroup E] [SMul ℂ E]
    {f : ℝ → E} {s : ℂ} {μ : Measure ℝ} :
    LaplaceConvergent f s μ ↔ Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ :=
  Iff.rfl

/-- `LaplaceConvergent` gives Bochner integrability of `t ↦ exp (-s * t) • f t`. -/
theorem LaplaceConvergent.integrable {E : Type*} [NormedAddCommGroup E] [SMul ℂ E]
    {f : ℝ → E} {s : ℂ} {μ : Measure ℝ} (h : LaplaceConvergent f s μ) :
    Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ :=
  h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SMul ℂ E]

/-- The Laplace transform `∫ t, exp (-s * t) • f t ∂μ`, defaulting to `μ = volume.restrict (Ioi 0)`,
following D. Osele, `Mathlib/Analysis/LaplaceTransform.lean` in `dennj/mathlib4`
(`mathlib4#40582`), `laplace`. -/
def laplace (f : ℝ → E) (s : ℂ) (μ : Measure ℝ := volume.restrict (Ioi 0)) : E :=
  ∫ t : ℝ, Complex.exp (-s * t) • f t ∂μ

/-- Unfolding characterization of `laplace`. -/
theorem laplace_def (f : ℝ → E) (s : ℂ) (μ : Measure ℝ := volume.restrict (Ioi 0)) :
    laplace f s μ = ∫ t : ℝ, Complex.exp (-s * t) • f t ∂μ :=
  (rfl)

/-- When `f` is not Laplace-convergent at `s`, the totalised `laplace` integral vanishes. -/
@[grind →]
theorem laplace_of_not_laplaceConvergent {f : ℝ → E} {s : ℂ} {μ : Measure ℝ}
    (h : ¬ LaplaceConvergent f s μ) : laplace f s μ = 0 :=
  integral_undef h

/-- `HasLaplace f s z μ`: the integrand `t ↦ exp (-s * t) • f t` is integrable for `μ` and its
Bochner integral equals `z`. With the default measure `volume.restrict (Ioi 0)` this is the
ordinary one-sided Laplace transform of `f` at `s : ℂ`, following D. Osele,
`Mathlib/Analysis/LaplaceTransform.lean` in `dennj/mathlib4` (`mathlib4#40582`), `HasLaplace`. -/
def HasLaplace (f : ℝ → E) (s : ℂ) (z : E) (μ : Measure ℝ := volume.restrict (Ioi 0)) : Prop :=
  Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ ∧
    ∫ t : ℝ, Complex.exp (-s * t) • f t ∂μ = z

/-- Unfolding characterization of `HasLaplace` in terms of `Integrable` and the Bochner integral. -/
theorem hasLaplace_def {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ} :
    HasLaplace f s z μ ↔
      Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ ∧
        ∫ t : ℝ, Complex.exp (-s * t) • f t ∂μ = z :=
  Iff.rfl

/-- Characterization of `HasLaplace` in terms of `LaplaceConvergent` and `laplace`. -/
@[grind =]
theorem hasLaplace_iff {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ} :
    HasLaplace f s z μ ↔ LaplaceConvergent f s μ ∧ laplace f s μ = z :=
  Iff.rfl

/-- `HasLaplace` implies Bochner integrability of `t ↦ exp (-s * t) • f t`. -/
theorem HasLaplace.integrable {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (h : HasLaplace f s z μ) : Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ :=
  h.1

/-- `HasLaplace` implies `LaplaceConvergent`. -/
theorem HasLaplace.laplaceConvergent {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (h : HasLaplace f s z μ) : LaplaceConvergent f s μ :=
  h.1

/-- `HasLaplace` identifies the Bochner integral `∫ t, exp (-s * t) • f t ∂μ`. -/
theorem HasLaplace.integral_eq {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (h : HasLaplace f s z μ) : ∫ t : ℝ, Complex.exp (-s * t) • f t ∂μ = z :=
  h.2

/-- `HasLaplace` identifies `laplace f s μ`. -/
theorem HasLaplace.laplace_eq {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (h : HasLaplace f s z μ) : laplace f s μ = z :=
  h.2

/-- A Laplace-convergent function has Laplace transform `laplace f s μ`. -/
theorem LaplaceConvergent.hasLaplace {f : ℝ → E} {s : ℂ} {μ : Measure ℝ}
    (h : LaplaceConvergent f s μ) : HasLaplace f s (laplace f s μ) μ :=
  ⟨h, rfl⟩

/-- The Laplace transform of `f` at `s` with respect to `μ` is unique. -/
theorem HasLaplace.unique {f : ℝ → E} {s : ℂ} {z z' : E} {μ : Measure ℝ}
    (h₁ : HasLaplace f s z μ) (h₂ : HasLaplace f s z' μ) : z = z' :=
  h₁.integral_eq.symm.trans h₂.integral_eq

end Defs

/-! ### Congruence and half-line endpoint invariance -/

section Congr

/-- `LaplaceConvergent` is preserved by almost-everywhere equality. -/
theorem LaplaceConvergent.congr_ae {E : Type*} [NormedAddCommGroup E] [SMul ℂ E]
    {f g : ℝ → E} {s : ℂ} {μ : Measure ℝ} (h : LaplaceConvergent f s μ) (hfg : f =ᵐ[μ] g) :
    LaplaceConvergent g s μ :=
  h.congr (hfg.mono fun t ht ↦ by simp only [ht])

/-- Almost-everywhere equal functions have the same Laplace convergence. -/
theorem laplaceConvergent_congr_ae {E : Type*} [NormedAddCommGroup E] [SMul ℂ E]
    {f g : ℝ → E} {s : ℂ} {μ : Measure ℝ} (hfg : f =ᵐ[μ] g) :
    LaplaceConvergent f s μ ↔ LaplaceConvergent g s μ :=
  ⟨fun h ↦ h.congr_ae hfg, fun h ↦ h.congr_ae hfg.symm⟩

/-- Functions agreeing on `(0, ∞)` have the same one-sided Laplace convergence. -/
theorem laplaceConvergent_congr {E : Type*} [NormedAddCommGroup E] [SMul ℂ E]
    {f g : ℝ → E} (hfg : EqOn f g (Ioi 0)) {s : ℂ} :
    LaplaceConvergent f s ↔ LaplaceConvergent g s :=
  laplaceConvergent_congr_ae (ae_restrict_of_forall_mem measurableSet_Ioi hfg)

/-- Because `{0}` is null for Lebesgue measure, restricting to `[0, ∞)` gives the same
`LaplaceConvergent` predicate as restricting to `(0, ∞)`. -/
@[simp, grind =]
theorem laplaceConvergent_restrict_Ici_iff {E : Type*} [NormedAddCommGroup E] [SMul ℂ E]
    {f : ℝ → E} {s : ℂ} :
    LaplaceConvergent f s (volume.restrict (Ici 0)) ↔ LaplaceConvergent f s :=
  integrableOn_Ici_iff_integrableOn_Ioi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SMul ℂ E]

/-- Almost-everywhere equal functions have equal Laplace integrals. -/
theorem laplace_congr_ae {f g : ℝ → E} {s : ℂ} {μ : Measure ℝ} (hfg : f =ᵐ[μ] g) :
    laplace f s μ = laplace g s μ :=
  integral_congr_ae (hfg.mono fun t ht ↦ by simp only [ht])

/-- Functions agreeing on `(0, ∞)` have equal one-sided Laplace integrals. -/
theorem laplace_congr {f g : ℝ → E} (hfg : EqOn f g (Ioi 0)) (s : ℂ) :
    laplace f s = laplace g s :=
  laplace_congr_ae (ae_restrict_of_forall_mem measurableSet_Ioi hfg)

/-- Restricting Lebesgue measure to `[0, ∞)` gives the same `laplace` value as `(0, ∞)`. -/
@[simp, grind =]
theorem laplace_restrict_Ici (f : ℝ → E) (s : ℂ) :
    laplace f s (volume.restrict (Ici 0)) = laplace f s :=
  integral_Ici_eq_integral_Ioi

/-- `HasLaplace` is preserved by almost-everywhere equality. -/
theorem HasLaplace.congr_ae {f g : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (h : HasLaplace f s z μ) (hfg : f =ᵐ[μ] g) : HasLaplace g s z μ :=
  ⟨h.laplaceConvergent.congr_ae hfg, (laplace_congr_ae hfg.symm).trans h.laplace_eq⟩

/-- Almost-everywhere equal functions satisfy the same `HasLaplace` predicate. -/
theorem hasLaplace_congr_ae {f g : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ} (hfg : f =ᵐ[μ] g) :
    HasLaplace f s z μ ↔ HasLaplace g s z μ :=
  ⟨fun h ↦ h.congr_ae hfg, fun h ↦ h.congr_ae hfg.symm⟩

/-- Functions agreeing on `(0, ∞)` satisfy the same one-sided `HasLaplace` predicate. -/
theorem hasLaplace_congr {f g : ℝ → E} (hfg : EqOn f g (Ioi 0)) {s : ℂ} {z : E} :
    HasLaplace f s z ↔ HasLaplace g s z :=
  hasLaplace_congr_ae (ae_restrict_of_forall_mem measurableSet_Ioi hfg)

/-- Restricting Lebesgue measure to `[0, ∞)` gives the same `HasLaplace` predicate as `(0, ∞)`. -/
@[simp, grind =]
theorem hasLaplace_restrict_Ici_iff {f : ℝ → E} {s : ℂ} {z : E} :
    HasLaplace f s z (volume.restrict (Ici 0)) ↔ HasLaplace f s z := by
  rw [hasLaplace_iff, hasLaplace_iff, laplaceConvergent_restrict_Ici_iff, laplace_restrict_Ici]

end Congr

/-! ### Linearity, frequency shifts, and positive dilation -/

section Zero

/-- When the `ℂ`-action preserves zero, the zero function is Laplace-convergent everywhere. -/
@[to_fun (attr := simp, grind .) laplaceConvergent_fun_zero]
theorem laplaceConvergent_zero {E : Type*} [NormedAddCommGroup E] [SMulZeroClass ℂ E]
    (s : ℂ) (μ : Measure ℝ := volume.restrict (Ioi 0)) :
    LaplaceConvergent (0 : ℝ → E) s μ := by
  simp [LaplaceConvergent]

/-- When the `ℂ`-action preserves zero, the Laplace integral of `0` is `0`. -/
@[to_fun (attr := simp, grind =) laplace_fun_zero]
theorem laplace_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SMulZeroClass ℂ E]
    (s : ℂ) (μ : Measure ℝ := volume.restrict (Ioi 0)) :
    laplace (0 : ℝ → E) s μ = 0 := by
  simp [laplace]

/-- When the `ℂ`-action preserves zero, the zero function has Laplace transform `0` at every `s`
and for every measure `μ`. -/
@[to_fun (attr := simp, grind .) hasLaplace_fun_zero]
theorem hasLaplace_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SMulZeroClass ℂ E]
    (s : ℂ) (μ : Measure ℝ := volume.restrict (Ioi 0)) :
    HasLaplace (0 : ℝ → E) s 0 μ :=
  ⟨laplaceConvergent_zero s μ, laplace_zero s μ⟩

end Zero

section Add

/-- Sum of two Laplace-convergent functions. -/
@[to_fun]
theorem LaplaceConvergent.add {E : Type*} [NormedAddCommGroup E] [DistribSMul ℂ E]
    {f g : ℝ → E} {s : ℂ} {μ : Measure ℝ}
    (hf : LaplaceConvergent f s μ) (hg : LaplaceConvergent g s μ) :
    LaplaceConvergent (f + g) s μ := by
  simpa only [LaplaceConvergent, Pi.add_apply, smul_add] using hf.integrable.fun_add hg.integrable

/-- Negation of a Laplace-convergent function. -/
@[to_fun]
theorem LaplaceConvergent.neg {E : Type*} [NormedAddCommGroup E] [DistribSMul ℂ E]
    {f : ℝ → E} {s : ℂ} {μ : Measure ℝ} (hf : LaplaceConvergent f s μ) :
    LaplaceConvergent (-f) s μ := by
  simpa only [LaplaceConvergent, Pi.neg_apply, smul_neg] using hf.integrable.fun_neg

/-- Negating a function preserves `LaplaceConvergent`. -/
-- `@[grind =]` applies only to the point-free `-f` form; Lean's `grind` rejects lambda patterns
-- binding `f` under `fun t ↦ -f t`.
@[grind =, to_fun (attr := simp) laplaceConvergent_fun_neg_iff]
theorem laplaceConvergent_neg_iff {E : Type*} [NormedAddCommGroup E] [DistribSMul ℂ E]
    {f : ℝ → E} {s : ℂ} {μ : Measure ℝ} :
    LaplaceConvergent (-f) s μ ↔ LaplaceConvergent f s μ :=
  ⟨fun h ↦ by simpa only [neg_neg] using h.neg, LaplaceConvergent.neg⟩

/-- Difference of two Laplace-convergent functions. -/
@[to_fun]
theorem LaplaceConvergent.sub {E : Type*} [NormedAddCommGroup E] [DistribSMul ℂ E]
    {f g : ℝ → E} {s : ℂ} {μ : Measure ℝ}
    (hf : LaplaceConvergent f s μ) (hg : LaplaceConvergent g s μ) :
    LaplaceConvergent (f - g) s μ := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DistribSMul ℂ E]

/-- Additivity of `laplace` on Laplace-convergent functions. -/
@[to_fun laplace_fun_add]
theorem laplace_add {f g : ℝ → E} {s : ℂ} {μ : Measure ℝ}
    (hf : LaplaceConvergent f s μ) (hg : LaplaceConvergent g s μ) :
    laplace (f + g) s μ = laplace f s μ + laplace g s μ := by
  simpa only [laplace, Pi.add_apply, smul_add] using integral_add hf.integrable hg.integrable

/-- Negation commutes with `laplace`. -/
@[grind =, to_fun (attr := simp) laplace_fun_neg]
theorem laplace_neg (f : ℝ → E) (s : ℂ) {μ : Measure ℝ} :
    laplace (-f) s μ = -laplace f s μ := by
  simp only [laplace, Pi.neg_apply, smul_neg, integral_neg]

/-- Subtraction of `laplace` on Laplace-convergent functions. -/
@[to_fun laplace_fun_sub]
theorem laplace_sub {f g : ℝ → E} {s : ℂ} {μ : Measure ℝ}
    (hf : LaplaceConvergent f s μ) (hg : LaplaceConvergent g s μ) :
    laplace (f - g) s μ = laplace f s μ - laplace g s μ := by
  simpa only [laplace, Pi.sub_apply, smul_sub] using integral_sub hf.integrable hg.integrable

/-- Additivity of `HasLaplace` under `DistribSMul ℂ E`. -/
@[to_fun]
theorem HasLaplace.add {f g : ℝ → E} {s : ℂ} {z w : E} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) (hg : HasLaplace g s w μ) :
    HasLaplace (f + g) s (z + w) μ := by
  rw [hasLaplace_iff]
  exact ⟨hf.laplaceConvergent.add hg.laplaceConvergent,
    by rw [laplace_add hf.laplaceConvergent hg.laplaceConvergent, hf.laplace_eq, hg.laplace_eq]⟩

/-- Negation of `HasLaplace` under `DistribSMul ℂ E`. -/
@[to_fun]
theorem HasLaplace.neg {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) : HasLaplace (-f) s (-z) μ := by
  rw [hasLaplace_iff]
  exact ⟨hf.laplaceConvergent.neg, by rw [laplace_neg, hf.laplace_eq]⟩

/-- Subtraction of `HasLaplace` under `DistribSMul ℂ E`. -/
@[to_fun]
theorem HasLaplace.sub {f g : ℝ → E} {s : ℂ} {z w : E} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) (hg : HasLaplace g s w μ) :
    HasLaplace (f - g) s (z - w) μ := by
  rw [hasLaplace_iff]
  exact ⟨hf.laplaceConvergent.sub hg.laplaceConvergent,
    by rw [laplace_sub hf.laplaceConvergent hg.laplaceConvergent, hf.laplace_eq, hg.laplace_eq]⟩

end Add

section SMulAndShift

/-- Scalar multiplication by a constant `c : 𝕜` commuting with the `ℂ`-action preserves
`LaplaceConvergent`. -/
@[to_fun]
theorem LaplaceConvergent.const_smul {E 𝕜 : Type*} [NormedAddCommGroup E] [SMul ℂ E]
    [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 E] [IsBoundedSMul 𝕜 E] [SMulCommClass 𝕜 ℂ E]
    {f : ℝ → E} {s : ℂ} {μ : Measure ℝ} (hf : LaplaceConvergent f s μ) (c : 𝕜) :
    LaplaceConvergent (c • f) s μ := by
  simpa only [LaplaceConvergent, Pi.smul_apply, smul_comm c] using hf.integrable.fun_smul c

/-- Scalar multiplication by a constant `c : 𝕜` commuting with `ℝ` and `ℂ` commutes with
`laplace`. -/
@[to_fun laplace_fun_const_smul]
theorem laplace_const_smul {E 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SMul ℂ E]
    [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E] [SMulCommClass ℝ 𝕜 E]
    [SMulCommClass 𝕜 ℂ E] (f : ℝ → E) (s : ℂ) (c : 𝕜) {μ : Measure ℝ} :
    laplace (c • f) s μ = c • laplace f s μ := by
  simp only [laplace, Pi.smul_apply, ← smul_comm c, integral_smul]

/-- Scalar multiplication by a constant `c : 𝕜` commuting with `ℝ` and `ℂ` scales `HasLaplace`
by `c`. -/
@[to_fun]
theorem HasLaplace.const_smul {E 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SMul ℂ E]
    [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [SMulCommClass ℝ 𝕜 E]
    [SMulCommClass 𝕜 ℂ E] {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) (c : 𝕜) :
    HasLaplace (c • f) s (c • z) μ := by
  refine ⟨hf.laplaceConvergent.const_smul c, ?_⟩
  simpa only [Pi.smul_apply, ← smul_comm c, hf.integral_eq] using hf.integrable.integral_smul c

/-- Multiplying `f` by `t ↦ exp (w * t)` shifts the Laplace parameter from `s` to `s - w`. -/
theorem laplaceConvergent_cexp_smul {E : Type*} [NormedAddCommGroup E] [MulAction ℂ E]
    {f : ℝ → E} (w : ℂ) {s : ℂ} {μ : Measure ℝ} :
    LaplaceConvergent (fun t : ℝ ↦ Complex.exp (w * t) • f t) s μ ↔
      LaplaceConvergent f (s - w) μ := by
  refine integrable_congr (.of_forall fun t ↦ ?_)
  dsimp only
  rw [smul_smul, ← Complex.exp_add]
  congr 2
  ring

/-- Multiplying `f` by `t ↦ exp (w * t)` shifts `laplace` from `s` to `s - w`. -/
theorem laplace_cexp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MulAction ℂ E]
    (f : ℝ → E) (w s : ℂ) {μ : Measure ℝ} :
    laplace (fun t : ℝ ↦ Complex.exp (w * t) • f t) s μ = laplace f (s - w) μ := by
  refine integral_congr_ae (.of_forall fun t ↦ ?_)
  dsimp only
  rw [smul_smul, ← Complex.exp_add]
  congr 2
  ring

/-- Multiplying `f` by `t ↦ exp (w * t)` shifts `HasLaplace` from `s` to `s - w`. -/
theorem hasLaplace_cexp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MulAction ℂ E]
    {f : ℝ → E} (w : ℂ) {s : ℂ} {z : E} {μ : Measure ℝ} :
    HasLaplace (fun t : ℝ ↦ Complex.exp (w * t) • f t) s z μ ↔ HasLaplace f (s - w) z μ := by
  rw [hasLaplace_iff, hasLaplace_iff, laplaceConvergent_cexp_smul, laplace_cexp_smul]

/-- Multiplying `f` by a real exponential `t ↦ Real.exp (a * t)` shifts `LaplaceConvergent` from
`s` to `s - a`. -/
theorem laplaceConvergent_exp_smul {E : Type*} [NormedAddCommGroup E] [SMul ℝ E] [MulAction ℂ E]
    [IsScalarTower ℝ ℂ E] {f : ℝ → E} (a : ℝ) {s : ℂ} {μ : Measure ℝ} :
    LaplaceConvergent (fun t : ℝ ↦ Real.exp (a * t) • f t) s μ ↔
      LaplaceConvergent f (s - a) μ := by
  rw [← laplaceConvergent_cexp_smul (a : ℂ)]
  refine laplaceConvergent_congr_ae (.of_forall fun t ↦ ?_)
  dsimp only
  rw [← smul_one_smul ℂ (Real.exp (a * t)) (f t), Complex.real_smul, mul_one,
    Complex.ofReal_exp, Complex.ofReal_mul]

/-- Multiplying `f` by a real exponential `t ↦ Real.exp (a * t)` shifts `laplace` from `s` to
`s - a`. -/
theorem laplace_exp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MulAction ℂ E]
    [IsScalarTower ℝ ℂ E] (f : ℝ → E) (a : ℝ) (s : ℂ) {μ : Measure ℝ} :
    laplace (fun t : ℝ ↦ Real.exp (a * t) • f t) s μ = laplace f (s - a) μ := by
  rw [← laplace_cexp_smul f (a : ℂ) s]
  refine laplace_congr_ae (.of_forall fun t ↦ ?_)
  dsimp only
  rw [← smul_one_smul ℂ (Real.exp (a * t)) (f t), Complex.real_smul, mul_one,
    Complex.ofReal_exp, Complex.ofReal_mul]

/-- Multiplying `f` by a real exponential `t ↦ Real.exp (a * t)` shifts `HasLaplace` from `s` to
`s - a`. -/
theorem hasLaplace_exp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MulAction ℂ E]
    [IsScalarTower ℝ ℂ E] {f : ℝ → E} (a : ℝ) {s : ℂ} {z : E} {μ : Measure ℝ} :
    HasLaplace (fun t : ℝ ↦ Real.exp (a * t) • f t) s z μ ↔ HasLaplace f (s - a) z μ := by
  rw [hasLaplace_iff, hasLaplace_iff, laplaceConvergent_exp_smul, laplace_exp_smul]

/-- Positive time dilation `t ↦ f (c * t)` preserves `LaplaceConvergent` with rescaled parameter
`s / c`. -/
theorem laplaceConvergent_comp_mul_left {E : Type*} [NormedAddCommGroup E] [SMul ℂ E]
    {f : ℝ → E} {s : ℂ} {c : ℝ} (hc : 0 < c) :
    LaplaceConvergent (fun t ↦ f (c * t)) s ↔ LaplaceConvergent f (s / c) := by
  have hc₀ : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have h := integrableOn_Ioi_comp_mul_left_iff
    (fun u : ℝ ↦ Complex.exp (-(s / c) * u) • f u) 0 hc
  rw [mul_zero] at h
  refine (integrable_congr (.of_forall fun t ↦ ?_)).trans h
  dsimp only
  congr 2
  rw [Complex.ofReal_mul]
  field_simp

/-- Positive time dilation `t ↦ f (c * t)` rescales `laplace` on `(0, ∞)` by `c⁻¹` at `s / c`. -/
theorem laplace_comp_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SMul ℂ E]
    (f : ℝ → E) (s : ℂ) {c : ℝ} (hc : 0 < c) :
    laplace (fun t ↦ f (c * t)) s = c⁻¹ • laplace f (s / c) := by
  have hc₀ : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  let g : ℝ → E := fun u ↦ Complex.exp (-(s / c) * u) • f u
  have heq : (fun t : ℝ ↦ Complex.exp (-s * t) • f (c * t)) = fun t : ℝ ↦ g (c * t) := by
    ext t
    simp only [g]
    congr 2
    rw [Complex.ofReal_mul]
    field_simp
  simpa only [laplace, g, mul_zero] using
    (congrArg (fun h ↦ ∫ t in Ioi (0 : ℝ), h t) heq).trans (integral_comp_mul_left_Ioi g 0 hc)

/-- Positive time dilation of `HasLaplace`: for `0 < c`, if `f` has Laplace transform `z` at
`s / c`, then `t ↦ f (c * t)` has Laplace transform `(c : ℂ)⁻¹ • z` at `s`. -/
theorem HasLaplace.comp_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MulAction ℂ E] [IsScalarTower ℝ ℂ E] {f : ℝ → E} {s : ℂ} {z : E} {c : ℝ} (hc : 0 < c)
    (hf : HasLaplace f (s / c) z) :
    HasLaplace (fun t ↦ f (c * t)) s ((c : ℂ)⁻¹ • z) := by
  rw [hasLaplace_iff, laplaceConvergent_comp_mul_left hc, laplace_comp_mul_left f s hc]
  refine ⟨hf.laplaceConvergent, ?_⟩
  rw [hf.laplace_eq, ← smul_one_smul ℂ c⁻¹ z, Complex.real_smul, mul_one, Complex.ofReal_inv]

end SMulAndShift

/-! ### Half-plane convergence, local integrability, and parameter differentiation -/

section HalfPlane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Multiplying by `t ↦ exp (-s * t)` preserves almost-everywhere strong measurability. -/
theorem aestronglyMeasurable_cexp_neg_mul_smul_iff {f : ℝ → E} {μ : Measure ℝ} (s : ℂ) :
    AEStronglyMeasurable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ ↔
      AEStronglyMeasurable f μ :=
  aestronglyMeasurable_fun_smul_iff₀
    (by fun_prop : Continuous fun t : ℝ ↦ Complex.exp (-s * t)).aestronglyMeasurable
    (ae_of_all _ fun _ ↦ Complex.exp_ne_zero _)

/-- Multiplying by `t ↦ exp (-s * t)` preserves interval integrability on every finite interval. -/
theorem intervalIntegrable_cexp_neg_mul_smul_iff {f : ℝ → E} {μ : Measure ℝ} {a b : ℝ} (s : ℂ) :
    IntervalIntegrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ a b ↔
      IntervalIntegrable f μ a b := by
  refine ⟨fun h ↦ ?_, fun h ↦
    h.continuousOn_smul (by fun_prop : Continuous fun t : ℝ ↦ Complex.exp (-s * t)).continuousOn⟩
  have h' :=
    h.continuousOn_smul (by fun_prop : Continuous fun t : ℝ ↦ Complex.exp (s * t)).continuousOn
  refine h'.congr fun t _ ↦ ?_
  simp [smul_smul, ← Complex.exp_add]

/-- If `f` is Laplace-convergent at `s`, then `f` is interval integrable between any two
nonnegative endpoints. -/
theorem LaplaceConvergent.intervalIntegrable {f : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent f s) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable f volume a b := by
  rw [← intervalIntegrable_cexp_neg_mul_smul_iff s, intervalIntegrable_iff]
  refine IntegrableOn.mono_set hf.integrable fun t ht ↦ ?_
  rw [mem_uIoc] at ht
  rcases ht with ⟨ht₁, _⟩ | ⟨ht₁, _⟩ <;> exact mem_Ioi.mpr (by linarith)

/-- Monotonicity of `LaplaceConvergent` in `Re s`: if `f` is Laplace-convergent at `s₀`, then `f`
is Laplace-convergent at every `s` with `s₀.re ≤ s.re`. -/
theorem LaplaceConvergent.of_re_le_re {f : ℝ → E} {s₀ s : ℂ}
    (hf : LaplaceConvergent f s₀) (hs : s₀.re ≤ s.re) : LaplaceConvergent f s := by
  have hmeas : AEStronglyMeasurable f (volume.restrict (Ioi 0)) :=
    (aestronglyMeasurable_cexp_neg_mul_smul_iff s₀).mp hf.integrable.aestronglyMeasurable
  refine hf.integrable.mono
    ((aestronglyMeasurable_cexp_neg_mul_smul_iff s).mpr hmeas)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_)
  simp only [norm_smul, Complex.norm_exp, Complex.re_mul_ofReal, Complex.neg_re]
  gcongr

/-- A function locally integrable on `[0, ∞)` of exponential order `O(exp (a * t))` at `+∞` is
Laplace-convergent at every `s` with `a < s.re`. -/
theorem laplaceConvergent_of_isBigO_exp {f : ℝ → E} {a : ℝ} {s : ℂ}
    (hloc : LocallyIntegrableOn f (Ici 0)) (hf : f =O[atTop] fun t : ℝ ↦ Real.exp (a * t))
    (hs : a < s.re) : LaplaceConvergent f s := by
  have hint : IntegrableOn (fun t : ℝ ↦ Real.exp (-s.re * t) • f t) (Ioi 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mp
      (integrableOn_exp_neg_smul_of_isBigO_exp hloc hf hs)
  refine Integrable.mono hint
    ((aestronglyMeasurable_cexp_neg_mul_smul_iff s).mpr
      (hloc.mono_set Ioi_subset_Ici_self).aestronglyMeasurable)
    (.of_forall fun t ↦ ?_)
  simp only [norm_smul, Complex.norm_exp, Complex.re_mul_ofReal, Complex.neg_re, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), le_rfl]

/-- If `f` is Laplace-convergent at `s₀`, then on the open half-plane `s₀.re < s.re` the function
`t ↦ -(t : ℂ) • f t` is Laplace-convergent and `laplace f` has complex derivative
`laplace (fun t ↦ -(t : ℂ) • f t) s` at `s`. -/
theorem LaplaceConvergent.hasDerivAt_laplace {f : ℝ → E} {s₀ s : ℂ}
    (hf : LaplaceConvergent f s₀) (hs : s₀.re < s.re) :
    LaplaceConvergent (fun t : ℝ ↦ -(t : ℂ) • f t) s ∧
      HasDerivAt (fun z ↦ laplace f z) (laplace (fun t : ℝ ↦ -(t : ℂ) • f t) s) s := by
  let δ : ℝ := (s.re - s₀.re) / 2
  have hδ : 0 < δ := half_pos (sub_pos.mpr hs)
  have hmeas : AEStronglyMeasurable f (volume.restrict (Ioi 0)) :=
    (aestronglyMeasurable_cexp_neg_mul_smul_iff s₀).mp hf.integrable.aestronglyMeasurable
  have hF_meas : ∀ z : ℂ, AEStronglyMeasurable (fun t : ℝ ↦ Complex.exp (-z * t) • f t)
      (volume.restrict (Ioi 0)) :=
    fun z ↦ (aestronglyMeasurable_cexp_neg_mul_smul_iff z).mpr hmeas
  have hF'_meas : ∀ z : ℂ, AEStronglyMeasurable
      (fun t : ℝ ↦ Complex.exp (-z * t) • (-(t : ℂ) • f t)) (volume.restrict (Ioi 0)) :=
    fun z ↦ (aestronglyMeasurable_cexp_neg_mul_smul_iff z).mpr
      ((by fun_prop : Continuous fun t : ℝ ↦ -(t : ℂ)).aestronglyMeasurable.smul hmeas)
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t ↦ Complex.exp (-z * t) • f t)
    (F' := fun z t ↦ Complex.exp (-z * t) • (-(t : ℂ) • f t))
    (bound := fun t : ℝ ↦ δ⁻¹ * ‖Complex.exp (-s₀ * t) • f t‖)
    (ball_mem_nhds s hδ) (.of_forall hF_meas) (hf.of_re_le_re hs.le).integrable (hF'_meas s)
    ?_ (hf.integrable.norm.const_mul δ⁻¹) (.of_forall fun t z _ ↦ ?_)
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t (ht : 0 < t) z hz ↦ ?_
    have hzre : s₀.re + δ ≤ z.re := by
      have h1 : |z.re - s.re| < δ :=
        (Complex.abs_re_le_norm (z - s)).trans_lt (mem_ball_iff_norm.mp hz)
      linarith [(abs_lt.mp h1).1, show δ = (s.re - s₀.re) / 2 from rfl]
    have hte : t * Real.exp (-δ * t) ≤ δ⁻¹ := by
      have h2 : δ * t ≤ Real.exp (δ * t) :=
        (by linarith : δ * t ≤ δ * t + 1).trans (Real.add_one_le_exp (δ * t))
      calc t * Real.exp (-δ * t)
          = δ⁻¹ * ((δ * t) * Real.exp (-δ * t)) := by field_simp
        _ ≤ δ⁻¹ * (Real.exp (δ * t) * Real.exp (-δ * t)) := by gcongr
        _ = δ⁻¹ := by rw [← Real.exp_add, show δ * t + -δ * t = 0 by ring, Real.exp_zero, mul_one]
    simp only [norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
      Complex.norm_exp, Complex.re_mul_ofReal, Complex.neg_re]
    calc Real.exp (-z.re * t) * (t * ‖f t‖)
        ≤ Real.exp (-(s₀.re + δ) * t) * (t * ‖f t‖) := by gcongr
      _ = (t * Real.exp (-δ * t)) * (Real.exp (-s₀.re * t) * ‖f t‖) := by
          rw [show -(s₀.re + δ) * t = -δ * t + -s₀.re * t by ring, Real.exp_add]; ring
      _ ≤ δ⁻¹ * (Real.exp (-s₀.re * t) * ‖f t‖) := by gcongr
  · exact ((((hasDerivAt_neg z).mul_const (t : ℂ)).cexp).smul_const (f t)).congr_deriv
      (by rw [neg_one_mul, mul_smul])

/-- If `f` is Laplace-convergent at `s₀`, then `laplace f` is complex-differentiable on the open
half-plane `{s : ℂ | s₀.re < s.re}`. -/
theorem LaplaceConvergent.differentiableOn_laplace {f : ℝ → E} {s₀ : ℂ}
    (hf : LaplaceConvergent f s₀) :
    DifferentiableOn ℂ (fun z ↦ laplace f z) {z : ℂ | s₀.re < z.re} :=
  fun _ hz ↦ (hf.hasDerivAt_laplace hz).2.differentiableAt.differentiableWithinAt

/-- If `F` represents the Laplace transform of `f` on a neighborhood of `s`, then
`t ↦ -(t : ℂ) • f t` has Laplace transform `deriv F s` at `s`. -/
theorem hasLaplace_neg_smul_deriv {f : ℝ → E} {F : ℂ → E} {s : ℂ}
    (hF : ∀ᶠ z in 𝓝 s, HasLaplace f z (F z)) :
    HasLaplace (fun t : ℝ ↦ -(t : ℂ) • f t) s (deriv F s) := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hF
  let s₀ : ℂ := s - ((ε / 2 : ℝ) : ℂ)
  have hs₀_mem : s₀ ∈ ball s ε := by
    simp [s₀, abs_of_pos hε, hε]
  have hs₀_lt : s₀.re < s.re := by
    simp [s₀, half_pos hε]
  obtain ⟨hconv, hderiv⟩ := (hball s₀ hs₀_mem).laplaceConvergent.hasDerivAt_laplace hs₀_lt
  have heq : F =ᶠ[𝓝 s] fun z ↦ laplace f z := hF.mono fun z hz ↦ hz.laplace_eq.symm
  exact ⟨hconv, (hderiv.congr_of_eventuallyEq heq).deriv.symm⟩

end HalfPlane

/-! ### The transform of a primitive and of a derivative -/

section LaplaceDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Finite-interval integration-by-parts identity for a primitive: if `f t = f 0 + ∫ u in 0..t, g u`
on `[0, T]` with `g` interval-integrable on `[0, T]`, then
`∫ t in 0..T, exp (-s * t) • g t = exp (-s * T) • f T - f 0 + s • ∫ t in 0..T, exp (-s * t) • f t`
for every `s : ℂ`. -/
theorem intervalIntegral_cexp_neg_mul_smul_of_primitive {f g : ℝ → E} (s : ℂ) {T : ℝ}
    (hT : 0 ≤ T) (hg : IntervalIntegrable g volume 0 T)
    (hfg : ∀ t ∈ Icc 0 T, f t = f 0 + ∫ u in (0 : ℝ)..t, g u) :
    ∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • g t =
      Complex.exp (-s * T) • f T - f 0 + s • ∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • f t := by
  let φ : ℝ → ℂ := fun t ↦ Complex.exp (-s * t)
  have hφ : ContDiff ℝ 1 φ :=
    Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)
  have hφ' (t : ℝ) : deriv φ t = -s * φ t :=
    ((((hasDerivAt_id' t).ofReal_comp.const_mul (-s)).cexp).congr_deriv
      (by simp [φ, mul_comm])).deriv
  have hibp := TauCeti.intervalIntegral.integral_deriv_smul_primitive_eq_sub_of_le hT hφ hg
  have hprim : EqOn (fun t ↦ deriv φ t • ∫ u in (0 : ℝ)..t, g u)
      (fun t ↦ (-s) • (φ t • f t) - deriv φ t • f 0) (uIcc 0 T) := fun t ht ↦ by
    rw [uIcc_of_le hT] at ht
    dsimp only
    rw [show ∫ u in (0 : ℝ)..t, g u = f t - f 0 from eq_sub_of_add_eq' (hfg t ht).symm,
      smul_sub, hφ' t, mul_smul]
  have hfint : IntervalIntegrable (fun t ↦ (-s) • (φ t • f t)) volume 0 T := by
    have hfcont : ContinuousOn f (uIcc 0 T) := by
      rw [uIcc_of_le hT]
      have hP : ContinuousOn (fun t ↦ f 0 + ∫ u in (0 : ℝ)..t, g u) (Icc 0 T) :=
        continuousOn_const.add
          ((intervalIntegral.continuousOn_primitive_interval' hg left_mem_uIcc).mono
            (by rw [uIcc_of_le hT]))
      exact hP.congr hfg
    exact (hφ.continuous.continuousOn.smul hfcont).intervalIntegrable.smul (-s)
  have h0int : IntervalIntegrable (fun t ↦ deriv φ t • f 0) volume 0 T :=
    ((hφ.continuous_deriv le_rfl).smul continuous_const).intervalIntegrable 0 T
  rw [intervalIntegral.integral_congr hprim, intervalIntegral.integral_sub hfint h0int,
    intervalIntegral.integral_smul, intervalIntegral.integral_smul_const,
    intervalIntegral.integral_deriv_eq_sub (fun x _ ↦ hφ.differentiable one_ne_zero x)
      ((hφ.continuous_deriv le_rfl).intervalIntegrable 0 T),
    show ∫ u in (0 : ℝ)..T, g u = f T - f 0 from eq_sub_of_add_eq' (hfg T ⟨hT, le_rfl⟩).symm]
    at hibp
  simp only [φ, Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_smul, sub_smul, one_smul,
    smul_sub] at hibp
  calc ∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • g t
      = Complex.exp (-s * T) • f T - Complex.exp (-s * T) • f 0 -
          (Complex.exp (-s * T) • f T - Complex.exp (-s * T) • f 0 -
            ∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • g t) := by abel
    _ = Complex.exp (-s * T) • f T - Complex.exp (-s * T) • f 0 -
          (-(s • ∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • f t) -
            (Complex.exp (-s * T) • f 0 - f 0)) := by rw [← hibp]
    _ = Complex.exp (-s * T) • f T - f 0 +
          s • ∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • f t := by abel

private lemma tendsto_cexp_neg_mul_smul_atTop_of_primitive {f g : ℝ → E} {s : ℂ}
    (hfg : ∀ t ∈ Ici (0 : ℝ), f t = f 0 + ∫ u in (0 : ℝ)..t, g u)
    (hf : LaplaceConvergent f s) (hg : LaplaceConvergent g s) :
    Tendsto (fun T : ℝ ↦ Complex.exp (-s * T) • f T) atTop
      (𝓝 (laplace g s + f 0 - s • laplace f s)) := by
  have h1 := intervalIntegral_tendsto_integral_Ioi 0 hg.integrable tendsto_id
  have h2 := intervalIntegral_tendsto_integral_Ioi 0 hf.integrable tendsto_id
  refine ((h1.add tendsto_const_nhds).sub (h2.const_smul s)).congr' ?_
  filter_upwards [Ici_mem_atTop (0 : ℝ)] with T (hT : 0 ≤ T)
  have hid := intervalIntegral_cexp_neg_mul_smul_of_primitive s hT
    (hg.intervalIntegrable le_rfl hT) (fun t ht ↦ hfg t ht.1)
  simp only [id_eq]
  rw [hid]
  abel

/-- If `f` is a primitive of `g` on `[0, ∞)` and both `f` and `g` are Laplace-convergent at `s`,
then the boundary term `exp (-s * T) • f T` tends to `0` as `T → +∞`. -/
theorem tendsto_cexp_neg_mul_smul_atTop_zero_of_primitive {f g : ℝ → E} {s : ℂ}
    (hfg : ∀ t ∈ Ici (0 : ℝ), f t = f 0 + ∫ u in (0 : ℝ)..t, g u)
    (hf : LaplaceConvergent f s) (hg : LaplaceConvergent g s) :
    Tendsto (fun t : ℝ ↦ Complex.exp (-s * t) • f t) atTop (𝓝 0) := by
  have hlim := tendsto_cexp_neg_mul_smul_atTop_of_primitive hfg hf hg
  have hL : laplace g s + f 0 - s • laplace f s = 0 := by
    have hint : IntegrableAtFilter (fun t : ℝ ↦ Complex.exp (-s * t) • f t) atTop :=
      ⟨Ioi 0, Ioi_mem_atTop 0, hf.integrable⟩
    refine hint.eq_zero_of_tendsto (fun U hU ↦ ?_) hlim
    rcases mem_atTop_sets.mp hU with ⟨b, hb⟩
    rw [← top_le_iff, ← Real.volume_Ici (a := b)]
    exact measure_mono hb
  rwa [hL] at hlim

/-- The transform of a derivative, primitive form: if `f` is a primitive of `g` on `[0, ∞)`,
`f` has Laplace transform `z` at `s`, and `t ↦ exp (-s * t) • g t` is integrable on `(0, ∞)`,
then `g` has Laplace transform `s • z - f 0` at `s`. No condition on `s.re` or auxiliary growth
bound on `f` is assumed (compare Lebl, *Notes on Diffy Qs*, version 6.11, §6.2.1, p. 300). -/
theorem hasLaplace_deriv_of_primitive {f g : ℝ → E} {s : ℂ} {z : E}
    (hfg : ∀ t ∈ Ici (0 : ℝ), f t = f 0 + ∫ u in (0 : ℝ)..t, g u)
    (hf : HasLaplace f s z)
    (hg : Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • g t) (volume.restrict (Ioi 0))) :
    HasLaplace g s (s • z - f 0) := by
  refine ⟨hg, ?_⟩
  have hL := tendsto_nhds_unique
    (tendsto_cexp_neg_mul_smul_atTop_of_primitive hfg hf.laplaceConvergent hg)
    (tendsto_cexp_neg_mul_smul_atTop_zero_of_primitive hfg hf.laplaceConvergent hg)
  rw [← hf.laplace_eq]
  exact eq_sub_of_add_eq (sub_eq_zero.mp hL)

/-- The transform of a derivative: for `f` continuous at `0` from the right and differentiable on
`(0, ∞)`, if `f` has Laplace transform `z` at `s` and `t ↦ exp (-s * t) • f' t` is integrable on
`(0, ∞)`, then `f'` has Laplace transform `s • z - f 0` at `s` (compare Lebl, *Notes on Diffy Qs*,
version 6.11, §6.2.1, p. 300). -/
theorem hasLaplace_deriv {f f' : ℝ → E} {s : ℂ} {z : E}
    (hf0 : ContinuousWithinAt f (Ici 0) 0)
    (hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t)
    (hf : HasLaplace f s z)
    (hf' : Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f' t) (volume.restrict (Ioi 0))) :
    HasLaplace f' s (s • z - f 0) := by
  refine hasLaplace_deriv_of_primitive (fun t (ht : 0 ≤ t) ↦ ?_) hf hf'
  rcases ht.eq_or_lt with rfl | ht'
  · simp
  · have hcont : ContinuousOn f (Icc 0 t) := by
      intro x hx
      rcases hx.1.eq_or_lt with rfl | hx₀
      · exact hf0.mono Icc_subset_Ici_self
      · exact (hderiv x hx₀).continuousAt.continuousWithinAt
    have hint : IntervalIntegrable f' volume 0 t :=
      LaplaceConvergent.intervalIntegrable hf' le_rfl ht'.le
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht'.le hcont
      (fun x hx ↦ hderiv x hx.1) hint, add_sub_cancel]

end LaplaceDeriv

/-! ### Explicit Laplace transforms and non-convergence on the closed left half-plane -/

section Examples

/-- A constant function `t ↦ x` is Laplace-convergent at `s` iff `x = 0` or `0 < s.re`. -/
-- Not `@[grind =]`: Lean's `grind` rejects patterns binding `x` inside a lambda `fun _ ↦ x`.
@[simp]
theorem laplaceConvergent_const_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {x : E} {s : ℂ} :
    LaplaceConvergent (fun _ : ℝ ↦ x) s ↔ x = 0 ∨ 0 < s.re := by
  by_cases hx : x = 0
  · simp [hx]
  · simp only [hx, false_or, LaplaceConvergent, integrable_smul_const hx,
      ← integrable_norm_iff
        (by fun_prop : Continuous fun t : ℝ ↦ Complex.exp (-s * t)).aestronglyMeasurable,
      Complex.norm_exp, Complex.re_mul_ofReal, Complex.neg_re]
    exact integrableOn_exp_mul_Ioi_iff.trans neg_lt_zero

/-- For `0 < s.re`, a constant function `t ↦ x` in a complex Banach space has Laplace transform
`s⁻¹ • x`. -/
theorem hasLaplace_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {s : ℂ} (hs : 0 < s.re) (x : E) :
    HasLaplace (fun _ : ℝ ↦ x) s (s⁻¹ • x) := by
  have hneg : (-s).re < 0 := by simpa using hs
  refine ⟨laplaceConvergent_const_iff.mpr (Or.inr hs), ?_⟩
  rw [integral_smul_const, integral_exp_mul_complex_Ioi hneg 0, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, neg_div_neg_eq, one_div]

/-- For `0 < s.re`, the constant function `1 : ℝ → ℂ` has Laplace transform `1 / s`. -/
@[to_fun hasLaplace_fun_one]
theorem hasLaplace_one {s : ℂ} (hs : 0 < s.re) :
    HasLaplace (1 : ℝ → ℂ) s (1 / s) := by
  simpa [Pi.one_def, one_div] using hasLaplace_const hs (1 : ℂ)

/-- A nonzero constant function has no Laplace transform at any `s` with `s.re ≤ 0`; in particular
`¬ HasLaplace (fun _ ↦ (1 : ℂ)) 0 0`. -/
theorem not_hasLaplace_const_of_re_nonpos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] {x : E} (hx : x ≠ 0) {s : ℂ} (hs : s.re ≤ 0) (z : E) :
    ¬ HasLaplace (fun _ : ℝ ↦ x) s z :=
  fun h ↦ ((laplaceConvergent_const_iff.mp h.laplaceConvergent).resolve_left hx).not_ge hs

/-- For `w.re < s.re`, the exponential `t ↦ exp (w * t)` has Laplace transform `1 / (s - w)`. -/
theorem hasLaplace_cexp {w s : ℂ} (hws : w.re < s.re) :
    HasLaplace (fun t : ℝ ↦ Complex.exp (w * t)) s (1 / (s - w)) := by
  have h := (hasLaplace_cexp_smul w (f := fun _ : ℝ ↦ (1 : ℂ))).mpr
    (hasLaplace_fun_one (by simpa using sub_pos.mpr hws))
  simpa using h

/-- For every `k : ℕ` and `0 < s.re`, the monomial `t ↦ (t : ℂ) ^ k` is Laplace-convergent at `s`.
-/
theorem laplaceConvergent_pow (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    LaplaceConvergent (fun t : ℝ ↦ (t : ℂ) ^ k) s := by
  have hk : 0 < ((k : ℂ) + 1).re := by
    rw [Complex.add_re, Complex.natCast_re, Complex.one_re]; positivity
  refine (Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi hk hs).congr_fun
    (fun t _ ↦ ?_) measurableSet_Ioi
  simp [add_sub_cancel_right, Complex.cpow_natCast, mul_comm]

/-- For every `k : ℕ` and `0 < s.re`, the monomial `t ↦ (t : ℂ) ^ k` has Laplace transform
`k! / s ^ (k + 1)`. -/
theorem hasLaplace_pow (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasLaplace (fun t : ℝ ↦ (t : ℂ) ^ k) s ((k.factorial : ℂ) / s ^ (k + 1)) := by
  refine ⟨laplaceConvergent_pow k hs, ?_⟩
  have hk : 0 < ((k : ℂ) + 1).re := by
    rw [Complex.add_re, Complex.natCast_re, Complex.one_re]; positivity
  have hval := Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hk hs
  have hcongr : ∫ t in Ioi (0 : ℝ), Complex.exp (-s * t) • (t : ℂ) ^ k =
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ ((k : ℂ) + 1 - 1) * Complex.exp (-(s * t)) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ by
      simp [add_sub_cancel_right, Complex.cpow_natCast, mul_comm]
  rw [hcongr, hval, Complex.Gamma_nat_eq_factorial, Complex.cpow_neg,
    show (k : ℂ) + 1 = ((k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.cpow_natCast, div_eq_mul_inv]

/-- For every `k : ℕ` and `w.re < s.re`, `t ↦ exp (w * t) * (t : ℂ) ^ k` has Laplace transform
`k! / (s - w) ^ (k + 1)`. -/
theorem hasLaplace_cexp_mul_pow (k : ℕ) {w s : ℂ} (hws : w.re < s.re) :
    HasLaplace (fun t : ℝ ↦ Complex.exp (w * t) * (t : ℂ) ^ k) s
      ((k.factorial : ℂ) / (s - w) ^ (k + 1)) := by
  exact (hasLaplace_cexp_smul w (f := fun t : ℝ ↦ (t : ℂ) ^ k)).mpr
    (hasLaplace_pow k (by simpa using sub_pos.mpr hws))

/-- For every `k : ℕ`, `a : ℝ`, and `a < s.re`, the real model `t ↦ exp (a * t) * t ^ k` cast to
`ℂ` has Laplace transform `k! / (s - a) ^ (k + 1)` (Delange 1954, Lemma 4, §5.1.2, p. 233, for
integer exponents). -/
theorem hasLaplace_exp_mul_pow (k : ℕ) {a : ℝ} {s : ℂ} (has : a < s.re) :
    HasLaplace (fun t : ℝ ↦ ((Real.exp (a * t) * t ^ k : ℝ) : ℂ)) s
      ((k.factorial : ℂ) / (s - a) ^ (k + 1)) := by
  refine (hasLaplace_cexp_mul_pow k (w := (a : ℂ)) (by simpa using has)).congr_ae
    (.of_forall fun t ↦ ?_)
  simp [Complex.ofReal_exp]

end Examples

end TauCeti
