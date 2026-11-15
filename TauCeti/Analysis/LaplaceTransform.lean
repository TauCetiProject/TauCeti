/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.Prod

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
  translation (`hasLaplace_cexp_smul`, `hasLaplace_exp_smul`), and positive time dilation
  (`HasLaplace.comp_mul_left`).
* Half-plane convergence and parameter differentiation: convergence at `s₀` propagates to every `s`
  with `s₀.re ≤ s.re` (`LaplaceConvergent.of_re_le_re`), exponential growth `O(exp (a * t))` gives
  convergence on `a < s.re` (`laplaceConvergent_of_isBigO_exp`), and on the open half-plane
  `s₀.re < s.re` the transform is complex-differentiable with derivative equal to the transform of
  `t ↦ -(t : ℂ) • f t` (`LaplaceConvergent.hasDerivAt_laplace`,
  `LaplaceConvergent.differentiableOn_laplace`, `HasLaplace.hasLaplace_neg_smul_deriv`).
* Transform of a derivative (`hasLaplace_deriv_of_primitive`, `hasLaplace_deriv`): in a complex
  Banach space, if `f` is a primitive of `g` on `[0, ∞)` (or right-continuous at `0` with derivative
  `f'` on `(0, ∞)`), `HasLaplace f s z`, and `t ↦ exp (-s * t) • g t` is integrable on `(0, ∞)`,
  then `HasLaplace g s (s • z - f 0)` with no restriction on `s.re` and no auxiliary growth bound;
  vanishing of the boundary term `exp (-s * T) • f T` at `+∞` is derived from integrability
  (`tendsto_cexp_neg_mul_smul_atTop_zero_of_primitive`).
* Explicit transforms: constants (`hasLaplace_const`, `hasLaplace_one`, and non-convergence on
  `s.re ≤ 0` via `not_hasLaplace_const_of_re_le_zero`), exponentials (`hasLaplace_cexp`), and
  monomials and exponentially weighted monomials (`hasLaplace_pow`, `hasLaplace_cexp_mul_pow`,
  `hasLaplace_exp_mul_pow`).

## References

* D. Osele, *The Laplace transform* (2026), declarations `LaplaceConvergent`, `laplace`, and
  `HasLaplace` at commit `90482cd37e85e423459de2ed103cea2f4d98cb20`, for the argument order,
  default measure, and scalar-action hypotheses of the transform predicate.
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
convergence of the one-sided Laplace integral `∫₀^∞ exp (-s * t) • f t dt`. -/
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

/-- The Laplace transform `∫ t, exp (-s * t) • f t ∂μ`, defaulting to `μ = volume.restrict (Ioi 0)`.
Following Dennj Osele, *The Laplace transform*, `laplace`. -/
def laplace (f : ℝ → E) (s : ℂ) (μ : Measure ℝ := volume.restrict (Ioi 0)) : E :=
  ∫ t : ℝ, Complex.exp (-s * t) • f t ∂μ

/-- Unfolding characterization of `laplace`. -/
theorem laplace_def (f : ℝ → E) (s : ℂ) (μ : Measure ℝ := volume.restrict (Ioi 0)) :
    laplace f s μ = ∫ t : ℝ, Complex.exp (-s * t) • f t ∂μ :=
  (rfl)

/-- When `f` is not Laplace-convergent at `s`, the totalised `laplace` integral vanishes. -/
theorem laplace_of_not_laplaceConvergent {f : ℝ → E} {s : ℂ} {μ : Measure ℝ}
    (h : ¬ LaplaceConvergent f s μ) : laplace f s μ = 0 :=
  integral_undef h

/-- `HasLaplace f s z μ`: the integrand `t ↦ exp (-s * t) • f t` is integrable for `μ` and its
Bochner integral equals `z`. With the default measure `volume.restrict (Ioi 0)` this is the
ordinary one-sided Laplace transform of `f` at `s : ℂ`, following Dennj Osele,
*The Laplace transform*, `HasLaplace`. -/
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
@[simp]
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
@[simp]
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
@[simp]
theorem hasLaplace_restrict_Ici_iff {f : ℝ → E} {s : ℂ} {z : E} :
    HasLaplace f s z (volume.restrict (Ici 0)) ↔ HasLaplace f s z := by
  rw [hasLaplace_iff, hasLaplace_iff, laplaceConvergent_restrict_Ici_iff, laplace_restrict_Ici]

end Congr

/-! ### Linearity, frequency shifts, and positive dilation -/

section Zero

/-- When the `ℂ`-action preserves zero, the zero function is Laplace-convergent everywhere. -/
@[simp]
theorem laplaceConvergent_zero {E : Type*} [NormedAddCommGroup E] [SMulZeroClass ℂ E]
    (s : ℂ) (μ : Measure ℝ := volume.restrict (Ioi 0)) :
    LaplaceConvergent (0 : ℝ → E) s μ := by
  simp [LaplaceConvergent]

/-- When the `ℂ`-action preserves zero, the Laplace integral of `0` is `0`. -/
@[simp]
theorem laplace_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SMulZeroClass ℂ E]
    (s : ℂ) (μ : Measure ℝ := volume.restrict (Ioi 0)) :
    laplace (0 : ℝ → E) s μ = 0 := by
  simp [laplace]

/-- When the `ℂ`-action preserves zero, the zero function has Laplace transform `0` at every `s`
and for every measure `μ`. -/
theorem hasLaplace_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SMulZeroClass ℂ E]
    (s : ℂ) (μ : Measure ℝ := volume.restrict (Ioi 0)) :
    HasLaplace (0 : ℝ → E) s 0 μ :=
  ⟨laplaceConvergent_zero s μ, laplace_zero s μ⟩

end Zero

section Add

/-- Sum of two Laplace-convergent functions. -/
theorem LaplaceConvergent.add {E : Type*} [NormedAddCommGroup E] [DistribSMul ℂ E]
    {f g : ℝ → E} {s : ℂ} {μ : Measure ℝ}
    (hf : LaplaceConvergent f s μ) (hg : LaplaceConvergent g s μ) :
    LaplaceConvergent (f + g) s μ := by
  simpa only [LaplaceConvergent, Pi.add_apply, smul_add] using hf.integrable.fun_add hg.integrable

/-- Negation of a Laplace-convergent function. -/
theorem LaplaceConvergent.neg {E : Type*} [NormedAddCommGroup E] [DistribSMul ℂ E]
    {f : ℝ → E} {s : ℂ} {μ : Measure ℝ} (hf : LaplaceConvergent f s μ) :
    LaplaceConvergent (-f) s μ := by
  simpa only [LaplaceConvergent, Pi.neg_apply, smul_neg] using hf.integrable.fun_neg

/-- Negating a function preserves `LaplaceConvergent`. -/
@[simp]
theorem laplaceConvergent_neg_iff {E : Type*} [NormedAddCommGroup E] [DistribSMul ℂ E]
    {f : ℝ → E} {s : ℂ} {μ : Measure ℝ} :
    LaplaceConvergent (-f) s μ ↔ LaplaceConvergent f s μ :=
  ⟨fun h ↦ by simpa only [neg_neg] using h.neg, LaplaceConvergent.neg⟩

/-- Difference of two Laplace-convergent functions. -/
theorem LaplaceConvergent.sub {E : Type*} [NormedAddCommGroup E] [DistribSMul ℂ E]
    {f g : ℝ → E} {s : ℂ} {μ : Measure ℝ}
    (hf : LaplaceConvergent f s μ) (hg : LaplaceConvergent g s μ) :
    LaplaceConvergent (f - g) s μ := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DistribSMul ℂ E]

/-- Additivity of `laplace` on Laplace-convergent functions. -/
theorem laplace_add {f g : ℝ → E} {s : ℂ} {μ : Measure ℝ}
    (hf : LaplaceConvergent f s μ) (hg : LaplaceConvergent g s μ) :
    laplace (f + g) s μ = laplace f s μ + laplace g s μ := by
  simpa only [laplace, Pi.add_apply, smul_add] using integral_add hf.integrable hg.integrable

/-- Negation commutes with `laplace`. -/
@[simp]
theorem laplace_neg (f : ℝ → E) (s : ℂ) {μ : Measure ℝ} :
    laplace (-f) s μ = -laplace f s μ := by
  simp only [laplace, Pi.neg_apply, smul_neg, integral_neg]

/-- Subtraction of `laplace` on Laplace-convergent functions. -/
theorem laplace_sub {f g : ℝ → E} {s : ℂ} {μ : Measure ℝ}
    (hf : LaplaceConvergent f s μ) (hg : LaplaceConvergent g s μ) :
    laplace (f - g) s μ = laplace f s μ - laplace g s μ := by
  simpa only [laplace, Pi.sub_apply, smul_sub] using integral_sub hf.integrable hg.integrable

/-- Additivity of `HasLaplace` under `DistribSMul ℂ E`. -/
theorem HasLaplace.add {f g : ℝ → E} {s : ℂ} {z w : E} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) (hg : HasLaplace g s w μ) :
    HasLaplace (f + g) s (z + w) μ := by
  rw [hasLaplace_iff]
  exact ⟨hf.laplaceConvergent.add hg.laplaceConvergent,
    by rw [laplace_add hf.laplaceConvergent hg.laplaceConvergent, hf.laplace_eq, hg.laplace_eq]⟩

/-- Negation of `HasLaplace` under `DistribSMul ℂ E`. -/
theorem HasLaplace.neg {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) : HasLaplace (-f) s (-z) μ := by
  rw [hasLaplace_iff]
  exact ⟨hf.laplaceConvergent.neg, by rw [laplace_neg, hf.laplace_eq]⟩

/-- Subtraction of `HasLaplace` under `DistribSMul ℂ E`. -/
theorem HasLaplace.sub {f g : ℝ → E} {s : ℂ} {z w : E} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) (hg : HasLaplace g s w μ) :
    HasLaplace (f - g) s (z - w) μ := by
  rw [hasLaplace_iff]
  exact ⟨hf.laplaceConvergent.sub hg.laplaceConvergent,
    by rw [laplace_sub hf.laplaceConvergent hg.laplaceConvergent, hf.laplace_eq, hg.laplace_eq]⟩

end Add

section SMulAndShift

/-- Scalar multiplication by `c : ℂ` preserves `LaplaceConvergent`. -/
theorem LaplaceConvergent.const_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℝ → E} {s : ℂ} {μ : Measure ℝ} (hf : LaplaceConvergent f s μ) (c : ℂ) :
    LaplaceConvergent (fun t ↦ c • f t) s μ := by
  simpa only [LaplaceConvergent, smul_comm _ c] using hf.integrable.fun_smul c

/-- Scalar multiplication by `c : ℂ` commutes with `laplace`. -/
theorem laplace_const_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] (f : ℝ → E) (s : ℂ) (c : ℂ) {μ : Measure ℝ} :
    laplace (fun t ↦ c • f t) s μ = c • laplace f s μ := by
  have : SMulCommClass ℝ ℂ E := ⟨fun r z x ↦ by
    rw [← smul_one_smul ℂ r (z • x), ← smul_one_smul ℂ r x, smul_smul, smul_smul, mul_comm]⟩
  simp only [laplace, smul_comm _ c, integral_smul]

/-- Scalar multiplication by `c : ℂ` scales `HasLaplace` by `c`. -/
theorem HasLaplace.const_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) (c : ℂ) :
    HasLaplace (fun t ↦ c • f t) s (c • z) μ := by
  rw [hasLaplace_iff]
  exact ⟨hf.laplaceConvergent.const_smul c, by rw [laplace_const_smul, hf.laplace_eq]⟩

/-- Scalar multiplication by a real constant `c : ℝ` preserves `LaplaceConvergent`. -/
theorem LaplaceConvergent.const_smul_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SMul ℂ E] [SMulCommClass ℝ ℂ E] {f : ℝ → E} {s : ℂ} {μ : Measure ℝ}
    (hf : LaplaceConvergent f s μ) (c : ℝ) :
    LaplaceConvergent (fun t ↦ c • f t) s μ := by
  simpa only [LaplaceConvergent, smul_comm c] using hf.integrable.fun_smul c

/-- Scalar multiplication by a real constant `c : ℝ` commutes with `laplace`. -/
theorem laplace_const_smul_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SMul ℂ E] [SMulCommClass ℝ ℂ E] (f : ℝ → E) (s : ℂ) (c : ℝ) {μ : Measure ℝ} :
    laplace (fun t ↦ c • f t) s μ = c • laplace f s μ := by
  simp only [laplace, ← smul_comm c, integral_smul]

/-- Scalar multiplication by a real constant `c : ℝ` scales `HasLaplace` by `c`. -/
theorem HasLaplace.const_smul_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SMul ℂ E] [SMulCommClass ℝ ℂ E] {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) (c : ℝ) :
    HasLaplace (fun t ↦ c • f t) s (c • z) μ := by
  rw [hasLaplace_iff]
  exact ⟨hf.laplaceConvergent.const_smul_real c, by rw [laplace_const_smul_real, hf.laplace_eq]⟩

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

/-- Multiplying `f` by a real exponential `t ↦ Real.exp (a * t)` shifts `HasLaplace` from `s` to
`s - a`. -/
theorem hasLaplace_exp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MulAction ℂ E]
    [IsScalarTower ℝ ℂ E] {f : ℝ → E} (a : ℝ) {s : ℂ} {z : E} {μ : Measure ℝ} :
    HasLaplace (fun t : ℝ ↦ Real.exp (a * t) • f t) s z μ ↔ HasLaplace f (s - a) z μ := by
  rw [← hasLaplace_cexp_smul (a : ℂ)]
  refine hasLaplace_congr_ae (.of_forall fun t ↦ ?_)
  dsimp only
  rw [← smul_one_smul ℂ (Real.exp (a * t)) (f t), Complex.real_smul, mul_one,
    Complex.ofReal_exp, Complex.ofReal_mul]

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
      AEStronglyMeasurable f μ := by
  refine ⟨fun h ↦ ?_, fun h ↦
    (by fun_prop : Continuous fun t : ℝ ↦ Complex.exp (-s * t)).aestronglyMeasurable.smul h⟩
  have h' :=
    (by fun_prop : Continuous fun t : ℝ ↦ Complex.exp (s * t)).aestronglyMeasurable.smul h
  refine h'.congr (.of_forall fun t ↦ ?_)
  simp [smul_smul, ← Complex.exp_add]

/-- Multiplying by `t ↦ exp (-s * t)` preserves interval integrability on every finite interval. -/
theorem intervalIntegrable_cexp_neg_mul_smul_iff {f : ℝ → E} {a b : ℝ} (s : ℂ) :
    IntervalIntegrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) volume a b ↔
      IntervalIntegrable f volume a b := by
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

/-- If `F` represents the Laplace transform of `f` on `s₀.re < z.re` and `f` is Laplace-convergent
at `s₀`, then `t ↦ -(t : ℂ) • f t` has Laplace transform `deriv F s` at every `s` with
`s₀.re < s.re`. -/
theorem HasLaplace.hasLaplace_neg_smul_deriv {f : ℝ → E} {F : ℂ → E} {s₀ s : ℂ}
    (hf₀ : LaplaceConvergent f s₀) (hF : ∀ z : ℂ, s₀.re < z.re → HasLaplace f z (F z))
    (hs : s₀.re < s.re) :
    HasLaplace (fun t : ℝ ↦ -(t : ℂ) • f t) s (deriv F s) := by
  obtain ⟨hconv, hderiv⟩ := hf₀.hasDerivAt_laplace hs
  have heq : F =ᶠ[𝓝 s] fun z ↦ laplace f z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact (hF z hz).laplace_eq.symm
  exact ⟨hconv, (hderiv.congr_of_eventuallyEq heq).deriv.symm⟩

end HalfPlane

/-! ### The transform of a primitive and of a derivative -/

section LaplaceDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

private lemma intervalIntegral_mul_cexp_neg_mul (s : ℂ) (a b : ℝ) :
    ∫ r in a..b, s * Complex.exp (-s * r) = Complex.exp (-s * a) - Complex.exp (-s * b) := by
  have hd : ∀ r ∈ uIcc a b,
      HasDerivAt (fun x : ℝ ↦ -Complex.exp (-s * x)) (s * Complex.exp (-s * r)) r := fun r _ ↦
    ((((hasDerivAt_id' r).ofReal_comp.const_mul (-s)).cexp).fun_neg).congr_deriv (by simp; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun r : ℝ ↦ s * Complex.exp (-s * r)).intervalIntegrable a b),
    sub_neg_eq_add, add_comm, sub_eq_add_neg]

/-- Finite-interval integration-by-parts identity for a primitive: if `f t = f 0 + ∫ u in 0..t, g u`
on `[0, T]` with `g` interval-integrable on `[0, T]`, then
`∫ t in 0..T, exp (-s * t) • g t = exp (-s * T) • f T - f 0 + s • ∫ t in 0..T, exp (-s * t) • f t`
for every `s : ℂ`. -/
theorem intervalIntegral_cexp_neg_mul_smul_of_primitive {f g : ℝ → E} (s : ℂ) {T : ℝ}
    (hT : 0 ≤ T) (hg : IntervalIntegrable g volume 0 T)
    (hfg : ∀ t ∈ Icc 0 T, f t = f 0 + ∫ u in (0 : ℝ)..t, g u) :
    ∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • g t =
      Complex.exp (-s * T) • f T - f 0 + s • ∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • f t := by
  let μT : Measure ℝ := volume.restrict (Ioc 0 T)
  let u : ℝ → ℂ := fun r ↦ s * Complex.exp (-s * r)
  have hu : Integrable u μT := (by fun_prop : Continuous u).integrableOn_Ioc
  let P : ℝ × ℝ → E := Set.indicator {z : ℝ × ℝ | z.2 ≤ z.1} (fun z ↦ u z.1 • g z.2)
  have hP : Integrable P (μT.prod μT) :=
    (hu.smul_prod hg.1).indicator (measurableSet_le measurable_snd measurable_fst)
  have hswap : ∫ r, ∫ t, P (r, t) ∂μT ∂μT = ∫ t, ∫ r, P (r, t) ∂μT ∂μT :=
    (integral_prod P hP).symm.trans (integral_prod_symm P hP)
  have hLHS : ∫ r, ∫ t, P (r, t) ∂μT ∂μT =
      s • (∫ r in (0 : ℝ)..T, Complex.exp (-s * r) • f r) -
        (1 - Complex.exp (-s * T)) • f 0 := by
    have hinner : ∀ r ∈ Ioc (0 : ℝ) T, ∫ t, P (r, t) ∂μT =
        s • (Complex.exp (-s * r) • f r) - u r • f 0 := fun r hr ↦ by
      have hset : Iic r ∩ Ioc 0 T = Ioc 0 r := by
        ext t; simp only [mem_inter_iff, mem_Iic, mem_Ioc]
        exact ⟨fun h ↦ ⟨h.2.1, h.1⟩, fun h ↦ ⟨h.2, h.1, h.2.trans hr.2⟩⟩
      change ∫ t, (Iic r).indicator (fun t ↦ u r • g t) t ∂μT = _
      rw [integral_indicator measurableSet_Iic]
      simp only [μT, Measure.restrict_restrict measurableSet_Iic, hset]
      rw [← intervalIntegral.integral_of_le hr.1.le, intervalIntegral.integral_smul,
        hfg r ⟨hr.1.le, hr.2⟩, ← mul_smul, smul_add, add_sub_cancel_left]
    have hsf : Integrable (fun r : ℝ ↦ s • (Complex.exp (-s * r) • f r)) μT := by
      have h1 := hP.integral_prod_left.congr (ae_restrict_of_forall_mem measurableSet_Ioc hinner)
      simpa only [sub_add_cancel] using h1.fun_add (hu.smul_const (f 0))
    rw [setIntegral_congr_fun measurableSet_Ioc hinner, integral_sub hsf (hu.smul_const (f 0)),
      integral_smul, ← intervalIntegral.integral_of_le hT, integral_smul_const,
      ← intervalIntegral.integral_of_le hT, intervalIntegral_mul_cexp_neg_mul,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hRHS : ∫ t, ∫ r, P (r, t) ∂μT ∂μT =
      (∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • g t) -
        Complex.exp (-s * T) • (f T - f 0) := by
    have hinner₂ : ∀ t ∈ Ioc (0 : ℝ) T, ∫ r, P (r, t) ∂μT =
        Complex.exp (-s * t) • g t - Complex.exp (-s * T) • g t := fun t ht ↦ by
      have hset : Ici t ∩ Ioc 0 T = Icc t T := by
        ext r; simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
        exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, ht.1.trans_le h.1, h.2⟩⟩
      change ∫ r, (Ici t).indicator (fun r ↦ u r • g t) r ∂μT = _
      rw [integral_indicator measurableSet_Ici]
      simp only [μT, Measure.restrict_restrict measurableSet_Ici, hset]
      rw [integral_smul_const, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le ht.2, intervalIntegral_mul_cexp_neg_mul, sub_smul]
    have hg₁ : Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • g t) μT :=
      ((intervalIntegrable_cexp_neg_mul_smul_iff s).mpr hg).1
    rw [setIntegral_congr_fun measurableSet_Ioc hinner₂,
      integral_sub hg₁ (hg.1.fun_smul (Complex.exp (-s * T))), integral_smul,
      ← intervalIntegral.integral_of_le hT, ← intervalIntegral.integral_of_le hT,
      hfg T ⟨hT, le_rfl⟩, add_sub_cancel_left]
  rw [hLHS, hRHS] at hswap
  have hswap' := congrArg (· + Complex.exp (-s * T) • (f T - f 0)) hswap
  simp only [sub_add_cancel] at hswap'
  rw [← hswap', sub_smul, one_smul, smul_sub]
  abel

/-- If `f` is a primitive of `g` on `[0, ∞)` and both `f` and `g` are Laplace-convergent at `s`,
then the boundary term `exp (-s * T) • f T` tends to `0` as `T → +∞`. -/
theorem tendsto_cexp_neg_mul_smul_atTop_zero_of_primitive {f g : ℝ → E} {s : ℂ}
    (hfg : ∀ t ∈ Ici (0 : ℝ), f t = f 0 + ∫ u in (0 : ℝ)..t, g u)
    (hf : LaplaceConvergent f s) (hg : LaplaceConvergent g s) :
    Tendsto (fun t : ℝ ↦ Complex.exp (-s * t) • f t) atTop (𝓝 0) := by
  set L : E := laplace g s + f 0 - s • laplace f s
  have hlim : Tendsto (fun T : ℝ ↦ Complex.exp (-s * T) • f T) atTop (𝓝 L) := by
    have h1 := intervalIntegral_tendsto_integral_Ioi 0 hg.integrable tendsto_id
    have h2 := intervalIntegral_tendsto_integral_Ioi 0 hf.integrable tendsto_id
    refine ((h1.add tendsto_const_nhds).sub (h2.const_smul s)).congr' ?_
    filter_upwards [Ici_mem_atTop (0 : ℝ)] with T (hT : 0 ≤ T)
    have hid := intervalIntegral_cexp_neg_mul_smul_of_primitive s hT
      (hg.intervalIntegrable le_rfl hT) (fun t ht ↦ hfg t ht.1)
    simp only [id_eq]
    rw [hid]
    abel
  have hL : L = 0 := by
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
  have h1 := intervalIntegral_tendsto_integral_Ioi 0 hg tendsto_id
  have h2 := intervalIntegral_tendsto_integral_Ioi 0 hf.integrable tendsto_id
  have h0 := tendsto_cexp_neg_mul_smul_atTop_zero_of_primitive hfg hf.laplaceConvergent hg
  have h3 := (h0.sub (tendsto_const_nhds (x := f 0))).add (h2.const_smul s)
  rw [hf.integral_eq, zero_sub, neg_add_eq_sub] at h3
  refine tendsto_nhds_unique h1 (h3.congr' ?_)
  filter_upwards [Ici_mem_atTop (0 : ℝ)] with T (hT : 0 ≤ T)
  simp only [id_eq]
  exact (intervalIntegral_cexp_neg_mul_smul_of_primitive s hT
    (LaplaceConvergent.intervalIntegrable hg le_rfl hT) (fun t ht ↦ hfg t ht.1)).symm

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

/-- For `0 < s.re`, a constant function `t ↦ x` in a complex Banach space has Laplace transform
`s⁻¹ • x`. -/
theorem hasLaplace_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {s : ℂ} (hs : 0 < s.re) (x : E) :
    HasLaplace (fun _ : ℝ ↦ x) s (s⁻¹ • x) := by
  have hneg : (-s).re < 0 := by simpa using hs
  refine ⟨(integrableOn_exp_mul_complex_Ioi hneg 0).smul_const x, ?_⟩
  rw [integral_smul_const, integral_exp_mul_complex_Ioi hneg 0, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, neg_div_neg_eq, one_div]

/-- For `0 < s.re`, the constant function `1 : ℝ → ℂ` has Laplace transform `1 / s`. -/
theorem hasLaplace_one {s : ℂ} (hs : 0 < s.re) :
    HasLaplace (fun _ : ℝ ↦ (1 : ℂ)) s (1 / s) := by
  simpa [one_div] using hasLaplace_const hs (1 : ℂ)

/-- A nonzero constant function is not Laplace-convergent at any `s` with `s.re ≤ 0`. -/
theorem not_laplaceConvergent_const_of_re_le_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {x : E} (hx : x ≠ 0) {s : ℂ} (hs : s.re ≤ 0) :
    ¬ LaplaceConvergent (fun _ : ℝ ↦ x) s := by
  intro h
  have hconst : IntegrableOn (fun _ : ℝ ↦ ‖x‖) (Ioi (0 : ℝ)) volume := by
    refine h.integrable.norm.mono measurable_const.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_)
    simp only [Real.norm_eq_abs, abs_norm, norm_smul, Complex.norm_exp,
      Complex.re_mul_ofReal, Complex.neg_re, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact le_mul_of_one_le_left (norm_nonneg x)
      (Real.one_le_exp (mul_nonneg (neg_nonneg.mpr hs) ht.le))
  rcases (integrableOn_const_iff (C := ‖x‖)).mp hconst with h0 | hfin
  · exact hx (norm_eq_zero.mp (eNorm_eq_zero.mp h0))
  · exact lt_irrefl ⊤ (Real.volume_Ioi ▸ hfin)

/-- A nonzero constant function has no Laplace transform at any `s` with `s.re ≤ 0`; in particular
`¬ HasLaplace (fun _ ↦ (1 : ℂ)) 0 0`. -/
theorem not_hasLaplace_const_of_re_le_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] {x : E} (hx : x ≠ 0) {s : ℂ} (hs : s.re ≤ 0) (z : E) :
    ¬ HasLaplace (fun _ : ℝ ↦ x) s z :=
  fun h ↦ not_laplaceConvergent_const_of_re_le_zero hx hs h.laplaceConvergent

/-- For `w.re < s.re`, the exponential `t ↦ exp (w * t)` has Laplace transform `1 / (s - w)`. -/
theorem hasLaplace_cexp {w s : ℂ} (hws : w.re < s.re) :
    HasLaplace (fun t : ℝ ↦ Complex.exp (w * t)) s (1 / (s - w)) := by
  have h := (hasLaplace_cexp_smul w (f := fun _ : ℝ ↦ (1 : ℂ))).mpr
    (hasLaplace_one (by simpa using sub_pos.mpr hws))
  simpa using h

/-- For every `k : ℕ` and `0 < s.re`, the monomial `t ↦ (t : ℂ) ^ k` is Laplace-convergent at `s`.
-/
theorem laplaceConvergent_pow (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    LaplaceConvergent (fun t : ℝ ↦ (t : ℂ) ^ k) s := by
  induction k generalizing s with
  | zero => simpa using (hasLaplace_one hs).laplaceConvergent
  | succ k ih =>
    have hs₀ : 0 < ((s.re / 2 : ℝ) : ℂ).re := by simpa using half_pos hs
    have hs₁ : ((s.re / 2 : ℝ) : ℂ).re < s.re := by simpa using half_lt_self hs
    refine (((ih hs₀).hasDerivAt_laplace hs₁).1.neg).congr_ae (.of_forall fun t ↦ ?_)
    simp [pow_succ']

/-- For every `k : ℕ` and `0 < s.re`, the monomial `t ↦ (t : ℂ) ^ k` has Laplace transform
`k! / s ^ (k + 1)`. -/
theorem hasLaplace_pow (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasLaplace (fun t : ℝ ↦ (t : ℂ) ^ k) s ((k.factorial : ℂ) / s ^ (k + 1)) := by
  induction k with
  | zero => simpa using hasLaplace_one hs
  | succ k ih =>
    have hf : HasLaplace (fun t : ℝ ↦ (t : ℂ) ^ (k + 1)) s
        (laplace (fun t : ℝ ↦ (t : ℂ) ^ (k + 1)) s) :=
      (laplaceConvergent_pow (k + 1) hs).hasLaplace
    have hf' : HasLaplace (fun t : ℝ ↦ ((k + 1 : ℕ) : ℂ) * (t : ℂ) ^ k) s
        (((k + 1 : ℕ) : ℂ) * ((k.factorial : ℂ) / s ^ (k + 1))) :=
      ih.const_smul ((k + 1 : ℕ) : ℂ)
    have hderiv : ∀ t ∈ Ioi (0 : ℝ),
        HasDerivAt (fun u : ℝ ↦ (u : ℂ) ^ (k + 1)) (((k + 1 : ℕ) : ℂ) * (t : ℂ) ^ k) t :=
      fun t _ ↦ by
        simpa only [Nat.add_sub_cancel] using (hasDerivAt_pow (k + 1) (t : ℂ)).comp_ofReal
    have hstep := hasLaplace_deriv
      (by fun_prop : Continuous fun u : ℝ ↦ (u : ℂ) ^ (k + 1)).continuousWithinAt
      hderiv hf hf'.integrable
    have heq := hstep.unique hf'
    simp only [Complex.ofReal_zero, zero_pow (Nat.succ_ne_zero k), sub_zero, smul_eq_mul] at heq
    have hs₀ : s ≠ 0 := fun h ↦ by simp [h] at hs
    rw [hasLaplace_iff]
    refine ⟨hf.laplaceConvergent, ?_⟩
    rw [Nat.factorial_succ, Nat.cast_mul]
    calc laplace (fun t : ℝ ↦ (t : ℂ) ^ (k + 1)) s
        = (s * laplace (fun t : ℝ ↦ (t : ℂ) ^ (k + 1)) s) / s :=
          (mul_div_cancel_left₀ _ hs₀).symm
      _ = (((k + 1 : ℕ) : ℂ) * ((k.factorial : ℂ) / s ^ (k + 1))) / s := by rw [heq]
      _ = ((k + 1 : ℕ) : ℂ) * (k.factorial : ℂ) / s ^ (k + 2) := by
          rw [mul_div_assoc', div_div, ← pow_succ]

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
