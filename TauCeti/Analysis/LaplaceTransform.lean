/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# One-sided Laplace transforms with complex parameter

This file develops the predicate `TauCeti.HasLaplace` for the ordinary one-sided Laplace transform
`∫₀^∞ e^(-s t) • f t dt = z` with complex parameter `s` and values in a normed space `E`,
bundling Bochner integrability of the integrand together with the value of the integral. Because the
Bochner integral of a non-integrable function is totalised to `0`, carrying integrability in the
predicate ensures that every Laplace assertion certifies genuine convergence.

The predicate's argument order, default measure `volume.restrict (Set.Ioi 0)`, and scalar-action
hypotheses follow Dennj Osele's draft `Mathlib/Analysis/LaplaceTransform.lean` (declarations
`LaplaceConvergent`, `laplace`, and `HasLaplace`).

## Main definitions and results

* `TauCeti.HasLaplace`: `f` has Laplace transform `z` at `s` with respect to `μ` (defaulting to
  Lebesgue measure on `(0, ∞)`).
* Algebraic and transformation rules: uniqueness (`HasLaplace.unique`), almost-everywhere
  congruence (`hasLaplace_congr`), zero, addition, negation, subtraction, finite sums, scalar
  multiplication (`HasLaplace.smul`, `HasLaplace.smul_const`), exponential frequency shifts
  (`HasLaplace.cexp_smul`), and positive time dilations (`HasLaplace.comp_mul_left`).
* Half-plane convergence and holomorphy: integrability propagates to the right half-plane
  (`integrableOn_cexp_neg_mul_smul_of_re_le`), and a Laplace transform on an open right half-plane
  is differentiable (`hasDerivAt_of_forall_hasLaplace`) with derivative given by multiplying `f` by
  `-t` (`hasLaplace_neg_smul_deriv_of_forall_hasLaplace`), hence analytic when `E` is complete
  (`analyticOnNhd_of_forall_hasLaplace`).
* Concrete transforms: the integer Gamma–Laplace model `t ↦ exp (c t) * t ^ k` has transform
  `k! / (s - c) ^ (k + 1)` on `Re c < Re s` (`hasLaplace_cexp_mul_pow`, with real-cast form
  `hasLaplace_ofReal_exp_mul_pow`), together with the exact convergence characterisations for
  vector-valued exponentials (`hasLaplace_cexp_smul_iff`), scalar exponentials
  (`hasLaplace_cexp_iff`), and nonzero constants (`hasLaplace_const_iff`).
* Transform of a derivative: in a complex Banach space, `hasLaplace_deriv_of_primitive` proves
  `HasLaplace g s (s • z - f 0)` whenever `f` is a primitive of `g` on `[0, ∞)`, `HasLaplace f s z`,
  and `e^(-s t) • g t` is integrable on `(0, ∞)`, with no restriction on `Re s` and no exponential
  growth bound; `hasLaplace_deriv` deduces the differentiable form via the fundamental theorem of
  calculus.

## References

* H. Delange, *Généralisation du théorème de Ikehara*, Ann. Sci. École Norm. Sup. (3) **71**
  (1954), 213–242 (standing Laplace-transform hypotheses, p. 213).
* J. Lebl, *Notes on Diffy Qs: Differential Equations for Engineers*, version 6.11 (2026),
  §6.2.1, p. 300 (the derivative rule under exponential order; generalized here to Banach-space
  primitives with only integrability hypotheses).
* D. Osele, *The Laplace transform* (2026),
  <https://github.com/dennj/mathlib4/blob/90482cd37e85e423459de2ed103cea2f4d98cb20/Mathlib/Analysis/LaplaceTransform.lean#L121-L123>
  (`LaplaceConvergent`, `laplace`, and `HasLaplace`).
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace TauCeti

section Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `HasLaplace f s z μ`: the integrand `t ↦ exp (-s * t) • f t` is integrable with respect to `μ`
and its Bochner integral equals `z`. With the default measure `volume.restrict (Ioi 0)` this is
the ordinary one-sided Laplace transform of `f` at the complex parameter `s`. -/
def HasLaplace [SMul ℂ E] (f : ℝ → E) (s : ℂ) (z : E)
    (μ : Measure ℝ := volume.restrict (Ioi 0)) : Prop :=
  Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ ∧
    ∫ t : ℝ, Complex.exp (-s * t) • f t ∂μ = z

/-- Unfolding characterization of `HasLaplace`. -/
theorem hasLaplace_iff [SMul ℂ E] {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ} :
    HasLaplace f s z μ ↔
      Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ ∧
        ∫ t : ℝ, Complex.exp (-s * t) • f t ∂μ = z :=
  Iff.rfl

/-- Introduction rule for `HasLaplace`. -/
theorem HasLaplace.mk [SMul ℂ E] {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (hint : Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ)
    (heq : ∫ t : ℝ, Complex.exp (-s * t) • f t ∂μ = z) :
    HasLaplace f s z μ :=
  hasLaplace_iff.mpr ⟨hint, heq⟩

/-- A function with a Laplace transform has an integrable Laplace integrand. -/
theorem HasLaplace.integrable [SMul ℂ E] {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (h : HasLaplace f s z μ) :
    Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ :=
  (hasLaplace_iff.mp h).1

/-- The Laplace integral equals the value recorded by `HasLaplace`. -/
theorem HasLaplace.integral_eq [SMul ℂ E] {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (h : HasLaplace f s z μ) :
    ∫ t : ℝ, Complex.exp (-s * t) • f t ∂μ = z :=
  (hasLaplace_iff.mp h).2

/-- The Laplace transform value at a given parameter and measure is unique. -/
theorem HasLaplace.unique [SMul ℂ E] {f : ℝ → E} {s : ℂ} {z z' : E} {μ : Measure ℝ}
    (h : HasLaplace f s z μ) (h' : HasLaplace f s z' μ) : z = z' :=
  h.integral_eq.symm.trans h'.integral_eq

/-- Functions that agree almost everywhere have the same Laplace transform. -/
theorem hasLaplace_congr [SMul ℂ E] {f g : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (hfg : f =ᵐ[μ] g) : HasLaplace f s z μ ↔ HasLaplace g s z μ := by
  have heq : (fun t : ℝ ↦ Complex.exp (-s * t) • f t) =ᵐ[μ]
      fun t : ℝ ↦ Complex.exp (-s * t) • g t :=
    hfg.mono fun _ ht ↦ by dsimp only; rw [ht]
  rw [hasLaplace_iff, hasLaplace_iff, integrable_congr heq, integral_congr_ae heq]

/-- Transport `HasLaplace` along almost-everywhere equality. -/
theorem HasLaplace.congr [SMul ℂ E] {f g : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (h : HasLaplace f s z μ) (hfg : f =ᵐ[μ] g) : HasLaplace g s z μ :=
  (hasLaplace_congr hfg).mp h

/-- The zero function has Laplace transform `0` at every complex parameter and measure. -/
theorem hasLaplace_zero [SMulZeroClass ℂ E] (s : ℂ) (μ : Measure ℝ := volume.restrict (Ioi 0)) :
    HasLaplace (0 : ℝ → E) s 0 μ :=
  HasLaplace.mk (by simp) (by simp)

/-- The zero function has Laplace transform `z` if and only if `z = 0`. -/
@[simp]
theorem hasLaplace_zero_iff [SMulZeroClass ℂ E] {s : ℂ} {z : E} {μ : Measure ℝ} :
    HasLaplace (0 : ℝ → E) s z μ ↔ z = 0 :=
  ⟨fun h ↦ h.unique (hasLaplace_zero s μ), fun hz ↦ hz ▸ hasLaplace_zero s μ⟩

/-- Additivity of the Laplace transform. -/
theorem HasLaplace.add [DistribSMul ℂ E] {f g : ℝ → E} {s : ℂ} {z w : E} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) (hg : HasLaplace g s w μ) :
    HasLaplace (f + g) s (z + w) μ := by
  refine HasLaplace.mk ?_ ?_
  · exact (hf.integrable.add hg.integrable).congr (.of_forall fun _ ↦ (smul_add ..).symm)
  · simp only [Pi.add_apply, smul_add]
    rw [integral_add hf.integrable hg.integrable, hf.integral_eq, hg.integral_eq]

/-- Negation of a function negates its Laplace transform. -/
theorem HasLaplace.neg [DistribSMul ℂ E] {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) : HasLaplace (-f) s (-z) μ := by
  refine HasLaplace.mk ?_ ?_
  · exact hf.integrable.neg.congr (.of_forall fun _ ↦ (smul_neg ..).symm)
  · simp only [Pi.neg_apply, smul_neg, integral_neg, hf.integral_eq]

/-- Subtraction of Laplace transforms. -/
theorem HasLaplace.sub [DistribSMul ℂ E] {f g : ℝ → E} {s : ℂ} {z w : E} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) (hg : HasLaplace g s w μ) :
    HasLaplace (f - g) s (z - w) μ := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- Finite additivity of the Laplace transform. -/
theorem hasLaplace_sum [DistribSMul ℂ E] {ι : Type*} (u : Finset ι) {f : ι → ℝ → E}
    {s : ℂ} {z : ι → E} {μ : Measure ℝ} (hf : ∀ i ∈ u, HasLaplace (f i) s (z i) μ) :
    HasLaplace (∑ i ∈ u, f i) s (∑ i ∈ u, z i) μ := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert a u ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a u)).add
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- Scalar multiplication commutes with the Laplace transform for any commuting normed ring `R`
(in particular `ℂ` and `ℝ`). -/
theorem HasLaplace.smul [SMul ℂ E] {R : Type*} [NormedRing R] [Module R E] [IsBoundedSMul R E]
    [SMulCommClass ℝ R E] [SMulCommClass ℂ R E] {f : ℝ → E} {s : ℂ} {z : E} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) (c : R) :
    HasLaplace (fun t : ℝ ↦ c • f t) s (c • z) μ := by
  refine HasLaplace.mk ?_ ?_
  · exact (hf.integrable.smul c).congr (.of_forall fun _ ↦ (smul_comm ..).symm)
  · simp_rw [smul_comm (Complex.exp (-s * _)) c]
    rw [hf.integrable.integral_smul c, hf.integral_eq]

/-- **Frequency shift**: multiplying `f` by `exp (c t)` shifts the Laplace parameter from `s - c`
to `s`. -/
theorem HasLaplace.cexp_smul [MulAction ℂ E] {f : ℝ → E} {c s : ℂ} {z : E} {μ : Measure ℝ}
    (hf : HasLaplace f (s - c) z μ) :
    HasLaplace (fun t : ℝ ↦ Complex.exp (c * t) • f t) s z μ := by
  have heq : (fun t : ℝ ↦ Complex.exp (-s * t) • (Complex.exp (c * t) • f t)) =
      fun t : ℝ ↦ Complex.exp (-(s - c) * t) • f t := by
    ext t
    rw [smul_smul, ← Complex.exp_add]
    congr 2
    ring
  exact HasLaplace.mk (heq ▸ hf.integrable) (heq ▸ hf.integral_eq)

/-- **Positive time dilation**: for `0 < c`, scaling the time variable by `c` divides the Laplace
parameter by `c` and scales the transform by `c⁻¹`. -/
theorem HasLaplace.comp_mul_left [MulAction ℂ E] [IsScalarTower ℝ ℂ E]
    {f : ℝ → E} {s : ℂ} {z : E} {c : ℝ} (hf : HasLaplace f (s / c) z) (hc : 0 < c) :
    HasLaplace (fun t : ℝ ↦ f (c * t)) s ((c : ℂ)⁻¹ • z) := by
  have hce : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  set g : ℝ → E := fun u : ℝ ↦ Complex.exp (-(s / c) * u) • f u
  have hcomp : (fun t : ℝ ↦ Complex.exp (-s * t) • f (c * t)) = fun t : ℝ ↦ g (c * t) := by
    ext t
    dsimp only [g]
    congr 2
    push_cast
    field_simp [hce]
  have hgi : IntegrableOn g (Ioi (c * 0)) volume := by
    rw [mul_zero]
    exact hf.integrable
  refine HasLaplace.mk ?_ ?_
  · rw [hcomp]
    exact (integrableOn_Ioi_comp_mul_left_iff g 0 hc).mpr hgi
  · rw [hcomp, integral_comp_mul_left_Ioi g 0 hc, mul_zero, hf.integral_eq,
      ← Complex.ofReal_inv, ← mul_one ((c⁻¹ : ℝ) : ℂ), ← Complex.real_smul, smul_assoc, one_smul]

end Basic

/-- Scaling a complex-valued function by a fixed vector in a complex Banach space scales its
Laplace transform by the same vector. -/
theorem HasLaplace.smul_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℝ → ℂ} {s z : ℂ} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) (a : E) :
    HasLaplace (fun t : ℝ ↦ f t • a) s (z • a) μ := by
  refine HasLaplace.mk ?_ ?_
  · exact (hf.integrable.smul_const a).congr (.of_forall fun _ ↦ smul_assoc ..)
  · simp_rw [← smul_assoc]
    rw [integral_smul_const, hf.integral_eq]

section HalfPlane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private lemma cexp_neg_mul_smul_factor (s₀ w : ℂ) (t : ℝ) (x : E) :
    Complex.exp (-w * t) • x = Complex.exp (-(w - s₀) * t) • (Complex.exp (-s₀ * t) • x) := by
  rw [smul_smul, ← Complex.exp_add]
  congr 2
  ring

/-- Multiplying an integrable Laplace integrand on `(0, ∞)` by `exp (-(s - s₀) t)` with
`Re s₀ ≤ Re s` preserves integrability: Laplace convergence propagates to the right half-plane. -/
theorem integrableOn_cexp_neg_mul_smul_of_re_le {f : ℝ → E} {s₀ s : ℂ}
    (hf : Integrable (fun t : ℝ ↦ Complex.exp (-s₀ * t) • f t) (volume.restrict (Ioi 0)))
    (hs : s₀.re ≤ s.re) :
    Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) (volume.restrict (Ioi 0)) := by
  simp_rw [cexp_neg_mul_smul_factor s₀ s]
  refine Integrable.mono' hf.norm
    ((by fun_prop : Continuous fun t : ℝ ↦ Complex.exp (-(s - s₀) * t)).aestronglyMeasurable.smul
      hf.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_smul, Complex.norm_exp, Complex.re_mul_ofReal, Complex.neg_re, Complex.sub_re]
  have hexp : Real.exp (-(s.re - s₀.re) * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Set.mem_Ioi.mp ht])
  exact mul_le_of_le_one_left (norm_nonneg _) hexp

/-- If `f` has a Laplace transform at `s₀` on `(0, ∞)`, its Laplace integrand remains integrable at
every `s` with `Re s₀ ≤ Re s`. -/
theorem HasLaplace.integrable_of_re_le {f : ℝ → E} {s₀ s : ℂ} {z : E}
    (hf : HasLaplace f s₀ z) (hs : s₀.re ≤ s.re) :
    Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) (volume.restrict (Ioi 0)) :=
  integrableOn_cexp_neg_mul_smul_of_re_le hf.integrable hs

/-- Strictly to the right of a point of convergence `s₀`, multiplying `f` by any natural power
`t ^ k` preserves integrability of the Laplace integrand on `(0, ∞)`. -/
theorem integrableOn_cexp_neg_mul_ofReal_pow_smul_of_re_lt {f : ℝ → E} {s₀ s : ℂ}
    (hf : Integrable (fun t : ℝ ↦ Complex.exp (-s₀ * t) • f t) (volume.restrict (Ioi 0)))
    (hs : s₀.re < s.re) (k : ℕ) :
    Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • ((t : ℂ) ^ k • f t))
      (volume.restrict (Ioi 0)) := by
  obtain ⟨M, _, hM⟩ := exists_rpow_mul_exp_neg_mul_le (σ := (k : ℝ)) (c := s.re - s₀.re)
    (Nat.cast_nonneg k) (sub_pos.mpr hs)
  have hre : (fun t : ℝ ↦ Complex.exp (-s * t) • ((t : ℂ) ^ k • f t)) =
      fun t : ℝ ↦ (Complex.exp (-(s - s₀) * t) * (t : ℂ) ^ k) • (Complex.exp (-s₀ * t) • f t) := by
    ext t
    rw [smul_comm, cexp_neg_mul_smul_factor s₀ s, smul_comm, smul_smul]
  rw [hre]
  refine Integrable.mono' (hf.norm.const_mul M)
    ((by fun_prop : Continuous fun t : ℝ ↦
      Complex.exp (-(s - s₀) * t) * (t : ℂ) ^ k).aestronglyMeasurable.smul
      hf.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := (Set.mem_Ioi.mp ht).le
  rw [norm_smul, norm_mul, Complex.norm_exp, Complex.re_mul_ofReal, Complex.neg_re, Complex.sub_re,
    norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0]
  have hb : Real.exp (-(s.re - s₀.re) * t) * t ^ k ≤ M := by
    simpa only [Real.rpow_natCast, mul_comm, neg_mul, mul_neg] using hM t ht0
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

/-- **Differentiation under the Laplace integral**: if `t ↦ exp (-s₀ t) • f t` is integrable on
`(0, ∞)` and `Re s₀ < Re s`, then `w ↦ ∫ t in Ioi 0, exp (-w t) • f t` is complex differentiable
at `s` with derivative `∫ t in Ioi 0, exp (-s t) • (-(t : ℂ) • f t)`. -/
theorem hasDerivAt_integral_cexp_neg_mul_smul {f : ℝ → E} {s₀ s : ℂ}
    (hf : Integrable (fun t : ℝ ↦ Complex.exp (-s₀ * t) • f t) (volume.restrict (Ioi 0)))
    (hs : s₀.re < s.re) :
    HasDerivAt (fun w : ℂ ↦ ∫ t in Ioi (0 : ℝ), Complex.exp (-w * t) • f t)
      (∫ t in Ioi (0 : ℝ), Complex.exp (-s * t) • (-(t : ℂ) • f t)) s := by
  set δ : ℝ := (s.re - s₀.re) / 2 with hδ_def
  have hδ : 0 < δ := half_pos (sub_pos.mpr hs)
  obtain ⟨M, _, hM⟩ := exists_rpow_mul_exp_neg_mul_le (σ := 1) (c := δ) zero_le_one hδ
  have hmeas_w : ∀ w : ℂ,
      AEStronglyMeasurable (fun t : ℝ ↦ Complex.exp (-w * t) • f t) (volume.restrict (Ioi 0)) := by
    intro w
    simp_rw [cexp_neg_mul_smul_factor s₀ w]
    exact (by fun_prop : Continuous fun t : ℝ ↦
      Complex.exp (-(w - s₀) * t)).aestronglyMeasurable.smul hf.aestronglyMeasurable
  have hmeas_deriv : AEStronglyMeasurable
      (fun t : ℝ ↦ Complex.exp (-s * t) • (-(t : ℂ) • f t)) (volume.restrict (Ioi 0)) := by
    have heq : (fun t : ℝ ↦ Complex.exp (-s * t) • (-(t : ℂ) • f t)) =
        fun t : ℝ ↦ (-(t : ℂ) * Complex.exp (-(s - s₀) * t)) • (Complex.exp (-s₀ * t) • f t) := by
      ext t
      rw [smul_comm, cexp_neg_mul_smul_factor s₀ s, smul_smul]
    rw [heq]
    exact (by fun_prop : Continuous fun t : ℝ ↦
      -(t : ℂ) * Complex.exp (-(s - s₀) * t)).aestronglyMeasurable.smul hf.aestronglyMeasurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0))
    (F := fun w (t : ℝ) ↦ Complex.exp (-w * t) • f t)
    (F' := fun w (t : ℝ) ↦ Complex.exp (-w * t) • (-(t : ℂ) • f t))
    (bound := fun t : ℝ ↦ M * ‖Complex.exp (-s₀ * t) • f t‖)
    (Metric.ball_mem_nhds s hδ) (.of_forall hmeas_w)
    (integrableOn_cexp_neg_mul_smul_of_re_le hf hs.le)
    hmeas_deriv ?_ (hf.norm.const_mul M) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    have ht0 : 0 ≤ t := (Set.mem_Ioi.mp ht).le
    have hwre : s₀.re + δ < w.re := by
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have h1 := (abs_lt.mp ((Complex.abs_re_le_norm (w - s)).trans_lt hw)).1
      rw [Complex.sub_re] at h1
      linarith
    rw [smul_comm, cexp_neg_mul_smul_factor s₀ w, smul_smul, norm_smul, norm_mul, norm_neg,
      Complex.norm_real, Real.norm_of_nonneg ht0, Complex.norm_exp, Complex.re_mul_ofReal,
      Complex.neg_re, Complex.sub_re]
    have hle : -(w.re - s₀.re) * t ≤ -(δ * t) := by nlinarith
    have hb : t * Real.exp (-(w.re - s₀.re) * t) ≤ M :=
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) ht0).trans <| by
        simpa only [Real.rpow_one] using hM t ht0
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  · filter_upwards with t w _
    have h1 : HasDerivAt (fun w : ℂ ↦ Complex.exp (-w * t))
        (Complex.exp (-w * t) * -(t : ℂ)) w := by
      simpa using ((hasDerivAt_id' w).neg.mul_const (t : ℂ)).cexp
    simpa only [smul_smul] using h1.smul_const (f t)

/-- If `F` is the Laplace transform of `f` on the open half-plane `Re s > a`, then `F` is complex
differentiable at every `s` with `Re s > a`, with derivative
`∫ t in Ioi 0, exp (-s t) • (-(t : ℂ) • f t)`. -/
theorem hasDerivAt_of_forall_hasLaplace {f : ℝ → E} {F : ℂ → E} {a : ℝ}
    (hF : ∀ w : ℂ, a < w.re → HasLaplace f w (F w)) {s : ℂ} (hs : a < s.re) :
    HasDerivAt F (∫ t in Ioi (0 : ℝ), Complex.exp (-s * t) • (-(t : ℂ) • f t)) s := by
  set σ₀ : ℝ := (a + s.re) / 2 with hσ₀_def
  have hσ₀a : a < σ₀ := by linarith
  have hσ₀s : σ₀ < s.re := by linarith
  have h0 : Integrable (fun t : ℝ ↦ Complex.exp (-(σ₀ : ℂ) * t) • f t)
      (volume.restrict (Ioi 0)) :=
    (hF σ₀ (by simpa using hσ₀a)).integrable
  have hd := hasDerivAt_integral_cexp_neg_mul_smul h0 (by simpa using hσ₀s)
  refine hd.congr_of_eventuallyEq ?_
  have hmem : {w : ℂ | a < w.re} ∈ 𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  filter_upwards [hmem] with w hw
  exact (hF w hw).integral_eq.symm

/-- If `F` is the Laplace transform of `f` on `Re s > a`, then `t ↦ -(t : ℂ) • f t` has Laplace
transform `deriv F s` at every `s` with `Re s > a`. -/
theorem hasLaplace_neg_smul_deriv_of_forall_hasLaplace {f : ℝ → E} {F : ℂ → E} {a : ℝ}
    (hF : ∀ w : ℂ, a < w.re → HasLaplace f w (F w)) {s : ℂ} (hs : a < s.re) :
    HasLaplace (fun t : ℝ ↦ -(t : ℂ) • f t) s (deriv F s) := by
  set σ₀ : ℝ := (a + s.re) / 2 with hσ₀_def
  have h0 : Integrable (fun t : ℝ ↦ Complex.exp (-(σ₀ : ℂ) * t) • f t)
      (volume.restrict (Ioi 0)) :=
    (hF σ₀ (by simp only [Complex.ofReal_re]; linarith)).integrable
  have hint : Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • (-(t : ℂ) • f t))
      (volume.restrict (Ioi 0)) := by
    have h1 := (integrableOn_cexp_neg_mul_ofReal_pow_smul_of_re_lt h0
      (by simp only [Complex.ofReal_re]; linarith) 1).neg
    exact h1.congr (.of_forall fun t ↦ by simp only [Pi.neg_apply, pow_one, neg_smul, smul_neg])
  exact HasLaplace.mk hint (hasDerivAt_of_forall_hasLaplace hF hs).deriv.symm

/-- In a complex Banach space, a Laplace transform on the open half-plane `Re s > a` is analytic
there. -/
theorem analyticOnNhd_of_forall_hasLaplace [CompleteSpace E] {f : ℝ → E} {F : ℂ → E} {a : ℝ}
    (hF : ∀ w : ℂ, a < w.re → HasLaplace f w (F w)) :
    AnalyticOnNhd ℂ F {s : ℂ | a < s.re} :=
  DifferentiableOn.analyticOnNhd
    (fun _ hs ↦ (hasDerivAt_of_forall_hasLaplace hF hs).differentiableAt.differentiableWithinAt)
    (isOpen_lt continuous_const Complex.continuous_re)

end HalfPlane

section Examples

/-- **Integer Gamma–Laplace model**: for `k : ℕ` and `Re c < Re s`, the function
`t ↦ exp (c * t) * t ^ k` has Laplace transform `k! / (s - c) ^ (k + 1)`. -/
theorem hasLaplace_cexp_mul_pow (k : ℕ) {c s : ℂ} (hs : c.re < s.re) :
    HasLaplace (fun t : ℝ ↦ Complex.exp (c * t) * (t : ℂ) ^ k) s
      ((k.factorial : ℂ) / (s - c) ^ (k + 1)) := by
  have hk : 0 < ((k + 1 : ℕ) : ℂ).re := by
    simp only [Nat.cast_add, Nat.cast_one, Complex.add_re, Complex.natCast_re, Complex.one_re]
    positivity
  have hsc : 0 < (s - c).re := by simpa using sub_pos.mpr hs
  have hfun : EqOn (fun t : ℝ ↦ Complex.exp (-s * t) • (Complex.exp (c * t) * (t : ℂ) ^ k))
      (fun t : ℝ ↦ (t : ℂ) ^ (((k + 1 : ℕ) : ℂ) - 1) * Complex.exp (-((s - c) * t))) (Ioi 0) := by
    intro t _
    simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Complex.cpow_natCast]
    rw [← mul_assoc, ← Complex.exp_add, mul_comm]
    congr 2
    ring
  refine HasLaplace.mk ?_ ?_
  · exact (Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi hk hsc).congr_fun
      (fun t ht ↦ (hfun ht).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi hfun,
      Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hk hsc,
      Complex.cpow_neg, Complex.cpow_natCast, Nat.cast_add, Nat.cast_one,
      Complex.Gamma_nat_eq_factorial, div_eq_mul_inv]

/-- Real-cast form of the integer Gamma–Laplace model: for `a : ℝ`, `k : ℕ`, and `a < Re s`,
`t ↦ ((Real.exp (a * t) * t ^ k : ℝ) : ℂ)` has Laplace transform `k! / (s - a) ^ (k + 1)`. -/
theorem hasLaplace_ofReal_exp_mul_pow (k : ℕ) {a : ℝ} {s : ℂ} (hs : a < s.re) :
    HasLaplace (fun t : ℝ ↦ ((Real.exp (a * t) * t ^ k : ℝ) : ℂ)) s
      ((k.factorial : ℂ) / (s - a) ^ (k + 1)) := by
  simpa only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_pow] using
    hasLaplace_cexp_mul_pow k (c := (a : ℂ)) (by simpa using hs)

/-- For `k : ℕ` and `0 < Re s`, `t ↦ (t : ℂ) ^ k` has Laplace transform `k! / s ^ (k + 1)`. -/
theorem hasLaplace_pow (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasLaplace (fun t : ℝ ↦ (t : ℂ) ^ k) s ((k.factorial : ℂ) / s ^ (k + 1)) := by
  simpa using hasLaplace_cexp_mul_pow k (c := 0) (by simpa using hs)

/-- For `Re c < Re s`, `t ↦ exp (c * t)` has Laplace transform `(s - c)⁻¹`. -/
theorem hasLaplace_cexp {c s : ℂ} (hs : c.re < s.re) :
    HasLaplace (fun t : ℝ ↦ Complex.exp (c * t)) s (s - c)⁻¹ := by
  simpa using hasLaplace_cexp_mul_pow 0 hs

/-- For `Re s ≤ Re c` and `a ≠ 0`, `t ↦ exp (c * t) • a` has no Laplace transform at `s` on
`(0, ∞)`. -/
theorem not_hasLaplace_cexp_smul_of_re_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MulAction ℂ E] [NormSMulClass ℂ E] {a : E} (ha : a ≠ 0) {c s : ℂ} (hs : s.re ≤ c.re) (z : E) :
    ¬ HasLaplace (fun t : ℝ ↦ Complex.exp (c * t) • a) s z := by
  intro h
  refine TauCeti.MeasureTheory.not_integrableOn_Ioi_of_eventually_le_norm
    (norm_pos_iff.mpr ha) 0 ?_ h.integrable
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have heq : Complex.exp (-s * t) • (Complex.exp (c * t) • a) = Complex.exp ((c - s) * t) • a := by
    rw [smul_smul, ← Complex.exp_add]
    congr 2
    ring
  rw [heq, norm_smul, Complex.norm_exp, Complex.re_mul_ofReal, Complex.sub_re]
  have h1 : 1 ≤ Real.exp ((c.re - s.re) * t) :=
    Real.one_le_exp (mul_nonneg (sub_nonneg.mpr hs) ht)
  simpa using mul_le_mul_of_nonneg_right h1 (norm_nonneg a)

/-- Exact characterization of the Laplace transform of `t ↦ exp (c * t) • a` for nonzero `a` in a
complex Banach space. -/
theorem hasLaplace_cexp_smul_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {a : E} (ha : a ≠ 0) {c s : ℂ} {z : E} :
    HasLaplace (fun t : ℝ ↦ Complex.exp (c * t) • a) s z ↔ c.re < s.re ∧ (s - c)⁻¹ • a = z := by
  refine ⟨fun h ↦ ?_, fun ⟨hs, hz⟩ ↦ hz ▸ (hasLaplace_cexp hs).smul_const a⟩
  have hs : c.re < s.re := by
    by_contra hle
    exact not_hasLaplace_cexp_smul_of_re_le ha (not_lt.mp hle) z h
  exact ⟨hs, ((hasLaplace_cexp hs).smul_const a).unique h⟩

/-- Exact characterization of the Laplace transform of `t ↦ exp (c * t)` on `(0, ∞)`. -/
theorem hasLaplace_cexp_iff {c s z : ℂ} :
    HasLaplace (fun t : ℝ ↦ Complex.exp (c * t)) s z ↔ c.re < s.re ∧ (s - c)⁻¹ = z := by
  simpa using hasLaplace_cexp_smul_iff (a := (1 : ℂ)) one_ne_zero (c := c) (s := s) (z := z)

/-- In a complex Banach space, the constant function `a` has Laplace transform `s⁻¹ • a` for
`0 < Re s`. -/
theorem hasLaplace_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (a : E) {s : ℂ} (hs : 0 < s.re) :
    HasLaplace (fun _ : ℝ ↦ a) s (s⁻¹ • a) := by
  simpa using (hasLaplace_cexp (c := 0) (by simpa using hs)).smul_const a

/-- Exact characterization of the Laplace transform of a nonzero constant function on `(0, ∞)`. -/
theorem hasLaplace_const_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {a : E} (ha : a ≠ 0) {s : ℂ} {z : E} :
    HasLaplace (fun _ : ℝ ↦ a) s z ↔ 0 < s.re ∧ s⁻¹ • a = z := by
  simpa using hasLaplace_cexp_smul_iff ha (c := 0) (s := s) (z := z)

end Examples

section Deriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- If `t ↦ exp (-s t) • g t` is integrable on `(0, ∞)`, then `g` is interval integrable on
`[a, b]` for all `0 ≤ a` and `0 ≤ b`. -/
theorem intervalIntegrable_of_integrableOn_cexp_neg_mul_smul {g : ℝ → E} {s : ℂ}
    (hg : Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • g t) (volume.restrict (Ioi 0)))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable g volume a b := by
  have hsub : uIoc a b ⊆ Ioi 0 :=
    Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (le_min ha hb))
  have hint : IntervalIntegrable (fun t : ℝ ↦ Complex.exp (-s * t) • g t) volume a b :=
    intervalIntegrable_iff.mpr (IntegrableOn.mono_set hg hsub)
  have hmul := hint.continuousOn_smul
    (by fun_prop : Continuous fun t : ℝ ↦ Complex.exp (s * t)).continuousOn
  refine hmul.congr fun t _ ↦ ?_
  rw [smul_smul, ← Complex.exp_add]
  simp

/-- **Finite-horizon integration by parts for the Laplace kernel** (primitive form): if
`f t = f 0 + ∫ u in 0..t, g u` on `[0, T]` with `g` interval integrable on `[0, T]`, then
`∫ t in 0..T, exp (-s t) • g t = exp (-s T) • f T - f 0 + s • ∫ t in 0..T, exp (-s t) • f t`. -/
theorem intervalIntegral_cexp_neg_mul_smul_of_primitive [CompleteSpace E] {f g : ℝ → E} (s : ℂ)
    {T : ℝ} (hT : 0 ≤ T) (hfg : ∀ t ∈ Icc (0 : ℝ) T, f t = f 0 + ∫ u in (0 : ℝ)..t, g u)
    (hg : IntervalIntegrable g volume 0 T) :
    ∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • g t =
      Complex.exp (-s * T) • f T - f 0 + s • ∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • f t := by
  let φ : ℝ → ℂ := fun t : ℝ ↦ Complex.exp (-s * t)
  have hφ_deriv : ∀ t : ℝ, HasDerivAt φ (-s * Complex.exp (-s * t)) t := fun t ↦ by
    simpa [φ, mul_comm] using (((hasDerivAt_id' t).ofReal_comp).const_mul (-s)).cexp
  have hφ_cd : ContDiff ℝ 1 φ :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  have hibp := TauCeti.intervalIntegral.integral_deriv_smul_primitive_eq_sub_of_le hT hφ_cd hg
  have hf_sub : ∀ t ∈ uIcc (0 : ℝ) T, ∫ u in (0 : ℝ)..t, g u = f t - f 0 := fun t ht ↦
    eq_sub_of_add_eq' (hfg t (uIcc_of_le hT ▸ ht)).symm
  have hfT : ∫ u in (0 : ℝ)..T, g u = f T - f 0 := hf_sub T right_mem_uIcc
  have hderiv_eq : ∀ t : ℝ, deriv φ t = -s * Complex.exp (-s * t) := fun t ↦ (hφ_deriv t).deriv
  have hf_cont : ContinuousOn f (uIcc (0 : ℝ) T) := by
    rw [uIcc_of_le hT]
    exact (continuousOn_const.add
      ((intervalIntegral.continuousOn_primitive_interval' hg
        (by rw [uIcc_of_le hT]; exact left_mem_Icc.mpr hT)).mono
        (by rw [uIcc_of_le hT]))).congr hfg
  have h1_int : IntervalIntegrable (fun t : ℝ ↦ (-s * Complex.exp (-s * t)) • f t) volume 0 T :=
    hf_cont.intervalIntegrable.continuousOn_smul
      (by fun_prop : Continuous fun t : ℝ ↦ -s * Complex.exp (-s * t)).continuousOn
  have h0_int : IntervalIntegrable (fun t : ℝ ↦ (-s * Complex.exp (-s * t)) • f 0) volume 0 T :=
    (by fun_prop : Continuous fun t : ℝ ↦ (-s * Complex.exp (-s * t)) • f 0).intervalIntegrable _ _
  have hlhs : ∫ t in (0 : ℝ)..T, deriv φ t • ∫ u in (0 : ℝ)..t, g u =
      -s • (∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • f t) -
        (Complex.exp (-s * T) - 1) • f 0 := by
    have hcongr : EqOn (fun t : ℝ ↦ deriv φ t • ∫ u in (0 : ℝ)..t, g u)
        (fun t : ℝ ↦ (-s * Complex.exp (-s * t)) • f t - (-s * Complex.exp (-s * t)) • f 0)
        (uIcc 0 T) := fun t ht ↦ by
      dsimp only
      rw [hderiv_eq, hf_sub t ht, smul_sub]
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_sub h1_int h0_int]
    congr 1
    · simp_rw [mul_smul, intervalIntegral.integral_smul]
    · rw [intervalIntegral.integral_smul_const,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hφ_deriv t)
          ((by fun_prop : Continuous fun t : ℝ ↦ -s * Complex.exp (-s * t)).intervalIntegrable 0 T)]
      simp [φ]
  rw [hlhs, hfT, smul_sub] at hibp
  dsimp only [φ] at hibp
  have hres : ∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • g t =
      Complex.exp (-s * T) • f T - Complex.exp (-s * T) • f 0 -
        (-s • (∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • f t) -
          (Complex.exp (-s * T) - 1) • f 0) := by
    rw [hibp]
    abel
  rw [hres, sub_smul, one_smul, neg_smul]
  abel

/-- **Transform of a derivative (primitive form)**: if `f` is a primitive of `g` on `[0, ∞)`,
`f` has Laplace transform `z` at `s`, and `t ↦ exp (-s t) • g t` is integrable on `(0, ∞)`, then
`g` has Laplace transform `s • z - f 0` at `s`. No condition on `Re s` and no exponential growth
bound on `f` are required. -/
theorem hasLaplace_deriv_of_primitive [CompleteSpace E] {f g : ℝ → E} {s : ℂ} {z : E}
    (hfg : ∀ t ∈ Ici (0 : ℝ), f t = f 0 + ∫ u in (0 : ℝ)..t, g u)
    (hf : HasLaplace f s z)
    (hg : Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • g t) (volume.restrict (Ioi 0))) :
    HasLaplace g s (s • z - f 0) := by
  have hlim_g : Tendsto (fun T : ℝ ↦ ∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • g t) atTop
      (𝓝 (∫ t in Ioi (0 : ℝ), Complex.exp (-s * t) • g t)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hg tendsto_id
  have hlim_f : Tendsto (fun T : ℝ ↦ ∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • f t) atTop
      (𝓝 z) := by
    rw [← hf.integral_eq]
    exact intervalIntegral_tendsto_integral_Ioi 0 hf.integrable tendsto_id
  -- Rearranging the finite-horizon identity shows `exp (-s T) • f T` tends to a limit `L`.
  set L : E := (∫ t in Ioi (0 : ℝ), Complex.exp (-s * t) • g t) + f 0 - s • z
  have hlim_bdry : Tendsto (fun T : ℝ ↦ Complex.exp (-s * T) • f T) atTop (𝓝 L) := by
    have hlim_rhs : Tendsto (fun T : ℝ ↦
        (∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • g t) + f 0 -
          s • ∫ t in (0 : ℝ)..T, Complex.exp (-s * t) • f t) atTop (𝓝 L) :=
      (hlim_g.add_const (f 0)).sub (hlim_f.const_smul s)
    refine hlim_rhs.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    have hibp := intervalIntegral_cexp_neg_mul_smul_of_primitive s hT
      (fun t ht ↦ hfg t ht.1) (intervalIntegrable_of_integrableOn_cexp_neg_mul_smul hg le_rfl hT)
    rw [hibp]
    abel
  -- Since `t ↦ exp (-s t) • f t` is integrable on `(0, ∞)`, its limit `L` at `+∞` must vanish.
  have hL : L = 0 := by
    refine IntegrableAtFilter.eq_zero_of_tendsto
      ⟨Ioi (0 : ℝ), Ioi_mem_atTop 0, hf.integrable⟩ ?_ hlim_bdry
    intro u hu
    obtain ⟨b, hb⟩ := mem_atTop_sets.mp hu
    rw [← top_le_iff, ← Real.volume_Ici (a := b)]
    exact measure_mono hb
  refine HasLaplace.mk hg ?_
  have hL' : (∫ t in Ioi (0 : ℝ), Complex.exp (-s * t) • g t) + f 0 - s • z = 0 := hL
  rw [sub_eq_zero] at hL'
  exact eq_sub_of_add_eq hL'

/-- **Transform of a derivative**: for `f` continuous from the right at `0` and differentiable on
`(0, ∞)`, if `f` has Laplace transform `z` at `s` and `t ↦ exp (-s t) • f' t` is integrable on
`(0, ∞)`, then `f'` has Laplace transform `s • z - f 0` at `s`. -/
theorem hasLaplace_deriv [CompleteSpace E] {f f' : ℝ → E} {s : ℂ} {z : E}
    (hf0 : ContinuousWithinAt f (Ici 0) 0)
    (hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t)
    (hf : HasLaplace f s z)
    (hf' : Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f' t) (volume.restrict (Ioi 0))) :
    HasLaplace f' s (s • z - f 0) := by
  refine hasLaplace_deriv_of_primitive (fun t ht ↦ ?_) hf hf'
  have hcont : ContinuousOn f (Icc 0 t) := by
    intro x hx
    rcases hx.1.eq_or_lt with rfl | hx0
    · exact hf0.mono fun _ hy ↦ hy.1
    · exact (hderiv x hx0).continuousAt.continuousWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hcont
    (fun x hx ↦ hderiv x hx.1)
    (intervalIntegrable_of_integrableOn_cexp_neg_mul_smul hf' le_rfl ht)
  rw [hftc, add_sub_cancel]

end Deriv

end TauCeti
