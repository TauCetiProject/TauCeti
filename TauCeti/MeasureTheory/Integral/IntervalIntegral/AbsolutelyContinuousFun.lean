/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Calculus along absolutely continuous curves

Mathlib's `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` is the fundamental theorem of
calculus for an absolutely continuous real function. This file composes it with a `C¹` function:
if `γ : ℝ → F` is an absolutely continuous curve in a normed space with derivative `V t` at almost
every time and `φ : F → ℝ` is `C¹`, then `∫_a^b φ'(γ t) (V t) dt = φ (γ b) - φ (γ a)`.
In finite dimension, it also extends Mathlib's real-valued derivative integrability and
fundamental-theorem results to curves.

## Main results

* `AbsolutelyContinuousOnInterval.integral_fderiv_apply_eq_sub`: the fundamental theorem of
  calculus for the composition of a `C¹` function with an absolutely continuous curve.
* `AbsolutelyContinuousOnInterval.intervalIntegrable_of_ae_hasDerivAt`: the almost-everywhere
  derivative of an absolutely continuous curve in a finite-dimensional space is interval
  integrable.
* `AbsolutelyContinuousOnInterval.integral_eq_sub_of_ae_hasDerivAt`: the fundamental theorem for
  the almost-everywhere derivative of an absolutely continuous curve in finite dimension.
* `AbsolutelyContinuousOnInterval.intervalIntegrable_deriv_of_finiteDimensional` and
  `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub_of_finiteDimensional`: integrability and
  the fundamental theorem for the canonical derivative of such a curve.
* `AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul_of_ae_hasDerivAt`:
  integration by parts with supplied almost-everywhere derivatives.
* `AbsolutelyContinuousOnInterval.integral_div_eq_log_sub_log`: the fundamental theorem for the
  logarithmic derivative of a nonvanishing absolutely continuous real function.
* `TauCeti.Probability.survival_eq_exp_integral_hazard`: a positive absolutely continuous
  survival function is reconstructed from its hazard rate.
* `ContinuousOn.absolutelyContinuousOnInterval_of_hasDerivAt_off_countable`: a continuous curve
  with an integrable derivative off a countable set is absolutely continuous.
* `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral'`: indefinite integrals
  with base point in the integrability interval are absolutely continuous in any real normed space.
* `IntervalIntegrable.integral_mul_pow_integral`: for a real `g` with primitive `G` based at `c`,
  `∫ s in c..d, g s * G s ^ k = G d ^ (k + 1) / (k + 1)`;
  `IntervalIntegrable.abs_integral_mul_abs_pow_integral` is its form with `|G|` for nonnegative `g`.
* `TauCeti.abs_integral_norm_mul_abs_pow`: with `Λ s = ∫ r in t₀..s, ‖M r‖`,
  `|∫ s in t₀..t, ‖M s‖ * |Λ s| ^ n| = |Λ t| ^ (n + 1) / (n + 1)`, and
  `TauCeti.norm_integral_le_abs_integral_norm_pow_div_factorial_mul`, the resulting inductive step
  of factorial bounds on iterated integrals.
* `TauCeti.intervalIntegral.intervalIntegrable_mul_add_integral` and
  `TauCeti.intervalIntegral.sq_add_integral_sub_sq`: integrability and integration by parts for
  the square of a primitive `c + ∫_{t₀}^· f` valued in a normed ring / finite-dimensional
  commutative real normed algebra.
* `TauCeti.intervalIntegral.sub_eq_add_integral_sub_of_eq_add_integral`,
  `TauCeti.intervalIntegral.intervalIntegrable_sub_mul_sub_of_eq_add_integral`,
  `TauCeti.intervalIntegral.sub_sq_sub_sub_sq_eq_of_eq_add_integral`,
  `TauCeti.intervalIntegral.sum_sub_sq_eq_of_eq_add_integral`, and
  `TauCeti.intervalIntegral.sum_sub_sq_le_of_eq_add_integral`: shared-noise cancellation,
  integrability, sum-of-squares energy identities, and real `ℓ²`-dissipation bound for two integral
  equations sharing an additive driving term.
-/

public section

open MeasureTheory Set

namespace AbsolutelyContinuousOnInterval

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {γ V : ℝ → F} {a b : ℝ}

/-- *Fundamental theorem of calculus* along an absolutely continuous curve: if `γ` is absolutely
continuous on `uIcc a b` with derivative `V t` at almost every `t ∈ uIoc a b` and `φ` is `C¹`, then
`∫ t in a..b, fderiv ℝ φ (γ t) (V t) = φ (γ b) - φ (γ a)`. The composition `φ ∘ γ` is absolutely
continuous because `φ` is Lipschitz on the compact image `γ '' uIcc a b`. -/
theorem integral_fderiv_apply_eq_sub (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hV : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt γ (V t) t) {φ : F → ℝ} (hφ : ContDiff ℝ 1 φ) :
    ∫ t in a..b, fderiv ℝ φ (γ t) (V t) = φ (γ b) - φ (γ a) := by
  refine Eq.trans (intervalIntegral.integral_congr_ae ?_)
    (hγ.comp_of_contDiffAt fun _ _ ↦ hφ.contDiffAt).integral_deriv_eq_sub
  filter_upwards [hV] with t ht hmem
  exact (HasFDerivAt.comp_hasDerivAt t (hφ.differentiable one_ne_zero (γ t)).hasFDerivAt
    (ht hmem)).deriv.symm

/-- The almost-everywhere derivative `V` of a curve `γ` which is absolutely continuous on
`uIcc a b` in a finite-dimensional real normed space is interval integrable on `a..b`. This reduces
to Mathlib's real-valued `AbsolutelyContinuousOnInterval.intervalIntegrable_deriv` in the
coordinates of a basis. -/
theorem intervalIntegrable_of_ae_hasDerivAt [FiniteDimensional ℝ F]
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hV : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt γ (V t) t) :
    IntervalIntegrable V volume a b := by
  let e := (Module.finBasis ℝ F).equivFun.toContinuousLinearEquiv
  rw [intervalIntegrable_iff, IntegrableOn, ← e.integrable_comp_iff,
    integrable_pi_iff]
  intro i
  let L : F →L[ℝ] ℝ := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ ℝ) i).comp (e : F →L[ℝ] _)
  refine (intervalIntegrable_iff.1
    (L.lipschitzWith.comp_absolutelyContinuousOnInterval hγ).intervalIntegrable_deriv).congr ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [hV] with t ht hmem
  exact (L.hasFDerivAt.comp_hasDerivAt t (ht hmem)).deriv

/-- The derivative of an absolutely continuous curve in a finite-dimensional real normed space
is interval integrable. -/
theorem intervalIntegrable_deriv_of_finiteDimensional [FiniteDimensional ℝ F]
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    IntervalIntegrable (deriv γ) volume a b := by
  apply hγ.intervalIntegrable_of_ae_hasDerivAt
  filter_upwards [hγ.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with t ht hmem
  exact (ht (uIoc_subset_uIcc hmem)).hasDerivAt

/-- The fundamental theorem of calculus for the almost-everywhere derivative of an absolutely
continuous curve in a finite-dimensional real normed space. -/
theorem integral_eq_sub_of_ae_hasDerivAt [FiniteDimensional ℝ F]
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hV : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt γ (V t) t) :
    ∫ t in a..b, V t = γ b - γ a := by
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun g ↦ ?_
  rw [← g.intervalIntegral_comp_comm (hγ.intervalIntegrable_of_ae_hasDerivAt hV), map_sub]
  simpa [g.fderiv] using hγ.integral_fderiv_apply_eq_sub hV g.contDiff

/-- The fundamental theorem of calculus for an absolutely continuous curve in a
finite-dimensional real normed space. -/
theorem integral_deriv_eq_sub_of_finiteDimensional [FiniteDimensional ℝ F]
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    ∫ t in a..b, deriv γ t = γ b - γ a := by
  apply hγ.integral_eq_sub_of_ae_hasDerivAt
  filter_upwards [hγ.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with t ht hmem
  exact (ht (uIoc_subset_uIcc hmem)).hasDerivAt

/-- For two absolutely continuous curves with the same left endpoint, their pointwise distance
is bounded by the `L¹` difference of their velocities over the whole interval. -/
theorem norm_sub_le_integral_norm_deriv_sub [FiniteDimensional ℝ F] {p : ℝ → F}
    (hp : AbsolutelyContinuousOnInterval p a b) (hγ : AbsolutelyContinuousOnInterval γ a b)
    (ha : p a = γ a) {t : ℝ} (ht : t ∈ Icc a b) :
    ‖p t - γ t‖ ≤ ∫ v in a..b, ‖deriv p v - deriv γ v‖ := by
  have hpI := hp.intervalIntegrable_deriv_of_finiteDimensional
  have hγI := hγ.intervalIntegrable_deriv_of_finiteDimensional
  have hsub : uIcc a t ⊆ uIcc a b := uIcc_subset_uIcc left_mem_uIcc
    ((uIcc_of_le (ht.1.trans ht.2)).symm ▸ ht)
  have heq : ∫ v in a..t, deriv p v - deriv γ v = p t - γ t := by
    rw [intervalIntegral.integral_sub (hpI.mono_set hsub) (hγI.mono_set hsub),
      (hp.mono hsub).integral_deriv_eq_sub_of_finiteDimensional,
      (hγ.mono hsub).integral_deriv_eq_sub_of_finiteDimensional, ha]
    abel
  rw [← heq]
  exact (intervalIntegral.norm_integral_le_integral_norm ht.1).trans
    (intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _) (hpI.sub hγI).norm)

/-- The derivative of a finite-dimensional AC curve is integrable on the ordered half-open
parameter interval. -/
theorem integrableOn_deriv_Ioc [FiniteDimensional ℝ F]
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    IntegrableOn (deriv γ) (Ioc a b) :=
  hγ.intervalIntegrable_deriv_of_finiteDimensional.1

/-- If an interval-integrable function `s` approximates the velocity of `γ` in `L¹` on `(a, b]`
to within `ε`, then the endpoint defect `γ b - γ a - ∫ s` has norm at most `ε`. For `a < b`, this
says that the average correction `(γ b - γ a - ∫ s) / (b - a)` to `s` has norm at most
`ε / (b - a)`. -/
theorem norm_sub_integral_le [FiniteDimensional ℝ F]
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hab : a ≤ b) {s : ℝ → F}
    (hsi : IntervalIntegrable s volume a b) {ε : ℝ}
    (hg : (∫ t in Ioc a b, ‖s t - deriv γ t‖) ≤ ε) :
    ‖γ b - γ a - ∫ t in a..b, s t‖ ≤ ε := by
  have hγi := hγ.intervalIntegrable_deriv_of_finiteDimensional
  have hEq : γ b - γ a - ∫ t in a..b, s t = ∫ t in a..b, deriv γ t - s t := by
    rw [intervalIntegral.integral_sub hγi hsi, hγ.integral_deriv_eq_sub_of_finiteDimensional]
  rw [hEq]
  apply (intervalIntegral.norm_integral_le_integral_norm hab).trans
  simpa only [intervalIntegral.integral_of_le hab, norm_sub_rev] using hg

end AbsolutelyContinuousOnInterval

namespace AbsolutelyContinuousOnInterval

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]
  {f f' g g' : ℝ → A} {a b : ℝ}

/-- **Integration by parts** for absolutely continuous functions valued in a finite-dimensional
real normed ring. The derivatives may be supplied only almost everywhere. -/
theorem integral_mul_deriv_eq_deriv_mul_of_ae_hasDerivAt
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hff' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (f' t) t)
    (hgg' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt g (g' t) t) :
    ∫ t in a..b, f t * g' t = f b * g b - f a * g a - ∫ t in a..b, f' t * g t := by
  have hprod : AbsolutelyContinuousOnInterval (fun t ↦ f t * g t) a b := hf.fun_mul' hg
  have hder : ∀ᵐ t, t ∈ uIoc a b →
      HasDerivAt (fun t ↦ f t * g t) (f' t * g t + f t * g' t) t := by
    filter_upwards [hff', hgg'] with t ht hu hmem
    exact (ht hmem).mul (hu hmem)
  have h := hprod.integral_eq_sub_of_ae_hasDerivAt hder
  rw [intervalIntegral.integral_add
    ((hf.intervalIntegrable_of_ae_hasDerivAt hff').mul_continuousOn hg.continuousOn)
    ((hg.intervalIntegrable_of_ae_hasDerivAt hgg').continuousOn_mul hf.continuousOn)] at h
  exact eq_sub_of_add_eq' h

end AbsolutelyContinuousOnInterval

namespace AbsolutelyContinuousOnInterval

variable {f V : ℝ → ℝ} {a b : ℝ}

private theorem ae_hasDerivAt_log (h0 : ∀ t ∈ uIcc a b, f t ≠ 0)
    (hV : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (V t) t) :
    ∀ᵐ t, t ∈ uIoc a b → HasDerivAt (fun t ↦ Real.log (f t)) (V t / f t) t := by
  filter_upwards [hV] with t ht hmem
  exact (ht hmem).log (h0 t (uIoc_subset_uIcc hmem))

/-- The logarithmic derivative `V / f` of an absolutely continuous real function `f` that does not
vanish on the interval is interval integrable, where `V` is the derivative of `f` at almost every
point. -/
theorem intervalIntegrable_div_of_ae_hasDerivAt (hf : AbsolutelyContinuousOnInterval f a b)
    (h0 : ∀ t ∈ uIcc a b, f t ≠ 0) (hV : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (V t) t) :
    IntervalIntegrable (fun t ↦ V t / f t) volume a b :=
  (hf.log h0).intervalIntegrable_of_ae_hasDerivAt (ae_hasDerivAt_log h0 hV)

/-- The fundamental theorem of calculus for the logarithmic derivative: if `f` is absolutely
continuous and nonvanishing on the interval, with derivative `V` at almost every point, then
`∫ t in a..b, V t / f t = log (f b) - log (f a)`. -/
theorem integral_div_eq_log_sub_log (hf : AbsolutelyContinuousOnInterval f a b)
    (h0 : ∀ t ∈ uIcc a b, f t ≠ 0) (hV : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (V t) t) :
    ∫ t in a..b, V t / f t = Real.log (f b) - Real.log (f a) :=
  (hf.log h0).integral_eq_sub_of_ae_hasDerivAt (ae_hasDerivAt_log h0 hV)

end AbsolutelyContinuousOnInterval

namespace TauCeti.Probability

variable {f : ℝ → ℝ} {a x : ℝ}

/-- **Survival reconstruction from the hazard rate.** If `S` is absolutely continuous on the
interval between `a` and `x`, is positive there, and has derivative `-f` almost everywhere, then
the hazard rate `f / S` is interval integrable and
`S x = S a * exp (-∫ t in a..x, f t / S t)`. -/
theorem survival_eq_exp_integral_hazard {S : ℝ → ℝ}
    (hS : AbsolutelyContinuousOnInterval S a x) (hpos : ∀ t ∈ uIcc a x, 0 < S t)
    (hderiv : ∀ᵐ t, t ∈ uIoc a x → HasDerivAt S (-f t) t) :
    IntervalIntegrable (fun t => f t / S t) volume a x ∧
      S x = S a * Real.exp (-∫ t in a..x, f t / S t) := by
  have hne : ∀ t ∈ uIcc a x, S t ≠ 0 := fun t ht => (hpos t ht).ne'
  have hint : IntervalIntegrable (fun t => f t / S t) volume a x := by
    have h : (fun t => f t / S t) = -fun t => -f t / S t := by
      ext t
      simp [neg_div]
    rw [h]
    exact (hS.intervalIntegrable_div_of_ae_hasDerivAt hne hderiv).neg
  refine ⟨hint, ?_⟩
  have h := hS.integral_div_eq_log_sub_log hne hderiv
  simp only [neg_div, intervalIntegral.integral_neg] at h
  have ha : 0 < S a := hpos a left_mem_uIcc
  have hx : 0 < S x := hpos x right_mem_uIcc
  rw [h, Real.exp_sub, Real.exp_log hx, Real.exp_log ha]
  field_simp

end TauCeti.Probability

/-- An indefinite interval integral in a real normed space is absolutely continuous on its
integrability interval, provided its base point belongs to that interval. -/
theorem IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral'
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {a b c : ℝ} (hf : IntervalIntegrable f volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun t ↦ ∫ v in c..t, f v) a b := by
  have hn := hf.norm.absolutelyContinuousOnInterval_intervalIntegral hc
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ ↦
    Finset.sum_nonneg fun _ _ ↦ dist_nonneg) ?_ hn
  have he : ∀ᶠ E in AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
      Filter.principal (AbsolutelyContinuousOnInterval.disjWithin a b),
      E ∈ AbsolutelyContinuousOnInterval.disjWithin a b :=
    Filter.eventually_inf_principal.mpr (by simp)
  filter_upwards [he] with E hE
  apply Finset.sum_le_sum
  intro i hi
  have hx := hf.mono_set (uIcc_subset_uIcc hc (hE.1 i hi).1)
  have hy := hf.mono_set (uIcc_subset_uIcc hc (hE.1 i hi).2)
  rw [dist_eq_norm, intervalIntegral.integral_interval_sub_left hx hy,
    Real.dist_eq, intervalIntegral.integral_interval_sub_left hx.norm hy.norm]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

/-- For `g` interval integrable on `c..d`, with primitive `G s = ∫ u in c..s, g u`, the integral
of `g * G ^ k` over `c..d` is `G d ^ (k + 1) / (k + 1)`, whatever the order of `c` and `d`. This
is the finite-interval form of `MeasureTheory.IntegrableOn.integral_Ioi_mul_pow_integral_Ioi`;
it gives the factorial decay of the Picard iterates of linear equations with integrable
coefficients. -/
theorem IntervalIntegrable.integral_mul_pow_integral {g : ℝ → ℝ} {c d : ℝ}
    (hg : IntervalIntegrable g volume c d) (k : ℕ) :
    ∫ s in c..d, g s * (∫ u in c..s, g u) ^ k = (∫ u in c..d, g u) ^ (k + 1) / (k + 1) := by
  set G : ℝ → ℝ := fun s ↦ ∫ u in c..s, g u
  have hpow : AbsolutelyContinuousOnInterval (fun s ↦ G s ^ (k + 1)) c d :=
    (hg.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).comp_of_contDiffAt
      (φ := fun x : ℝ ↦ x ^ (k + 1)) fun _ _ ↦ (contDiff_id.pow _).contDiffAt
  have hderiv : ∀ᵐ s, s ∈ uIoc c d →
      deriv (fun s ↦ G s ^ (k + 1)) s = (k + 1) * (g s * G s ^ k) := by
    filter_upwards [hg.ae_hasDerivAt_integral] with s hs hsI
    rw [((hs (uIoc_subset_uIcc hsI) c left_mem_uIcc).fun_pow (k + 1)).deriv]
    push_cast
    ring
  have h := hpow.integral_deriv_eq_sub
  rw [intervalIntegral.integral_congr_ae hderiv, intervalIntegral.integral_const_mul] at h
  simp only [G, intervalIntegral.integral_same, zero_pow k.succ_ne_zero, sub_zero] at h
  rw [← h]
  field_simp

/-- For `g` interval integrable and almost everywhere nonnegative between `c` and `d`, with
primitive `G s = ∫ u in c..s, g u`, the integral of `g * |G| ^ k` over `c..d` has absolute value
`|G d| ^ (k + 1) / (k + 1)`, whatever the order of `c` and `d`. -/
theorem IntervalIntegrable.abs_integral_mul_abs_pow_integral {g : ℝ → ℝ} {c d : ℝ}
    (hg : IntervalIntegrable g volume c d) (hg₀ : ∀ᵐ s ∂volume.restrict (uIcc c d), 0 ≤ g s)
    (k : ℕ) :
    |∫ s in c..d, g s * |∫ u in c..s, g u| ^ k| = |∫ u in c..d, g u| ^ (k + 1) / (k + 1) := by
  set G : ℝ → ℝ := fun s ↦ ∫ u in c..s, g u
  -- `G` has a constant sign `σ` between `c` and `d`.
  obtain ⟨σ, hσ, hG⟩ : ∃ σ : ℝ, |σ| = 1 ∧ ∀ s ∈ uIcc c d, |G s| = σ * G s := by
    rcases le_total c d with h | h
    · rw [uIcc_of_le h] at hg₀
      refine ⟨1, abs_one, fun s hs ↦ ?_⟩
      rw [uIcc_of_le h] at hs
      rw [one_mul, abs_of_nonneg (intervalIntegral.integral_nonneg_of_ae_restrict hs.1
        (ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc_right hs.2) hg₀))]
    · rw [uIcc_of_ge h] at hg₀
      refine ⟨-1, by simp, fun s hs ↦ ?_⟩
      rw [uIcc_of_ge h] at hs
      rw [neg_one_mul, abs_of_nonpos]
      simp only [G]
      rw [intervalIntegral.integral_symm, neg_nonpos]
      exact intervalIntegral.integral_nonneg_of_ae_restrict hs.2
        (ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc_left hs.1) hg₀)
  have h : ∫ s in c..d, g s * |G s| ^ k = σ ^ k * ∫ s in c..d, g s * G s ^ k := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    simp only [hG s hs, mul_pow]
    ring
  rw [h, hg.integral_mul_pow_integral]
  simp [abs_mul, abs_div, abs_pow, hσ, abs_of_pos (by positivity : (0 : ℝ) < k + 1)]

namespace TauCeti

open intervalIntegral
open scoped Nat

/-- With `Λ s = ∫ r in t₀..s, ‖M r‖` for a function `M` into a normed group, the integral of
`‖M‖ |Λ| ^ n` from `t₀` to `t` is `|Λ t| ^ (n + 1) / (n + 1)`, in either order of `t₀` and `t`. -/
theorem abs_integral_norm_mul_abs_pow {G : Type*} [NormedAddCommGroup G] {M : ℝ → G} {t₀ t : ℝ}
    (hM : IntervalIntegrable (fun s ↦ ‖M s‖) volume t₀ t) (n : ℕ) :
    |∫ s in t₀..t, ‖M s‖ * |∫ r in t₀..s, ‖M r‖| ^ n| =
      |∫ s in t₀..t, ‖M s‖| ^ (n + 1) / (n + 1) :=
  hM.abs_integral_mul_abs_pow_integral (.of_forall fun _ ↦ norm_nonneg _) n

/-- **The inductive step of a factorial bound.** With `Λ r = ∫ u in t₀..r, ‖M u‖` for a function
`M` into a normed group, if `‖f r‖ ≤ ‖M r‖ * (|Λ r| ^ n / n! * K)` for almost every `r` between
`t₀` and `t`, with `0 ≤ K`, then `‖∫ r in t₀..t, f r‖ ≤ |Λ t| ^ (n + 1) / (n + 1)! * K`. -/
theorem norm_integral_le_abs_integral_norm_pow_div_factorial_mul {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] {f : ℝ → F} {M : ℝ → G}
    {t₀ t K : ℝ} (hK : 0 ≤ K) (hM : IntervalIntegrable (fun s ↦ ‖M s‖) volume t₀ t) {n : ℕ}
    (hf : ∀ᵐ r ∂volume.restrict (uIoc t₀ t),
      ‖f r‖ ≤ ‖M r‖ * (|∫ u in t₀..r, ‖M u‖| ^ n / n ! * K)) :
    ‖∫ r in t₀..t, f r‖ ≤ |∫ r in t₀..t, ‖M r‖| ^ (n + 1) / (n + 1)! * K := by
  refine (norm_integral_le_abs_of_norm_le hf (hM.mul_continuousOn
    ((((continuousOn_primitive_interval' hM left_mem_uIcc).abs.pow n).div_const _).mul
      continuousOn_const))).trans_eq ?_
  have : (fun s ↦ ‖M s‖ * (|∫ r in t₀..s, ‖M r‖| ^ n / n ! * K)) =
      fun s ↦ K / n ! * (‖M s‖ * |∫ r in t₀..s, ‖M r‖| ^ n) := by
    ext s
    ring
  rw [this, intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg (by positivity),
    abs_integral_norm_mul_abs_pow hM, Nat.factorial_succ]
  push_cast
  field_simp

end TauCeti

/-- A continuous curve with an integrable derivative outside a countable exceptional set is
absolutely continuous on its parameter interval. -/
theorem ContinuousOn.absolutelyContinuousOnInterval_of_hasDerivAt_off_countable
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f f' : ℝ → F} {a b : ℝ} {s : Set ℝ} (hf : ContinuousOn f (uIcc a b))
    (hs : s.Countable)
    (hd : ∀ t ∈ Ioo (min a b) (max a b) \ s, HasDerivAt f (f' t) t)
    (hi : IntervalIntegrable f' volume a b) : AbsolutelyContinuousOnInterval f a b := by
  -- Embed `F` isometrically in its completion, where the fundamental theorem of calculus holds.
  let L : F →L[ℝ] UniformSpace.Completion F := UniformSpace.Completion.toComplL
  have hL : Isometry L := (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℝ) (E := F)).isometry
  rw [← hL.absolutelyContinuousOnInterval_comp_iff]
  have hf : ContinuousOn (L ∘ f) (uIcc a b) := L.continuous.comp_continuousOn hf
  have hd : ∀ t ∈ Ioo (min a b) (max a b) \ s, HasDerivAt (L ∘ f) (L (f' t)) t :=
    fun t ht ↦ L.hasFDerivAt.comp_hasDerivAt t (hd t ht)
  have hi : IntervalIntegrable (L ∘ f') volume a b := by
    rw [intervalIntegrable_iff] at hi ⊢
    exact L.integrable_comp hi
  have hbase : min a b ∈ uIcc a b := ⟨le_rfl, min_le_max⟩
  have hI := hi.absolutelyContinuousOnInterval_intervalIntegral' hbase
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ L (f (min a b))) a b :=
    (LipschitzWith.const (L (f (min a b)))).lipschitzOnWith.absolutelyContinuousOnInterval
  apply (hc.add hI).congr
  intro t ht
  have hsub : uIcc (min a b) t ⊆ uIcc a b := uIcc_subset_uIcc hbase ht
  have hFTC := integral_eq_of_hasDerivAt_off_countable (L ∘ f) (L ∘ f') hs (hf.mono hsub)
    (fun u hu ↦ hd u ⟨⟨by simpa only [min_eq_left ht.1] using hu.1.1,
      (by simpa only [max_eq_right ht.1] using hu.1.2 : u < t).trans_le ht.2⟩, hu.2⟩)
    (hi.mono_set hsub)
  simp only [Pi.add_apply, Function.comp_apply] at hFTC ⊢
  rw [hFTC]
  abel

namespace TauCeti.intervalIntegral

/-! ### Square of a primitive and sum-of-squares energy identities -/

/-- If `f : ℝ → A` is interval integrable on `t₀..a` and `t₀..b`, then
`s ↦ f s * (c + ∫ u in t₀..s, f u ∂μ)` is interval integrable on `a..b`. -/
theorem intervalIntegrable_mul_add_integral {A : Type*} [NormedRing A] [NormedSpace ℝ A]
    {μ : Measure ℝ} [NullSingletonClass μ] {f : ℝ → A} (c : A) {t₀ a b : ℝ}
    (hfa : IntervalIntegrable f μ t₀ a) (hfb : IntervalIntegrable f μ t₀ b) :
    IntervalIntegrable (fun s ↦ f s * (c + ∫ u in t₀..s, f u ∂μ)) μ a b := by
  have hfab : IntervalIntegrable f μ a b := hfa.symm.trans hfb
  have hcont : ContinuousOn (fun s ↦ c + ∫ u in t₀..s, f u ∂μ) (uIcc a b) := by
    refine ((continuousOn_const (c := c + ∫ u in t₀..a, f u ∂μ)).add
      (_root_.intervalIntegral.continuousOn_primitive_interval'
        (a := a) hfab left_mem_uIcc)).congr fun s hs ↦ ?_
    rw [Pi.add_apply, add_assoc, _root_.intervalIntegral.integral_add_adjacent_intervals hfa
      (hfab.mono_set (uIcc_subset_uIcc_left hs))]
  exact hfab.mul_continuousOn hcont

/-- **Integration by parts for the square of an indefinite integral.** If `f : ℝ → A` is interval
integrable on `t₀..a` and `t₀..b` with values in a finite-dimensional commutative real normed
algebra `A`, then
`(c + ∫ s in t₀..b, f s) ^ 2 - (c + ∫ s in t₀..a, f s) ^ 2 =
  2 * ∫ s in a..b, f s * (c + ∫ u in t₀..s, f u)`. -/
theorem sq_add_integral_sub_sq {A : Type*} [NormedCommRing A] [NormedAlgebra ℝ A]
    [FiniteDimensional ℝ A] {f : ℝ → A} (c : A) {t₀ a b : ℝ}
    (hfa : IntervalIntegrable f volume t₀ a) (hfb : IntervalIntegrable f volume t₀ b) :
    (c + ∫ s in t₀..b, f s) ^ 2 - (c + ∫ s in t₀..a, f s) ^ 2 =
      2 * ∫ s in a..b, f s * (c + ∫ u in t₀..s, f u) := by
  -- Re-center the primitive at `a` using additivity so all derivatives live on `uIcc a b`.
  have hfab : IntervalIntegrable f volume a b := hfa.symm.trans hfb
  let c' : A := c + ∫ u in t₀..a, f u
  let g : ℝ → A := fun u ↦ c' + ∫ s in a..u, f s
  have hsplit : ∀ s ∈ uIcc a b, g s = c + ∫ u in t₀..s, f u := fun s hs ↦ by
    simp only [g, c', add_assoc, _root_.intervalIntegral.integral_add_adjacent_intervals hfa
      (hfab.mono_set (uIcc_subset_uIcc_left hs))]
  have hg_ac : AbsolutelyContinuousOnInterval g a b :=
    (LipschitzWith.const c').lipschitzOnWith.absolutelyContinuousOnInterval.add
      (hfab.absolutelyContinuousOnInterval_intervalIntegral' left_mem_uIcc)
  have hg_deriv : ∀ᵐ u, u ∈ uIoc a b → HasDerivAt g (f u) u := by
    filter_upwards [hfab.ae_hasDerivAt_integral] with u hu hmem
    exact (hu (uIoc_subset_uIcc hmem) a left_mem_uIcc).const_add c'
  have hibp := hg_ac.integral_mul_deriv_eq_deriv_mul_of_ae_hasDerivAt hg_ac hg_deriv hg_deriv
  have hcomm : (∫ s in a..b, g s * f s) = ∫ s in a..b, f s * g s :=
    _root_.intervalIntegral.integral_congr fun s _ ↦ mul_comm _ _
  have hcongr : (∫ s in a..b, f s * g s) = ∫ s in a..b, f s * (c + ∫ u in t₀..s, f u) :=
    _root_.intervalIntegral.integral_congr fun s hs ↦ by rw [hsplit s hs]
  rw [← hsplit b right_mem_uIcc, ← hsplit a left_mem_uIcc, ← hcongr, pow_two, pow_two, two_mul]
  rw [hcomm] at hibp
  exact (eq_sub_iff_add_eq.1 hibp).symm

/-- If `X = x + w + ∫ u in t₀..t, F u ∂μ` and `Y = y + w + ∫ u in t₀..t, G u ∂μ` with `F` and `G`
interval integrable on `t₀..t`, then the shared additive term `w` cancels:
`X - Y = (x - y) + ∫ u in t₀..t, (F u - G u) ∂μ`. -/
theorem sub_eq_add_integral_sub_of_eq_add_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {μ : Measure ℝ} {x y w X Y : E} {F G : ℝ → E} {t₀ t : ℝ}
    (hF : IntervalIntegrable F μ t₀ t) (hG : IntervalIntegrable G μ t₀ t)
    (hX : X = x + w + ∫ u in t₀..t, F u ∂μ) (hY : Y = y + w + ∫ u in t₀..t, G u ∂μ) :
    X - Y = (x - y) + ∫ u in t₀..t, (F u - G u) ∂μ := by
  rw [_root_.intervalIntegral.integral_sub hF hG, hX, hY]
  abel

/-- On `uIoc t₁ t₂`, if `X` and `Y` satisfy two integral equations sharing an additive driving
term `w`, then `u ↦ (F u - G u) * (X u - Y u)` is interval integrable on `t₁..t₂` because `w`
cancels and `X - Y` agrees with the continuous indefinite integral of `F - G`. -/
theorem intervalIntegrable_sub_mul_sub_of_eq_add_integral {A : Type*} [NormedRing A]
    [NormedSpace ℝ A] {μ : Measure ℝ} [NullSingletonClass μ] {x y : A} {w X Y F G : ℝ → A}
    {t₀ t₁ t₂ : ℝ}
    (hF₁ : IntervalIntegrable F μ t₀ t₁) (hF₂ : IntervalIntegrable F μ t₀ t₂)
    (hG₁ : IntervalIntegrable G μ t₀ t₁) (hG₂ : IntervalIntegrable G μ t₀ t₂)
    (hX : ∀ t ∈ uIoc t₁ t₂, X t = x + w t + ∫ u in t₀..t, F u ∂μ)
    (hY : ∀ t ∈ uIoc t₁ t₂, Y t = y + w t + ∫ u in t₀..t, G u ∂μ) :
    IntervalIntegrable (fun u ↦ (F u - G u) * (X u - Y u)) μ t₁ t₂ := by
  refine (intervalIntegrable_mul_add_integral (x - y) (hF₁.sub hG₁) (hF₂.sub hG₂)).congr
    fun t ht ↦ ?_
  have hsub : uIcc t₁ t ⊆ uIcc t₁ t₂ := uIcc_subset_uIcc_left (uIoc_subset_uIcc ht)
  rw [← sub_eq_add_integral_sub_of_eq_add_integral
    (hF₁.trans ((hF₁.symm.trans hF₂).mono_set hsub))
    (hG₁.trans ((hG₁.symm.trans hG₂).mono_set hsub)) (hX t ht) (hY t ht)]

/-- **Square-difference identity for two integral equations sharing an additive driving term.**
If `X` and `Y` take values in a finite-dimensional commutative real normed algebra `A` and satisfy
`X t = x + w t + ∫ u in t₀..t, F u` and `Y t = y + w t + ∫ u in t₀..t, G u` for all
`t ∈ uIcc t₁ t₂`, with `F` and `G` interval integrable on `t₀..t₁` and `t₀..t₂`, then
`(X t₂ - Y t₂) ^ 2 - (X t₁ - Y t₁) ^ 2 = 2 * ∫ u in t₁..t₂, (F u - G u) * (X u - Y u)`. -/
theorem sub_sq_sub_sub_sq_eq_of_eq_add_integral {A : Type*} [NormedCommRing A] [NormedAlgebra ℝ A]
    [FiniteDimensional ℝ A] {x y : A} {w X Y F G : ℝ → A} {t₀ t₁ t₂ : ℝ}
    (hF₁ : IntervalIntegrable F volume t₀ t₁) (hF₂ : IntervalIntegrable F volume t₀ t₂)
    (hG₁ : IntervalIntegrable G volume t₀ t₁) (hG₂ : IntervalIntegrable G volume t₀ t₂)
    (hX : ∀ t ∈ uIcc t₁ t₂, X t = x + w t + ∫ u in t₀..t, F u)
    (hY : ∀ t ∈ uIcc t₁ t₂, Y t = y + w t + ∫ u in t₀..t, G u) :
    (X t₂ - Y t₂) ^ 2 - (X t₁ - Y t₁) ^ 2 =
      2 * ∫ u in t₁..t₂, (F u - G u) * (X u - Y u) := by
  have hsub (t : ℝ) (ht : t ∈ uIcc t₁ t₂) : X t - Y t = (x - y) + ∫ u in t₀..t, (F u - G u) :=
    sub_eq_add_integral_sub_of_eq_add_integral
      (hF₁.trans ((hF₁.symm.trans hF₂).mono_set (uIcc_subset_uIcc_left ht)))
      (hG₁.trans ((hG₁.symm.trans hG₂).mono_set (uIcc_subset_uIcc_left ht)))
      (hX t ht) (hY t ht)
  rw [hsub t₂ right_mem_uIcc, hsub t₁ left_mem_uIcc,
    sq_add_integral_sub_sq (x - y) (hF₁.sub hG₁) (hF₂.sub hG₂)]
  congr 1
  exact _root_.intervalIntegral.integral_congr fun u hu ↦ by rw [← hsub u hu]

/-- **Sum-of-squares energy identity for two integral equations sharing an additive driving term.**
If `X` and `Y` take values in `ι → A` for a finite-dimensional commutative real normed algebra `A`
and satisfy `X t i = x i + w t i + ∫ u in t₀..t, F u i` and
`Y t i = y i + w t i + ∫ u in t₀..t, G u i` for all `t ∈ uIcc t₁ t₂` and `i ∈ s`, with `F · i`
and `G · i` interval integrable on `t₀..t₁` and `t₀..t₂`, then the change in
`∑ i ∈ s, (X t i - Y t i) ^ 2` from `t₁` to `t₂` equals twice the integrated drift-difference
pairing `∫ u in t₁..t₂, ∑ i ∈ s, (F u i - G u i) * (X u i - Y u i)`.
No continuity assumption on `X`, `Y`, or `w` is needed because the shared `w` cancels.
For `A = ℝ`, this is the `ℓ²`-energy identity. -/
theorem sum_sub_sq_eq_of_eq_add_integral {ι A : Type*} [NormedCommRing A] [NormedAlgebra ℝ A]
    [FiniteDimensional ℝ A] (s : Finset ι) {x y : ι → A} {w X Y F G : ℝ → ι → A} {t₀ t₁ t₂ : ℝ}
    (hF₁ : ∀ i ∈ s, IntervalIntegrable (fun u ↦ F u i) volume t₀ t₁)
    (hF₂ : ∀ i ∈ s, IntervalIntegrable (fun u ↦ F u i) volume t₀ t₂)
    (hG₁ : ∀ i ∈ s, IntervalIntegrable (fun u ↦ G u i) volume t₀ t₁)
    (hG₂ : ∀ i ∈ s, IntervalIntegrable (fun u ↦ G u i) volume t₀ t₂)
    (hX : ∀ t ∈ uIcc t₁ t₂, ∀ i ∈ s, X t i = x i + w t i + ∫ u in t₀..t, F u i)
    (hY : ∀ t ∈ uIcc t₁ t₂, ∀ i ∈ s, Y t i = y i + w t i + ∫ u in t₀..t, G u i) :
    ∑ i ∈ s, (X t₂ i - Y t₂ i) ^ 2 - ∑ i ∈ s, (X t₁ i - Y t₁ i) ^ 2 =
      2 * ∫ u in t₁..t₂, ∑ i ∈ s, (F u i - G u i) * (X u i - Y u i) := by
  rw [← Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun i hi ↦ sub_sq_sub_sub_sq_eq_of_eq_add_integral
      (hF₁ i hi) (hF₂ i hi) (hG₁ i hi) (hG₂ i hi)
      (fun t ht ↦ hX t ht i hi) (fun t ht ↦ hY t ht i hi),
    ← Finset.mul_sum,
    ← _root_.intervalIntegral.integral_finsetSum fun i hi ↦
      intervalIntegrable_sub_mul_sub_of_eq_add_integral (hF₁ i hi) (hF₂ i hi) (hG₁ i hi) (hG₂ i hi)
        (fun t ht ↦ hX t (uIoc_subset_uIcc ht) i hi)
        (fun t ht ↦ hY t (uIoc_subset_uIcc ht) i hi)]

/-- **`ℓ²`-dissipation for two integral equations sharing an additive driving term.**
Under the hypotheses of `sum_sub_sq_eq_of_eq_add_integral` with `t₁ ≤ t₂`, if the drift-difference
pairing is nonpositive on `(t₁, t₂)`, then
`∑ i ∈ s, (X t₂ i - Y t₂ i) ^ 2 ≤ ∑ i ∈ s, (X t₁ i - Y t₁ i) ^ 2`. -/
theorem sum_sub_sq_le_of_eq_add_integral {ι : Type*} (s : Finset ι) {x y : ι → ℝ}
    {w X Y F G : ℝ → ι → ℝ} {t₀ t₁ t₂ : ℝ} (ht : t₁ ≤ t₂)
    (hF₁ : ∀ i ∈ s, IntervalIntegrable (fun u ↦ F u i) volume t₀ t₁)
    (hF₂ : ∀ i ∈ s, IntervalIntegrable (fun u ↦ F u i) volume t₀ t₂)
    (hG₁ : ∀ i ∈ s, IntervalIntegrable (fun u ↦ G u i) volume t₀ t₁)
    (hG₂ : ∀ i ∈ s, IntervalIntegrable (fun u ↦ G u i) volume t₀ t₂)
    (hX : ∀ t ∈ uIcc t₁ t₂, ∀ i ∈ s, X t i = x i + w t i + ∫ u in t₀..t, F u i)
    (hY : ∀ t ∈ uIcc t₁ t₂, ∀ i ∈ s, Y t i = y i + w t i + ∫ u in t₀..t, G u i)
    (hnonpos : ∀ u ∈ Ioo t₁ t₂, ∑ i ∈ s, (F u i - G u i) * (X u i - Y u i) ≤ 0) :
    ∑ i ∈ s, (X t₂ i - Y t₂ i) ^ 2 ≤ ∑ i ∈ s, (X t₁ i - Y t₁ i) ^ 2 := by
  have hid := sum_sub_sq_eq_of_eq_add_integral s hF₁ hF₂ hG₁ hG₂ hX hY
  have hint : IntervalIntegrable
      (fun u ↦ ∑ i ∈ s, (F u i - G u i) * (X u i - Y u i)) volume t₁ t₂ :=
    (IntervalIntegrable.sum s fun i hi ↦
      intervalIntegrable_sub_mul_sub_of_eq_add_integral (hF₁ i hi) (hF₂ i hi) (hG₁ i hi) (hG₂ i hi)
        (fun t ht ↦ hX t (uIoc_subset_uIcc ht) i hi)
        (fun t ht ↦ hY t (uIoc_subset_uIcc ht) i hi)).congr
      fun u _ ↦ Finset.sum_apply u s _
  have hint_nonpos :
      ∫ u in t₁..t₂, ∑ i ∈ s, (F u i - G u i) * (X u i - Y u i) ≤ 0 := by
    rw [← _root_.intervalIntegral.integral_zero (a := t₁) (b := t₂)]
    exact _root_.intervalIntegral.integral_mono_on_of_le_Ioo ht hint intervalIntegrable_const
      hnonpos
  exact sub_nonpos.mp (hid ▸ mul_nonpos_of_nonneg_of_nonpos zero_le_two hint_nonpos)

end TauCeti.intervalIntegral
