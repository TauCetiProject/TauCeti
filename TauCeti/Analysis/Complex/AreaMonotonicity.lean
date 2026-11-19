/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.Calculus.PowerGrowth
import TauCeti.Analysis.Analytic.Order
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Monotonicity for holomorphic curves

Let `u` be a holomorphic map from an open set `U ⊆ ℂ` to a complex inner product space `E`, such
as `ℂⁿ` with its standard symplectic form `ω(v, w) = Im ⟪v, w⟫`. The pullback `u*ω` is
`‖u'‖² dx ∧ dy`, so `∫ ‖u'‖²` is the symplectic area of `u`, counted with multiplicity. This file
proves the monotonicity theorem for such curves: if `u` passes through the centre `u z₀` of a
ball of radius `r` and is proper over that ball, then its area inside the ball is at least
`m π r²`, where `m ≥ 1` is the local multiplicity of `u` at `z₀`, the order of vanishing of
`u - u z₀`. In particular the area is at least `π r²` even when `z₀` is a critical point of `u`.

Properness over the ball is the hypothesis that the sets `{z ∈ U | ‖u z - u z₀‖ ≤ t}`, `t < r`,
are compact. It holds, for instance, when `u` is a map from a closed Riemann surface which is
holomorphic over the ball, and the preimage of the ball lies in a single coordinate chart,
identified with the open set `U ⊆ ℂ`: for a map from `S² = ℂ ∪ {∞}` whose preimage of the ball
avoids `∞`, `U` is that preimage. This is the form in which the monotonicity lemma enters
Gromov's proof of the nonsqueezing theorem: a holomorphic sphere through the centre of a
symplectically embedded ball, on which the almost complex structure is standard, has area at
least that of a flat disc through the centre, once the preimage of the ball is read in a chart.

The proof has three steps.

* **The monotonicity identity** (`TauCeti.setIntegral_mul_norm_deriv_sq_eq`). For a `C¹` cutoff `φ`,
  integrating by parts against the compactly supported radial field
  `φ(‖u - x₀‖²) ⟪u - x₀, u'⟫` gives
  `∫_U φ(‖u - x₀‖²) ‖u'‖² = -∫_U φ'(‖u - x₀‖²) |⟪u - x₀, u'⟫|²`,
  because the antiholomorphic Wirtinger derivative `(∂/∂x + i ∂/∂y) / 2` of `⟪u - x₀, u'⟫` is
  `‖u'‖²` for holomorphic `u`. For nonincreasing `φ`, the Cauchy–Schwarz inequality
  `|⟪u - x₀, u'⟫| ≤ ‖u - x₀‖ ‖u'‖` turns this into an inequality.
* **Monotonicity** (`TauCeti.monotoneOn_setIntegral_mul_norm_deriv_sq_div_sq`). Applied to the
  cutoffs `χ(· / t²)`, the inequality is the Euler inequality `2 I(t) ≤ t I'(t)` for the weighted
  area `I(t) = ∫_U χ(‖u - x₀‖² / t²) ‖u'‖²`, so `I(t) / t²` is nondecreasing.
* **The blow-up limit.** Near `z₀`, `u - u z₀ = (z - z₀) ^ m • g` with `g z₀ ≠ 0`. Rescaling by
  `z = z₀ + s ζ` and `t = s ^ m`, the normalized weighted areas `I(s ^ m) / s ^ (2 m)` converge as
  `s → 0` to the weighted area of the model branched cover `ζ ↦ ζ ^ m • g z₀`, which is
  `m π ∫₀^∞ χ` by polar coordinates. Letting `χ` increase to the indicator of `[0, 1)` then
  gives the bound on the area of the ball.

## Main results

* `TauCeti.setIntegral_mul_norm_deriv_sq_eq`: the monotonicity identity.
* `TauCeti.monotoneOn_setIntegral_mul_norm_deriv_sq_div_sq`: the weighted area divided by `t²` is
  nondecreasing.
* `TauCeti.ofReal_analyticOrderNatAt_mul_pi_mul_sq_le_setLIntegral_enorm_deriv_sq`: the area over
  the ball of radius `r` is at least `m π r²`, for the local multiplicity `m`.
* `TauCeti.ofReal_pi_mul_sq_le_setLIntegral_enorm_deriv_sq`: the area over the ball of radius `r`
  is at least `π r²`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Chapter 4 (the monotonicity lemma) and Chapter 9
  (Gromov's nonsqueezing theorem).
* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. **82** (1985),
  307–347, §0.3.A (nonsqueezing).
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology Complex Metric
open scoped Real InnerProductSpace

namespace TauCeti

/-- A function vanishing on `(ρ, ∞)` has vanishing derivative there. -/
private theorem deriv_eq_zero_of_lt {φ : ℝ → ℝ} {ρ s : ℝ} (hφρ : ∀ s, ρ < s → φ s = 0)
    (hs : ρ < s) : deriv φ s = 0 :=
  (eventuallyEq_of_mem (Ioi_mem_nhds hs) fun x hx ↦ hφρ x hx).deriv_eq.trans (deriv_const _ _)

/-- A point of `U` outside the sublevel set `{z ∈ U | f z ≤ ρ}` lies above level `ρ`. -/
private theorem lt_of_notMem_sep {U : Set ℂ} {f : ℂ → ℝ} {ρ : ℝ} {z : ℂ} (hz : z ∈ U)
    (hzK : z ∉ {z ∈ U | f z ≤ ρ}) : ρ < f z :=
  not_le.1 fun h ↦ hzK ⟨hz, h⟩

/-- Beyond radius `t`, the squared ratio `a ^ 2 / t ^ 2` exceeds `1`. -/
private theorem one_lt_sq_div_sq {a t : ℝ} (ht : 0 < t) (h : t < a) : 1 < a ^ 2 / t ^ 2 :=
  (one_lt_div (by positivity)).2 (pow_lt_pow_left₀ h ht.le two_ne_zero)

/-- A nonincreasing cutoff vanishing on `(1, ∞)` is nonnegative. -/
private theorem cutoff_nonneg {χ : ℝ → ℝ} (hχa : Antitone χ) (hχ1 : ∀ s, 1 < s → χ s = 0)
    (x : ℝ) : 0 ≤ χ x :=
  (hχ1 (max x 2) (by linarith [le_max_right x 2])) ▸ hχa (le_max_left x 2)

/-- For `m ≠ 0`, the power `s ^ m` is below any positive level for `s` near `0`. -/
private theorem eventually_pow_lt {m : ℕ} (hm : m ≠ 0) {t : ℝ} (ht : 0 < t) :
    ∀ᶠ s in 𝓝 (0 : ℝ), s ^ m < t :=
  ((continuous_pow m).tendsto' 0 0 (zero_pow hm)).eventually (gt_mem_nhds ht)

/-- A function continuous on `U` that vanishes off a compact subset `K ⊆ U` is integrable on
`U`. -/
private theorem integrableOn_of_sdiff_eq_zero {U K : Set ℂ} {f : ℂ → ℝ} (hU : MeasurableSet U)
    (hf : ContinuousOn f U) (hKU : K ⊆ U) (hK : IsCompact K) (h0 : ∀ z ∈ U \ K, f z = 0) :
    IntegrableOn f U :=
  ((hf.mono hKU).integrableOn_compact hK).of_forall_sdiff_eq_zero hU h0

/-- The rescaled point `z₀ + s ζ` lies in the closed disc of radius `δ ≥ s ‖ζ‖` about `z₀`. -/
private theorem add_smul_mem_closedBall {z₀ ζ : ℂ} {s δ : ℝ} (hs : 0 ≤ s) (hsζ : s * ‖ζ‖ ≤ δ) :
    z₀ + s • ζ ∈ closedBall z₀ δ := by
  rwa [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hs]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The radial field `φ (‖u‖²) ⟪u, u'⟫` of a holomorphic map `u`, cut off by `φ`. Integration by
parts against it gives the monotonicity identity. -/
private def radialField (φ : ℝ → ℝ) (u : ℂ → E) (z : ℂ) : ℂ :=
  ((φ (‖u z‖ ^ 2) : ℝ) : ℂ) * ⟪u z, deriv u z⟫_ℂ

/-- The derivative of `TauCeti.radialField φ u` at `z` in the direction `v`. -/
private def radialFieldDeriv (φ : ℝ → ℝ) (u : ℂ → E) (v z : ℂ) : ℂ :=
  (((deriv φ (‖u z‖ ^ 2) * (2 * re ⟪u z, v • deriv u z⟫_ℂ)) : ℝ) : ℂ) * ⟪u z, deriv u z⟫_ℂ +
    ((φ (‖u z‖ ^ 2) : ℝ) : ℂ) *
      (v * ⟪u z, deriv (deriv u) z⟫_ℂ + (starRingEnd ℂ) v * ((‖deriv u z‖ ^ 2 : ℝ) : ℂ))

/-- The derivatives of the radial field at the points where `u` is holomorphic. -/
private theorem hasLineDerivAt_radialField {U : Set ℂ} {u : ℂ → E} {φ : ℝ → ℝ}
    (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) (hφ : ContDiff ℝ 1 φ) {z : ℂ} (hz : z ∈ U)
    (v : ℂ) : HasLineDerivAt ℝ (radialField φ u) (radialFieldDeriv φ u v z) z v := by
  have hγ : HasDerivAt (fun t : ℝ ↦ z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hdu : DifferentiableAt ℂ u z := hu.differentiableAt (hU.mem_nhds hz)
  have hddu : DifferentiableAt ℂ (deriv u) z :=
    ((hu.analyticOnNhd hU).deriv z hz).differentiableAt
  have h1 : HasDerivAt (fun t : ℝ ↦ u (z + t • v)) (v • deriv u z) 0 := by
    have hdu' : HasDerivAt u (deriv u z) (z + (0 : ℝ) • v) := by simpa using hdu.hasDerivAt
    simpa [Function.comp_def] using hdu'.scomp (0 : ℝ) hγ
  have h2 : HasDerivAt (fun t : ℝ ↦ deriv u (z + t • v)) (v • deriv (deriv u) z) 0 := by
    have hddu' : HasDerivAt (deriv u) (deriv (deriv u) z) (z + (0 : ℝ) • v) := by
      simpa using hddu.hasDerivAt
    simpa [Function.comp_def] using hddu'.scomp (0 : ℝ) hγ
  have hn : HasDerivAt (fun t : ℝ ↦ ‖u (z + t • v)‖ ^ 2) (2 * re ⟪u z, v • deriv u z⟫_ℂ) 0 := by
    have := reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (h1.inner ℂ h1)
    convert this using 1
    · ext t
      simp [inner_self_eq_norm_sq_to_K, ← ofReal_pow]
    · rw [← inner_conj_symm (v • deriv u z) (u (z + (0 : ℝ) • v))]
      simp only [zero_smul, add_zero, reCLM_apply, map_add, conj_re]
      ring
  have hφ' : HasDerivAt (fun t : ℝ ↦ φ (‖u (z + t • v)‖ ^ 2))
      (deriv φ (‖u z‖ ^ 2) * (2 * re ⟪u z, v • deriv u z⟫_ℂ)) 0 := by
    have hφz : HasDerivAt φ (deriv φ (‖u z‖ ^ 2)) (‖u (z + (0 : ℝ) • v)‖ ^ 2) := by
      simpa using ((hφ.differentiable one_ne_zero) (‖u z‖ ^ 2)).hasDerivAt
    simpa [Function.comp_def] using hφz.comp (0 : ℝ) hn
  have hi : HasDerivAt (fun t : ℝ ↦ ⟪u (z + t • v), deriv u (z + t • v)⟫_ℂ)
      (v * ⟪u z, deriv (deriv u) z⟫_ℂ + (starRingEnd ℂ) v * ((‖deriv u z‖ ^ 2 : ℝ) : ℂ)) 0 := by
    have := h1.inner ℂ h2
    simpa [inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K, add_comm] using this
  have := hφ'.ofReal_comp.mul hi
  simp only [zero_smul, add_zero] at this
  rw [HasLineDerivAt]
  unfold radialField radialFieldDeriv
  exact this

/-- The radial field, cut off by a function `φ` vanishing on `(ρ, ∞)`, vanishes on `U` outside
the compact sublevel set `K = {z ∈ U | ‖u z‖² ≤ ρ}`. So, extended by zero outside `K`, it has
the line derivatives of `TauCeti.radialField` on `K` and vanishing ones off `K`. -/
private theorem hasLineDerivAt_indicator_radialField {U : Set ℂ} {u : ℂ → E} {φ : ℝ → ℝ}
    {ρ : ℝ} (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) (hφ : ContDiff ℝ 1 φ)
    (hφρ : ∀ s, ρ < s → φ s = 0) (hK : IsCompact {z ∈ U | ‖u z‖ ^ 2 ≤ ρ}) (v z : ℂ) :
    HasLineDerivAt ℝ ({z ∈ U | ‖u z‖ ^ 2 ≤ ρ}.indicator (radialField φ u))
      ({z ∈ U | ‖u z‖ ^ 2 ≤ ρ}.indicator (radialFieldDeriv φ u v) z) z v := by
  set K := {z ∈ U | ‖u z‖ ^ 2 ≤ ρ}
  by_cases hzK : z ∈ K
  · rw [indicator_of_mem hzK]
    refine (hasLineDerivAt_radialField hU hu hφ hzK.1 v).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hzK.1] with w hw
    by_cases hwK : w ∈ K
    · exact indicator_of_mem hwK _
    · simp [indicator_of_notMem hwK, radialField, hφρ _ (lt_of_notMem_sep hw hwK)]
  · rw [indicator_of_notMem hzK]
    have h0 : HasLineDerivAt ℝ (fun _ ↦ (0 : ℂ)) 0 z v := by
      simpa using (hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) z).hasLineDerivAt v
    refine h0.congr_of_eventuallyEq ?_
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hzK] with w hw using
      indicator_of_notMem hw _

/-- The derivatives of the cut-off radial field integrate to zero: it is compactly supported. -/
private theorem integral_indicator_radialFieldDeriv {U : Set ℂ} {u : ℂ → E} {φ : ℝ → ℝ}
    {ρ : ℝ} (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) (hφ : ContDiff ℝ 1 φ)
    (hφρ : ∀ s, ρ < s → φ s = 0) (hK : IsCompact {z ∈ U | ‖u z‖ ^ 2 ≤ ρ}) (v : ℂ) :
    Integrable ({z ∈ U | ‖u z‖ ^ 2 ≤ ρ}.indicator (radialFieldDeriv φ u v)) ∧
      ∫ z, {z ∈ U | ‖u z‖ ^ 2 ≤ ρ}.indicator (radialFieldDeriv φ u v) z = 0 := by
  set K := {z ∈ U | ‖u z‖ ^ 2 ≤ ρ}
  have hKU : K ⊆ U := fun z hz ↦ hz.1
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hcu : ContinuousOn u U := hu.continuousOn
  have hcdu : ContinuousOn (deriv u) U := (hu.analyticOnNhd hU).deriv.continuousOn
  have hcddu : ContinuousOn (deriv (deriv u)) U := (hu.analyticOnNhd hU).deriv.deriv.continuousOn
  have hcφ : Continuous φ := hφ.continuous
  have hint : Integrable (K.indicator (radialFieldDeriv φ u v)) := by
    refine (integrable_indicator_iff hKm).2 (ContinuousOn.integrableOn_compact hK ?_)
    exact ContinuousOn.mono (by unfold radialFieldDeriv; fun_prop) hKU
  have hPint : Integrable (K.indicator (radialField φ u)) := by
    refine (integrable_indicator_iff hKm).2 (ContinuousOn.integrableOn_compact hK ?_)
    exact ContinuousOn.mono (by unfold radialField; fun_prop) hKU
  refine ⟨hint, ?_⟩
  -- Integration by parts against the constant `1`.
  have := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := volume) (f := fun _ ↦ (1 : ℂ)) (f' := fun _ ↦ 0) (g := K.indicator (radialField φ u))
    (g' := K.indicator (radialFieldDeriv φ u v)) (v := v) (B := ContinuousLinearMap.mul ℝ ℂ)
    (by simp) (by simpa using hint) (by simpa using hPint)
    (fun z _ ↦ by simpa using (hasFDerivAt_const (𝕜 := ℝ) (1 : ℂ) z).hasLineDerivAt v)
    (fun z _ ↦ hasLineDerivAt_indicator_radialField hU hu hφ hφρ hK v z)
  simpa using this

omit [CompleteSpace E] in
/-- The complex combination `D₁ + i Dᵢ` of the derivatives of the radial field in the directions
`1` and `i`, that is twice its antiholomorphic Wirtinger derivative, is twice the real expression
of the monotonicity identity. -/
private theorem radialFieldDeriv_add_I_mul (φ : ℝ → ℝ) (u : ℂ → E) (z : ℂ) :
    radialFieldDeriv φ u 1 z + I * radialFieldDeriv φ u I z =
      ((2 * (deriv φ (‖u z‖ ^ 2) * ‖⟪u z, deriv u z⟫_ℂ‖ ^ 2 +
        φ (‖u z‖ ^ 2) * ‖deriv u z‖ ^ 2) : ℝ) : ℂ) := by
  simp only [radialFieldDeriv, inner_smul_right]
  apply Complex.ext <;>
    simp [Complex.sq_norm, normSq_apply, mul_re, mul_im] <;> ring

/-- **The monotonicity identity at the origin**, on the compact sublevel set. -/
private theorem setIntegral_mul_norm_deriv_sq_eq_aux {U : Set ℂ} {u : ℂ → E} {φ : ℝ → ℝ} {ρ : ℝ}
    (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) (hφ : ContDiff ℝ 1 φ)
    (hφρ : ∀ s, ρ < s → φ s = 0) (hK : IsCompact {z ∈ U | ‖u z‖ ^ 2 ≤ ρ}) :
    ∫ z in {z ∈ U | ‖u z‖ ^ 2 ≤ ρ}, φ (‖u z‖ ^ 2) * ‖deriv u z‖ ^ 2 =
      -∫ z in {z ∈ U | ‖u z‖ ^ 2 ≤ ρ}, deriv φ (‖u z‖ ^ 2) * ‖⟪u z, deriv u z⟫_ℂ‖ ^ 2 := by
  set K := {z ∈ U | ‖u z‖ ^ 2 ≤ ρ}
  have hKU : K ⊆ U := fun z hz ↦ hz.1
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hcu : ContinuousOn u U := hu.continuousOn
  have hcdu : ContinuousOn (deriv u) U := (hu.analyticOnNhd hU).deriv.continuousOn
  have hcφ : Continuous φ := hφ.continuous
  obtain ⟨hint1, hzero1⟩ := integral_indicator_radialFieldDeriv hU hu hφ hφρ hK 1
  obtain ⟨hintI, hzeroI⟩ := integral_indicator_radialFieldDeriv hU hu hφ hφρ hK I
  have hsum : ∫ z, K.indicator (fun z ↦ 2 * (deriv φ (‖u z‖ ^ 2) * ‖⟪u z, deriv u z⟫_ℂ‖ ^ 2 +
      φ (‖u z‖ ^ 2) * ‖deriv u z‖ ^ 2)) z = 0 := by
    have : (∫ z, K.indicator (radialFieldDeriv φ u 1) z) +
        I * ∫ z, K.indicator (radialFieldDeriv φ u I) z = 0 := by
      rw [hzero1, hzeroI, mul_zero, add_zero]
    rw [← integral_const_mul, ← integral_add hint1 (hintI.const_mul I)] at this
    have hcomb : ∀ z, K.indicator (radialFieldDeriv φ u 1) z +
        I * K.indicator (radialFieldDeriv φ u I) z =
        ((K.indicator (fun z ↦ 2 * (deriv φ (‖u z‖ ^ 2) * ‖⟪u z, deriv u z⟫_ℂ‖ ^ 2 +
          φ (‖u z‖ ^ 2) * ‖deriv u z‖ ^ 2)) z : ℝ) : ℂ) := by
      intro z
      by_cases hz : z ∈ K
      · simp only [indicator_of_mem hz]
        exact radialFieldDeriv_add_I_mul φ u z
      · simp [indicator_of_notMem hz]
    rw [integral_congr_ae (Eventually.of_forall hcomb), integral_complex_ofReal] at this
    exact_mod_cast this
  rw [integral_indicator hKm] at hsum
  have hA : IntegrableOn (fun z ↦ deriv φ (‖u z‖ ^ 2) * ‖⟪u z, deriv u z⟫_ℂ‖ ^ 2) K :=
    ContinuousOn.integrableOn_compact hK (ContinuousOn.mono (by fun_prop) hKU)
  have hB : IntegrableOn (fun z ↦ φ (‖u z‖ ^ 2) * ‖deriv u z‖ ^ 2) K :=
    ContinuousOn.integrableOn_compact hK (ContinuousOn.mono (by fun_prop) hKU)
  rw [integral_const_mul, integral_add hA hB] at hsum
  linarith

/-- **The monotonicity identity for holomorphic curves.** Let `u` be holomorphic on an open set
`U ⊆ ℂ` with values in a complex inner product space, `x₀` a point, and `φ` a `C¹` cutoff
vanishing on `(ρ, ∞)` such that the sublevel set `{z ∈ U | ‖u z - x₀‖² ≤ ρ}` is compact. Then

`∫_U φ(‖u - x₀‖²) ‖u'‖² = -∫_U φ'(‖u - x₀‖²) |⟪u - x₀, u'⟫|²`.

The left side is the area of `u` weighted by the cutoff, since `‖u'‖²` is the area density of a
holomorphic map. -/
theorem setIntegral_mul_norm_deriv_sq_eq {U : Set ℂ} {u : ℂ → E} {x₀ : E} {φ : ℝ → ℝ} {ρ : ℝ}
    (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) (hφ : ContDiff ℝ 1 φ)
    (hφρ : ∀ s, ρ < s → φ s = 0) (hK : IsCompact {z ∈ U | ‖u z - x₀‖ ^ 2 ≤ ρ}) :
    ∫ z in U, φ (‖u z - x₀‖ ^ 2) * ‖deriv u z‖ ^ 2 =
      -∫ z in U, deriv φ (‖u z - x₀‖ ^ 2) * ‖⟪u z - x₀, deriv u z⟫_ℂ‖ ^ 2 := by
  have hu' : DifferentiableOn ℂ (fun z ↦ u z - x₀) U := hu.sub_const x₀
  have hd : deriv (fun z ↦ u z - x₀) = deriv u := funext fun z ↦ deriv_sub_const x₀
  have key := setIntegral_mul_norm_deriv_sq_eq_aux hU hu' hφ hφρ hK
  rw [hd] at key
  have hKU : {z ∈ U | ‖u z - x₀‖ ^ 2 ≤ ρ} ⊆ U := fun z hz ↦ hz.1
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hKU
      (fun z hz ↦ by simp [hφρ _ (lt_of_notMem_sep hz.1 hz.2)]),
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hKU
      (fun z hz ↦ by simp [deriv_eq_zero_of_lt hφρ (lt_of_notMem_sep hz.1 hz.2)])]
  exact key

/-- The monotonicity inequality: for a nonincreasing cutoff, the weighted area is at most
`-∫_U φ'(‖u - x₀‖²) ‖u - x₀‖² ‖u'‖²`, by the Cauchy–Schwarz inequality
`|⟪u - x₀, u'⟫| ≤ ‖u - x₀‖ ‖u'‖` in `TauCeti.setIntegral_mul_norm_deriv_sq_eq`. -/
private theorem setIntegral_mul_norm_deriv_sq_le {U : Set ℂ} {u : ℂ → E} {x₀ : E} {φ : ℝ → ℝ}
    {ρ : ℝ} (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) (hφ : ContDiff ℝ 1 φ)
    (hφa : Antitone φ) (hφρ : ∀ s, ρ < s → φ s = 0)
    (hK : IsCompact {z ∈ U | ‖u z - x₀‖ ^ 2 ≤ ρ}) :
    ∫ z in U, φ (‖u z - x₀‖ ^ 2) * ‖deriv u z‖ ^ 2 ≤
      -∫ z in U, deriv φ (‖u z - x₀‖ ^ 2) * ‖u z - x₀‖ ^ 2 * ‖deriv u z‖ ^ 2 := by
  rw [setIntegral_mul_norm_deriv_sq_eq hU hu hφ hφρ hK, neg_le_neg_iff]
  have hKU : {z ∈ U | ‖u z - x₀‖ ^ 2 ≤ ρ} ⊆ U := fun z hz ↦ hz.1
  have hcu : ContinuousOn u U := hu.continuousOn
  have hcdu : ContinuousOn (deriv u) U := (hu.analyticOnNhd hU).deriv.continuousOn
  refine setIntegral_mono_on ?_ ?_ hU.measurableSet fun z _ ↦ ?_
  iterate 2
    exact integrableOn_of_sdiff_eq_zero hU.measurableSet (by fun_prop) hKU hK
      fun z hz ↦ by simp [deriv_eq_zero_of_lt hφρ (lt_of_notMem_sep hz.1 hz.2)]
  have hφ' : deriv φ (‖u z - x₀‖ ^ 2) ≤ 0 := hφa.deriv_nonpos
  rw [mul_assoc]
  refine mul_le_mul_of_nonpos_left ?_ hφ'
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2

/-- The derivative of `t ↦ χ (a / t²)`. -/
private theorem hasDerivAt_comp_div_sq {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (a : ℝ) {t : ℝ}
    (ht : t ≠ 0) :
    HasDerivAt (fun t ↦ χ (a / t ^ 2)) (deriv χ (a / t ^ 2) * (-2 * a / t ^ 3)) t := by
  have h1 : HasDerivAt (fun t : ℝ ↦ a / t ^ 2) (-2 * a / t ^ 3) t := by
    have := ((hasDerivAt_pow 2 t).inv (pow_ne_zero 2 ht)).const_mul a
    convert this using 1
    · ext t
      simp [div_eq_mul_inv]
    · field_simp
      ring
  exact ((hχ.differentiable one_ne_zero) _).hasDerivAt.comp t h1

/-- The cutoff area density `χ(‖u - x₀‖² / t²) ‖u'‖²` is integrable on `U` when the sublevel set
`{z ∈ U | ‖u z - x₀‖ ≤ t}` is compact. -/
private theorem integrableOn_cutoff {U : Set ℂ} {u : ℂ → E} {x₀ : E} {χ : ℝ → ℝ} {t : ℝ}
    (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) (hχ : Continuous χ)
    (hχ1 : ∀ s, 1 < s → χ s = 0) (ht : 0 < t) (hK : IsCompact {z ∈ U | ‖u z - x₀‖ ≤ t}) :
    IntegrableOn (fun z ↦ χ (‖u z - x₀‖ ^ 2 / t ^ 2) * ‖deriv u z‖ ^ 2) U := by
  have hcu : ContinuousOn u U := hu.continuousOn
  have hcdu : ContinuousOn (deriv u) U := (hu.analyticOnNhd hU).deriv.continuousOn
  have hKU : {z ∈ U | ‖u z - x₀‖ ≤ t} ⊆ U := fun z hz ↦ hz.1
  refine integrableOn_of_sdiff_eq_zero hU.measurableSet (by fun_prop) hKU hK ?_
  rintro z ⟨hz, hzK⟩
  simp [hχ1 _ (one_lt_sq_div_sq ht (lt_of_notMem_sep hz hzK))]

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] in
/-- The bound on the `t`-derivative `χ'(f / t²) (-2 f / t³) N` of the weighted area density, for
`0 ≤ f ≤ ρ²`, `|N| ≤ M` and `t₀ / 2 < t`, given a bound `C` for `χ'` on `[0, ρ² / (t₀ / 2)²]`. -/
private theorem abs_deriv_cutoff_le {χ : ℝ → ℝ} {C M ρ t₀ t f N : ℝ} (ht₀ : 0 < t₀)
    (ht : t₀ / 2 < t) (hf : 0 ≤ f) (hfρ : f ≤ ρ ^ 2) (hN : |N| ≤ M)
    (hC : ∀ x ∈ Icc 0 (ρ ^ 2 / (t₀ / 2) ^ 2), ‖deriv χ x‖ ≤ C) :
    |deriv χ (f / t ^ 2) * (-2 * f / t ^ 3) * N| ≤ C * (2 * ρ ^ 2 / (t₀ / 2) ^ 3) * M := by
  have ht0 : 0 < t := by linarith
  have hΛ : f / t ^ 2 ∈ Icc 0 (ρ ^ 2 / (t₀ / 2) ^ 2) :=
    ⟨by positivity, div_le_div₀ (by positivity) hfρ (by positivity)
      (pow_le_pow_left₀ (by positivity) ht.le 2)⟩
  have h1 : |deriv χ (f / t ^ 2)| ≤ C := by simpa using hC _ hΛ
  have h2 : |-2 * f / t ^ 3| ≤ 2 * ρ ^ 2 / (t₀ / 2) ^ 3 := by
    rw [abs_div, abs_mul, abs_neg, abs_two, abs_of_nonneg hf, abs_of_pos (by positivity)]
    exact div_le_div₀ (by positivity) (by linarith) (by positivity)
      (pow_le_pow_left₀ (by positivity) ht.le 3)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans h1
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) hC0) hN (abs_nonneg _)
    (mul_nonneg hC0 (by positivity))

/-- The weighted area `t ↦ ∫_U χ(‖u - x₀‖² / t²) ‖u'‖²` is differentiable on `(0, r)`. -/
private theorem hasDerivAt_integral_cutoff {U : Set ℂ} {u : ℂ → E} {x₀ : E} {χ : ℝ → ℝ}
    {r : ℝ} (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) (hχ : ContDiff ℝ 1 χ)
    (hχ1 : ∀ s, 1 < s → χ s = 0)
    (hK : ∀ t < r, IsCompact {z ∈ U | ‖u z - x₀‖ ≤ t}) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 r) :
    HasDerivAt (fun t ↦ ∫ z in U, χ (‖u z - x₀‖ ^ 2 / t ^ 2) * ‖deriv u z‖ ^ 2)
      (∫ z in U, deriv χ (‖u z - x₀‖ ^ 2 / t₀ ^ 2) * (-2 * ‖u z - x₀‖ ^ 2 / t₀ ^ 3) *
        ‖deriv u z‖ ^ 2) t₀ := by
  obtain ⟨ht₀, ht₀r⟩ := ht₀
  have hcu : ContinuousOn u U := hu.continuousOn
  have hcdu : ContinuousOn (deriv u) U := (hu.analyticOnNhd hU).deriv.continuousOn
  have hcχ : Continuous χ := hχ.continuous
  have hcdχ : Continuous (deriv χ) := hχ.continuous_deriv le_rfl
  -- Dominate the `t`-derivative for `t` near `t₀`, on the compact sublevel set at level `ρ`.
  set ρ := (t₀ + r) / 2
  have hρ₀ : t₀ < ρ := by simp only [ρ]; linarith
  have hρr : ρ < r := by simp only [ρ]; linarith
  set K := {z ∈ U | ‖u z - x₀‖ ≤ ρ}
  have hKc : IsCompact K := hK ρ hρr
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn
    (f := fun z ↦ ‖deriv u z‖ ^ 2) (ContinuousOn.mono (by fun_prop) fun z hz ↦ hz.1)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := 0) (b := ρ ^ 2 / (t₀ / 2) ^ 2))
    |>.exists_bound_of_continuousOn hcdχ.continuousOn
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict U)
    (F := fun t z ↦ χ (‖u z - x₀‖ ^ 2 / t ^ 2) * ‖deriv u z‖ ^ 2) (x₀ := t₀)
    (s := Ioo (t₀ / 2) ρ) (bound := K.indicator fun _ ↦ C * (2 * ρ ^ 2 / (t₀ / 2) ^ 3) * M)
    (Ioo_mem_nhds (by linarith) hρ₀)
    (Eventually.of_forall fun t ↦
      ContinuousOn.aestronglyMeasurable (by fun_prop) hU.measurableSet)
    (integrableOn_cutoff hU hu hcχ hχ1 ht₀ (hK t₀ ht₀r))
    (ContinuousOn.aestronglyMeasurable (by fun_prop) hU.measurableSet) ?_
    ((integrable_indicator_iff hKc.measurableSet).2 (integrableOn_const hKc.measure_ne_top)
      |>.restrict)
    (Eventually.of_forall fun z t ht ↦
      (hasDerivAt_comp_div_sq hχ _ (by linarith [ht.1] : (0 : ℝ) < t).ne').mul_const _)).2
  refine (ae_restrict_mem hU.measurableSet).mono fun z hz t ht ↦ ?_
  by_cases hzK : z ∈ K
  · rw [indicator_of_mem hzK, Real.norm_eq_abs]
    exact abs_deriv_cutoff_le ht₀ ht.1 (sq_nonneg _) (pow_le_pow_left₀ (norm_nonneg _) hzK.2 2)
      (by simpa using hM z hzK) hC
  · -- Outside `K`, `‖u - x₀‖ > ρ > t`, so `χ'` is evaluated beyond `1`, where it vanishes.
    have h1 : 1 < ‖u z - x₀‖ ^ 2 / t ^ 2 :=
      one_lt_sq_div_sq (by linarith [ht.1]) (ht.2.trans (lt_of_notMem_sep hz hzK))
    simp [indicator_of_notMem hzK, deriv_eq_zero_of_lt hχ1 h1]

/-- The weighted area satisfies the Euler inequality `2 I(t) ≤ t I'(t)`: this is the monotonicity
inequality `TauCeti.setIntegral_mul_norm_deriv_sq_le` for the cutoff `χ (· / t²)`. -/
private theorem two_mul_integral_cutoff_le {U : Set ℂ} {u : ℂ → E} {x₀ : E} {χ : ℝ → ℝ}
    {t : ℝ} (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) (hχ : ContDiff ℝ 1 χ)
    (hχa : Antitone χ) (hχ1 : ∀ s, 1 < s → χ s = 0) (ht : 0 < t)
    (hK : IsCompact {z ∈ U | ‖u z - x₀‖ ≤ t}) :
    2 * ∫ z in U, χ (‖u z - x₀‖ ^ 2 / t ^ 2) * ‖deriv u z‖ ^ 2 ≤
      t * ∫ z in U, deriv χ (‖u z - x₀‖ ^ 2 / t ^ 2) * (-2 * ‖u z - x₀‖ ^ 2 / t ^ 3) *
        ‖deriv u z‖ ^ 2 := by
  have hφ : ContDiff ℝ 1 fun s ↦ χ (s / t ^ 2) := hχ.comp (contDiff_id.div_const _)
  have hφa : Antitone fun s ↦ χ (s / t ^ 2) :=
    hχa.comp_monotone fun a b hab ↦ div_le_div_of_nonneg_right hab (by positivity)
  have hdφ : ∀ s, deriv (fun s ↦ χ (s / t ^ 2)) s = deriv χ (s / t ^ 2) / t ^ 2 := by
    intro s
    have := ((hχ.differentiable one_ne_zero) (s / t ^ 2)).hasDerivAt.comp s
      ((hasDerivAt_id s).div_const (t ^ 2))
    exact this.deriv.trans (by simp [div_eq_mul_inv])
  have key := setIntegral_mul_norm_deriv_sq_le (x₀ := x₀) hU hu hφ hφa
    (ρ := t ^ 2) (fun s hs ↦ hχ1 _ ((one_lt_div (by positivity)).2 hs))
    (by simpa [pow_le_pow_iff_left₀ (norm_nonneg _) ht.le two_ne_zero] using hK)
  simp_rw [hdφ] at key
  have : t * ∫ z in U, deriv χ (‖u z - x₀‖ ^ 2 / t ^ 2) * (-2 * ‖u z - x₀‖ ^ 2 / t ^ 3) *
        ‖deriv u z‖ ^ 2 =
      2 * -∫ z in U, deriv χ (‖u z - x₀‖ ^ 2 / t ^ 2) / t ^ 2 * ‖u z - x₀‖ ^ 2 *
        ‖deriv u z‖ ^ 2 := by
    rw [← integral_const_mul, ← integral_neg, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
    field_simp
  rw [this]
  linarith

/-- **Monotonicity of the weighted area of a holomorphic curve.** Let `u` be holomorphic on an
open set `U ⊆ ℂ` and `x₀` a point such that the sublevel sets `{z ∈ U | ‖u z - x₀‖ ≤ t}`,
`t < r`, are compact. For a nonincreasing `C¹` cutoff `χ` vanishing on `(1, ∞)`, the area of
`u` weighted by `χ(‖u - x₀‖² / t²)`, divided by `t²`, is nondecreasing in `t ∈ (0, r)`. This is
a smoothed form of the statement that the area of `u` in the ball of radius `t` around `x₀`,
divided by the area `π t²` of a flat disc, is nondecreasing. -/
theorem monotoneOn_setIntegral_mul_norm_deriv_sq_div_sq {U : Set ℂ} {u : ℂ → E} {x₀ : E}
    {χ : ℝ → ℝ} {r : ℝ} (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) (hχ : ContDiff ℝ 1 χ)
    (hχa : Antitone χ) (hχ1 : ∀ s, 1 < s → χ s = 0)
    (hK : ∀ t < r, IsCompact {z ∈ U | ‖u z - x₀‖ ≤ t}) :
    MonotoneOn (fun t ↦ (∫ z in U, χ (‖u z - x₀‖ ^ 2 / t ^ 2) * ‖deriv u z‖ ^ 2) / t ^ 2)
      (Ioo 0 r) := by
  have h := fun t (ht : t ∈ Ioo 0 r) ↦ hasDerivAt_integral_cutoff hU hu hχ hχ1 hK ht
  have := monotoneOn_div_rpow_of_mul_le_mul_deriv (α := 2) (convex_Ioo 0 r)
    (fun t ht ↦ ht.1) (fun t ht ↦ (h t ht).continuousAt.continuousWithinAt)
    (by simpa using h) (by simpa using fun t (ht : t ∈ Ioo 0 r) ↦
      two_mul_integral_cutoff_le hU hu hχ hχa hχ1 ht.1 (hK t ht.2))
  simpa [Real.rpow_two] using this

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] in
/-- The area of the model branched cover `ζ ↦ ζ ^ m • c`, weighted by a radial cutoff:
`∫_ℂ χ((|ζ| ^ m a)²) (m |ζ| ^ (m - 1) a)² = m π ∫₀^∞ χ` for `a > 0`. -/
private theorem integral_model_branched_cover {χ : ℝ → ℝ} {m : ℕ} (hm : 1 ≤ m) {a : ℝ}
    (ha : 0 < a) :
    ∫ ζ : ℂ, χ ((‖ζ‖ ^ m * a) ^ 2) * (m * ‖ζ‖ ^ (m - 1) * a) ^ 2 =
      m * π * ∫ s in Ioi 0, χ s := by
  have h := integral_fun_norm_addHaar (volume : Measure ℂ)
    (fun y ↦ χ ((y ^ m * a) ^ 2) * (m * y ^ (m - 1) * a) ^ 2)
  simp only [Complex.finrank_real_complex, measureReal_def, Complex.volume_ball] at h
  rw [h]
  have hsub := integral_comp_rpow_Ioi_of_pos (g := fun y ↦ χ (a ^ 2 * y))
    (p := 2 * m) (by positivity)
  rw [integral_comp_mul_left_Ioi _ 0 (by positivity), mul_zero] at hsub
  have hcongr : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • (χ ((y ^ m * a) ^ 2) *
      (m * y ^ (m - 1) * a) ^ 2) =
      (m * a ^ 2 / 2) * ∫ x in Ioi (0 : ℝ), ((2 * m : ℝ) * x ^ ((2 * m : ℝ) - 1)) •
        χ (a ^ 2 * x ^ (2 * m : ℝ)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) ↦ ?_
    have h1 : (2 * m : ℝ) - 1 = ((2 * m - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    have h2 : (2 * m : ℝ) = ((2 * m : ℕ) : ℝ) := by push_cast; ring
    rw [h1, Real.rpow_natCast, h2, Real.rpow_natCast]
    simp only [smul_eq_mul]
    have h3 : y ^ (2 * m - 1) = y * (y ^ (m - 1)) ^ 2 := by
      rw [← pow_mul, ← pow_succ']
      congr 1
      omega
    have h4 : y ^ (2 * m) = (y ^ m) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [h3, h4]
    push_cast
    field_simp
  rw [hcongr, hsub]
  simp only [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal zero_le_one,
    one_pow, one_mul, ENNReal.coe_toReal, NNReal.coe_real_pi]
  field_simp
  ring

/-- Near a point `z₀` at which `u - u z₀` vanishes to finite order `m`, a holomorphic `u` is
`u z₀ + (z - z₀) ^ m • g z` with `g z₀ ≠ 0`, on a closed disc on which `g` and `g'` are
continuous. -/
private theorem exists_closedBall_factorization {U : Set ℂ} {u : ℂ → E} {z₀ : ℂ}
    (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) (hz₀ : z₀ ∈ U) {m : ℕ}
    (hm : analyticOrderAt (fun z ↦ u z - u z₀) z₀ = m) :
    ∃ g : ℂ → E, ∃ δ > 0, g z₀ ≠ 0 ∧ closedBall z₀ δ ⊆ U ∧
      ContinuousOn g (closedBall z₀ δ) ∧ ContinuousOn (deriv g) (closedBall z₀ δ) ∧
      ∀ z ∈ closedBall z₀ δ, u z - u z₀ = (z - z₀) ^ m • g z ∧
        deriv u z = ((m : ℂ) * (z - z₀) ^ (m - 1)) • g z + (z - z₀) ^ m • deriv g z := by
  have hw : AnalyticAt ℂ (fun z ↦ u z - u z₀) z₀ :=
    (hu.analyticOnNhd hU z₀ hz₀).sub analyticAt_const
  obtain ⟨g, hg, hg0, hfac⟩ := hw.analyticOrderAt_eq_natCast.1 hm
  have hev : ∀ᶠ z in 𝓝 z₀, z ∈ U ∧ AnalyticAt ℂ g z ∧
      ∀ᶠ y in 𝓝 z, u y - u z₀ = (y - z₀) ^ m • g y :=
    Filter.Eventually.and (hU.mem_nhds hz₀) (hg.eventually_analyticAt.and hfac.eventually_nhds)
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 hev
  have hP : ∀ z ∈ closedBall z₀ (ε / 2), z ∈ U ∧ AnalyticAt ℂ g z ∧
      ∀ᶠ y in 𝓝 z, u y - u z₀ = (y - z₀) ^ m • g y := fun z hz ↦
    hεP (lt_of_le_of_lt (mem_closedBall.1 hz) (by linarith))
  refine ⟨g, ε / 2, by positivity, hg0, fun z hz ↦ (hP z hz).1,
    fun z hz ↦ (hP z hz).2.1.continuousAt.continuousWithinAt,
    fun z hz ↦ (hP z hz).2.1.deriv.continuousAt.continuousWithinAt, fun z hz ↦ ?_⟩
  obtain ⟨-, hgz, hfz⟩ := hP z hz
  refine ⟨hfz.self_of_nhds, ?_⟩
  have hd : HasDerivAt (fun y ↦ (y - z₀) ^ m • g y)
      ((z - z₀) ^ m • deriv g z + ((m : ℂ) * (z - z₀) ^ (m - 1) * 1) • g z) z :=
    (((hasDerivAt_id z).sub_const z₀).pow m).smul hgz.differentiableAt.hasDerivAt
  have hfz' : (fun y ↦ u y - u z₀) =ᶠ[𝓝 z] fun y ↦ (y - z₀) ^ m • g y := hfz
  rw [← deriv_sub_const (u z₀), hfz'.deriv_eq, hd.deriv, mul_one, add_comm]

omit [CompleteSpace E] in
/-- Rescaling the factorized map and its derivative at `z₀ + s ζ`: the squared norms of
`(s ζ) ^ m • G₀` and of `m (s ζ) ^ (m - 1) • G₀ + (s ζ) ^ m • G₁` are `s ^ (2 m)` and
`s ^ (2 m - 2)` times those of `ζ ^ m • G₀` and `m ζ ^ (m - 1) • G₀ + s ζ ^ m • G₁`. -/
private theorem norm_sq_rescale {m : ℕ} (hm : 1 ≤ m) {s : ℝ} (hs : 0 < s) (ζ : ℂ) (G₀ G₁ : E) :
    ‖(((s : ℂ) * ζ) ^ m) • G₀‖ ^ 2 / (s ^ m) ^ 2 = (‖ζ‖ ^ m * ‖G₀‖) ^ 2 ∧
      ‖((m : ℂ) * ((s : ℂ) * ζ) ^ (m - 1)) • G₀ + ((s : ℂ) * ζ) ^ m • G₁‖ ^ 2 *
          (s ^ 2 / (s ^ m) ^ 2) =
        ‖((m : ℂ) * ζ ^ (m - 1)) • G₀ + ((s : ℂ) * ζ ^ m) • G₁‖ ^ 2 := by
  refine ⟨?_, ?_⟩
  · rw [norm_smul, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    field_simp
    ring
  · have hvec : ((m : ℂ) * ((s : ℂ) * ζ) ^ (m - 1)) • G₀ + ((s : ℂ) * ζ) ^ m • G₁ =
        ((s : ℂ) ^ (m - 1)) • (((m : ℂ) * ζ ^ (m - 1)) • G₀ + ((s : ℂ) * ζ ^ m) • G₁) := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
      simp only [Nat.add_sub_cancel, smul_add, smul_smul]
      congr 2 <;> ring
    rw [hvec, norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, mul_pow,
      ← pow_mul]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
    simp only [Nat.add_sub_cancel]
    field_simp
    ring

/-- The weighted area density of `u` at scale `s ^ m` around `z₀`, rescaled by `z = z₀ + s ζ`
and normalized so that its integral is the normalized weighted area at radius `s ^ m`. -/
private def rescaledDensity (U : Set ℂ) (u : ℂ → E) (z₀ : ℂ) (χ : ℝ → ℝ) (m : ℕ) (s : ℝ)
    (ζ : ℂ) : ℝ :=
  U.indicator (fun z ↦ χ (‖u z - u z₀‖ ^ 2 / (s ^ m) ^ 2) * ‖deriv u z‖ ^ 2) (z₀ + s • ζ) *
    (s ^ 2 / (s ^ m) ^ 2)

/-- The rescaled density of `TauCeti.rescaledDensity`, written through a factorization
`u - u z₀ = (z - z₀) ^ m • g`; it is continuous in `s` down to `s = 0`. -/
private def blowupProfile (g : ℂ → E) (z₀ : ℂ) (χ : ℝ → ℝ) (m : ℕ) (ζ : ℂ) (s : ℝ) : ℝ :=
  χ ((‖ζ‖ ^ m * ‖g (z₀ + s • ζ)‖) ^ 2) *
    ‖((m : ℂ) * ζ ^ (m - 1)) • g (z₀ + s • ζ) + ((s : ℂ) * ζ ^ m) • deriv g (z₀ + s • ζ)‖ ^ 2

omit [CompleteSpace E] in
/-- On the disc of a factorization `u - u z₀ = (z - z₀) ^ m • g`, the rescaled density is the
blow-up profile. -/
private theorem rescaledDensity_eq_blowupProfile {U : Set ℂ} {u : ℂ → E} {z₀ : ℂ}
    {χ : ℝ → ℝ} {m : ℕ} {g : ℂ → E} {δ : ℝ} (hm : 1 ≤ m) (hball : closedBall z₀ δ ⊆ U)
    (hfac : ∀ z ∈ closedBall z₀ δ, u z - u z₀ = (z - z₀) ^ m • g z ∧
      deriv u z = ((m : ℂ) * (z - z₀) ^ (m - 1)) • g z + (z - z₀) ^ m • deriv g z)
    {s : ℝ} (hs : 0 < s) {ζ : ℂ} (hsζ : s * ‖ζ‖ ≤ δ) :
    rescaledDensity U u z₀ χ m s ζ = blowupProfile g z₀ χ m ζ s := by
  have hz : z₀ + s • ζ ∈ closedBall z₀ δ := add_smul_mem_closedBall hs.le hsζ
  obtain ⟨hfu, hfdu⟩ := hfac _ hz
  have hsub : z₀ + s • ζ - z₀ = (s : ℂ) * ζ := by rw [add_sub_cancel_left, real_smul]
  rw [hsub] at hfu hfdu
  obtain ⟨h1, h2⟩ := norm_sq_rescale hm hs ζ (g (z₀ + s • ζ)) (deriv g (z₀ + s • ζ))
  simp only [rescaledDensity, blowupProfile, indicator_of_mem (hball hz), hfu, hfdu, mul_assoc,
    h2, h1]

/-- The rescaled density at scale `s` is integrable, with integral the normalized weighted area
`(∫_U χ(‖u - u z₀‖² / t²) ‖u'‖²) / t²` at radius `t = s ^ m`. -/
private theorem integral_rescaledDensity {U : Set ℂ} {u : ℂ → E} {z₀ : ℂ} {χ : ℝ → ℝ} {m : ℕ}
    {r : ℝ} (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) (hχ : Continuous χ)
    (hχ1 : ∀ s, 1 < s → χ s = 0) (hK : ∀ t < r, IsCompact {z ∈ U | ‖u z - u z₀‖ ≤ t})
    {s : ℝ} (hs : 0 < s) (hsr : s ^ m < r) :
    Integrable (rescaledDensity U u z₀ χ m s) ∧
      ∫ ζ, rescaledDensity U u z₀ χ m s ζ =
        (∫ z in U, χ (‖u z - u z₀‖ ^ 2 / (s ^ m) ^ 2) * ‖deriv u z‖ ^ 2) / (s ^ m) ^ 2 := by
  have hG := (integrable_indicator_iff hU.measurableSet).2
    (integrableOn_cutoff hU hu hχ hχ1 (pow_pos hs m) (hK _ hsr))
  refine ⟨((hG.comp_add_left z₀).comp_smul hs.ne').mul_const _, ?_⟩
  simp only [rescaledDensity]
  rw [integral_mul_const, Measure.integral_comp_smul volume (fun ζ ↦ U.indicator _ (z₀ + ζ)),
    integral_add_left_eq_self, integral_indicator hU.measurableSet,
    Complex.finrank_real_complex, abs_of_pos (by positivity), smul_eq_mul]
  field_simp

omit [CompleteSpace E] in
/-- As `s → 0`, the blow-up profile tends to the weighted area density of the model branched
cover `ζ ↦ ζ ^ m • g z₀`. -/
private theorem tendsto_blowupProfile {g : ℂ → E} {z₀ : ℂ} {χ : ℝ → ℝ} {m : ℕ}
    (hχ : Continuous χ) (hg : ContinuousAt g z₀) (hdg : ContinuousAt (deriv g) z₀) (ζ : ℂ) :
    Tendsto (blowupProfile g z₀ χ m ζ) (𝓝 0)
      (𝓝 (χ ((‖ζ‖ ^ m * ‖g z₀‖) ^ 2) * (m * ‖ζ‖ ^ (m - 1) * ‖g z₀‖) ^ 2)) := by
  have hγ : Tendsto (fun s : ℝ ↦ z₀ + s • ζ) (𝓝 0) (𝓝 z₀) := by
    have : Continuous (fun s : ℝ ↦ z₀ + s • ζ) := by fun_prop
    simpa using this.tendsto 0
  have hg' := hg.tendsto.comp hγ
  have hdg' := hdg.tendsto.comp hγ
  have hs : Tendsto (fun s : ℝ ↦ ((s : ℂ) * ζ ^ m)) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_ofReal.tendsto (0 : ℝ)).mul_const (ζ ^ m)
  have := ((hχ.tendsto _).comp (((tendsto_const_nhds (x := ‖ζ‖ ^ m)).mul hg'.norm).pow 2)).mul
    ((((tendsto_const_nhds (x := (m : ℂ) * ζ ^ (m - 1))).smul hg').add
      (hs.smul hdg')).norm.pow 2)
  convert this using 2
  · rfl
  · simp only [zero_smul, add_zero, norm_smul, norm_mul, norm_pow, Complex.norm_natCast]

omit [CompleteSpace E] in
/-- A uniform bound on the blow-up profile for `‖ζ‖ ≤ R` and small `s`, from bounds on `g` and
`g'` on the disc of the factorization. -/
private theorem blowupProfile_le {g : ℂ → E} {z₀ : ℂ} {χ : ℝ → ℝ} {m : ℕ} {δ R Mg Mdg : ℝ}
    (hχa : Antitone χ) (hχ1 : ∀ s, 1 < s → χ s = 0)
    (hMg : ∀ z ∈ closedBall z₀ δ, ‖g z‖ ≤ Mg) (hMdg : ∀ z ∈ closedBall z₀ δ, ‖deriv g z‖ ≤ Mdg)
    {s : ℝ} {ζ : ℂ} (hs : 0 < s) (hs1 : s ≤ 1) (hζ : ‖ζ‖ ≤ R) (hsζ : s * ‖ζ‖ ≤ δ) :
    ‖blowupProfile g z₀ χ m ζ s‖ ≤ χ 0 * (m * R ^ (m - 1) * Mg + R ^ m * Mdg) ^ 2 := by
  have hz : z₀ + s • ζ ∈ closedBall z₀ δ := add_smul_mem_closedBall hs.le hsζ
  have hχ0 := cutoff_nonneg hχa hχ1
  rw [blowupProfile, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hχ0 _) (sq_nonneg _))]
  refine mul_le_mul (hχa (sq_nonneg _)) (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
    (sq_nonneg _) (hχ0 0)
  have hR : 0 ≤ R := (norm_nonneg _).trans hζ
  have hgb : ‖g (z₀ + s • ζ)‖ ≤ Mg := hMg _ hz
  have hdgb : ‖deriv g (z₀ + s • ζ)‖ ≤ Mdg := hMdg _ hz
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, norm_mul, norm_pow, Complex.norm_natCast]
    gcongr
  · rw [norm_smul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    calc s * ‖ζ‖ ^ m * ‖deriv g (z₀ + s • ζ)‖ ≤ 1 * R ^ m * Mdg := by gcongr
      _ = R ^ m * Mdg := by ring

/-- **The blow-up limit**: on a ball of radius `R`, the integrals of the rescaled densities tend,
as `s → 0`, to the integral of the weighted area density of the model branched cover. -/
private theorem tendsto_setIntegral_rescaledDensity {U : Set ℂ} {u : ℂ → E} {z₀ : ℂ}
    {χ : ℝ → ℝ} {m : ℕ} {r R : ℝ} {g : ℂ → E} {δ : ℝ} (hU : IsOpen U)
    (hu : DifferentiableOn ℂ u U) (hχ : Continuous χ) (hχa : Antitone χ)
    (hχ1 : ∀ s, 1 < s → χ s = 0) (hK : ∀ t < r, IsCompact {z ∈ U | ‖u z - u z₀‖ ≤ t})
    (hr : 0 < r) (hm : 1 ≤ m) (hR : 0 < R) (hδ : 0 < δ) (hball : closedBall z₀ δ ⊆ U)
    (hgc : ContinuousOn g (closedBall z₀ δ)) (hdgc : ContinuousOn (deriv g) (closedBall z₀ δ))
    (hfac : ∀ z ∈ closedBall z₀ δ, u z - u z₀ = (z - z₀) ^ m • g z ∧
      deriv u z = ((m : ℂ) * (z - z₀) ^ (m - 1)) • g z + (z - z₀) ^ m • deriv g z) :
    Tendsto (fun s ↦ ∫ ζ in ball (0 : ℂ) R, rescaledDensity U u z₀ χ m s ζ) (𝓝[>] 0)
      (𝓝 (∫ ζ in ball (0 : ℂ) R,
        χ ((‖ζ‖ ^ m * ‖g z₀‖) ^ 2) * (m * ‖ζ‖ ^ (m - 1) * ‖g z₀‖) ^ 2)) := by
  obtain ⟨Mg, hMg⟩ := (isCompact_closedBall z₀ δ).exists_bound_of_continuousOn hgc
  obtain ⟨Mdg, hMdg⟩ := (isCompact_closedBall z₀ δ).exists_bound_of_continuousOn hdgc
  refine tendsto_integral_filter_of_dominated_convergence
    (fun _ ↦ χ 0 * (m * R ^ (m - 1) * Mg + R ^ m * Mdg) ^ 2) ?_ ?_
    (integrableOn_const measure_ball_lt_top.ne) ?_
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_pow_lt (Nat.one_le_iff_ne_zero.1 hm) hr)]
      with s (hs : 0 < s) hsr
    exact (integral_rescaledDensity hU hu hχ hχ1 hK hs hsr).1.aestronglyMeasurable.restrict
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds (by positivity :
      (0 : ℝ) < min 1 (δ / R)))] with s (hs : 0 < s) hsδ
    refine (ae_restrict_mem measurableSet_ball).mono fun ζ hζ ↦ ?_
    rw [mem_ball_zero_iff] at hζ
    have hsR : s * R ≤ δ := (le_div_iff₀ hR).1 (hsδ.le.trans (min_le_right _ _))
    have hsζ : s * ‖ζ‖ ≤ δ := (mul_le_mul_of_nonneg_left hζ.le hs.le).trans hsR
    rw [rescaledDensity_eq_blowupProfile hm hball hfac hs hsζ]
    exact blowupProfile_le hχa hχ1 (fun z hz ↦ by simpa using hMg z hz)
      (fun z hz ↦ by simpa using hMdg z hz) hs (hsδ.le.trans (min_le_left _ _)) hζ.le hsζ
  · refine Eventually.of_forall fun ζ ↦ ((tendsto_blowupProfile hχ
      (hgc.continuousAt (closedBall_mem_nhds z₀ hδ))
      (hdgc.continuousAt (closedBall_mem_nhds z₀ hδ)) ζ).mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds (by positivity :
      (0 : ℝ) < δ / (‖ζ‖ + 1)))] with s (hs : 0 < s) hsδ
    refine (rescaledDensity_eq_blowupProfile hm hball hfac hs ?_).symm
    rw [lt_div_iff₀ (by positivity)] at hsδ
    nlinarith [norm_nonneg ζ]

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] in
/-- The weighted area density of the model branched cover vanishes outside a ball. -/
private theorem model_density_eq_zero {χ : ℝ → ℝ} (hχ1 : ∀ s, 1 < s → χ s = 0) {m : ℕ}
    (hm : 1 ≤ m) {a : ℝ} (ha : 0 < a) {ζ : ℂ} (hζ : ζ ∉ ball (0 : ℂ) (max 1 a⁻¹ + 1)) :
    χ ((‖ζ‖ ^ m * a) ^ 2) * (m * ‖ζ‖ ^ (m - 1) * a) ^ 2 = 0 := by
  rw [mem_ball_zero_iff, not_lt] at hζ
  have h1 : 1 ≤ ‖ζ‖ := by linarith [le_max_left 1 a⁻¹]
  have h2 : a⁻¹ < ‖ζ‖ := by linarith [le_max_right 1 a⁻¹]
  have h3 : 1 < ‖ζ‖ ^ m * a := by
    calc 1 = a⁻¹ * a := (inv_mul_cancel₀ ha.ne').symm
      _ < ‖ζ‖ * a := by gcongr
      _ ≤ ‖ζ‖ ^ m * a := by gcongr; exact le_self_pow₀ h1 (by omega)
  simp [hχ1 _ (one_lt_pow₀ h3 two_ne_zero)]

/-- **The blow-up at a point of multiplicity `m`.** If `u - u z₀` vanishes to order `m` at
`z₀ ∈ U`, the normalized weighted area `(∫_U χ(‖u - u z₀‖² / t²) ‖u'‖²) / t²` is at least
`m π ∫₀^∞ χ`, the normalized weighted area of the model branched cover `ζ ↦ ζ ^ m`. The
normalized weighted area is nondecreasing in `t`, and as `t → 0` the rescalings
`ζ ↦ (u (z₀ + t ^ (1 / m) ζ) - u z₀) / t` converge to `ζ ↦ ζ ^ m • g z₀`. -/
private theorem analyticOrderNatAt_mul_pi_mul_integral_le_integral_div_sq {U : Set ℂ} {u : ℂ → E}
    {z₀ : ℂ} {χ : ℝ → ℝ} {r t : ℝ} (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) (hz₀ : z₀ ∈ U)
    (hχ : ContDiff ℝ 1 χ) (hχa : Antitone χ) (hχ1 : ∀ s, 1 < s → χ s = 0)
    (hK : ∀ t < r, IsCompact {z ∈ U | ‖u z - u z₀‖ ≤ t}) (ht : t ∈ Ioo 0 r) :
    analyticOrderNatAt (fun z ↦ u z - u z₀) z₀ * π * ∫ s in Ioi 0, χ s ≤
      (∫ z in U, χ (‖u z - u z₀‖ ^ 2 / t ^ 2) * ‖deriv u z‖ ^ 2) / t ^ 2 := by
  set m := analyticOrderNatAt (fun z ↦ u z - u z₀) z₀ with hm_def
  set A : ℝ → ℝ := fun t ↦ (∫ z in U, χ (‖u z - u z₀‖ ^ 2 / t ^ 2) * ‖deriv u z‖ ^ 2) / t ^ 2
  have hχ0 := cutoff_nonneg hχa hχ1
  by_cases htop : analyticOrderAt (fun z ↦ u z - u z₀) z₀ = ⊤
  · simpa [m, analyticOrderNatAt, htop] using div_nonneg (setIntegral_nonneg hU.measurableSet
      fun z _ ↦ mul_nonneg (hχ0 _) (sq_nonneg _)) (sq_nonneg t)
  obtain ⟨g, δ, hδ, hg0, hball, hgc, hdgc, hfac⟩ :=
    exists_closedBall_factorization hU hu hz₀ (Nat.cast_analyticOrderNatAt htop).symm
  rw [← hm_def] at hfac
  have hm : 1 ≤ m := by
    by_contra h
    have := (hfac z₀ (mem_closedBall_self hδ.le)).1
    rw [show m = 0 by omega, sub_self, pow_zero, one_smul] at this
    exact hg0 this.symm
  have ha : 0 < ‖g z₀‖ := norm_pos_iff.2 hg0
  set R := max 1 ‖g z₀‖⁻¹ + 1
  -- Eventually, the integral of the rescaled density over the ball of radius `R` is at most
  -- the normalized weighted area at radius `s ^ m < t`, hence at radius `t`.
  have hupper : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∫ ζ in ball (0 : ℂ) R, rescaledDensity U u z₀ χ m s ζ ≤
      A t := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_pow_lt (Nat.one_le_iff_ne_zero.1 hm) ht.1)]
      with s (hs : 0 < s) hst
    obtain ⟨hint, heq⟩ := integral_rescaledDensity hU hu hχ.continuous hχ1 hK hs (hst.trans ht.2)
    calc ∫ ζ in ball (0 : ℂ) R, rescaledDensity U u z₀ χ m s ζ
        ≤ ∫ ζ, rescaledDensity U u z₀ χ m s ζ :=
          setIntegral_le_integral hint (Eventually.of_forall fun ζ ↦ mul_nonneg
            (indicator_nonneg (fun z _ ↦ mul_nonneg (hχ0 _) (sq_nonneg _)) _) (by positivity))
      _ = A (s ^ m) := heq
      _ ≤ A t := monotoneOn_setIntegral_mul_norm_deriv_sq_div_sq hU hu hχ hχa hχ1 hK
          ⟨pow_pos hs m, hst.trans ht.2⟩ ht hst.le
  have hle := le_of_tendsto (tendsto_setIntegral_rescaledDensity hU hu hχ.continuous hχa hχ1 hK
    (ht.1.trans ht.2) hm (by positivity) hδ hball hgc hdgc hfac) hupper
  rwa [setIntegral_eq_integral_of_forall_compl_eq_zero
    fun ζ hζ ↦ model_density_eq_zero hχ1 hm ha hζ, integral_model_branched_cover hm ha] at hle

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] in
/-- The smooth cutoffs `s ↦ smoothTransition ((1 - s) / ε)`, equal to `1` on `(-∞, 1 - ε]` and to
`0` on `[1, ∞)`, have integral at least `1 - ε` over `(0, ∞)`. -/
private theorem sub_le_integral_smoothTransition {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    1 - ε ≤ ∫ s in Ioi 0, Real.smoothTransition ((1 - s) / ε) := by
  have hc : Continuous fun s : ℝ ↦ Real.smoothTransition ((1 - s) / ε) := by fun_prop
  have hint : IntegrableOn (fun s : ℝ ↦ Real.smoothTransition ((1 - s) / ε)) (Ioi 0) := by
    refine (hc.integrableOn_Icc (a := 0) (b := 1)).of_forall_sdiff_eq_zero measurableSet_Ioi ?_
    rintro s ⟨hs, hs'⟩
    simp only [mem_Icc, not_and_or, not_le] at hs'
    rcases hs' with hs' | hs'
    · exact absurd (mem_Ioi.1 hs) (not_lt.2 hs'.le)
    · exact Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)
  calc 1 - ε = ∫ s in Ioc 0 (1 - ε), Real.smoothTransition ((1 - s) / ε) := by
        rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ ↦ (1 : ℝ)) fun s hs ↦
          Real.smoothTransition.one_of_one_le ((le_div_iff₀ hε).2 (by linarith [hs.2]))]
        simp [hε1.le]
    _ ≤ ∫ s in Ioi 0, Real.smoothTransition ((1 - s) / ε) :=
        setIntegral_mono_set hint
          (Eventually.of_forall fun _ ↦ Real.smoothTransition.nonneg _)
          (ae_of_all _ fun _ hx ↦ Ioc_subset_Ioi_self hx)

/-- The area weighted by a cutoff `0 ≤ χ ≤ 1` vanishing on `(1, ∞)`, at a radius `t < r`, is at
most the area over the preimage of the open ball of radius `r`. -/
private theorem ofReal_integral_cutoff_le_lintegral {U : Set ℂ} {u : ℂ → E} {x₀ : E}
    {χ : ℝ → ℝ} {r t : ℝ} (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) (hχ : Continuous χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχle : ∀ x, χ x ≤ 1) (hχ1 : ∀ s, 1 < s → χ s = 0)
    (hK : IsCompact {z ∈ U | ‖u z - x₀‖ ≤ t}) (ht : t ∈ Ioo 0 r) :
    ENNReal.ofReal (∫ z in U, χ (‖u z - x₀‖ ^ 2 / t ^ 2) * ‖deriv u z‖ ^ 2) ≤
      ∫⁻ z in {z ∈ U | ‖u z - x₀‖ < r}, ‖deriv u z‖ₑ ^ 2 := by
  set S := {z ∈ U | ‖u z - x₀‖ < r}
  have hcu : ContinuousOn u U := hu.continuousOn
  have hS : MeasurableSet S := by
    have : S = U ∩ (fun z ↦ ‖u z - x₀‖) ⁻¹' Iio r := by ext; simp [S]
    rw [this]
    exact (ContinuousOn.isOpen_inter_preimage (by fun_prop) hU isOpen_Iio).measurableSet
  rw [ofReal_integral_eq_lintegral_ofReal (integrableOn_cutoff hU hu hχ hχ1 ht.1 hK)
    (Eventually.of_forall fun z ↦ mul_nonneg (hχ0 _) (sq_nonneg _))]
  calc ∫⁻ z in U, ENNReal.ofReal (χ (‖u z - x₀‖ ^ 2 / t ^ 2) * ‖deriv u z‖ ^ 2)
      ≤ ∫⁻ z in U, S.indicator (fun z ↦ ‖deriv u z‖ₑ ^ 2) z := by
        refine setLIntegral_mono' hU.measurableSet fun z hz ↦ ?_
        by_cases hzS : z ∈ S
        · rw [indicator_of_mem hzS, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (sq_nonneg _) (hχle _))
        · have hlt : t < ‖u z - x₀‖ := by
            simp only [S, mem_ofPred_eq, not_and, not_lt] at hzS
            exact ht.2.trans_le (hzS hz)
          simp [hχ1 _ (one_lt_sq_div_sq ht.1 hlt)]
    _ = ∫⁻ z in S, ‖deriv u z‖ₑ ^ 2 := by
        rw [lintegral_indicator hS, Measure.restrict_restrict hS,
          inter_eq_left.2 fun z (hz : z ∈ S) ↦ hz.1]

/-- For each `ε ∈ (0, 1)`, the area over the preimage of the ball of radius `r` is at least
`m π (1 - ε)³ r²`: apply the blow-up bound to the cutoff `smoothTransition ((1 - s) / ε)` at
radius `(1 - ε) r`. -/
private theorem ofReal_analyticOrderNatAt_mul_pi_mul_le_lintegral_of_mem_Ioo {U : Set ℂ}
    {u : ℂ → E} {z₀ : ℂ} {r : ℝ} (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) (hz₀ : z₀ ∈ U)
    (hr : 0 ≤ r)
    (hK : ∀ t < r, IsCompact {z ∈ U | ‖u z - u z₀‖ ≤ t}) {ε : ℝ} (hε : ε ∈ Ioo 0 1) :
    ENNReal.ofReal (analyticOrderNatAt (fun z ↦ u z - u z₀) z₀ * π * ((1 - ε) ^ 3 * r ^ 2)) ≤
      ∫⁻ z in {z ∈ U | ‖u z - u z₀‖ < r}, ‖deriv u z‖ₑ ^ 2 := by
  obtain ⟨hε, hε1⟩ := hε
  rcases hr.eq_or_lt with hr0 | hr0
  · simp [← hr0]
  set χ : ℝ → ℝ := fun s ↦ Real.smoothTransition ((1 - s) / ε)
  have hχ : ContDiff ℝ 1 χ := Real.smoothTransition.contDiff.comp (by fun_prop)
  have hχa : Antitone χ := fun a b hab ↦
    Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) hε.le)
  have hχ1 : ∀ s, 1 < s → χ s = 0 := fun s hs ↦
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)
  set t := (1 - ε) * r
  have ht : t ∈ Ioo 0 r := ⟨by positivity, by simp only [t]; nlinarith⟩
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (ofReal_integral_cutoff_le_lintegral hU hu
    hχ.continuous (fun _ ↦ Real.smoothTransition.nonneg _)
    (fun _ ↦ Real.smoothTransition.le_one _) hχ1 (hK t ht.2) ht)
  have h1 := sub_le_integral_smoothTransition hε hε1
  have h2 := (le_div_iff₀ (by positivity : (0 : ℝ) < t ^ 2)).1
    (analyticOrderNatAt_mul_pi_mul_integral_le_integral_div_sq hU hu hz₀ hχ hχa hχ1 hK ht)
  calc analyticOrderNatAt (fun z ↦ u z - u z₀) z₀ * π * ((1 - ε) ^ 3 * r ^ 2)
      = analyticOrderNatAt (fun z ↦ u z - u z₀) z₀ * π * (1 - ε) * t ^ 2 := by
        simp only [t]; ring
    _ ≤ analyticOrderNatAt (fun z ↦ u z - u z₀) z₀ * π * (∫ s in Ioi 0, χ s) * t ^ 2 := by
        gcongr
    _ ≤ _ := h2

/-- **Monotonicity for holomorphic curves, with multiplicity.** Let `u` be holomorphic on an
open set `U ⊆ ℂ` with values in a complex inner product space, and `z₀ ∈ U` a point such that
the sets `{z ∈ U | ‖u z - u z₀‖ ≤ t}`, `t < r`, are compact; for instance `U ⊆ ℂ = S² \ {∞}` is
the preimage of a ball of radius `r` around `u z₀` under a map from `S²` holomorphic over the
ball, when that preimage avoids `∞`. Then the area of `u`
over the preimage of that open ball is at least `m π r²`, where `m` is the order of vanishing of
`u - u z₀` at `z₀`, its local multiplicity. The area is the integral of `‖u'‖²`, the pullback of
the standard symplectic form by the holomorphic map `u`. -/
theorem ofReal_analyticOrderNatAt_mul_pi_mul_sq_le_setLIntegral_enorm_deriv_sq {U : Set ℂ}
    {u : ℂ → E} {z₀ : ℂ} {r : ℝ} (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) (hz₀ : z₀ ∈ U)
    (hr : 0 ≤ r)
    (hK : ∀ t < r, IsCompact {z ∈ U | ‖u z - u z₀‖ ≤ t}) :
    ENNReal.ofReal (analyticOrderNatAt (fun z ↦ u z - u z₀) z₀ * π * r ^ 2) ≤
      ∫⁻ z in {z ∈ U | ‖u z - u z₀‖ < r}, ‖deriv u z‖ₑ ^ 2 := by
  -- Let `ε → 0` in `ofReal_analyticOrderNatAt_mul_pi_mul_le_lintegral_of_mem_Ioo`.
  set m := analyticOrderNatAt (fun z ↦ u z - u z₀) z₀
  have hlim : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal (m * π * ((1 - ε) ^ 3 * r ^ 2))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (m * π * r ^ 2))) := by
    have : Continuous fun ε : ℝ ↦ ENNReal.ofReal (m * π * ((1 - ε) ^ 3 * r ^ 2)) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hlim (by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with ε hε using
      ofReal_analyticOrderNatAt_mul_pi_mul_le_lintegral_of_mem_Ioo hU hu hz₀ hr hK hε)

/-- **Monotonicity for holomorphic curves.** Let `u` be holomorphic on an open set `U ⊆ ℂ` with
values in a complex inner product space, and `z₀ ∈ U` a point such that the sets
`{z ∈ U | ‖u z - u z₀‖ ≤ t}`, `t < r`, are compact. Then the area of `u` over the preimage of the
open ball of radius `r` around `u z₀` is at least `π r²`, also when `z₀` is a critical point of
`u`. -/
theorem ofReal_pi_mul_sq_le_setLIntegral_enorm_deriv_sq {U : Set ℂ} {u : ℂ → E} {z₀ : ℂ} {r : ℝ}
    (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) (hz₀ : z₀ ∈ U) (hr : 0 ≤ r)
    (hK : ∀ t < r, IsCompact {z ∈ U | ‖u z - u z₀‖ ≤ t}) :
    ENNReal.ofReal (π * r ^ 2) ≤ ∫⁻ z in {z ∈ U | ‖u z - u z₀‖ < r}, ‖deriv u z‖ₑ ^ 2 := by
  rcases hr.eq_or_lt with rfl | hr0
  · simp
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    (ofReal_analyticOrderNatAt_mul_pi_mul_sq_le_setLIntegral_enorm_deriv_sq hU hu hz₀ hr hK)
  have hK0 : IsCompact {z ∈ U | u z - u z₀ = 0} := by
    simpa using hK 0 hr0
  have hm : (1 : ℝ) ≤ analyticOrderNatAt (fun z ↦ u z - u z₀) z₀ := by
    exact_mod_cast ((hu.analyticOnNhd hU).sub analyticOnNhd_const)
      |>.one_le_analyticOrderNatAt_of_isCompact hU hz₀ (sub_self _) hK0
  rw [mul_assoc]
  exact le_mul_of_one_le_left (by positivity) hm

end TauCeti
