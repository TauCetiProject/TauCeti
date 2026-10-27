/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.PoissonIntegral.Ball
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import TauCeti.Analysis.Complex.ParametricIntegral
import TauCeti.Analysis.InnerProductSpace.Harmonic.Ball
import TauCeti.Analysis.InnerProductSpace.Harmonic.Isometry

/-!
# Harmonic functions are real analytic

Let `E` be a finite-dimensional real inner product space. This file proves that a function
`f : E → F`, with `F` finite-dimensional, which is harmonic at a point is real analytic there
(`InnerProductSpace.HarmonicAt.analyticAt`). Mathlib proves this for `E = ℂ` by writing a harmonic
function locally as the real part of a holomorphic one (`HarmonicAt.analyticAt`); that argument has
no analogue in other dimensions. Consequently harmonic functions satisfy unique continuation: two
functions harmonic on a connected open set which agree near one of its points agree on all of it
(`InnerProductSpace.HarmonicOnNhd.eqOn_of_preconnected_of_eventuallyEq`). This is how potentials
of distributions, which are harmonic off the support, are shown to vanish on whole components of
the complement of the support.

## The argument

By the Poisson representation `TauCeti.eqOn_ballPoissonIntegral_of_harmonicOnNhd`, a function
harmonic near the closed unit ball of `ℝⁿ` is, in the open ball, the Poisson integral

`P[g](x) = ∫_S K(x, y) g(y) dσ(y)`,  `K(x, y) = (1 - ‖x‖²) / (n ωₙ ‖x - y‖ⁿ)`,

of its boundary values `g`. The kernel extends holomorphically to complex arguments: with
`q(w) = ∑ i, w i ^ 2`, the function

`(z, w) ↦ (1 - q z) / (n ωₙ q(z - w) ^ (n / 2))`

on `ℂⁿ × ℂⁿ` is holomorphic near every pair `(x, y)` of distinct real points, since there
`q(x - y) = ‖x - y‖²` is a positive real number, at which the principal power is holomorphic. It
restricts to `K` on real points. Integrating over the sphere preserves holomorphy in `z`
(`TauCeti.analyticAt_integral_smul`), so `P[g]` is the restriction to `ℝⁿ` of a holomorphic
function on a neighbourhood of the ball in `ℂⁿ`, hence real analytic there
(`TauCeti.analyticOnNhd_ballPoissonIntegral`). A general harmonic function is reduced to this case
by an isometry with `ℝⁿ`, a translation and a dilation.

## Main declarations

* `TauCeti.analyticOnNhd_ballPoissonIntegral`: the Poisson integral of integrable boundary data is
  real analytic in the open unit ball.
* `InnerProductSpace.HarmonicAt.analyticAt`, `InnerProductSpace.HarmonicOnNhd.analyticOnNhd`:
  harmonic functions are real analytic.
* `InnerProductSpace.HarmonicOnNhd.eqOn_of_preconnected_of_eventuallyEq`: unique continuation of
  harmonic functions.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.2.3, Theorem 10.
* S. Axler, P. Bourdon, W. Ramey, *Harmonic Function Theory*, 2nd ed., Chapter 1.
-/

public section

noncomputable section

open Complex InnerProductSpace MeasureTheory Metric Set Filter

open scoped Topology

namespace TauCeti

variable {n : ℕ}

/-! ### The complexified Poisson kernel -/

/-- The inclusion of `ℝⁿ` into `ℂⁿ`, coordinatewise. -/
private def complexify (n : ℕ) : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℂ) :=
  (ContinuousLinearMap.piMap fun _ ↦ ofRealCLM).comp
    (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap

private theorem complexify_apply (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    complexify n x i = x i := by
  simp [complexify]

/-- The complex quadratic form `q(w) = ∑ i, w i ^ 2` on `ℂⁿ`, which restricts to `‖x‖²` on
`ℝⁿ`. -/
private def sumSq (w : Fin n → ℂ) : ℂ :=
  ∑ i, w i ^ 2

private theorem sumSq_complexify (x : EuclideanSpace ℝ (Fin n)) :
    sumSq (complexify n x) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  simp [sumSq, complexify_apply, EuclideanSpace.real_norm_sq_eq]

private theorem analyticAt_sumSq (w : Fin n → ℂ) : AnalyticAt ℂ sumSq w :=
  Finset.analyticAt_fun_sum _ fun i _ ↦ (analyticAt_pi_iff.1 analyticAt_id i).pow 2

/-- The holomorphic extension of the Poisson kernel of the unit ball to `ℂⁿ × ℂⁿ`. -/
private def complexPoissonKernel (n : ℕ) (p : (Fin n → ℂ) × (Fin n → ℂ)) : ℂ :=
  (1 - sumSq p.1) / ((n : ℂ) * (volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) : ℂ) *
    sumSq (p.1 - p.2) ^ ((n : ℂ) / 2))

/-- On real points the complexified kernel is the Poisson kernel. -/
private theorem complexPoissonKernel_complexify (x y : EuclideanSpace ℝ (Fin n)) :
    complexPoissonKernel n (complexify n x, complexify n y) = ballPoissonKernel n x y := by
  have hpos : 0 ≤ ‖x - y‖ := norm_nonneg _
  have hpow : ((‖x - y‖ ^ 2 : ℝ) : ℂ) ^ ((n : ℂ) / 2) = ((‖x - y‖ ^ n : ℝ) : ℂ) := by
    rw [show ((n : ℂ) / 2) = (((n : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (by positivity), ← Real.rpow_natCast ‖x - y‖ 2, ← Real.rpow_mul hpos,
      ← Real.rpow_natCast]
    congr 2
    ring
  rw [complexPoissonKernel, ← map_sub, sumSq_complexify, sumSq_complexify, hpow,
    ballPoissonKernel_def]
  norm_cast

/-- The complexified kernel is holomorphic near every pair of distinct real points. -/
private theorem analyticAt_complexPoissonKernel (hn : n ≠ 0) {x y : EuclideanSpace ℝ (Fin n)}
    (hxy : x ≠ y) :
    AnalyticAt ℂ (complexPoissonKernel n) (complexify n x, complexify n y) := by
  have hq : sumSq (complexify n x - complexify n y) = ((‖x - y‖ ^ 2 : ℝ) : ℂ) := by
    rw [← map_sub, sumSq_complexify]
  have hq₀ : 0 < ‖x - y‖ ^ 2 := by
    have := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    positivity
  have hdiff : AnalyticAt ℂ (fun p : (Fin n → ℂ) × (Fin n → ℂ) ↦ sumSq (p.1 - p.2))
      (complexify n x, complexify n y) :=
    (analyticAt_sumSq _).comp (analyticAt_fst.sub analyticAt_snd)
  refine (analyticAt_const.sub ((analyticAt_sumSq _).comp analyticAt_fst)).div
    (analyticAt_const.mul (hdiff.cpow analyticAt_const ?_)) ?_
  · simpa [hq] using ofReal_mem_slitPlane.mpr hq₀
  · simp only [hq, ne_eq, mul_eq_zero, Nat.cast_eq_zero, hn, ofReal_eq_zero, false_or,
      cpow_eq_zero_iff, not_or, not_and, not_not]
    exact ⟨(volume_real_unitBall_pos n).ne', fun h ↦ absurd h hq₀.ne'⟩

/-! ### Analyticity of the Poisson integral -/

/-- **The Poisson integral is real analytic.** For integrable boundary data `g` on the unit
sphere of `ℝⁿ`, the Poisson integral `P[g]` is real analytic in the open unit ball. -/
theorem analyticOnNhd_ballPoissonIntegral {g : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ}
    (hg : Integrable g volume.toSphere) :
    AnalyticOnNhd ℝ (ballPoissonIntegral g) (ball 0 1) := by
  intro x hx
  rcases eq_or_ne n 0 with rfl | hn
  · -- `ℝ⁰` is a point, on which every function is analytic.
    exact analyticAt_const.congr
      (Eventually.of_forall fun y ↦ congrArg (ballPoissonIntegral g) (Subsingleton.elim x y))
  have hxS : ∀ y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, x ≠ y := fun y hxy ↦ by
    rw [mem_ball_zero_iff, hxy, norm_eq_of_mem_sphere y] at hx
    exact lt_irrefl _ hx
  -- The holomorphic extension `F` of the Poisson integral to complex arguments.
  set F : (Fin n → ℂ) → ℂ := fun z ↦
    ∫ y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      (g y : ℂ) • complexPoissonKernel n (z, complexify n y) ∂volume.toSphere
  have hF : AnalyticAt ℂ F (complexify n x) := by
    refine analyticAt_integral_smul ((isCompact_sphere 0 1).image (complexify n).continuous)
      ((complexify n).continuous.comp continuous_subtype_val)
      (fun y ↦ mem_image_of_mem _ y.2) ?_ hg.ofReal
    rintro _ ⟨y, hy, rfl⟩
    exact analyticAt_complexPoissonKernel hn (hxS ⟨y, hy⟩)
  -- On real points, `F` is the Poisson integral.
  have hFP : ballPoissonIntegral g = fun x' ↦ (F (complexify n x')).re := by
    ext x'
    simp only [F, complexPoissonKernel_complexify, smul_eq_mul, ← ofReal_mul,
      ballPoissonIntegral_def, mul_comm (g _)]
    rw [integral_complex_ofReal, ofReal_re]
  rw [hFP]
  exact (reCLM.analyticAt _).comp (hF.restrictScalars.comp ((complexify n).analyticAt x))

end TauCeti

/-! ### Harmonic functions are analytic -/

namespace InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : E → F} {x : E}

open TauCeti in
/-- A real-valued harmonic function is real analytic. -/
private theorem HarmonicAt.analyticAt_real {f : E → ℝ} (hf : HarmonicAt f x) :
    AnalyticAt ℝ f x := by
  rcases subsingleton_or_nontrivial E with _ | _
  · exact analyticAt_const.congr (Eventually.of_forall fun y ↦ congrArg f (Subsingleton.elim x y))
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.1 (isOpen_setOfPred_harmonicAt (f := f)) x hf
  set d := Module.finrank ℝ E
  have hd : d ≠ 0 := Module.finrank_pos.ne'
  set e := (stdOrthonormalBasis ℝ E).repr
  set r := R / 2
  have hr : 0 < r := half_pos hR
  -- The rescaled function `v y = f (x + r • y)`, transported to `ℝᵈ`, is harmonic on `ball 0 2`.
  set v : EuclideanSpace ℝ (Fin d) → ℝ := fun y ↦ f (x + r • e.symm y)
  have hv : HarmonicOnNhd v (ball 0 2) := by
    have h₁ : HarmonicOnNhd (fun y ↦ f (x + r • y)) (ball 0 2) :=
      (harmonicOnNhd_comp_const_add_smul_ball_radius_iff x hr.ne' 2).2 fun y hy ↦
        hball (by rwa [Real.norm_of_nonneg hr.le, show r * 2 = R by ring] at hy)
    have h₂ := (harmonicOnNhd_comp_linearIsometryEquiv_right_iff e.symm).2 h₁
    rwa [LinearIsometryEquiv.preimage_ball, map_zero] at h₂
  -- By the Poisson representation, `v` is analytic in the unit ball, in particular at `0`.
  have hv₀ : AnalyticAt ℝ v 0 := by
    have hvc : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ContinuousAt v y :=
      fun y hy ↦ (hv y (closedBall_subset_ball one_lt_two hy)).1.continuousAt
    have hvS : Continuous fun y : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ↦ v y :=
      continuous_iff_continuousAt.2 fun y ↦
        (hvc y (sphere_subset_closedBall y.2)).comp continuous_subtype_val.continuousAt
    have hrep := eqOn_ballPoissonIntegral_of_harmonicOnNhd hd
      (fun y hy ↦ (hvc y hy).continuousWithinAt) (hv.mono (ball_subset_ball one_le_two))
    refine (analyticOnNhd_ballPoissonIntegral (hvS.integrable_of_hasCompactSupport
      (.of_compactSpace _)) 0 (mem_ball_self one_pos)).congr ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self one_pos)] with y hy
    exact (hrep hy).symm
  -- `f` is `v` composed with the affine map `z ↦ e (r⁻¹ • (z - x))`, sending `x` to `0`.
  set L : E →L[ℝ] EuclideanSpace ℝ (Fin d) := r⁻¹ • (e.toContinuousLinearEquiv : E →L[ℝ] _)
  have hfv : f = fun z ↦ v (L (z - x)) := funext fun z ↦ by
    simp [v, L, smul_smul, hr.ne']
  rw [hfv]
  have hψ : AnalyticAt ℝ (fun z ↦ L (z - x)) x :=
    (L.analyticAt _).comp (analyticAt_id.sub analyticAt_const)
  exact AnalyticAt.comp (f := fun z ↦ L (z - x)) (by simpa using hv₀) hψ

/-- **Harmonic functions are real analytic.** A function on a finite-dimensional real inner
product space, with values in a finite-dimensional real normed space, which is harmonic at a
point is real analytic there. -/
theorem HarmonicAt.analyticAt (hf : HarmonicAt f x) : AnalyticAt ℝ f x := by
  -- Reduce to real-valued functions through the coordinates of a basis of `F`.
  set b := Module.finBasis ℝ F
  set c := b.equivFunL
  have hc : AnalyticAt ℝ (c ∘ f) x := analyticAt_pi_iff.2 fun i ↦
    ((hf.comp_CLM ((ContinuousLinearMap.proj i).comp c.toContinuousLinearMap)).analyticAt_real)
  simpa [Function.comp_def] using (c.symm.toContinuousLinearMap.analyticAt _).comp hc

/-- **Harmonic functions are real analytic.** A function harmonic on a neighbourhood of a set is
real analytic there. -/
theorem HarmonicOnNhd.analyticOnNhd {s : Set E} (hf : HarmonicOnNhd f s) :
    AnalyticOnNhd ℝ f s :=
  fun x hx ↦ (hf x hx).analyticAt

/-- **Unique continuation for harmonic functions.** Two functions harmonic on a preconnected set
`U`, which agree in a neighbourhood of a point of `U`, agree on all of `U`. -/
theorem HarmonicOnNhd.eqOn_of_preconnected_of_eventuallyEq {f g : E → F} {U : Set E}
    (hf : HarmonicOnNhd f U) (hg : HarmonicOnNhd g U) (hU : IsPreconnected U) {z₀ : E}
    (h₀ : z₀ ∈ U) (hfg : f =ᶠ[𝓝 z₀] g) : EqOn f g U :=
  hf.analyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hg.analyticOnNhd hU h₀ hfg

end InnerProductSpace
