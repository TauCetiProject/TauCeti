/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.PoissonIntegral.Analytic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Ball
import TauCeti.Analysis.InnerProductSpace.Harmonic.Isometry

/-!
# Harmonic functions are real analytic

Let `E` be a finite-dimensional real inner product space. This file proves that a function
`f : E → F`, with `F` finite-dimensional, which is harmonic at a point is real analytic there
(`InnerProductSpace.HarmonicAt.analyticAt`). Mathlib proves this for `E = ℂ` by writing a harmonic
function locally as the real part of a holomorphic one (`HarmonicAt.analyticAt`); that argument has
no analogue in other dimensions. Consequently harmonic functions satisfy unique continuation: two
functions harmonic on a connected open set which agree near one of its points agree on all of it,
by applying Mathlib's identity principle `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` to
`InnerProductSpace.HarmonicOnNhd.analyticOnNhd`. This is how potentials of distributions, which
are harmonic off the support, are shown to vanish on whole components of the complement of the
support.

## The argument

By the Poisson representation `TauCeti.eqOn_ballPoissonIntegral_of_harmonicOnNhd`, a function
harmonic near the closed unit ball of `ℝⁿ` is, in the open ball, the Poisson integral of its
boundary values, which is real analytic there (`TauCeti.analyticOnNhd_ballPoissonIntegral`). A
general harmonic function is reduced to this case by an isometry with `ℝⁿ`, a translation and a
dilation.

## Main declarations

* `InnerProductSpace.HarmonicAt.analyticAt`, `InnerProductSpace.HarmonicOnNhd.analyticOnNhd`:
  harmonic functions are real analytic.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.2.3, Theorem 10.
* S. Axler, P. Bourdon, W. Ramey, *Harmonic Function Theory*, 2nd ed., Chapter 1.
-/

public section

noncomputable section

open InnerProductSpace Metric Set Filter

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
  have hr₂ : r * 2 = R := by ring
  -- The rescaled function `v y = f (x + r • y)`, transported to `ℝᵈ`, is harmonic on `ball 0 2`.
  set v : EuclideanSpace ℝ (Fin d) → ℝ := fun y ↦ f (x + r • e.symm y)
  have hv : HarmonicOnNhd v (ball 0 2) := by
    have h₁ : HarmonicOnNhd (fun y ↦ f (x + r • y)) (ball 0 2) :=
      (harmonicOnNhd_comp_const_add_smul_ball_radius_iff x hr.ne' 2).2 fun y hy ↦
        hball (by rwa [Real.norm_of_nonneg hr.le, hr₂] at hy)
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

end InnerProductSpace
