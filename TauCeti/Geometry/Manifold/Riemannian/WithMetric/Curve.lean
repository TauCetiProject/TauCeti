/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic
public import TauCeti.Geometry.Manifold.Riemannian.ArcLength
import TauCeti.Geometry.Manifold.ContMDiff.Defs
import TauCeti.Geometry.Manifold.Diffeomorph.Basic

/-!
# Curve speed, length and energy in a chosen metric

The tautological map to `WithMetric g` transports a curve to the copy carrying `g`.
Its native speed, real path length and energy are computed directly from `g.inner`
and the original curve velocity. The speed and energy identities also cover the
totalized zero velocity of a nondifferentiable curve.

## References

* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section

open Bundle Filter MeasureTheory Set TauCeti.Manifold
open scoped ContDiff Manifold Topology

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {γ : ℝ → M}

/-- The speed of a curve in the copy carrying `g₀` is the square root of its squared norm
computed with `g₀`. No differentiability assumption on the curve is required. -/
theorem norm_curveVelocity_toWithMetric
    (g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (u : ℝ) :
    ‖curveVelocity I (TauCeti.WithMetric.toWithMetric g₀ ∘ γ) u‖ =
      Real.sqrt (g₀.inner (γ u) (curveVelocity I γ u) (curveVelocity I γ u)) := by
  have hv : curveVelocity I (TauCeti.WithMetric.toWithMetric g₀ ∘ γ) u =
      mfderiv I I (TauCeti.WithMetric.toWithMetric g₀) (γ u) (curveVelocity I γ u) := by
    rw [curveVelocity_apply, curveVelocity_apply,
      ← TauCeti.WithMetric.coe_diffeomorph_symm ∞,
      Diffeomorph.mfderiv_diffeomorph_comp _ (by simp)]
    rfl
  have hback : mfderiv I I TauCeti.WithMetric.ofWithMetric
      (TauCeti.WithMetric.toWithMetric g₀ (γ u))
      (curveVelocity I (TauCeti.WithMetric.toWithMetric g₀ ∘ γ) u) = curveVelocity I γ u :=
    (congrArg (mfderiv I I TauCeti.WithMetric.ofWithMetric
      (TauCeti.WithMetric.toWithMetric g₀ (γ u))) hv).trans
        (TauCeti.WithMetric.mfderiv_ofWithMetric_mfderiv_toWithMetric _ _)
  rw [norm_eq_sqrt_real_inner, TauCeti.WithMetric.inner_def]
  simpa only [Function.comp_apply, TauCeti.WithMetric.ofWithMetric_toWithMetric] using
    congrArg Real.sqrt (congrArg₂ (fun v w ↦ g₀.inner (γ u) v w) hback hback)

/-- The native length of a `C¹` curve in the copy carrying `g₀` is the integral of its speed
computed with `g₀`, on a positively oriented interval. -/
theorem toReal_pathELength_toWithMetric_eq_integral
    (g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {a b : ℝ} (hab : a ≤ b) (hγ : ∀ u ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ u) :
    (Manifold.pathELength I (TauCeti.WithMetric.toWithMetric g₀ ∘ γ) a b).toReal =
      ∫ u in a..b, Real.sqrt (g₀.inner (γ u) (curveVelocity I γ u)
        (curveVelocity I γ u)) := by
  let O := {u | ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ u}
  have hOo : IsOpen O := TauCeti.isOpen_setOfPred_contMDiffAt (by simp)
  have hγO : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ O := fun _ hu ↦ hu.contMDiffWithinAt
  have hc := (TauCeti.WithMetric.contMDiff_toWithMetric (g := g₀)).comp_contMDiffOn hγO
  rw [hc.pathELength_eq_ofReal_integral_norm_curveVelocityWithin hγ,
    ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hab (fun _ _ ↦ norm_nonneg _))]
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Icc a b := by simpa only [uIcc_of_le hab] using hu
  dsimp only
  rw [curveVelocityWithin_of_mem_nhds (hOo.mem_nhds (hγ u hu'))]
  exact norm_curveVelocity_toWithMetric g₀ u

/-- The native energy of a curve in the copy carrying `g₀` is half the integral of its
squared speed computed with `g₀`. Both interval orientations and zero velocities are allowed. -/
theorem energy_toWithMetric_eq_integral
    (g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (a b : ℝ) :
    energy I (TauCeti.WithMetric.toWithMetric g₀ ∘ γ) a b =
      (∫ u in a..b, g₀.inner (γ u) (curveVelocity I γ u) (curveVelocity I γ u)) / 2 := by
  rw [energy_def]
  congr 1
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [norm_curveVelocity_toWithMetric g₀ u, Real.sq_sqrt]
  by_cases hv : curveVelocity I γ u = 0
  · simp [hv]
  · exact (g₀.pos (γ u) _ hv).le

end Bundle.ContMDiffRiemannianMetric
