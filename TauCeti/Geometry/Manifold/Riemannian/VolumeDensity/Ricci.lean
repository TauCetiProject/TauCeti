/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Exponential.Ricci.Comparison
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Normal
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Curvature.Volume
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Ricci upper volume comparison on a normal ball

The genuine exponential density comparison under a radial Ricci lower bound, integrated using
normal coordinates, bounds the Riemannian volume of a normal ball by the constant-curvature
model ball volume. The normal-domain hypothesis restricts this theorem to balls before the
cut locus; no global cut-locus or Bishop–Gromov assertion is made.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 11.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section

open Bundle CovariantDerivative MeasureTheory Metric Set
open scoped ContDiff ENNReal InnerProductSpace Manifold Topology

namespace TauCeti.Manifold.IsNormalDomain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  {p : M} {U : Set (TangentSpace I p)}

/-- Smoothness supplies the continuity needed by the native volume. -/
local instance instIsContinuousRiemannianBundle :
    IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)

/-- **Bishop upper volume comparison on a normal ball.** In positive dimension, a lower radial
Ricci bound gives the constant-curvature model upper bound for the Riemannian volume of a ball
contained in a normal domain. No completeness assumption is needed. -/
theorem riemannianVolume_ball_le_model_of_ricci (h : IsNormalDomain I M p U)
    (hdim : 0 < Module.finrank ℝ E) {κ r : ℝ}
    (hsub : Metric.ball (0 : TangentSpace I p) r ⊆ U)
    (hRic : ∀ v ∈ Metric.ball (0 : TangentSpace I p) r, ∀ t ∈ Ioo (0 : ℝ) 1,
      ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * κ * ‖v‖ ^ 2 ≤
        (leviCivitaConnection I M).ricciTensor (riemannianExp I M p (t • v))
          (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) v)
          (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) v)) :
    riemannianVolume I M (Metric.ball p r) ≤
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * modelBallVolume κ (Module.finrank ℝ E) r) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) := by
  by_cases hr : 0 < r
  swap
  · rw [Metric.ball_eq_empty.mpr (not_lt.mp hr), measure_empty]
    exact zero_le
  have hFdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) =
      Module.finrank ℝ E := finrank_euclideanSpace_fin
  have : Nontrivial (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    Module.nontrivial_of_finrank_pos (hFdim.symm ▸ hdim)
  let A : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃ₗᵢ[ℝ] TangentSpace I p :=
    ((stdOrthonormalBasis ℝ (TangentSpace I p)).reindex
      (finCongr (finrank_tangentSpace p))).repr.symm
  have hmodel :
      ∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) r,
        ENNReal.ofReal (curvatureSine (κ * ‖x‖ ^ 2) 1 ^ (Module.finrank ℝ E - 1)) =
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * modelBallVolume κ (Module.finrank ℝ E) r) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) := by
    by_cases hn : Module.finrank ℝ E = 1
    · have hflat := setLIntegral_ball_curvatureSine_pow
        (F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) volume (κ := 0) hr.le
        (by simp)
      simpa only [hFdim, hn, Nat.sub_self, pow_zero, modelBallVolume_one_dim] using hflat
    have hdim2 : 1 < Module.finrank ℝ E := by omega
    have hbound := h.le_pi_div_sqrt_of_ball_of_ricci hdim2 hsub hRic
    simpa only [hFdim] using setLIntegral_ball_curvatureSine_pow
      (F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) volume hr.le hbound
  rw [h.riemannianVolume_ball_eq_setLIntegral_normDet A hsub, ← hmodel]
  apply setLIntegral_mono' measurableSet_ball
  intro x hx
  have hAx : A x ∈ Metric.ball (0 : TangentSpace I p) r := by
    rw [mem_ball_zero_iff, A.norm_map]
    exact mem_ball_zero_iff.mp hx
  have hdensity := h.normDet_mfderiv_riemannianExp_le_curvatureSine_pow
    (hsub hAx) (hRic (A x) hAx)
  exact ENNReal.ofReal_le_ofReal (by simpa only [A.norm_map] using hdensity)

end TauCeti.Manifold.IsNormalDomain
