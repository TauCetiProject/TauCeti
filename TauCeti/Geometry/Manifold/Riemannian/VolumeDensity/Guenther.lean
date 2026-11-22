/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Curvature.Volume
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Completeness
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Exponential.Comparison
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Exponential.Metric
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Normal

/-!
# Günther's volume comparison theorem

Combining the normal-ball volume formula in
`TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Normal` with the radial Jacobian lower bound
from `TauCeti.Geometry.Manifold.Riemannian.Jacobi.Exponential.Comparison` and the polar model
integral in `TauCeti.Analysis.SpecialFunctions.Trigonometric.Curvature.Volume` yields
**Günther's volume comparison theorem**: if `exp_p` is injective on `Metric.ball 0 r` with `0 < r`
and `r ≤ π / √κ` (when `κ > 0`), and every radial plane along rays in `Metric.ball 0 r` has
sectional curvature at most `κ`, then the Riemannian volume of `Metric.ball p r` is at least
`(n * modelBallVolume κ n r) * ω_n`, where `n = finrank ℝ E` and `ω_n` is the Euclidean unit-ball
volume (which equals the radius-`r` ball volume in the `n`-dimensional model space of constant
curvature `κ` for `n ≥ 1`, and vanishes when `n = 0`). When `M` has constant sectional curvature
`κ` (`HasSectionalCurvatureAt` on all tangent two-planes) along every closed ray in
`Metric.ball 0 r`, equality holds in every positive dimension.

## Main results

* `TauCeti.guenther_of_subset_expDomain`: local Günther volume comparison on any Riemannian manifold
  once `Metric.ball 0 r ⊆ expDomain I M p`.
* `TauCeti.guenther`, `TauCeti.guenther_of_sectionalCurvature_le`: Günther's volume comparison
  theorem on complete Riemannian manifolds, in both curvature-numerator and `sectionalCurvature`
  form.
* `TauCeti.ofReal_pow_mul_volume_ball_le_riemannianVolume_ball_of_sectionalCurvature_nonpos`:
  Euclidean ball volume lower bound `r ^ n * ω_n ≤ Vol(B(p, r))` under radial sectional curvature
  `≤ 0`.
* `TauCeti.riemannianVolume_ball_of_hasSectionalCurvatureAt`: exact volume of an injective geodesic
  ball in constant sectional curvature `κ` (in positive dimension).

## References

* P. Günther, *Einige Sätze über das Volumenelement eines Riemannschen Raumes*, Publ. Math.
  Debrecen **7** (1960), 78–93.
* A. Gray, *Tubes*, 2nd ed., Progress in Mathematics 221, Birkhäuser (2004), §3.3.
* K.-K. Kwong, *Quantitative comparison theorems in Riemannian and Kähler geometry*, Theorem 10(2).
* J.-H. Eschenburg, *Comparison Theorems in Riemannian Geometry*, §3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapters 10–11.
-/

public section

open Bundle CovariantDerivative MeasureTheory Metric Real Set
open scoped ContDiff ENNReal InnerProductSpace Manifold Topology

noncomputable section

namespace TauCeti

section Guenther

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]

omit [I.Boundaryless] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] [MeasurableSpace M] [BorelSpace M] [LindelofSpace M] in
/-- Canonical linear isometry equivalence from `EuclideanSpace ℝ (Fin (finrank ℝ E))` to
`TangentSpace I p`. -/
private def tangentEuclideanEquiv (p : M) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃ₗᵢ[ℝ] TangentSpace I p :=
  ((stdOrthonormalBasis ℝ (TangentSpace I p)).reindex (finCongr (finrank_tangentSpace p))).repr.symm

/-- **Günther's volume comparison theorem (local form on `expDomain`).** Suppose `0 < r`, with
`r ≤ π / √κ` when `κ > 0`, `Metric.ball 0 r ⊆ expDomain I M p`, `exp_p` is injective on
`Metric.ball 0 r`, and every radial plane along rays in `Metric.ball 0 r` has sectional curvature
at most `κ`. Then `Vol(B(p, r)) ≥ (n * modelBallVolume κ n r) * ω_n`. No completeness hypothesis on
`M` is needed. -/
theorem guenther_of_subset_expDomain {p : M} {κ r : ℝ} (hr : 0 < r)
    (hbound : 0 < κ → r ≤ π / √κ)
    (hsub : Metric.ball (0 : TangentSpace I p) r ⊆ Manifold.expDomain I M p)
    (hinj : InjOn (Manifold.riemannianExp I M p) (Metric.ball 0 r))
    (hK : ∀ v ∈ Metric.ball (0 : TangentSpace I p) r, ∀ t ∈ Ioo (0 : ℝ) 1,
      ∀ u : TangentSpace I (Manifold.riemannianExp I M p (t • v)),
        LinearIndependent ℝ
          ![u, mfderiv 𝓘(ℝ, TangentSpace I p) I (Manifold.riemannianExp I M p) (t • v) v] →
          (leviCivitaConnection I M).sectionalCurvature
            (isMetricCompatible_leviCivitaConnection I)
            (Manifold.riemannianExp I M p (t • v)) u
            (mfderiv 𝓘(ℝ, TangentSpace I p) I (Manifold.riemannianExp I M p) (t • v) v) ≤ κ) :
    ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * modelBallVolume κ (Module.finrank ℝ E) r) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) ≤
      riemannianVolume I M (Metric.ball p r) := by
  by_cases hdim : Module.finrank ℝ E = 0
  · simp [hdim]
  · have hFdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) =
        Module.finrank ℝ E := finrank_euclideanSpace_fin
    have : Nontrivial (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
      Module.nontrivial_of_finrank_pos (hFdim.symm ▸ Nat.pos_of_ne_zero hdim)
    let A : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃ₗᵢ[ℝ] TangentSpace I p :=
      tangentEuclideanEquiv (I := I) p
    have hd : Manifold.IsNormalDomain I M p (Metric.ball 0 r) :=
      Manifold.isNormalDomain_ball_of_sectionalCurvature_le hr hbound hsub hinj hK
    have hmodel :
        ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * modelBallVolume κ (Module.finrank ℝ E) r) *
          volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) =
        ∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) r,
          ENNReal.ofReal (curvatureSine (κ * ‖x‖ ^ 2) 1 ^ (Module.finrank ℝ E - 1)) := by
      simpa only [hFdim] using
        (setLIntegral_ball_curvatureSine_pow
          (F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) volume hr.le hbound).symm
    refine (hmodel.trans_le (setLIntegral_mono' measurableSet_ball fun x hx ↦ ?_)).trans_eq
      (hd.riemannianVolume_ball_eq_setLIntegral_normDet A subset_rfl).symm
    have hx_norm : ‖A x‖ < r := by
      rw [A.norm_map]
      exact mem_ball_zero_iff.mp hx
    have hAx : A x ∈ Metric.ball (0 : TangentSpace I p) r := mem_ball_zero_iff.mpr hx_norm
    have hcs_eq : curvatureSine (κ * ‖x‖ ^ 2) 1 ^ (Module.finrank ℝ E - 1) =
        curvatureSine (κ * ‖A x‖ ^ 2) 1 ^ (Module.finrank ℝ E - 1) := by
      rw [A.norm_map]
    exact ENNReal.ofReal_le_ofReal (hcs_eq.trans_le
      (Manifold.curvatureSine_pow_le_normDet_mfderiv_riemannianExp (hsub hAx) (hK (A x) hAx)
        fun hκ ↦ hx_norm.trans_le (hbound hκ)))

/-- **Günther's volume comparison theorem (`sectionalCurvature` form).** On a complete Riemannian
manifold, if `exp_p` is injective on `Metric.ball 0 r` with `0 < r` and `r ≤ π / √κ` (when `κ > 0`),
and every radial plane along rays in `Metric.ball 0 r` has sectional curvature at most `κ`, then
`Vol(B(p, r)) ≥ (n * modelBallVolume κ n r) * ω_n`. -/
theorem guenther_of_sectionalCurvature_le [CompleteSpace M] (p : M) {κ r : ℝ} (hr : 0 < r)
    (hbound : 0 < κ → r ≤ π / √κ)
    (hinj : InjOn (Manifold.riemannianExp I M p) (Metric.ball 0 r))
    (hK : ∀ v ∈ Metric.ball (0 : TangentSpace I p) r, ∀ t ∈ Ioo (0 : ℝ) 1,
      ∀ u : TangentSpace I (Manifold.riemannianExp I M p (t • v)),
        LinearIndependent ℝ
          ![u, mfderiv 𝓘(ℝ, TangentSpace I p) I (Manifold.riemannianExp I M p) (t • v) v] →
          (leviCivitaConnection I M).sectionalCurvature
            (isMetricCompatible_leviCivitaConnection I)
            (Manifold.riemannianExp I M p (t • v)) u
            (mfderiv 𝓘(ℝ, TangentSpace I p) I (Manifold.riemannianExp I M p) (t • v) v) ≤ κ) :
    ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * modelBallVolume κ (Module.finrank ℝ E) r) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) ≤
      riemannianVolume I M (Metric.ball p r) :=
  guenther_of_subset_expDomain hr hbound
    ((Manifold.expDomain_eq_univ_of_completeSpace (I := I) p).symm ▸ subset_univ _) hinj hK

/-- **Günther's volume comparison theorem.** Let `M` be a complete Riemannian manifold and `p : M`.
Suppose `0 < r`, with `r ≤ π / √κ` when `κ > 0`, `exp_p` is injective on `Metric.ball 0 r`, and
along every ray in `Metric.ball 0 r` the radial curvature numerator satisfies
`⟪R(u, γ') γ', u⟫ ≤ κ (‖u‖² ‖γ'‖² - ⟪u, γ'⟫²)`. Then the Riemannian volume of `Metric.ball p r` is
at least `(n * modelBallVolume κ n r) * ω_n`, which equals the volume of a ball of radius `r` in
the simply connected `n`-dimensional model space of constant curvature `κ` in positive dimension
`n ≥ 1` (and vanishes when `n = 0`). -/
theorem guenther [CompleteSpace M] (p : M) {κ r : ℝ} (hr : 0 < r)
    (hbound : 0 < κ → r ≤ π / √κ)
    (hinj : InjOn (Manifold.riemannianExp I M p) (Metric.ball 0 r))
    (hK : ∀ v ∈ Metric.ball (0 : TangentSpace I p) r, ∀ t ∈ Ioo (0 : ℝ) 1,
      ∀ u : TangentSpace I (Manifold.riemannianExp I M p (t • v)),
        inner ℝ ((leviCivitaConnection I M).curvatureTensor
          (Manifold.riemannianExp I M p (t • v)) u
          (mfderiv 𝓘(ℝ, TangentSpace I p) I (Manifold.riemannianExp I M p) (t • v) v)
          (mfderiv 𝓘(ℝ, TangentSpace I p) I (Manifold.riemannianExp I M p) (t • v) v)) u ≤
        κ * (‖u‖ ^ 2 * ‖mfderiv 𝓘(ℝ, TangentSpace I p) I
            (Manifold.riemannianExp I M p) (t • v) v‖ ^ 2 -
          (inner ℝ u (mfderiv 𝓘(ℝ, TangentSpace I p) I
            (Manifold.riemannianExp I M p) (t • v) v)) ^ 2)) :
    ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * modelBallVolume κ (Module.finrank ℝ E) r) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) ≤
      riemannianVolume I M (Metric.ball p r) := by
  refine guenther_of_sectionalCurvature_le p hr hbound hinj fun v hv t ht ↦ ?_
  rw [(leviCivitaConnection I M).forall_sectionalCurvature_le_fixed_iff
    (isMetricCompatible_leviCivitaConnection I)]
  intro u
  rw [Matrix.real_det_gram_fin_two, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  exact hK v hv t ht u

/-- **Euclidean ball volume lower bound under nonpositive radial sectional curvature.** When
`0 < r`, `Metric.ball 0 r ⊆ expDomain I M p`, `exp_p` is injective on `Metric.ball 0 r`, and every
radial plane along rays in `Metric.ball 0 r` has nonpositive sectional curvature, the Riemannian
volume of `Metric.ball p r` is at least the Euclidean ball volume `r ^ n * ω_n`. -/
theorem ofReal_pow_mul_volume_ball_le_riemannianVolume_ball_of_sectionalCurvature_nonpos
    {p : M} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball (0 : TangentSpace I p) r ⊆ Manifold.expDomain I M p)
    (hinj : InjOn (Manifold.riemannianExp I M p) (Metric.ball 0 r))
    (hK : ∀ v ∈ Metric.ball (0 : TangentSpace I p) r, ∀ t ∈ Ioo (0 : ℝ) 1,
      ∀ u : TangentSpace I (Manifold.riemannianExp I M p (t • v)),
        LinearIndependent ℝ
          ![u, mfderiv 𝓘(ℝ, TangentSpace I p) I (Manifold.riemannianExp I M p) (t • v) v] →
          (leviCivitaConnection I M).sectionalCurvature
            (isMetricCompatible_leviCivitaConnection I)
            (Manifold.riemannianExp I M p (t • v)) u
            (mfderiv 𝓘(ℝ, TangentSpace I p) I (Manifold.riemannianExp I M p) (t • v) v) ≤ 0) :
    ENNReal.ofReal (r ^ Module.finrank ℝ E) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) ≤
      riemannianVolume I M (Metric.ball p r) := by
  let A : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃ₗᵢ[ℝ] TangentSpace I p :=
    tangentEuclideanEquiv (I := I) p
  have hd : Manifold.IsNormalDomain I M p (Metric.ball 0 r) :=
    Manifold.isNormalDomain_ball_of_sectionalCurvature_le hr (fun h0 ↦ absurd h0 (lt_irrefl 0))
      hsub hinj hK
  have hlhs : ENNReal.ofReal (r ^ Module.finrank ℝ E) *
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) =
      ∫⁻ _ in Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) r, (1 : ℝ≥0∞) := by
    rw [setLIntegral_one, Measure.addHaar_ball_of_pos volume (0 : EuclideanSpace ℝ _) hr,
      finrank_euclideanSpace_fin]
  refine (hlhs.trans_le (setLIntegral_mono' measurableSet_ball fun x hx ↦ ?_)).trans_eq
    (hd.riemannianVolume_ball_eq_setLIntegral_normDet A subset_rfl).symm
  have hAx : A x ∈ Metric.ball (0 : TangentSpace I p) r := by
    rw [mem_ball_zero_iff, A.norm_map]
    exact mem_ball_zero_iff.mp hx
  have hjac := Manifold.curvatureSine_pow_le_normDet_mfderiv_riemannianExp (κ := 0)
    (hsub hAx) (hK (A x) hAx) (fun h0 ↦ absurd h0 (lt_irrefl 0))
  simp only [zero_mul, curvatureSine_zero_left, one_pow] at hjac
  exact ENNReal.ofReal_one.symm.trans_le (ENNReal.ofReal_le_ofReal hjac)

/-- **Exact geodesic ball volume in constant sectional curvature.** In positive dimension
`0 < finrank ℝ E`, if `0 < r` (with `r ≤ π / √κ` when `κ > 0`), `Metric.ball 0 r ⊆ expDomain I M p`,
`exp_p` is injective on `Metric.ball 0 r`, and `M` has constant sectional curvature `κ` along every
closed ray in `Metric.ball 0 r`, then `Vol(B(p, r)) = (n * modelBallVolume κ n r) * ω_n`.
(In dimension zero a positive-radius ball is `{p}` of counting volume `1`, while the factor
`n = 0` vanishes.) -/
theorem riemannianVolume_ball_of_hasSectionalCurvatureAt {p : M} {κ r : ℝ}
    (hdim : 0 < Module.finrank ℝ E) (hr : 0 < r) (hbound : 0 < κ → r ≤ π / √κ)
    (hsub : Metric.ball (0 : TangentSpace I p) r ⊆ Manifold.expDomain I M p)
    (hinj : InjOn (Manifold.riemannianExp I M p) (Metric.ball 0 r))
    (hK : ∀ v ∈ Metric.ball (0 : TangentSpace I p) r, ∀ t ∈ Icc (0 : ℝ) 1,
      (leviCivitaConnection I M).HasSectionalCurvatureAt
        (isMetricCompatible_leviCivitaConnection I)
        (Manifold.riemannianExp I M p (t • v)) κ) :
    riemannianVolume I M (Metric.ball p r) =
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * modelBallVolume κ (Module.finrank ℝ E) r) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) := by
  have hFdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) =
      Module.finrank ℝ E := finrank_euclideanSpace_fin
  have : Nontrivial (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    Module.nontrivial_of_finrank_pos (hFdim.symm ▸ hdim)
  let A : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃ₗᵢ[ℝ] TangentSpace I p :=
    tangentEuclideanEquiv (I := I) p
  have hd : Manifold.IsNormalDomain I M p (Metric.ball 0 r) :=
    Manifold.isNormalDomain_ball_of_sectionalCurvature_le hr hbound hsub hinj
      fun v hv t ht u huv ↦ ((hK v hv t (Ioo_subset_Icc_self ht)).sectionalCurvature_eq u _ huv).le
  have hcongr : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) r,
      ENNReal.ofReal (LinearMap.normDet (U := TangentSpace I p)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (Manifold.riemannianExp I M p) (A x)).toLinearMap) =
      ENNReal.ofReal
        (curvatureSine (κ * ‖x‖ ^ 2) 1 ^
          (Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) - 1)) := by
    intro x hx
    have hx_norm : ‖A x‖ < r := by
      rw [A.norm_map]
      exact mem_ball_zero_iff.mp hx
    have hAx : A x ∈ Metric.ball (0 : TangentSpace I p) r := mem_ball_zero_iff.mpr hx_norm
    have hcs_nonneg : 0 ≤ curvatureSine (κ * ‖A x‖ ^ 2) 1 :=
      (curvatureSine_mul_sq_one_pos (norm_nonneg _)
        fun hκ ↦ hx_norm.trans_le (hbound hκ)).le
    have habs : |curvatureSine (κ * ‖A x‖ ^ 2) 1| ^ (Module.finrank ℝ E - 1) =
        curvatureSine (κ * ‖x‖ ^ 2) 1 ^
          (Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) - 1) := by
      rw [abs_of_nonneg hcs_nonneg, A.norm_map, hFdim]
    exact congrArg ENNReal.ofReal
      ((Manifold.normDet_mfderiv_riemannianExp_of_hasSectionalCurvatureAt (hsub hAx)
        (hK (A x) hAx)).trans habs)
  have hmodel :
      ∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) r,
        ENNReal.ofReal
          (curvatureSine (κ * ‖x‖ ^ 2) 1 ^
            (Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) - 1)) =
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * modelBallVolume κ (Module.finrank ℝ E) r) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) := by
    simpa only [hFdim] using
      setLIntegral_ball_curvatureSine_pow
        (F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) volume hr.le hbound
  exact (hd.riemannianVolume_ball_eq_setLIntegral_normDet A subset_rfl).trans <|
    (setLIntegral_congr_fun measurableSet_ball hcongr).trans hmodel

end Guenther

end TauCeti
