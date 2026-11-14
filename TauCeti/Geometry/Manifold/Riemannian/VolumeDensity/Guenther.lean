/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Curvature.Volume
public import TauCeti.Geometry.Manifold.Riemannian.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Geometry.Euclidean.Volume.Polar
import TauCeti.Geometry.Euclidean.Volume.Sphere
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Completeness
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Exponential.Comparison
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables

/-!
# Normal-ball volume formula and Günther's volume comparison theorem

Through any linear isometry `A : F ≃ₗᵢ[ℝ] TangentSpace I p` from a real inner product Borel space
`F`, the Riemannian exponential map on a normal domain `U ⊆ T_p M` pulls the Riemannian volume back
to Lebesgue measure on `F` weighted by the geometric Jacobian
`LinearMap.normDet (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (A x)).toLinearMap`.
When `Metric.ball 0 r ⊆ U` on a Riemannian metric manifold, Gauss's lemma identifies the exponential
image of `Metric.ball 0 r` with the metric ball `Metric.ball p r`, expressing the Riemannian volume
of `Metric.ball p r` directly as a Euclidean ball integral of `normDet (d exp_p)`.

Integrating the radial Jacobian lower bound from
`TauCeti.Geometry.Manifold.Riemannian.Jacobi.Exponential.Comparison` in Euclidean polar coordinates
yields **Günther's volume comparison theorem**: if `exp_p` is injective on `Metric.ball 0 r` with
`0 < r` and `r ≤ π / √κ` (when `κ > 0`), and every radial plane along rays in `Metric.ball 0 r` has
sectional curvature at most `κ`, then the Riemannian volume of `Metric.ball p r` is at least
`(n * modelBallVolume κ n r) * ω_n`, where `n = finrank ℝ E` and `ω_n` is the Euclidean unit-ball
volume. When radial planes have constant sectional curvature `κ`, equality holds in every positive
dimension.

## Main results

* `TauCeti.Manifold.IsNormalDomain.riemannianVolume_image_eq_setLIntegral_normDet`,
  `TauCeti.Manifold.IsNormalDomain.riemannianVolume_ball_eq_setLIntegral_normDet`: Riemannian volume
  of exponential images and geodesic balls as Euclidean integrals of `normDet (d exp_p)`.
* `TauCeti.guenther_of_subset_expDomain`: local Günther volume comparison on any Riemannian manifold
  once `Metric.ball 0 r ⊆ expDomain I M p`.
* `TauCeti.guenther`, `TauCeti.guenther_of_sectionalCurvature_le`: Günther's volume comparison
  theorem on complete Riemannian manifolds, in both curvature-numerator and `sectionalCurvature`
  form.
* `TauCeti.guenther_nonpos`: Euclidean ball volume lower bound `r ^ n * ω_n ≤ Vol(B(p, r))` under
  radial sectional curvature `≤ 0`.
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

/-! ### Polar integration of the model Jacobian on an inner product space -/

namespace TauCeti

section PolarModel

open Classical in
private theorem measurable_curvatureSine_mul_norm_sq {F : Type*} [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F] (κ : ℝ) :
    Measurable (fun x : F ↦ curvatureSine (κ * ‖x‖ ^ 2) 1) := by
  have heq : (fun x : F ↦ curvatureSine (κ * ‖x‖ ^ 2) 1) =
      fun x : F ↦ if x = 0 then (1 : ℝ) else curvatureSine κ ‖x‖ / ‖x‖ := by
    ext x
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx, curvatureSine_mul_sq_one κ (norm_ne_zero_iff.mpr hx)]
  rw [heq]
  exact Measurable.ite (measurableSet_singleton (0 : F)) measurable_const
    (((contDiff_curvatureSine κ).continuous.measurable.comp measurable_norm).div measurable_norm)

/-- Polar integration of the model angular Jacobian `curvatureSine (κ * ‖x‖ ^ 2) 1 ^ (n - 1)` over
`Metric.ball (0 : F) r` in a nontrivial finite-dimensional real inner product space `F`. -/
private theorem setLIntegral_ball_curvatureSine_pow {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    [Nontrivial F] {κ r : ℝ} (hr : 0 ≤ r) (hbound : 0 < κ → r ≤ π / √κ) :
    ∫⁻ x in Metric.ball (0 : F) r,
        ENNReal.ofReal (curvatureSine (κ * ‖x‖ ^ 2) 1 ^ (Module.finrank ℝ F - 1)) =
      ENNReal.ofReal ((Module.finrank ℝ F : ℝ) * modelBallVolume κ (Module.finrank ℝ F) r) *
        volume (Metric.ball (0 : F) 1) := by
  set n := Module.finrank ℝ F
  have hg : Measurable (fun x : F ↦ ENNReal.ofReal (curvatureSine (κ * ‖x‖ ^ 2) 1 ^ (n - 1))) :=
    ((measurable_curvatureSine_mul_norm_sq κ).pow_const _).ennreal_ofReal
  rw [setLIntegral_ball_eq_lintegral_Ioo_setLIntegral_sphere (0 : F) r hg]
  have hinner : ∀ t ∈ Ioo (0 : ℝ) r,
      (∫⁻ y in sphere (0 : F) t,
        ENNReal.ofReal (curvatureSine (κ * ‖y‖ ^ 2) 1 ^ (n - 1)) ∂μHE[n - 1]) =
      ((n : ℝ≥0∞) * volume (Metric.ball (0 : F) 1)) *
        ENNReal.ofReal (curvatureSine κ t ^ (n - 1)) := by
    intro t ht
    have ht0 : t ≠ 0 := ht.1.ne'
    have hcs : 0 ≤ curvatureSine κ t :=
      (curvatureSine_pos ht.1 fun hκ ↦ ht.2.trans_le (hbound hκ)).le
    have hsphere : ∀ y ∈ sphere (0 : F) t,
        ENNReal.ofReal (curvatureSine (κ * ‖y‖ ^ 2) 1 ^ (n - 1)) =
          ENNReal.ofReal ((curvatureSine κ t / t) ^ (n - 1)) := by
      intro y hy
      rw [mem_sphere_zero_iff_norm.mp hy, curvatureSine_mul_sq_one κ ht0]
    rw [setLIntegral_congr_fun isClosed_sphere.measurableSet hsphere, setLIntegral_const,
      euclideanHausdorffMeasure_sphere (0 : F) ht.1]
    have hmul : ENNReal.ofReal ((curvatureSine κ t / t) ^ (n - 1)) * ENNReal.ofReal t ^ (n - 1) =
        ENNReal.ofReal (curvatureSine κ t ^ (n - 1)) := by
      rw [← ENNReal.ofReal_pow ht.1.le,
        ← ENNReal.ofReal_mul (pow_nonneg (div_nonneg hcs ht.1.le) _), ← mul_pow,
        div_mul_cancel₀ _ ht0]
    calc ENNReal.ofReal ((curvatureSine κ t / t) ^ (n - 1)) *
          ((n : ℝ≥0∞) * volume (Metric.ball (0 : F) 1) * ENNReal.ofReal t ^ (n - 1))
        = ((n : ℝ≥0∞) * volume (Metric.ball (0 : F) 1)) *
          (ENNReal.ofReal ((curvatureSine κ t / t) ^ (n - 1)) * ENNReal.ofReal t ^ (n - 1)) := by
          ring
      _ = ((n : ℝ≥0∞) * volume (Metric.ball (0 : F) 1)) *
          ENNReal.ofReal (curvatureSine κ t ^ (n - 1)) := by rw [hmul]
  have hmeas : Measurable (fun t : ℝ ↦ ENNReal.ofReal (curvatureSine κ t ^ (n - 1))) :=
    ((contDiff_curvatureSine κ).continuous.measurable.pow_const _).ennreal_ofReal
  rw [setLIntegral_congr_fun measurableSet_Ioo hinner, lintegral_const_mul _ hmeas,
    ← ofReal_modelBallVolume_eq_lintegral_Ioo n hr hbound, ← ENNReal.ofReal_natCast n, mul_assoc,
    mul_comm (volume _), ← mul_assoc, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]

end PolarModel

end TauCeti

/-! ### Riemannian volume on normal domains via Euclidean coordinates -/

namespace TauCeti.Manifold.IsNormalDomain

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- **Volume of an exponential image inside a normal domain.** For any linear isometry equivalence
`A : F ≃ₗᵢ[ℝ] TangentSpace I p` mapping an open set `s ⊆ F` into a normal domain `U`, the
Riemannian volume of `exp_p '' (A '' s)` is the Lebesgue integral over `s` of the geometric
Jacobian `normDet (d(exp_p)_{A x})`. -/
theorem riemannianVolume_image_eq_setLIntegral_normDet
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    {p : M} {U : Set (TangentSpace I p)} (h : IsNormalDomain I M p U)
    (A : F ≃ₗᵢ[ℝ] TangentSpace I p) {s : Set F} (hs : IsOpen s) (hmap : MapsTo A s U) :
    riemannianVolume I M (riemannianExp I M p '' (A '' s)) =
      ∫⁻ x in s, ENNReal.ofReal (LinearMap.normDet (U := TangentSpace I p)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (A x)).toLinearMap) := by
  have hdim : Module.finrank ℝ F = Module.finrank ℝ E :=
    A.toLinearEquiv.finrank_eq.trans (TauCeti.finrank_tangentSpace p)
  let b := stdOrthonormalBasis ℝ F
  obtain ⟨Φ, hsource, hcoe⟩ :=
    h.exists_partialDiffeomorph_riemannianExp_comp A.toContinuousLinearEquiv hs hmap
  have htarget : Φ.target = riemannianExp I M p '' (A '' s) := by
    rw [← Φ.toPartialEquiv.image_source_eq_target, hsource, ← image_comp]
    exact congrFun (congrArg image hcoe) s
  have hcov := (Φ.ofLE (m := 1) (by simp)).setLIntegral_riemannianVolume_eq b.toBasis hdim
    (φ := fun _ ↦ 1) measurable_const
  -- `PartialDiffeomorph` coerces through `toPartialEquiv`, so `ofLE_toPartialEquiv` rewrites the
  -- source, target, and forward map of `Φ.ofLE _` back to those of `Φ`.
  change ∫⁻ _ in (Φ.ofLE (m := 1) (by simp)).toPartialEquiv.target, 1 ∂riemannianVolume I M =
    ∫⁻ x in (Φ.ofLE (m := 1) (by simp)).toPartialEquiv.source,
      ENNReal.ofReal (TauCeti.riemannianJacobian (I := I) b.toBasis
        (Φ.ofLE (m := 1) (by simp)).toPartialEquiv x) * 1 ∂b.toBasis.addHaar at hcov
  rw [PartialDiffeomorph.ofLE_toPartialEquiv, setLIntegral_one, htarget, hsource,
    b.addHaar_eq_volume] at hcov
  rw [hcov]
  refine setLIntegral_congr_fun hs.measurableSet fun x hx ↦ ?_
  have hf : MDifferentiableAt 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (A x) :=
    (h.isLocalDiffeomorphOn ⟨A x, hmap hx⟩).contMDiffAt.mdifferentiableAt (by simp)
  have hmap_basis : b.toBasis.map A.toContinuousLinearEquiv.toLinearEquiv = (b.map A).toBasis :=
    (b.toBasis_map A).symm
  have hJ : TauCeti.riemannianJacobian (I := I) b.toBasis Φ.toPartialEquiv x =
      TauCeti.riemannianJacobian (I := I) (b.map A).toBasis (riemannianExp I M p) (A x) := by
    rw [show (Φ.toPartialEquiv : F → M) = riemannianExp I M p ∘ A.toContinuousLinearEquiv from hcoe,
      TauCeti.riemannianJacobian_comp_continuousLinearEquiv A.toContinuousLinearEquiv b.toBasis hf,
      hmap_basis]
    rfl
  exact (mul_one _).trans
    (congrArg ENNReal.ofReal (hJ.trans (TauCeti.riemannianJacobian_eq_normDet (b.map A) _ (A x))))

/-- **Volume of a normal geodesic ball.** When `Metric.ball 0 r` lies in a normal domain `U` at `p`
on a boundaryless Riemannian metric manifold, the Riemannian volume of `Metric.ball p r` is the
integral over `Metric.ball (0 : F) r` of `normDet (d(exp_p)_{A x})`. -/
theorem riemannianVolume_ball_eq_setLIntegral_normDet [I.Boundaryless]
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    {p : M} {U : Set (TangentSpace I p)} {r : ℝ} (h : IsNormalDomain I M p U)
    (A : F ≃ₗᵢ[ℝ] TangentSpace I p) (hU : Metric.ball 0 r ⊆ U) :
    riemannianVolume I M (Metric.ball p r) =
      ∫⁻ x in Metric.ball (0 : F) r, ENNReal.ofReal (LinearMap.normDet (U := TangentSpace I p)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (A x)).toLinearMap) := by
  have him : A '' Metric.ball (0 : F) r = Metric.ball 0 r := by simp
  have hmap : MapsTo A (Metric.ball (0 : F) r) U := fun x hx ↦ hU (him ▸ mem_image_of_mem A hx)
  rw [← h.image_riemannianExp_ball_eq_ball hU, ← him]
  exact h.riemannianVolume_image_eq_setLIntegral_normDet A Metric.isOpen_ball hmap

end TauCeti.Manifold.IsNormalDomain

/-! ### Günther's volume comparison theorem and constant-curvature equality -/

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
          (F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) hr.le hbound).symm
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
      (Manifold.pow_le_normDet_mfderiv_riemannianExp (hsub hAx) (hK (A x) hAx)
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
bounded below by the volume `(n * modelBallVolume κ n r) * ω_n` of a ball of radius `r` in the
simply connected `n`-dimensional model space of constant curvature `κ`. -/
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
theorem guenther_nonpos {p : M} {r : ℝ} (hr : 0 < r)
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
  by_cases hdim : Module.finrank ℝ E = 0
  · have hFdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) = 0 :=
      finrank_euclideanSpace_fin.trans hdim
    have : Subsingleton (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
      Module.finrank_zero_iff.mp hFdim
    let A : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃ₗᵢ[ℝ] TangentSpace I p :=
      tangentEuclideanEquiv (I := I) p
    have hd : Manifold.IsNormalDomain I M p (Metric.ball 0 r) :=
      Manifold.isNormalDomain_ball_of_sectionalCurvature_le hr (fun h0 ↦ absurd h0 (lt_irrefl 0))
        hsub hinj hK
    have hball_r : Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) r = univ :=
      eq_univ_of_forall fun x ↦ by simp [Subsingleton.elim x 0, hr]
    have hball_one : Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1 = univ :=
      eq_univ_of_forall fun x ↦ by simp [Subsingleton.elim x 0]
    have hp : ENNReal.ofReal (r ^ Module.finrank ℝ E) = 1 := by simp [hdim]
    have hlhs : ENNReal.ofReal (r ^ Module.finrank ℝ E) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) =
        volume (univ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
      rw [hp, one_mul, hball_one]
    have hv0 : ∀ v : TangentSpace I p, v = 0 →
        LinearMap.normDet (U := TangentSpace I p)
          (mfderiv 𝓘(ℝ, TangentSpace I p) I (Manifold.riemannianExp I M p) v).toLinearMap = 1 := by
      rintro _ rfl
      exact Manifold.normDet_mfderiv_riemannianExp_zero p
    have h1 : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) r,
        ENNReal.ofReal (LinearMap.normDet (U := TangentSpace I p)
          (mfderiv 𝓘(ℝ, TangentSpace I p) I
            (Manifold.riemannianExp I M p) (A x)).toLinearMap) = 1 :=
      fun x _ ↦ (congrArg ENNReal.ofReal
        (hv0 (A x) (by simp [Subsingleton.elim x 0]))).trans ENNReal.ofReal_one
    have hrhs : riemannianVolume I M (Metric.ball p r) =
        volume (univ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) :=
      (hd.riemannianVolume_ball_eq_setLIntegral_normDet A subset_rfl).trans <|
        (setLIntegral_congr_fun measurableSet_ball h1).trans <|
          (setLIntegral_one _).trans (congrArg _ hball_r)
    exact hlhs.trans_le hrhs.symm.le
  · have h := guenther_of_subset_expDomain hr (fun h0 ↦ absurd h0 (lt_irrefl 0)) hsub hinj hK
    have hnR : (Module.finrank ℝ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hdim
    rw [modelBallVolume_zero_curvature hdim, mul_div_cancel₀ _ hnR] at h
    exact h

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
    have hcs_nonneg : 0 ≤ curvatureSine (κ * ‖A x‖ ^ 2) 1 := by
      by_cases hx0 : A x = 0
      · simp [hx0]
      · have hpos : 0 < ‖A x‖ := norm_pos_iff.mpr hx0
        rw [curvatureSine_mul_sq_one κ hpos.ne']
        exact (div_pos (curvatureSine_pos hpos fun hκ ↦ hx_norm.trans_le (hbound hκ)) hpos).le
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
        (F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) hr.le hbound
  exact (hd.riemannianVolume_ball_eq_setLIntegral_normDet A subset_rfl).trans <|
    (setLIntegral_congr_fun measurableSet_ball hcongr).trans hmodel

end Guenther

end TauCeti
