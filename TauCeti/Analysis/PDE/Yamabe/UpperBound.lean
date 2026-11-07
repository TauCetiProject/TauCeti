/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Quotient
public import TauCeti.Analysis.PDE.Yamabe.SphereConstant
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Analysis.PDE.Yamabe.Bubble.Cutoff
import TauCeti.Geometry.Manifold.ContMDiff.ChartCutoff
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume

/-!
# The Yamabe quotient is at most the Yamabe constant of the sphere

Let `(M, g)` be a Riemannian manifold without boundary of dimension `n > 2`, and let
`Q_g(u) = (∫ (aₙ |grad u|² + Scal_g u²) dV_g) / (∫ |u| ^ pₙ dV_g) ^ (2 / pₙ)` be its Yamabe
quotient (`TauCeti.Yamabe.yamabeQuotient`). This file proves that every nonempty open set of `M`
carries a nonnegative smooth compactly supported test function `u` with positive critical mass and
`Q_g(u) < Y(Sⁿ) + ε`, for any `ε > 0`, where `Y(Sⁿ) = n (n - 1) |Sⁿ| ^ (2 / n)` is the Yamabe
constant of the round sphere
(`TauCeti.Yamabe.exists_contMDiff_hasCompactSupport_yamabeQuotient_lt`).
Consequently every lower bound of `Q_g` on such test functions is at most `Y(Sⁿ)`
(`TauCeti.Yamabe.le_sphereYamabeConstant_of_forall_le_yamabeQuotient`). Thus the Yamabe invariant
of a closed manifold, an infimum of `Q_g` over a class of functions containing these test
functions, is at most the Yamabe constant of the sphere.

The test functions are transplanted Euclidean test functions concentrated at a point `p`. Choose
coordinates at `p` which are orthonormal for `g_p`. In them, the Euclidean Sobolev quotient
`aₙ ∫ |dv|² / ‖v‖_{pₙ}²` of a suitable cutoff of a Yamabe bubble is below `Y(Sⁿ) + ε / 2`
(`TauCeti.Yamabe.exists_contDiff_hasCompactSupport_sobolev_quotient_lt`). Rescale it to
`v (t⁻¹ x)`, supported in a coordinate ball of radius proportional to `t`, and transplant it to
`M`. The Euclidean quotient is invariant under this rescaling, while on a small enough ball the
metric and the volume density differ from their values at `p` by factors `1 ± η`, and the
curvature term `∫ Scal_g u²` is of order `t²` relative to the energy. Hence `Q_g(u)` is at most
`((1 + η) ³ aₙ ∫ |dv|² + O(t²)) / ((1 - η) ^ (2 / pₙ) ‖v‖_{pₙ}²)`, which is below `Y(Sⁿ) + ε` once
`η` and `t` are small.

The metric enters through the length of the Riemannian gradient
(`TauCeti.Manifold.eventually_norm_mgradient_le_mul_norm_fderiv_comp_extChartAt_symm`) and the
chart volume density, normalized at `p` by the orthonormal coordinates
(`TauCeti.map_addHaar_eq_chartVolumeDensity_inv_smul_volume`).

## Main results

* `TauCeti.Yamabe.exists_contMDiff_hasCompactSupport_yamabeQuotient_lt`: test functions supported
  in any nonempty open set with Yamabe quotient below `Y(Sⁿ) + ε`.
* `TauCeti.Yamabe.le_sphereYamabeConstant_of_forall_le_yamabeQuotient`: a lower bound of the
  Yamabe quotient on nonnegative smooth compactly supported test functions is at most `Y(Sⁿ)`.

## References

* T. Aubin, *Équations différentielles non linéaires et problème de Yamabe concernant la courbure
  scalaire*, J. Math. Pures Appl. 55 (1976), 269–296.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §3 (the
  universal bound `λ(M) ≤ λ(Sⁿ)`, due to Aubin).
-/

public section

open Bundle Filter MeasureTheory Metric Module Set TauCeti.Manifold
open scoped ContDiff ENNReal NNReal Manifold Topology InnerProductSpace

noncomputable section

namespace TauCeti.Yamabe

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

omit [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Around the chart image of `p` there is a coordinate ball in the chart target whose chart
preimage lies in a given neighbourhood `U` of `p`, on which the chart density is within a factor
`1 ± η` of its value at `p`, the scalar curvature is bounded by `|Scal_g p| + 1`, and the length
of every gradient is at most `1 + η` times the length of the coordinate differential measured with
the metric at `p`. -/
private lemma exists_ball_forall_chart_close [I.Boundaryless] (p : M) {η : ℝ} (hη : 0 < η)
    {U : Set M} (hU : U ∈ 𝓝 p) :
    ∃ R > 0, ball (extChartAt I p p) R ⊆ (extChartAt I p).target ∧
      ∀ y ∈ ball (extChartAt I p p) R, (extChartAt I p).symm y ∈ U ∧
        chartVolumeDensity (I := I) p ((extChartAt I p).symm y) ∈
          Icc ((1 - η) * chartVolumeDensity (I := I) p p)
            ((1 + η) * chartVolumeDensity (I := I) p p) ∧
        |(CovariantDerivative.leviCivitaConnection I M).scalarCurvature
            ((extChartAt I p).symm y)| ≤
          |(CovariantDerivative.leviCivitaConnection I M).scalarCurvature p| + 1 ∧
        ∀ f : M → ℝ, DifferentiableAt ℝ (f ∘ (extChartAt I p).symm) y →
          ‖mgradient I f ((extChartAt I p).symm y)‖ ≤ (1 + η) * ‖(fderiv ℝ
            (f ∘ (extChartAt I p).symm) y ∘L
              (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p :
                TangentSpace I p →L[ℝ] ℝ)‖ := by
  set φ := extChartAt I p
  set ρ := chartVolumeDensity (I := I) p
  set Scal := (CovariantDerivative.leviCivitaConnection I M).scalarCurvature
  have hp : p ∈ (trivializationAt E (TangentSpace I) p).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' p
  have hρp : 0 < ρ p := chartVolumeDensity_pos p hp
  have hρc : ContinuousAt ρ p := by
    have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
    have : IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x) :=
      IsContinuousRiemannianBundle.toIsContMDiffZero
    exact (contMDiffOn_chartVolumeDensity (I := I) (n := 0) p).continuousOn.continuousAt
      ((trivializationAt E (TangentSpace I) p).open_baseSet.mem_nhds hp)
  have hScal : Continuous Scal :=
    (CovariantDerivative.leviCivitaConnection I M).contMDiff_scalarCurvature.continuous
  have hW : ∀ᶠ x in 𝓝 p, x ∈ U ∧ ρ x ∈ Icc ((1 - η) * ρ p) ((1 + η) * ρ p) ∧
      |Scal x| ≤ |Scal p| + 1 ∧ ∀ f : M → ℝ, DifferentiableAt ℝ (f ∘ φ.symm) (φ x) →
        ‖mgradient I f x‖ ≤ (1 + η) * ‖(fderiv ℝ (f ∘ φ.symm) (φ x) ∘L
          (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p :
            TangentSpace I p →L[ℝ] ℝ)‖ := by
    filter_upwards [hU, hρc.eventually (Icc_mem_nhds (show (1 - η) * ρ p < ρ p by nlinarith)
        (show ρ p < (1 + η) * ρ p by nlinarith)),
      (continuous_abs.comp hScal).continuousAt.eventually (Iio_mem_nhds (lt_add_one |Scal p|)),
      eventually_norm_mgradient_le_mul_norm_fderiv_comp_extChartAt_symm (I := I) p
        (show 1 < 1 + η by linarith)] with x hxU hxρ hxS hxg
    exact ⟨hxU, hxρ, hxS.le, hxg⟩
  have hsymm : Tendsto φ.symm (𝓝 (φ p)) (𝓝 p) := by
    have h := continuousAt_extChartAt_symm (I := I) p
    rwa [ContinuousAt, extChartAt_to_inv] at h
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.1
    (inter_mem (extChartAt_target_mem_nhds (I := I) p) (hsymm.eventually hW))
  refine ⟨R, hR, fun y hy ↦ (hball hy).1, fun y hy ↦ ?_⟩
  obtain ⟨hyt, hyU, hyρ, hyS, hyg⟩ := hball hy
  refine ⟨hyU, hyρ, hyS, fun f hf ↦ ?_⟩
  have h := hyg f
  rw [φ.right_inv hyt] at h
  exact h hf

omit [T2Space M] [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
/-- Coordinates at `p` which are orthonormal for the metric at `p`: a continuous linear
equivalence `L` of the model space with Euclidean space, matching the metric at `p` through an
isometry `O` of the tangent space, and carrying the coordinate Haar measure to the Euclidean
volume divided by the chart density at `p`. -/
private lemma exists_equiv_map_addHaar_eq_smul_volume (p : M) :
    ∃ L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)),
      (∃ O : TangentSpace I p ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)),
        ∀ ξ : TangentSpace I p,
          L ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p ξ) = O ξ) ∧
      Measure.map L (finBasis ℝ E).addHaar =
        (chartVolumeDensity (I := I) p p)⁻¹.toNNReal • volume := by
  set e := trivializationAt E (TangentSpace I) p
  have hp : p ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  let O : TangentSpace I p ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
    (stdOrthonormalBasis ℝ (TangentSpace I p)).repr
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
    (e.continuousLinearEquivAt ℝ p hp).symm.trans O.toContinuousLinearEquiv
  have hLapp (w : E) : L w = O (e.symmL ℝ p w) := by
    simp [L, e.symm_continuousLinearEquivAt_eq hp]
  refine ⟨L, ⟨O, fun ξ ↦ by rw [hLapp, e.symmL_continuousLinearMapAt hp]⟩, ?_⟩
  exact map_addHaar_eq_chartVolumeDensity_inv_smul_volume p L fun v w ↦ by
    rw [hLapp, hLapp, O.inner_map_map]

/-- A Euclidean test function `v` supported in the unit ball, with Sobolev quotient below
`Y(Sⁿ) + ε / 2`, together with a distortion `η ∈ (0, 1)` for which the bound
`((1 + η) ³ A + S (1 + η) η ² B) / ((1 - η) ^ (2 / pₙ) D ^ (2 / pₙ))` on the Yamabe quotient of its
transplant is below `Y(Sⁿ) + ε`; here `A = aₙ ∫ |dv|²`, `B = ∫ v²` and `D = ∫ |v| ^ pₙ`. -/
private lemma exists_contDiff_hasCompactSupport_and_distortion {n : ℕ} (hn : 2 < n) {ε S : ℝ}
    (hε : 0 < ε) :
    ∃ v : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧
      tsupport v ⊆ ball 0 1 ∧ (∀ z, 0 ≤ v z) ∧ 0 < ∫ z, |v z| ^ criticalExponent n ∧
      ∃ η ∈ Ioo (0 : ℝ) 1,
        ((1 + η) ^ 3 * (conformalCoefficient n * ∫ z, ‖fderiv ℝ v z‖ ^ 2) +
            S * (1 + η) * η ^ 2 * ∫ z, v z ^ 2) /
          ((1 - η) ^ (2 / criticalExponent n) * (∫ z, |v z| ^ criticalExponent n) ^
            (2 / criticalExponent n)) < sphereYamabeConstant n + ε := by
  have hF : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  obtain ⟨v, hv, hvc, hvsupp, hv0, hD, hq⟩ :=
    exists_contDiff_hasCompactSupport_sobolev_quotient_lt (E := EuclideanSpace ℝ (Fin n))
      (Ω := ball 0 1) (by rwa [hF]) isOpen_ball (nonempty_ball.2 one_pos) (half_pos hε)
  rw [hF] at hD hq
  refine ⟨v, hv, hvc, hvsupp, hv0, hD, ?_⟩
  set P := criticalExponent n
  set A := conformalCoefficient n * ∫ z, ‖fderiv ℝ v z‖ ^ 2
  set B := ∫ z, v z ^ 2
  set D := ∫ z, |v z| ^ P
  set G : ℝ → ℝ := fun η ↦
    ((1 + η) ^ 3 * A + S * (1 + η) * η ^ 2 * B) / ((1 - η) ^ (2 / P) * D ^ (2 / P))
  have hG : Tendsto G (𝓝 0) (𝓝 (A / D ^ (2 / P))) := by
    have hcont : ContinuousAt G 0 := by
      refine ContinuousAt.div (by fun_prop) (ContinuousAt.mul ?_ continuousAt_const) ?_
      · exact (continuousAt_const.sub continuousAt_id).rpow_const (Or.inl (by simp))
      · simp only [sub_zero, Real.one_rpow, one_mul]
        exact (Real.rpow_pos_of_pos hD _).ne'
    simpa [G] using hcont.tendsto
  obtain ⟨η, hη, hGη⟩ : ∃ η ∈ Ioo (0 : ℝ) 1, G η < sphereYamabeConstant n + ε :=
    (Filter.Eventually.and (Ioo_mem_nhdsGT one_pos)
      ((hG.mono_left nhdsWithin_le_nhds).eventually_lt_const (by linarith))).exists
  exact ⟨η, hη, hGη⟩

omit [FiniteDimensional ℝ E] in
/-- The set of points whose rescaled coordinate `Ψ y = t⁻¹ • L (y - x)` lies in the support of a
function supported in the unit ball is contained in a compact subset of the ball of radius `R`
around `x`, as soon as `t ‖L⁻¹‖ < R`. -/
private lemma exists_isCompact_subset_ball_forall_mem_tsupport
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E))) (x : E) {t R : ℝ} (ht0 : 0 < t)
    (htR : t * ‖(L.symm : EuclideanSpace ℝ (Fin (finrank ℝ E)) →L[ℝ] E)‖ < R)
    {v : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ} (hvc : HasCompactSupport v)
    (hvsupp : tsupport v ⊆ ball 0 1) {Ψ : E → EuclideanSpace ℝ (Fin (finrank ℝ E))}
    (hΨ : Ψ = fun y ↦ t⁻¹ • L (y - x)) :
    ∃ K : Set E, IsCompact K ∧ K ⊆ ball x R ∧ ∀ y, Ψ y ∈ tsupport v → y ∈ K := by
  set C := ‖(L.symm : EuclideanSpace ℝ (Fin (finrank ℝ E)) →L[ℝ] E)‖
  have hΨ_eq (y : E) : y = x + L.symm (t • Ψ y) := by
    simp [hΨ, smul_smul, ht0.ne']
  refine ⟨(fun z ↦ x + L.symm (t • z)) '' tsupport v, hvc.isCompact.image (by fun_prop), ?_,
    fun y hy ↦ ⟨Ψ y, hy, (hΨ_eq y).symm⟩⟩
  rintro _ ⟨z, hz, rfl⟩
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 (hvsupp hz)
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
  calc ‖L.symm (t • z)‖
      ≤ C * ‖t • z‖ := (L.symm : EuclideanSpace ℝ (Fin (finrank ℝ E)) →L[ℝ] E).le_opNorm _
    _ = t * C * ‖z‖ := by rw [norm_smul, Real.norm_of_nonneg ht0.le]; ring
    _ ≤ t * C := mul_le_of_le_one_right (by positivity) hz1.le
    _ < R := htR

/-- Integrals of functions of the rescaled coordinate `Ψ y = t⁻¹ • L (y - x)` are Euclidean
integrals scaled by `t ^ n / ρ`, when `L` carries the coordinate Haar measure to `ρ⁻¹` times the
Euclidean volume. -/
private lemma integral_comp_rescale_eq {ρ t : ℝ} (hρ : 0 < ρ) (ht0 : 0 < t)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)))
    (hmap : Measure.map L (finBasis ℝ E).addHaar = ρ⁻¹.toNNReal • volume) (x : E)
    {Ψ : E → EuclideanSpace ℝ (Fin (finrank ℝ E))} (hΨ : Ψ = fun y ↦ t⁻¹ • L (y - x))
    (k : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ) :
    ∫ y, k (Ψ y) ∂(finBasis ℝ E).addHaar = ρ⁻¹ * (t ^ finrank ℝ E * ∫ z, k z) := by
  subst hΨ
  have h := integral_map_equiv L.toHomeomorph.toMeasurableEquiv (μ := (finBasis ℝ E).addHaar)
    fun z ↦ k (t⁻¹ • z)
  simp only [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph] at h
  calc ∫ y, k (t⁻¹ • L (y - x)) ∂(finBasis ℝ E).addHaar
      = ∫ z, k (t⁻¹ • z) ∂Measure.map L (finBasis ℝ E).addHaar := by
        rw [integral_sub_right_eq_self (fun y ↦ k (t⁻¹ • L y)) x, h]
    _ = ρ⁻¹ * ∫ z, k (t⁻¹ • z) := by
        rw [hmap, integral_smul_nnreal_measure]
        simp [NNReal.smul_def, hρ.le]
    _ = ρ⁻¹ * (t ^ finrank ℝ E * ∫ z, k z) := by
        rw [Measure.integral_comp_inv_smul_of_nonneg _ _ ht0.le, finrank_euclideanSpace_fin,
          smul_eq_mul]

/-- A continuous function of the rescaled coordinate `Ψ`, vanishing outside a set `T`, is
integrable and supported in the ball of radius `R`, when the preimage of `T` under the continuous
map `Ψ` lies in a compact subset of that ball. -/
private lemma integrable_comp_and_support_subset_ball {R : ℝ} {x : E}
    {Ψ : E → EuclideanSpace ℝ (Fin (finrank ℝ E))} (hΨc : Continuous Ψ) {K : Set E}
    (hK : IsCompact K) (hKR : K ⊆ ball x R) {T : Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hΨK : ∀ y, Ψ y ∈ T → y ∈ K) {k : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ}
    (hk : Continuous k) (hkz : ∀ z ∉ T, k z = 0) :
    Integrable (fun y ↦ k (Ψ y)) (finBasis ℝ E).addHaar ∧
      Function.support (fun y ↦ k (Ψ y)) ⊆ ball x R :=
  ⟨(hk.comp hΨc).integrable_of_hasCompactSupport
    (HasCompactSupport.intro hK fun y hy ↦ hkz _ fun h ↦ hy (hΨK y h)),
    fun y hy ↦ hKR (hΨK y (by_contra fun h ↦ hy (hkz _ h)))⟩

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
/-- A smooth nonnegative function on the model space supported in a compact subset `K` of a
coordinate ball, transplanted to the manifold: it is a smooth nonnegative compactly supported
function whose support lies in any `U` containing the chart preimage of the ball, and which agrees
with `w` in the chart. -/
private lemma exists_contMDiff_transplant (p : M) {R : ℝ} {U : Set M}
    (hballt : ball (extChartAt I p p) R ⊆ (extChartAt I p).target)
    (hballU : ∀ y ∈ ball (extChartAt I p p) R, (extChartAt I p).symm y ∈ U) {K : Set E}
    (hK : IsCompact K) (hKR : K ⊆ ball (extChartAt I p p) R) {w : E → ℝ}
    (hw : ContDiff ℝ ∞ w) (hw0 : ∀ y, 0 ≤ w y) (hwK : tsupport w ⊆ K) :
    ∃ u : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ u ∧ HasCompactSupport u ∧ tsupport u ⊆ U ∧
      (∀ x, 0 ≤ u x) ∧
      (∀ x ∈ tsupport u, x ∈ (extChartAt I p).source ∧
        extChartAt I p x ∈ ball (extChartAt I p p) R) ∧
      ∀ y ∈ ball (extChartAt I p p) R, u ((extChartAt I p).symm y) = w y := by
  set φ := extChartAt I p
  obtain ⟨u, hu, huc, htsupp, hu_symm⟩ := exists_contMDiff_comp_extChartAt_symm_eq (c := p) hw
    (HasCompactSupport.intro hK fun y hy ↦ image_eq_zero_of_notMem_tsupport fun h ↦
      hy (hwK h)) (hwK.trans (hKR.trans hballt))
  have hsup (x : M) (hx : x ∈ tsupport u) : x ∈ φ.source ∧ φ x ∈ ball (φ p) R := by
    obtain ⟨y, hy, rfl⟩ := htsupp hx
    have hyt := hballt (hKR (hwK hy))
    exact ⟨φ.map_target hyt, by rw [φ.right_inv hyt]; exact hKR (hwK hy)⟩
  refine ⟨u, hu, huc, fun x hx ↦ ?_, fun x ↦ ?_, hsup, fun y hy ↦ hu_symm y (hballt hy)⟩
  · obtain ⟨hxs, hxb⟩ := hsup x hx
    have h := hballU _ hxb
    rwa [φ.left_inv hxs] at h
  · by_cases hx : x ∈ tsupport u
    · obtain ⟨y, hy, rfl⟩ := htsupp hx
      rw [hu_symm y (hballt (hKR (hwK hy)))]
      exact hw0 _
    · rw [image_eq_zero_of_notMem_tsupport hx]

omit [T2Space M] [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
/-- The Riemannian gradient of the transplant `u` of `v ∘ Ψ`, where `Ψ y = t⁻¹ • L (y - φ p)` and
`L` is orthonormal for the metric at `p` (through `O`), is at most `(1 + η) t⁻¹ |dv (Ψ y)|` at
every point where gradients are controlled by coordinate differentials up to the factor `1 + η`. -/
private lemma norm_mgradient_transplant_le (p : M) {R t η : ℝ} (ht0 : 0 < t) (hη : 0 ≤ 1 + η)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)))
    (O : TangentSpace I p ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)))
    (hLO : ∀ ξ : TangentSpace I p,
      L ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p ξ) = O ξ)
    {v : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ} (hv : ContDiff ℝ ∞ v)
    {Ψ : E → EuclideanSpace ℝ (Fin (finrank ℝ E))}
    (hΨ : Ψ = fun y ↦ t⁻¹ • L (y - extChartAt I p p)) {u : M → ℝ}
    (hu_symm : ∀ y ∈ ball (extChartAt I p p) R, u ((extChartAt I p).symm y) = v (Ψ y))
    {y : E} (hy : y ∈ ball (extChartAt I p p) R)
    (hg : ∀ f : M → ℝ, DifferentiableAt ℝ (f ∘ (extChartAt I p).symm) y →
      ‖mgradient I f ((extChartAt I p).symm y)‖ ≤ (1 + η) * ‖(fderiv ℝ
        (f ∘ (extChartAt I p).symm) y ∘L
          (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p :
            TangentSpace I p →L[ℝ] ℝ)‖) :
    ‖mgradient I u ((extChartAt I p).symm y)‖ ≤ (1 + η) * (t⁻¹ * ‖fderiv ℝ v (Ψ y)‖) := by
  have hΨd : HasFDerivAt Ψ (t⁻¹ • (L : E →L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)))) y := by
    have h := ((L : E →L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E))).hasFDerivAt.comp y
      ((hasFDerivAt_id y).sub_const (extChartAt I p p))).const_smul t⁻¹
    rw [ContinuousLinearMap.comp_id] at h
    rw [hΨ]
    exact h
  have hw : ContDiff ℝ ∞ fun y ↦ v (Ψ y) := hv.comp (by rw [hΨ]; fun_prop)
  have heq : u ∘ (extChartAt I p).symm =ᶠ[𝓝 y] fun y ↦ v (Ψ y) :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hy) hu_symm
  have hd : DifferentiableAt ℝ (u ∘ (extChartAt I p).symm) y :=
    ((hw.differentiable (by simp)) y).congr_of_eventuallyEq heq
  refine (hg u hd).trans (mul_le_mul_of_nonneg_left (le_of_eq ?_) hη)
  have hfd : fderiv ℝ (fun y ↦ v (Ψ y)) y = fderiv ℝ v (Ψ y) ∘L
      (t⁻¹ • (L : E →L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)))) :=
    (((hv.differentiable (by simp)) (Ψ y)).hasFDerivAt.comp y hΨd).fderiv
  have hcomp : (fderiv ℝ (fun y ↦ v (Ψ y)) y ∘L
      (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p :
        TangentSpace I p →L[ℝ] ℝ) =
      (t⁻¹ • fderiv ℝ v (Ψ y)) ∘L
        (O : TangentSpace I p →L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E))) := by
    ext ξ
    simp only [hfd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_comp,
      smul_apply, ContinuousLinearEquiv.coe_coe, ← hLO,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, map_smul, smul_eq_mul]
  rw [heq.fderiv_eq, hcomp, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.2 ht0.le)]

omit [T2Space M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The Dirichlet energy of the transplant `u` is at most `(1 + η) ³ t ^ (n - 2)` times the
Euclidean energy of `v`, where `Ψ` rescales coordinates by `t⁻¹`. -/
private lemma integral_norm_mgradient_sq_le (p : M) {R t η : ℝ} (hn : 2 < finrank ℝ E)
    (ht0 : 0 < t) (hη0 : 0 < η) (hρp : 0 < chartVolumeDensity (I := I) p p)
    (hballt : ball (extChartAt I p p) R ⊆ (extChartAt I p).target)
    {v : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ} (hv : ContDiff ℝ ∞ v)
    {Ψ : E → EuclideanSpace ℝ (Fin (finrank ℝ E))} {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ) ∞ u) (huc : HasCompactSupport u)
    (hsup : ∀ x ∈ tsupport u, x ∈ (extChartAt I p).source ∧
      extChartAt I p x ∈ ball (extChartAt I p p) R)
    (hρ : ∀ y ∈ ball (extChartAt I p p) R, chartVolumeDensity (I := I) p
      ((extChartAt I p).symm y) ≤ (1 + η) * chartVolumeDensity (I := I) p p)
    (hgrad : ∀ y ∈ ball (extChartAt I p p) R, ‖mgradient I u ((extChartAt I p).symm y)‖ ≤
      (1 + η) * (t⁻¹ * ‖fderiv ℝ v (Ψ y)‖))
    (hint : ∀ k : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ, Continuous k →
      (∀ z ∉ tsupport v, k z = 0) → Integrable (fun y ↦ k (Ψ y)) (finBasis ℝ E).addHaar)
    (hcv : ∀ k : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ, ∫ y, k (Ψ y) ∂(finBasis ℝ E).addHaar =
      (chartVolumeDensity (I := I) p p)⁻¹ * (t ^ finrank ℝ E * ∫ z, k z)) :
    ∫ x, ‖mgradient I u x‖ ^ 2 ∂riemannianVolume I M ≤
      (1 + η) ^ 3 * t ^ (finrank ℝ E - 2) * ∫ z, ‖fderiv ℝ v z‖ ^ 2 := by
  set ρ := chartVolumeDensity (I := I) p
  have hu1 : ContMDiff I 𝓘(ℝ) 1 u := hu.of_le (by simp)
  have hgradsq : Continuous fun x ↦ ‖mgradient I u x‖ ^ 2 :=
    continuous_norm_sq_mgradient hu1
  have hgrad0 (x : M) (hx : x ∉ tsupport u) : mgradient I u x = 0 :=
    mgradient_eq_zero_iff.2 ((notMem_tsupport_iff_eventuallyEq.1 hx).mvfderiv_eq.trans
      mvfderiv_zero)
  have hsupp_grad : Function.support (fun x ↦ ‖mgradient I u x‖ ^ 2) ⊆ tsupport u := fun x hx ↦
    by_contra fun h ↦ hx (by simp [hgrad0 x h])
  have hdv0 (z : EuclideanSpace ℝ (Fin (finrank ℝ E))) (hz : z ∉ tsupport v) :
      ‖fderiv ℝ v z‖ ^ 2 = 0 := by
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hz (tsupport_fderiv_subset ℝ h)), norm_zero,
      sq, zero_mul]
  have htn : t ^ finrank ℝ E = t ^ (finrank ℝ E - 2) * t ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel hn.le]
  have h := integral_riemannianVolume_le_mul_integral_of_support_subset p isOpen_ball hballt
    (fun x ↦ sq_nonneg _) (hgradsq.integrable_of_hasCompactSupport (huc.mono' hsupp_grad))
    (fun x hx ↦ hsup x (by_contra fun h ↦ hx (by simp [hgrad0 x h]))) (fun y ↦ sq_nonneg _)
    (hint _ ((hv.continuous_fderiv (by simp)).norm.pow 2) hdv0)
    (c := (1 + η) ^ 3 * ρ p * (t⁻¹) ^ 2) (by positivity) fun y hy ↦ by
      calc ρ ((extChartAt I p).symm y) * ‖mgradient I u ((extChartAt I p).symm y)‖ ^ 2
          ≤ ((1 + η) * ρ p) * ((1 + η) * (t⁻¹ * ‖fderiv ℝ v (Ψ y)‖)) ^ 2 :=
            mul_le_mul (hρ y hy) (pow_le_pow_left₀ (norm_nonneg _) (hgrad y hy) 2)
              (sq_nonneg _) (by positivity)
        _ = (1 + η) ^ 3 * ρ p * (t⁻¹) ^ 2 * ‖fderiv ℝ v (Ψ y)‖ ^ 2 := by ring
  refine h.trans (le_of_eq ?_)
  rw [hcv (fun z ↦ ‖fderiv ℝ v z‖ ^ 2), htn]
  field_simp

omit [T2Space M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The `L²` norm of the transplant `u` is at most `(1 + η) t ^ n` times that of `v`. -/
private lemma integral_sq_le (p : M) {R t η : ℝ} (ht0 : 0 < t) (hη0 : 0 < η)
    (hρp : 0 < chartVolumeDensity (I := I) p p)
    (hballt : ball (extChartAt I p p) R ⊆ (extChartAt I p).target)
    {v : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ} (hv : ContDiff ℝ ∞ v)
    {Ψ : E → EuclideanSpace ℝ (Fin (finrank ℝ E))} {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ) ∞ u) (huc : HasCompactSupport u)
    (hsup : ∀ x ∈ tsupport u, x ∈ (extChartAt I p).source ∧
      extChartAt I p x ∈ ball (extChartAt I p p) R)
    (hu_symm : ∀ y ∈ ball (extChartAt I p p) R, u ((extChartAt I p).symm y) = v (Ψ y))
    (hρ : ∀ y ∈ ball (extChartAt I p p) R, chartVolumeDensity (I := I) p
      ((extChartAt I p).symm y) ≤ (1 + η) * chartVolumeDensity (I := I) p p)
    (hint : ∀ k : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ, Continuous k →
      (∀ z ∉ tsupport v, k z = 0) → Integrable (fun y ↦ k (Ψ y)) (finBasis ℝ E).addHaar)
    (hcv : ∀ k : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ, ∫ y, k (Ψ y) ∂(finBasis ℝ E).addHaar =
      (chartVolumeDensity (I := I) p p)⁻¹ * (t ^ finrank ℝ E * ∫ z, k z)) :
    ∫ x, u x ^ 2 ∂riemannianVolume I M ≤ (1 + η) * t ^ finrank ℝ E * ∫ z, v z ^ 2 := by
  have hsupp_sq : Function.support (fun x ↦ u x ^ 2) ⊆ tsupport u := fun x hx ↦
    by_contra fun h ↦ hx (by simp [image_eq_zero_of_notMem_tsupport h])
  have h := integral_riemannianVolume_le_mul_integral_of_support_subset p isOpen_ball hballt
    (fun x ↦ sq_nonneg (u x))
    ((hu.continuous.pow 2).integrable_of_hasCompactSupport (huc.mono' hsupp_sq))
    (fun x hx ↦ hsup x (by_contra fun h ↦ hx (by simp [image_eq_zero_of_notMem_tsupport h])))
    (fun y ↦ sq_nonneg _)
    (hint (fun z ↦ v z ^ 2) (hv.continuous.pow 2) fun z hz ↦ by
      simp [image_eq_zero_of_notMem_tsupport hz])
    (c := (1 + η) * chartVolumeDensity (I := I) p p) (by positivity) fun y hy ↦ by
      rw [hu_symm y hy]
      exact mul_le_mul_of_nonneg_right (hρ y hy) (sq_nonneg _)
  refine h.trans (le_of_eq ?_)
  rw [hcv (fun z ↦ v z ^ 2)]
  field_simp

omit [T2Space M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The critical mass of the transplant `u` is at least `(1 - η) t ^ n` times that of `v`. -/
private lemma le_integral_abs_rpow {R t η : ℝ} (p : M) (hn : 2 < finrank ℝ E) (ht0 : 0 < t)
    (hη1 : η < 1) (hρp : 0 < chartVolumeDensity (I := I) p p)
    (hballt : ball (extChartAt I p p) R ⊆ (extChartAt I p).target)
    {v : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ} (hv : ContDiff ℝ ∞ v)
    {Ψ : E → EuclideanSpace ℝ (Fin (finrank ℝ E))} {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ) ∞ u) (huc : HasCompactSupport u)
    (hsup : ∀ x ∈ tsupport u, x ∈ (extChartAt I p).source ∧
      extChartAt I p x ∈ ball (extChartAt I p p) R)
    (hu_symm : ∀ y ∈ ball (extChartAt I p p) R, u ((extChartAt I p).symm y) = v (Ψ y))
    (hρ : ∀ y ∈ ball (extChartAt I p p) R, (1 - η) * chartVolumeDensity (I := I) p p ≤
      chartVolumeDensity (I := I) p ((extChartAt I p).symm y))
    (hint : ∀ k : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ, Continuous k →
      (∀ z ∉ tsupport v, k z = 0) → Integrable (fun y ↦ k (Ψ y)) (finBasis ℝ E).addHaar)
    (hsb : ∀ k : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ, Continuous k →
      (∀ z ∉ tsupport v, k z = 0) →
        Function.support (fun y ↦ k (Ψ y)) ⊆ ball (extChartAt I p p) R)
    (hcv : ∀ k : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ, ∫ y, k (Ψ y) ∂(finBasis ℝ E).addHaar =
      (chartVolumeDensity (I := I) p p)⁻¹ * (t ^ finrank ℝ E * ∫ z, k z)) :
    (1 - η) * t ^ finrank ℝ E * ∫ z, |v z| ^ criticalExponent (finrank ℝ E) ≤
      ∫ x, |u x| ^ criticalExponent (finrank ℝ E) ∂riemannianVolume I M := by
  have hP := criticalExponent_pos hn
  have hη1' : 0 < 1 - η := by linarith
  have hPz (z : ℝ) (hz : z = 0) : |z| ^ criticalExponent (finrank ℝ E) = 0 := by
    rw [hz, abs_zero, Real.zero_rpow hP.ne']
  have hcontP : Continuous fun r : ℝ ↦ |r| ^ criticalExponent (finrank ℝ E) :=
    continuous_abs.rpow_const fun _ ↦ Or.inr hP.le
  have hvz (z : EuclideanSpace ℝ (Fin (finrank ℝ E))) (hz : z ∉ tsupport v) :
      |v z| ^ criticalExponent (finrank ℝ E) = 0 :=
    hPz _ (image_eq_zero_of_notMem_tsupport hz)
  have h := mul_integral_le_integral_riemannianVolume_of_support_subset p isOpen_ball hballt
    (fun x ↦ Real.rpow_nonneg (abs_nonneg (u x)) _)
    ((hcontP.comp hu.continuous).integrable_of_hasCompactSupport (huc.mono' fun x hx ↦
      by_contra fun h ↦ hx (hPz _ (image_eq_zero_of_notMem_tsupport h))))
    (fun x hx ↦ hsup x (by_contra fun h ↦ hx (hPz _ (image_eq_zero_of_notMem_tsupport h))))
    (fun y ↦ Real.rpow_nonneg (abs_nonneg _) _)
    (hint (fun z ↦ |v z| ^ criticalExponent (finrank ℝ E)) (hcontP.comp hv.continuous) hvz)
    (hsb _ (hcontP.comp hv.continuous) hvz)
    (c := (1 - η) * chartVolumeDensity (I := I) p p) (by positivity) fun y hy ↦ by
      rw [hu_symm y hy]
      exact mul_le_mul_of_nonneg_right (hρ y hy) (Real.rpow_nonneg (abs_nonneg _) _)
  refine le_of_eq_of_le ?_ h
  rw [hcv (fun z ↦ |v z| ^ criticalExponent (finrank ℝ E))]
  field_simp

/-- The Yamabe numerator of the transplant `u` is controlled by the bounds on its Dirichlet energy
and `L²` norm, where the scalar curvature is at most `S` on the support of `u`. -/
private lemma integral_numerator_le (p : M) {R t η a S J B : ℝ} {u : M → ℝ}
    (hn : 2 < finrank ℝ E) (ha : 0 ≤ a) (hS : 0 ≤ S) (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (huc : HasCompactSupport u)
    (hsup : ∀ x ∈ tsupport u, x ∈ (extChartAt I p).source ∧
      extChartAt I p x ∈ ball (extChartAt I p p) R)
    (hScal : ∀ y ∈ ball (extChartAt I p p) R,
      |(CovariantDerivative.leviCivitaConnection I M).scalarCurvature
        ((extChartAt I p).symm y)| ≤ S)
    (hIg : ∫ x, ‖mgradient I u x‖ ^ 2 ∂riemannianVolume I M ≤
      (1 + η) ^ 3 * t ^ (finrank ℝ E - 2) * J)
    (hI2 : ∫ x, u x ^ 2 ∂riemannianVolume I M ≤ (1 + η) * t ^ finrank ℝ E * B) :
    ∫ x, (a * ‖mgradient I u x‖ ^ 2 +
        (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * u x ^ 2)
          ∂riemannianVolume I M ≤
      t ^ (finrank ℝ E - 2) * ((1 + η) ^ 3 * (a * J) + S * (1 + η) * t ^ 2 * B) := by
  set Scal := (CovariantDerivative.leviCivitaConnection I M).scalarCurvature
  have hu1 : ContMDiff I 𝓘(ℝ) 1 u := hu.of_le (by simp)
  have hgradsq : Continuous fun x ↦ ‖mgradient I u x‖ ^ 2 :=
    continuous_norm_sq_mgradient hu1
  have hgrad0 (x : M) (hx : x ∉ tsupport u) : mgradient I u x = 0 :=
    mgradient_eq_zero_iff.2 ((notMem_tsupport_iff_eventuallyEq.1 hx).mvfderiv_eq.trans
      mvfderiv_zero)
  have hint₁ : Integrable (fun x ↦ a * ‖mgradient I u x‖ ^ 2) (riemannianVolume I M) :=
    (hgradsq.integrable_of_hasCompactSupport (huc.mono' fun x hx ↦
      by_contra fun h ↦ hx (by simp [hgrad0 x h]))).const_mul a
  have hint₂ (g : M → ℝ) (hg : Continuous g) :
      Integrable (fun x ↦ g x * u x ^ 2) (riemannianVolume I M) :=
    (hg.mul (hu.continuous.pow 2)).integrable_of_hasCompactSupport (huc.mono' fun x hx ↦
      by_contra fun h ↦ hx (by simp [image_eq_zero_of_notMem_tsupport h]))
  have hScalc : Continuous Scal :=
    (CovariantDerivative.leviCivitaConnection I M).contMDiff_scalarCurvature.continuous
  have htn : t ^ finrank ℝ E = t ^ (finrank ℝ E - 2) * t ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel hn.le]
  calc ∫ x, (a * ‖mgradient I u x‖ ^ 2 + Scal x * u x ^ 2) ∂riemannianVolume I M
      ≤ ∫ x, (a * ‖mgradient I u x‖ ^ 2 + S * u x ^ 2) ∂riemannianVolume I M := by
        refine integral_mono (hint₁.add (hint₂ Scal hScalc))
          (hint₁.add (hint₂ _ continuous_const)) fun x ↦ add_le_add le_rfl ?_
        by_cases hx : x ∈ tsupport u
        · obtain ⟨hxs, hxb⟩ := hsup x hx
          have hS' := hScal _ hxb
          rw [(extChartAt I p).left_inv hxs] at hS'
          exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans hS') (sq_nonneg _)
        · simp [image_eq_zero_of_notMem_tsupport hx]
    _ = a * ∫ x, ‖mgradient I u x‖ ^ 2 ∂riemannianVolume I M +
        S * ∫ x, u x ^ 2 ∂riemannianVolume I M := by
        rw [integral_add hint₁ (hint₂ _ continuous_const), integral_const_mul,
          integral_const_mul]
    _ ≤ a * ((1 + η) ^ 3 * t ^ (finrank ℝ E - 2) * J) +
        S * ((1 + η) * t ^ finrank ℝ E * B) := by gcongr
    _ = t ^ (finrank ℝ E - 2) * ((1 + η) ^ 3 * (a * J) + S * (1 + η) * t ^ 2 * B) := by
        rw [htn]; ring

/-- The `(2 / pₙ)`-th power of the critical mass is at least `(1 - η) ^ (2 / pₙ) t ^ (n - 2)` times
that of `v`, using `(t ^ n) ^ (2 / pₙ) = t ^ (n - 2)`. -/
private lemma rpow_two_div_criticalExponent_le {n : ℕ} (hn : 2 < n) {η t D J : ℝ} (hη : η < 1)
    (ht0 : 0 < t) (hD : 0 < D) (hIP : (1 - η) * t ^ n * D ≤ J) :
    (1 - η) ^ (2 / criticalExponent n) * t ^ (n - 2) * D ^ (2 / criticalExponent n) ≤
      J ^ (2 / criticalExponent n) := by
  have hP := criticalExponent_pos hn
  have hη1' : 0 < 1 - η := by linarith
  have htP : (t ^ n) ^ (2 / criticalExponent n) = t ^ (n - 2) := by
    have hexp : (n : ℝ) * (2 / criticalExponent n) = (n - 2 : ℕ) := by
      have : (n : ℝ) ≠ 0 := by positivity
      rw [two_div_criticalExponent]
      push_cast [hn.le]
      field_simp
    rw [← Real.rpow_natCast_mul ht0.le, hexp, Real.rpow_natCast]
  calc (1 - η) ^ (2 / criticalExponent n) * t ^ (n - 2) * D ^ (2 / criticalExponent n)
      = ((1 - η) * t ^ n * D) ^ (2 / criticalExponent n) := by
        rw [Real.mul_rpow (by positivity) hD.le, Real.mul_rpow hη1'.le (by positivity), htP]
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hIP (by positivity)

/-- The final estimate of the Yamabe quotient of the transplant: the numerator and denominator
bounds give a quotient at most the distortion bound, using `t ≤ η`. -/
private lemma div_rpow_le_distortion_bound {n : ℕ} {P η t S A B D N J : ℝ} (hη1 : η < 1)
    (ht0 : 0 < t) (htη : t ≤ η) (hS : 0 ≤ S) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 < D)
    (hnum : N ≤ t ^ (n - 2) * ((1 + η) ^ 3 * A + S * (1 + η) * t ^ 2 * B))
    (hden : (1 - η) ^ (2 / P) * t ^ (n - 2) * D ^ (2 / P) ≤ J ^ (2 / P)) :
    N / J ^ (2 / P) ≤
      ((1 + η) ^ 3 * A + S * (1 + η) * η ^ 2 * B) / ((1 - η) ^ (2 / P) * D ^ (2 / P)) := by
  have hη1' := sub_pos.2 hη1
  have hη0 : 0 < η := ht0.trans_le htη
  calc N / J ^ (2 / P)
      ≤ t ^ (n - 2) * ((1 + η) ^ 3 * A + S * (1 + η) * t ^ 2 * B) /
        ((1 - η) ^ (2 / P) * t ^ (n - 2) * D ^ (2 / P)) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = ((1 + η) ^ 3 * A + S * (1 + η) * t ^ 2 * B) / ((1 - η) ^ (2 / P) * D ^ (2 / P)) := by
        have : t ^ (n - 2) ≠ 0 := pow_ne_zero _ ht0.ne'
        field_simp
    _ ≤ _ := by gcongr

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- **The transplanted test function.** Given orthonormal coordinates `L` at `p` (see
`exists_equiv_map_addHaar_eq_smul_volume`), a Euclidean test function `v` supported in the unit
ball and a scale `t` with `t ‖L⁻¹‖ < R`, the function `v (t⁻¹ • L (· - φ p))` transplants to a
smooth nonnegative compactly supported function `u` on `M`, supported in `U`, with Dirichlet energy
and `L²` norm at most `(1 + η) ³ t ^ (n - 2)` and `(1 + η) t ^ n` times those of `v`, and critical
mass at least `(1 - η) t ^ n` times that of `v`, where the density and the metric are
`η`-close to their values at `p` on the chart ball of radius `R`. -/
private lemma exists_transplant_bounds (p : M) {R t η : ℝ} {U : Set M} (hn : 2 < finrank ℝ E)
    (hη0 : 0 < η) (hη1 : η < 1) (ht0 : 0 < t) (hρp : 0 < chartVolumeDensity (I := I) p p)
    (hballt : ball (extChartAt I p p) R ⊆ (extChartAt I p).target)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)))
    (htR : t * ‖(L.symm : EuclideanSpace ℝ (Fin (finrank ℝ E)) →L[ℝ] E)‖ < R)
    (O : TangentSpace I p ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)))
    (hLO : ∀ ξ : TangentSpace I p,
      L ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p ξ) = O ξ)
    (hmap : Measure.map L (finBasis ℝ E).addHaar =
      (chartVolumeDensity (I := I) p p)⁻¹.toNNReal • volume)
    {v : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) (hvsupp : tsupport v ⊆ ball 0 1) (hv0 : ∀ z, 0 ≤ v z)
    (hballU : ∀ y ∈ ball (extChartAt I p p) R, (extChartAt I p).symm y ∈ U)
    (hρ : ∀ y ∈ ball (extChartAt I p p) R, chartVolumeDensity (I := I) p
      ((extChartAt I p).symm y) ∈ Icc ((1 - η) * chartVolumeDensity (I := I) p p)
        ((1 + η) * chartVolumeDensity (I := I) p p))
    (hg : ∀ y ∈ ball (extChartAt I p p) R, ∀ f : M → ℝ,
      DifferentiableAt ℝ (f ∘ (extChartAt I p).symm) y →
        ‖mgradient I f ((extChartAt I p).symm y)‖ ≤ (1 + η) * ‖(fderiv ℝ
          (f ∘ (extChartAt I p).symm) y ∘L
            (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p :
              TangentSpace I p →L[ℝ] ℝ)‖) :
    ∃ u : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ u ∧ HasCompactSupport u ∧ tsupport u ⊆ U ∧
      (∀ x, 0 ≤ u x) ∧
      (∀ x ∈ tsupport u, x ∈ (extChartAt I p).source ∧
        extChartAt I p x ∈ ball (extChartAt I p p) R) ∧
      ∫ x, ‖mgradient I u x‖ ^ 2 ∂riemannianVolume I M ≤
        (1 + η) ^ 3 * t ^ (finrank ℝ E - 2) * ∫ z, ‖fderiv ℝ v z‖ ^ 2 ∧
      ∫ x, u x ^ 2 ∂riemannianVolume I M ≤ (1 + η) * t ^ finrank ℝ E * ∫ z, v z ^ 2 ∧
      (1 - η) * t ^ finrank ℝ E * ∫ z, |v z| ^ criticalExponent (finrank ℝ E) ≤
        ∫ x, |u x| ^ criticalExponent (finrank ℝ E) ∂riemannianVolume I M := by
  set Ψ : E → EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
    fun y ↦ t⁻¹ • L (y - extChartAt I p p) with hΨ
  obtain ⟨K, hK, hKR, hΨK⟩ :=
    exists_isCompact_subset_ball_forall_mem_tsupport L (extChartAt I p p) ht0 htR hvc hvsupp hΨ
  have hΨc : Continuous Ψ := by rw [hΨ]; fun_prop
  obtain ⟨u, hu, huc, huU, hu0, hsup, hu_symm⟩ := exists_contMDiff_transplant p hballt hballU hK
    hKR (hv.comp (by rw [hΨ]; fun_prop) : ContDiff ℝ ∞ fun y ↦ v (Ψ y)) (fun y ↦ hv0 _)
    (closure_minimal (fun y hy ↦ hΨK y (subset_tsupport _ hy)) hK.isClosed)
  have hint : ∀ k : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ, Continuous k →
      (∀ z ∉ tsupport v, k z = 0) → Integrable (fun y ↦ k (Ψ y)) (finBasis ℝ E).addHaar :=
    fun k hk hkz ↦ (integrable_comp_and_support_subset_ball hΨc hK hKR hΨK hk hkz).1
  have hsb : ∀ k : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ, Continuous k →
      (∀ z ∉ tsupport v, k z = 0) →
        Function.support (fun y ↦ k (Ψ y)) ⊆ ball (extChartAt I p p) R :=
    fun k hk hkz ↦ (integrable_comp_and_support_subset_ball hΨc hK hKR hΨK hk hkz).2
  have hcv := integral_comp_rescale_eq hρp ht0 L hmap (extChartAt I p p) hΨ
  exact ⟨u, hu, huc, huU, hu0, hsup,
    integral_norm_mgradient_sq_le p hn ht0 hη0 hρp hballt hv hu huc hsup
      (fun y hy ↦ (hρ y hy).2)
      (fun y hy ↦ norm_mgradient_transplant_le p ht0 (by linarith) L O hLO hv hΨ hu_symm hy
        (hg y hy)) hint hcv,
    integral_sq_le p ht0 hη0 hρp hballt hv hu huc hsup hu_symm (fun y hy ↦ (hρ y hy).2) hint hcv,
    le_integral_abs_rpow p hn ht0 hη1 hρp hballt hv hu huc hsup hu_symm (fun y hy ↦ (hρ y hy).1)
      hint hsb hcv⟩

/-- **Test functions with Yamabe quotient below the sphere constant.** On a Riemannian manifold
without boundary of dimension `n > 2`, every nonempty open set `U` contains the support of a
nonnegative smooth compactly supported function `u` with positive critical mass
`∫ |u| ^ pₙ dV > 0` and Yamabe quotient `Q_g(u) < Y(Sⁿ) + ε`, for any `ε > 0`. -/
theorem exists_contMDiff_hasCompactSupport_yamabeQuotient_lt [I.Boundaryless]
    (hn : 2 < finrank ℝ E) {U : Set M} (hU : IsOpen U) (hUne : U.Nonempty) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ u : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ u ∧ HasCompactSupport u ∧ tsupport u ⊆ U ∧
      (∀ x, 0 ≤ u x) ∧
      (0 < ∫ x, |u x| ^ criticalExponent (finrank ℝ E) ∂riemannianVolume I M) ∧
      yamabeQuotient I u < sphereYamabeConstant (finrank ℝ E) + ε := by
  obtain ⟨p, hpU⟩ := hUne
  set S := |(CovariantDerivative.leviCivitaConnection I M).scalarCurvature p| + 1
  have hρp : 0 < chartVolumeDensity (I := I) p p :=
    chartVolumeDensity_pos p (FiberBundle.mem_baseSet_trivializationAt' p)
  obtain ⟨L, ⟨O, hLO⟩, hmap⟩ := exists_equiv_map_addHaar_eq_smul_volume (I := I) p
  obtain ⟨v, hv, hvc, hvsupp, hv0, hD, η, ⟨hη0, hη1⟩, hGη⟩ :=
    exists_contDiff_hasCompactSupport_and_distortion (S := S) hn hε
  obtain ⟨R, hR, hballt, hball⟩ :=
    exists_ball_forall_chart_close (I := I) p hη0 (hU.mem_nhds hpU)
  set C := ‖(L.symm : EuclideanSpace ℝ (Fin (finrank ℝ E)) →L[ℝ] E)‖
  set t := min η (R / (C + 1))
  have ht0 : 0 < t := lt_min hη0 (div_pos hR (by positivity))
  have htη : t ≤ η := min_le_left _ _
  have htR : t * C < R := by
    have h1 : t ≤ R / (C + 1) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [norm_nonneg (L.symm : EuclideanSpace ℝ (Fin (finrank ℝ E)) →L[ℝ] E)]
  obtain ⟨u, hu, huc, huU, hu0, hsup, hIg, hI2, hIP⟩ := exists_transplant_bounds p hn hη0 hη1 ht0
    hρp hballt L htR O hLO hmap hv hvc hvsupp hv0 (fun y hy ↦ (hball y hy).1)
    (fun y hy ↦ (hball y hy).2.1) (fun y hy ↦ (hball y hy).2.2.2)
  have hnum := integral_numerator_le p hn (conformalCoefficient_pos hn).le (by positivity) hu huc
    hsup (fun y hy ↦ (hball y hy).2.2.1) hIg hI2
  have hden := rpow_two_div_criticalExponent_le hn hη1 ht0 hD hIP
  have hη1' := sub_pos.2 hη1
  refine ⟨u, hu, huc, huU, hu0, (by positivity : 0 < (1 - η) * t ^ finrank ℝ E *
    ∫ z, |v z| ^ criticalExponent (finrank ℝ E)).trans_le hIP, ?_⟩
  rw [yamabeQuotient_def]
  exact (div_rpow_le_distortion_bound hη1 ht0 htη (by positivity)
    (mul_nonneg (conformalCoefficient_pos hn).le (integral_nonneg fun _ ↦ sq_nonneg _))
    (integral_nonneg fun _ ↦ sq_nonneg _) hD hnum hden).trans_lt hGη

/-- **The Yamabe invariant is at most that of the sphere.** On a nonempty Riemannian manifold
without boundary of dimension `n > 2`, a lower bound `c` for the Yamabe quotient of all
nonnegative smooth compactly supported functions with positive critical mass satisfies
`c ≤ Y(Sⁿ)`. -/
theorem le_sphereYamabeConstant_of_forall_le_yamabeQuotient [I.Boundaryless] [Nonempty M]
    (hn : 2 < finrank ℝ E) {c : ℝ}
    (hc : ∀ u : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ u → HasCompactSupport u → (∀ x, 0 ≤ u x) →
      0 < ∫ x, |u x| ^ criticalExponent (finrank ℝ E) ∂riemannianVolume I M →
        c ≤ yamabeQuotient I u) :
    c ≤ sphereYamabeConstant (finrank ℝ E) :=
  le_of_forall_pos_lt_add fun ε hε ↦ by
    obtain ⟨u, hu, huc, -, hu0, hpos, hQ⟩ :=
      exists_contMDiff_hasCompactSupport_yamabeQuotient_lt (I := I) hn isOpen_univ
        (univ_nonempty (α := M)) hε
    exact (hc u hu huc hu0 hpos).trans_lt hQ

end TauCeti.Yamabe
