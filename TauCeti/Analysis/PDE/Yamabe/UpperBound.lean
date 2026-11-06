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
  set n := finrank ℝ E
  set P := criticalExponent n
  set a := conformalCoefficient n
  set φ := extChartAt I p
  set e := trivializationAt E (TangentSpace I) p
  set μ := (finBasis ℝ E).addHaar
  set ρ := chartVolumeDensity (I := I) p
  set Scal := (CovariantDerivative.leviCivitaConnection I M).scalarCurvature
  have hp : p ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  have hρp : 0 < ρ p := chartVolumeDensity_pos p hp
  have hP : 0 < P := criticalExponent_pos hn
  have ha : 0 < a := conformalCoefficient_pos hn
  /- Step 1: coordinates `L : E ≃ F` which are orthonormal for the metric at `p`, in which the
  coordinate measure is the Euclidean volume divided by `ρ p`. -/
  let F := EuclideanSpace ℝ (Fin n)
  have hF : finrank ℝ F = n := finrank_euclideanSpace_fin
  let O : TangentSpace I p ≃ₗᵢ[ℝ] F := (stdOrthonormalBasis ℝ (TangentSpace I p)).repr
  let L : E ≃L[ℝ] F := (e.continuousLinearEquivAt ℝ p hp).symm.trans O.toContinuousLinearEquiv
  have hLapp (w : E) : L w = O (e.symmL ℝ p w) := by
    simp [L, e.symm_continuousLinearEquivAt_eq hp]
  have hLO (ξ : TangentSpace I p) : L (e.continuousLinearMapAt ℝ p ξ) = O ξ := by
    rw [hLapp, e.symmL_continuousLinearMapAt hp]
  have hmap : Measure.map L μ = (ρ p)⁻¹.toNNReal • volume :=
    map_addHaar_eq_chartVolumeDensity_inv_smul_volume p L fun v w ↦ by
      rw [hLapp, hLapp, O.inner_map_map]
  /- Step 2: a Euclidean test function `v` supported in the unit ball, with Sobolev quotient
  `A / D ^ (2 / P)` below `Y(Sⁿ) + ε / 2`, and a distortion `η` of the metric and the density
  for which the resulting bound `G η` on the Yamabe quotient is below `Y(Sⁿ) + ε`. -/
  obtain ⟨v, hv, hvc, hvsupp, hv0, hD, hq⟩ :=
    exists_contDiff_hasCompactSupport_sobolev_quotient_lt (E := F) (Ω := ball 0 1) (by rwa [hF])
      isOpen_ball (nonempty_ball.2 one_pos) (half_pos hε)
  rw [hF] at hD hq
  set A := a * ∫ z, ‖fderiv ℝ v z‖ ^ 2
  set B := ∫ z, v z ^ 2 with hB_def
  set D := ∫ z, |v z| ^ P with hD_def
  set S := |Scal p| + 1
  have hS : 0 ≤ S := by positivity
  have hB : 0 ≤ B := integral_nonneg fun _ ↦ sq_nonneg _
  have hA : 0 ≤ A := mul_nonneg ha.le (integral_nonneg fun _ ↦ sq_nonneg _)
  set G : ℝ → ℝ := fun η ↦
    ((1 + η) ^ 3 * A + S * (1 + η) * η ^ 2 * B) / ((1 - η) ^ (2 / P) * D ^ (2 / P))
  have hG : Tendsto G (𝓝 0) (𝓝 (A / D ^ (2 / P))) := by
    have hcont : ContinuousAt G 0 := by
      refine ContinuousAt.div (by fun_prop) (ContinuousAt.mul ?_ continuousAt_const) ?_
      · exact (continuousAt_const.sub continuousAt_id).rpow_const (Or.inl (by simp))
      · simp only [sub_zero, Real.one_rpow, one_mul]
        exact (Real.rpow_pos_of_pos hD _).ne'
    simpa [G] using hcont.tendsto
  obtain ⟨η, ⟨hη0, hη1⟩, hGη⟩ : ∃ η ∈ Ioo (0 : ℝ) 1, G η < sphereYamabeConstant n + ε :=
    (Filter.Eventually.and (Ioo_mem_nhdsGT one_pos)
      ((hG.mono_left nhdsWithin_le_nhds).eventually_lt_const (by linarith))).exists
  have hη1' : 0 < 1 - η := by linarith
  /- Step 3: a coordinate ball `B(φ p, R)` on which the metric and the density are `η`-close to
  their values at `p`, and a scale `t ≤ η` for which `y ↦ v (t⁻¹ • L (y - φ p))` is supported in
  the compact set `K ⊆ B(φ p, R)`. -/
  obtain ⟨R, hR, hballt, hball⟩ := exists_ball_forall_chart_close (I := I) p hη0
    (hU.mem_nhds hpU)
  set C := ‖(L.symm : F →L[ℝ] E)‖
  set t := min η (R / (C + 1))
  have ht0 : 0 < t := lt_min hη0 (div_pos hR (by positivity))
  have htη : t ≤ η := min_le_left _ _
  have htR : t * C < R := by
    have h1 : t ≤ R / (C + 1) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [norm_nonneg (L.symm : F →L[ℝ] E)]
  set Ψ : E → F := fun y ↦ t⁻¹ • L (y - φ p)
  have hΨ_eq (y : E) : y = φ p + L.symm (t • Ψ y) := by
    simp [Ψ, smul_smul, ht0.ne']
  have hΨd (y : E) : HasFDerivAt Ψ (t⁻¹ • (L : E →L[ℝ] F)) y := by
    have h := ((L : E →L[ℝ] F).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const (φ p))).const_smul
      t⁻¹
    rw [ContinuousLinearMap.comp_id] at h
    exact h
  set K := (fun z ↦ φ p + L.symm (t • z)) '' tsupport v
  have hK : IsCompact K := hvc.isCompact.image (by fun_prop)
  have hKR : K ⊆ ball (φ p) R := by
    rintro _ ⟨z, hz, rfl⟩
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 (hvsupp hz)
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    calc ‖L.symm (t • z)‖ ≤ C * ‖t • z‖ := (L.symm : F →L[ℝ] E).le_opNorm _
      _ = t * C * ‖z‖ := by rw [norm_smul, Real.norm_of_nonneg ht0.le]; ring
      _ ≤ t * C := mul_le_of_le_one_right (by positivity) hz1.le
      _ < R := htR
  have hΨK (y : E) (hy : Ψ y ∈ tsupport v) : y ∈ K := ⟨Ψ y, hy, (hΨ_eq y).symm⟩
  -- Step 4: the test function `u` on `M`, transplanted from `w = v ∘ Ψ`.
  set w : E → ℝ := fun y ↦ v (Ψ y)
  have hw : ContDiff ℝ ∞ w := hv.comp (by fun_prop)
  have hwK : tsupport w ⊆ K :=
    closure_minimal (fun y hy ↦ hΨK y (subset_tsupport _ hy)) hK.isClosed
  obtain ⟨u, hu, huc, htsupp, hu_symm⟩ := exists_contMDiff_comp_extChartAt_symm_eq (c := p) hw
    (HasCompactSupport.intro hK fun y hy ↦ image_eq_zero_of_notMem_tsupport fun h ↦
      hy (hwK h)) (hwK.trans (hKR.trans hballt))
  have hK'W (x : M) (hx : x ∈ φ.symm '' tsupport w) : x ∈ φ.source ∧ φ x ∈ ball (φ p) R := by
    obtain ⟨y, hy, rfl⟩ := hx
    have hyt := hballt (hKR (hwK hy))
    exact ⟨φ.map_target hyt, by rw [φ.right_inv hyt]; exact hKR (hwK hy)⟩
  have hu0 (x : M) : 0 ≤ u x := by
    by_cases hx : x ∈ tsupport u
    · obtain ⟨y, hy, rfl⟩ := htsupp hx
      rw [hu_symm y (hballt (hKR (hwK hy)))]
      exact hv0 _
    · rw [image_eq_zero_of_notMem_tsupport hx]
  have huU : tsupport u ⊆ U := fun x hx ↦ by
    obtain ⟨hxs, hxb⟩ := hK'W x (htsupp hx)
    have h := (hball _ hxb).1
    rwa [φ.left_inv hxs] at h
  have hgrad0 (x : M) (hx : x ∉ tsupport u) : mgradient I u x = 0 :=
    mgradient_eq_zero_iff.2 ((notMem_tsupport_iff_eventuallyEq.1 hx).mvfderiv_eq.trans
      mvfderiv_zero)
  -- The gradient of `u` at `φ.symm y` is at most `(1 + η) t⁻¹ |dv (Ψ y)|`.
  have hgrad (y : E) (hy : y ∈ ball (φ p) R) :
      ‖mgradient I u (φ.symm y)‖ ≤ (1 + η) * (t⁻¹ * ‖fderiv ℝ v (Ψ y)‖) := by
    have hyt := hballt hy
    have heq : u ∘ φ.symm =ᶠ[𝓝 y] w :=
      Filter.eventually_of_mem ((isOpen_extChartAt_target p).mem_nhds hyt) hu_symm
    have hd : DifferentiableAt ℝ (u ∘ φ.symm) y :=
      ((hw.differentiable (by simp)) y).congr_of_eventuallyEq heq
    refine ((hball y hy).2.2.2 u hd).trans (mul_le_mul_of_nonneg_left (le_of_eq ?_) (by linarith))
    have hfd : fderiv ℝ w y = fderiv ℝ v (Ψ y) ∘L (t⁻¹ • (L : E →L[ℝ] F)) :=
      (((hv.differentiable (by simp)) (Ψ y)).hasFDerivAt.comp y (hΨd y)).fderiv
    have hcomp : (fderiv ℝ w y ∘L e.continuousLinearMapAt ℝ p : TangentSpace I p →L[ℝ] ℝ) =
        (t⁻¹ • fderiv ℝ v (Ψ y)) ∘L (O : TangentSpace I p →L[ℝ] F) := by
      ext ξ
      simp [hfd, ← hLO]
    rw [heq.fderiv_eq, hcomp, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.2 ht0.le)]
  /- Step 5: integrals over `M` of functions supported in `tsupport u` are computed in the ball,
  and integrals over `E` of functions of `Ψ y` are integrals over `F`, scaled by `t ^ n / ρ p`. -/
  have hu1 : ContMDiff I 𝓘(ℝ) 1 u := hu.of_le (by simp)
  have hgradsq : Continuous fun x ↦ ‖mgradient I u x‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using continuous_inner_mgradient hu1 hu1
  have hsupp_tsupp {f : M → ℝ} (hf : ∀ x ∉ tsupport u, f x = 0) :
      Function.support f ⊆ φ.source ∩ φ ⁻¹' ball (φ p) R := fun x hx ↦
    hK'W x (htsupp (by_contra fun h ↦ hx (hf x h)))
  have hsupp_grad : Function.support (fun x ↦ ‖mgradient I u x‖ ^ 2) ⊆ tsupport u := fun x hx ↦
    by_contra fun h ↦ hx (by simp [hgrad0 x h])
  have hsupp_sq (g : M → ℝ) : Function.support (fun x ↦ g x * u x ^ 2) ⊆ tsupport u :=
    fun x hx ↦ by_contra fun h ↦ hx (by simp [image_eq_zero_of_notMem_tsupport h])
  have hint (k : F → ℝ) (hk : Continuous k) (hkz : ∀ z ∉ tsupport v, k z = 0) :
      Integrable (fun y ↦ k (Ψ y)) μ :=
    (hk.comp (by fun_prop)).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hK fun y hy ↦ hkz _ fun h ↦ hy (hΨK y h))
  have hsupp_ball (k : F → ℝ) (hkz : ∀ z ∉ tsupport v, k z = 0) :
      Function.support (fun y ↦ k (Ψ y)) ⊆ ball (φ p) R := fun y hy ↦
    hKR (hΨK y (by_contra fun h ↦ hy (hkz _ h)))
  have hcv (k : F → ℝ) : ∫ y, k (Ψ y) ∂μ = (ρ p)⁻¹ * (t ^ n * ∫ z, k z) := by
    have h := integral_map_equiv L.toHomeomorph.toMeasurableEquiv (μ := μ) fun z ↦ k (t⁻¹ • z)
    simp only [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph] at h
    calc ∫ y, k (Ψ y) ∂μ = ∫ z, k (t⁻¹ • z) ∂Measure.map L μ := by
          rw [integral_sub_right_eq_self (fun y ↦ k (t⁻¹ • L y)) (φ p), h]
      _ = (ρ p)⁻¹ * ∫ z, k (t⁻¹ • z) := by
          rw [hmap, integral_smul_nnreal_measure]
          simp [NNReal.smul_def, hρp.le]
      _ = (ρ p)⁻¹ * (t ^ n * ∫ z, k z) := by
          rw [Measure.integral_comp_inv_smul_of_nonneg _ _ ht0.le, hF, smul_eq_mul]
  have hdv0 (z : F) (hz : z ∉ tsupport v) : ‖fderiv ℝ v z‖ ^ 2 = 0 := by
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hz (tsupport_fderiv_subset ℝ h)), norm_zero,
      sq, zero_mul]
  have hv0' (z : F) (hz : z ∉ tsupport v) : v z = 0 := image_eq_zero_of_notMem_tsupport hz
  have htn : t ^ n = t ^ (n - 2) * t ^ 2 := by rw [← pow_add, Nat.sub_add_cancel hn.le]
  -- Step 6: the Dirichlet energy, the `L²` norm and the critical mass of `u`.
  have hIg : ∫ x, ‖mgradient I u x‖ ^ 2 ∂riemannianVolume I M ≤
      (1 + η) ^ 3 * t ^ (n - 2) * ∫ z, ‖fderiv ℝ v z‖ ^ 2 := by
    have h := integral_riemannianVolume_le_mul_integral_of_support_subset p isOpen_ball hballt
      (fun x ↦ sq_nonneg _) (hgradsq.integrable_of_hasCompactSupport (huc.mono' hsupp_grad))
      (hsupp_tsupp fun x hx ↦ by simp [hgrad0 x hx]) (fun y ↦ sq_nonneg _)
      (hint _ ((hv.continuous_fderiv (by simp)).norm.pow 2) hdv0)
      (c := (1 + η) ^ 3 * ρ p * (t⁻¹) ^ 2) (by positivity) fun y hy ↦ by
        calc ρ (φ.symm y) * ‖mgradient I u (φ.symm y)‖ ^ 2
            ≤ ((1 + η) * ρ p) * ((1 + η) * (t⁻¹ * ‖fderiv ℝ v (Ψ y)‖)) ^ 2 :=
              mul_le_mul (hball y hy).2.1.2 (pow_le_pow_left₀ (norm_nonneg _) (hgrad y hy) 2)
                (sq_nonneg _) (by positivity)
          _ = (1 + η) ^ 3 * ρ p * (t⁻¹) ^ 2 * ‖fderiv ℝ v (Ψ y)‖ ^ 2 := by ring
    refine h.trans (le_of_eq ?_)
    rw [hcv (fun z ↦ ‖fderiv ℝ v z‖ ^ 2), htn]
    field_simp
  have hI2 : ∫ x, u x ^ 2 ∂riemannianVolume I M ≤ (1 + η) * t ^ n * B := by
    have h := integral_riemannianVolume_le_mul_integral_of_support_subset p isOpen_ball hballt
      (fun x ↦ sq_nonneg (u x))
      ((hu.continuous.pow 2).integrable_of_hasCompactSupport (huc.mono' (by
        simpa using hsupp_sq 1)))
      (hsupp_tsupp fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx])
      (fun y ↦ sq_nonneg _)
      (hint (fun z ↦ v z ^ 2) (hv.continuous.pow 2) fun z hz ↦ by simp [hv0' z hz])
      (c := (1 + η) * ρ p) (by positivity) fun y hy ↦ by
        rw [hu_symm y (hballt hy)]
        exact mul_le_mul_of_nonneg_right (hball y hy).2.1.2 (sq_nonneg _)
    refine h.trans (le_of_eq ?_)
    rw [hcv (fun z ↦ v z ^ 2), hB_def]
    field_simp
  have hIP : (1 - η) * t ^ n * D ≤ ∫ x, |u x| ^ P ∂riemannianVolume I M := by
    have hPz (z : ℝ) (hz : z = 0) : |z| ^ P = 0 := by rw [hz, abs_zero, Real.zero_rpow hP.ne']
    have hcontP : Continuous fun r : ℝ ↦ |r| ^ P :=
      continuous_abs.rpow_const fun _ ↦ Or.inr hP.le
    have h := mul_integral_le_integral_riemannianVolume_of_support_subset p isOpen_ball hballt
      (fun x ↦ Real.rpow_nonneg (abs_nonneg (u x)) P)
      ((hcontP.comp hu.continuous).integrable_of_hasCompactSupport (huc.mono' fun x hx ↦
        by_contra fun h ↦ hx (hPz _ (image_eq_zero_of_notMem_tsupport h))))
      (hsupp_tsupp fun x hx ↦ hPz _ (image_eq_zero_of_notMem_tsupport hx))
      (fun y ↦ Real.rpow_nonneg (abs_nonneg _) P)
      (hint (fun z ↦ |v z| ^ P) (hcontP.comp hv.continuous) fun z hz ↦ hPz _ (hv0' z hz))
      (hsupp_ball _ fun z hz ↦ hPz _ (hv0' z hz))
      (c := (1 - η) * ρ p) (by positivity) fun y hy ↦ by
        rw [hu_symm y (hballt hy)]
        exact mul_le_mul_of_nonneg_right (hball y hy).2.1.1 (Real.rpow_nonneg (abs_nonneg _) P)
    refine le_of_eq_of_le ?_ h
    rw [hcv (fun z ↦ |v z| ^ P), hD_def]
    field_simp
  -- Step 7: the numerator, where the scalar curvature is at most `S` on the support of `u`.
  have hnum : ∫ x, (a * ‖mgradient I u x‖ ^ 2 + Scal x * u x ^ 2) ∂riemannianVolume I M ≤
      t ^ (n - 2) * ((1 + η) ^ 3 * A + S * (1 + η) * t ^ 2 * B) := by
    have hint₁ : Integrable (fun x ↦ a * ‖mgradient I u x‖ ^ 2) (riemannianVolume I M) :=
      (hgradsq.integrable_of_hasCompactSupport (huc.mono' hsupp_grad)).const_mul a
    have hint₂ (g : M → ℝ) (hg : Continuous g) :
        Integrable (fun x ↦ g x * u x ^ 2) (riemannianVolume I M) :=
      (hg.mul (hu.continuous.pow 2)).integrable_of_hasCompactSupport (huc.mono' (hsupp_sq g))
    have hScal : Continuous Scal :=
      (CovariantDerivative.leviCivitaConnection I M).contMDiff_scalarCurvature.continuous
    calc ∫ x, (a * ‖mgradient I u x‖ ^ 2 + Scal x * u x ^ 2) ∂riemannianVolume I M
        ≤ ∫ x, (a * ‖mgradient I u x‖ ^ 2 + S * u x ^ 2) ∂riemannianVolume I M := by
          refine integral_mono (hint₁.add (hint₂ Scal hScal)) (hint₁.add (hint₂ _ continuous_const))
            fun x ↦ add_le_add le_rfl ?_
          by_cases hx : x ∈ tsupport u
          · obtain ⟨hxs, hxb⟩ := hK'W x (htsupp hx)
            have hS' := (hball _ hxb).2.2.1
            rw [φ.left_inv hxs] at hS'
            exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans hS') (sq_nonneg _)
          · simp [image_eq_zero_of_notMem_tsupport hx]
      _ = a * ∫ x, ‖mgradient I u x‖ ^ 2 ∂riemannianVolume I M +
          S * ∫ x, u x ^ 2 ∂riemannianVolume I M := by
          rw [integral_add hint₁ (hint₂ _ continuous_const), integral_const_mul,
            integral_const_mul]
      _ ≤ a * ((1 + η) ^ 3 * t ^ (n - 2) * ∫ z, ‖fderiv ℝ v z‖ ^ 2) +
          S * ((1 + η) * t ^ n * B) := by gcongr
      _ = t ^ (n - 2) * ((1 + η) ^ 3 * A + S * (1 + η) * t ^ 2 * B) := by rw [htn]; ring
  -- Step 8: the denominator, using `(t ^ n) ^ (2 / P) = t ^ (n - 2)`.
  have hden : (1 - η) ^ (2 / P) * t ^ (n - 2) * D ^ (2 / P) ≤
      (∫ x, |u x| ^ P ∂riemannianVolume I M) ^ (2 / P) := by
    have htP : (t ^ n) ^ (2 / P) = t ^ (n - 2) := by
      have hexp : (n : ℝ) * (2 / P) = (n - 2 : ℕ) := by
        have : (n : ℝ) ≠ 0 := by positivity
        rw [two_div_criticalExponent]
        push_cast [hn.le]
        field_simp
      rw [← Real.rpow_natCast_mul ht0.le, hexp, Real.rpow_natCast]
    calc (1 - η) ^ (2 / P) * t ^ (n - 2) * D ^ (2 / P) = ((1 - η) * t ^ n * D) ^ (2 / P) := by
          rw [Real.mul_rpow (by positivity) hD.le, Real.mul_rpow hη1'.le (by positivity), htP]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hIP (by positivity)
  -- Step 9: the quotient is at most `G η`, using `t ≤ η`.
  refine ⟨u, hu, huc, huU, hu0, (by positivity : 0 < (1 - η) * t ^ n * D).trans_le hIP, ?_⟩
  rw [yamabeQuotient_def]
  calc _ ≤ t ^ (n - 2) * ((1 + η) ^ 3 * A + S * (1 + η) * t ^ 2 * B) /
        ((1 - η) ^ (2 / P) * t ^ (n - 2) * D ^ (2 / P)) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = ((1 + η) ^ 3 * A + S * (1 + η) * t ^ 2 * B) / ((1 - η) ^ (2 / P) * D ^ (2 / P)) := by
        have : t ^ (n - 2) ≠ 0 := pow_ne_zero _ ht0.ne'
        field_simp
    _ ≤ G η := by
        simp only [G]
        gcongr
    _ < _ := hGη

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
