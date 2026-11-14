/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.ApproximateTangent
public import TauCeti.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Measure.Haar.Lipschitz

/-!
# Tangential differentiation and the tangential Jacobian on rectifiable sets

Let `E` be a subset of a finite-dimensional real inner product space `V` and let `g : V → W` take
values in a real normed space `W`. On a countably `k`-rectifiable set `E` (which may contain a
dense `μHE[k]`-null dust set), a Lipschitz map need not be classically differentiable relative to
`E` at almost every point; the natural notion is **approximate tangential differentiability**
(Federer 3.2.16 and 3.2.19; Ambrosio–Fusco–Pallara Definition 2.88):

* `TauCeti.HasTangentialFDerivAt k E g L x`: `E` admits a unique approximate tangent `k`-plane `P`
  at `x`, the continuous linear map `L : V →L[ℝ] W` vanishes on `Pᗮ` (`L ∘L P.starProjection = L`),
  and for every `ε > 0` the superlevel set `{z ∈ E ∩ closedBall x r | ε * dist z x < ‖g z - g x -
  L (z - x)‖}` has `k`-dimensional density zero at `x`.
* `TauCeti.tangentialFDeriv k E g x : V →L[ℝ] W`: the canonical tangential derivative (and `0` when
  `g` is not tangentially differentiable along `E` at `x`). Its ambient type `V →L[ℝ] W` does not
  depend on `x`, avoiding dependent-type transport across points or `μHE[k]`-null modifications of
  `E`.
* `TauCeti.tangentialJacobian k E g x : ℝ`: when `W` is an inner product space, the `k`-dimensional
  geometric Jacobian `LinearMap.normDet` of `tangentialFDeriv k E g x` restricted to
  `approximateTangentPlane k E x` (and `0` where `g` is not tangentially differentiable).

Almost-everywhere tangential differentiability and measurability on countably `k`-rectifiable sets
are proved in `TauCeti.Geometry.MeasureTheory.Rectifiable.Rademacher`.

## Main results

* `TauCeti.HasTangentialFDerivAt.unique`: the tangential derivative `L` is unconditionally unique
  at every point `x`, for arbitrary sets `E` and functions `g`.
* Invariance of `HasTangentialFDerivAt`, `tangentialFDeriv`, and `tangentialJacobian` under
  `E₁ =ᵐ[μHE[k]] E₂`, `E₁ =ᶠ[𝓝 x] E₂`, `EqOn g₁ g₂ E` (at `x ∈ E`), and
  `g₁ =ᵐ[μHE[k].restrict E] g₂` (almost everywhere on `E`), together with linearity and
  compatibility with classical `HasFDerivWithinAt`.
* **Parametrization chain rule** (`HasFDerivWithinAt.hasTangentialFDerivAt_of_comp`,
  `HasFDerivWithinAt.tangentialFDeriv_comp_eq`, `HasFDerivWithinAt.tangentialJacobian_mul_normDet`):
  at a Lebesgue density-one regular point `u₀` of an inverse-Lipschitz patch `f '' s ⊆ E` where
  `E \ f '' s` has density zero, differentiability of `g ∘ f` within `s` implies tangential
  differentiability of `g` along `E` at `f u₀`, with `(tangentialFDeriv ... (f u₀)) ∘L Df(u₀) =
  D(g ∘ f)(u₀)` and `tangentialJacobian ... (f u₀) * Df(u₀).normDet = D(g ∘ f)(u₀).normDet`, as
  well as sharp operator-norm and Jacobian bounds `‖tangentialFDeriv‖ ≤ K` and
  `tangentialJacobian ≤ K ^ k` when `g` is `K`-Lipschitz on `E`.

## References

* H. Federer, *Geometric Measure Theory*, 3.2.16 and 3.2.19.
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Definition 2.88 and Theorem 2.90.
* F. Morgan, *Geometric Measure Theory: A Beginner's Guide*, §3.6.
-/

public section

open Filter Function Metric MeasureTheory Measure Module Set
open scoped ENNReal NNReal Topology symmDiff RealInnerProductSpace

namespace TauCeti

/-! ### Auxiliary linear-algebraic and measure-theoretic lemmas -/

/-- The geometric Jacobian `normDet` of a continuous linear map `T : U →L[ℝ] W` from a
finite-dimensional real inner product space `U` into a real inner product space `W` is bounded by
`‖T‖ ^ dim U`. -/
theorem normDet_le_opNorm_pow {U W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U] [NormedAddCommGroup W] [InnerProductSpace ℝ W] (T : U →L[ℝ] W) :
    T.toLinearMap.normDet ≤ ‖T‖ ^ finrank ℝ U := by
  let _ : MeasurableSpace U := borel U
  have : BorelSpace U := ⟨rfl⟩
  let _ : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  have hvol_pos : 0 < volume (ball (0 : U) 1) := measure_ball_pos volume 0 zero_lt_one
  have hvol_top : volume (ball (0 : U) 1) ≠ ∞ := measure_ball_lt_top.ne
  have h1 : ENNReal.ofReal T.toLinearMap.normDet * volume (ball (0 : U) 1) ≤
      ENNReal.ofReal (‖T‖ ^ finrank ℝ U) * volume (ball (0 : U) 1) := by
    rw [← T.toLinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume,
      ← InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
      ENNReal.ofReal_pow (norm_nonneg T), ← coe_nnNorm, ENNReal.ofReal_coe_nnreal]
    exact T.lipschitzWith.lipschitzOnWith.euclideanHausdorffMeasure_image_le (finrank ℝ U)
  have h2 := ENNReal.div_le_div_right h1 (volume (ball (0 : U) 1))
  rw [ENNReal.mul_div_cancel_right hvol_pos.ne' hvol_top,
    ENNReal.mul_div_cancel_right hvol_pos.ne' hvol_top] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg (norm_nonneg T) _)).mp h2

/-- At a Lebesgue density-one point `u₀` of `s ⊆ U`, small shifted balls in any unit direction `w`
meet `s` at arbitrarily small scales. -/
private lemma exists_mem_inter_shifted_closedBall_of_tendsto {U : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [MeasurableSpace U] [BorelSpace U] {s : Set U} {u₀ w : U} {η δ : ℝ}
    (hdens : Tendsto (fun r => volume (s ∩ closedBall u₀ r) / volume (closedBall (0 : U) r))
      (𝓝[>] 0) (𝓝 1))
    (hw : ‖w‖ = 1) (hη0 : 0 < η) (hη_half : η ≤ 1 / 2) (hδ : 0 < δ) :
    ∃ ρ ∈ Ioo 0 δ, (s ∩ closedBall (u₀ + (ρ / 2) • w) ((η / 4) * ρ)).Nonempty := by
  by_contra! hemp
  have : Nontrivial U := ⟨⟨w, 0, fun h => by simp [h] at hw⟩⟩
  set D : ℝ → Set U := fun ρ => closedBall (u₀ + (ρ / 2) • w) ((η / 4) * ρ)
  set α : ℝ≥0∞ := ENNReal.ofReal (η / 4) ^ finrank ℝ U
  have hα0 : 0 < α := ENNReal.pow_pos (ENNReal.ofReal_pos.mpr (by positivity)) _
  have hineq : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      volume (s ∩ closedBall u₀ ρ) / volume (closedBall (0 : U) ρ) + α ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with ρ hρ
    have hρ0 : 0 < ρ := hρ.1
    have hD_sub : D ρ ⊆ closedBall u₀ ρ := fun x hx => by
      rw [mem_closedBall] at hx ⊢
      calc dist x u₀ ≤ dist x (u₀ + (ρ / 2) • w) + dist (u₀ + (ρ / 2) • w) u₀ :=
            dist_triangle _ _ _
        _ ≤ (η / 4) * ρ + (ρ / 2) * 1 := by
            gcongr
            simp [dist_eq_norm, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ ρ / 2), hw]
        _ ≤ ρ := by nlinarith
    have hV0_pos : 0 < volume (closedBall (0 : U) ρ) := measure_closedBall_pos volume 0 hρ0
    have hV0_top : volume (closedBall (0 : U) ρ) ≠ ∞ := measure_closedBall_lt_top.ne
    have hcenter (x : U) (r : ℝ) : volume (closedBall x r) = volume (closedBall (0 : U) r) :=
      (volume_closedBall_eq_euclidean x r).trans (volume_closedBall_eq_euclidean 0 r).symm
    have hvolD : volume (D ρ) = α * volume (closedBall (0 : U) ρ) := by
      rw [hcenter, addHaar_closedBall_mul volume 0 (by positivity) hρ0.le,
        ENNReal.ofReal_pow (by positivity)]
    have hsub_diff : s ∩ closedBall u₀ ρ ⊆ closedBall u₀ ρ \ D ρ := fun x ⟨hxs, hxB⟩ =>
      ⟨hxB, fun hxD => notMem_empty x (hemp ρ hρ ▸ ⟨hxs, hxD⟩)⟩
    have hadd : volume (s ∩ closedBall u₀ ρ) + α * volume (closedBall (0 : U) ρ) ≤
        volume (closedBall (0 : U) ρ) := by
      calc volume (s ∩ closedBall u₀ ρ) + α * volume (closedBall (0 : U) ρ)
          ≤ volume (closedBall u₀ ρ \ D ρ) + volume (D ρ) := by
            rw [hvolD]; exact add_le_add (measure_mono (μ := volume) hsub_diff) le_rfl
        _ = volume (closedBall (0 : U) ρ) := by
            rw [← measure_union disjoint_sdiff_self_left measurableSet_closedBall,
              sdiff_union_of_subset hD_sub, hcenter]
    have hdiv := ENNReal.div_le_div_right hadd (volume (closedBall (0 : U) ρ))
    rwa [ENNReal.add_div, ENNReal.mul_div_cancel_right hV0_pos.ne' hV0_top,
      ENNReal.div_self hV0_pos.ne' hV0_top] at hdiv
  have h1α : 1 + α ≤ 1 :=
    le_of_tendsto_of_tendsto (hdens.add tendsto_const_nhds) tendsto_const_nhds hineq
  have hα_le : α ≤ 0 :=
    (ENNReal.add_le_add_iff_left ENNReal.one_ne_top).mp (by simpa only [add_zero] using h1α)
  exact not_le_of_gt hα0 hα_le

/-- Top-dimensional Hausdorff measure bound for a thin slab of half-width `ε * r` around the
hyperplane `(ℝ ∙ u₀)ᗮ` inside `closedBall x r`. -/
private lemma slab_measure_div_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {x u₀ : V} (hu₀ : ‖u₀‖ = 1) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    μHE[finrank ℝ V]
        {z ∈ closedBall x r | infDist (z - x) ((ℝ ∙ u₀)ᗮ : Set V) ≤ ε * r} /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ V))) r) ≤
        ENNReal.ofReal ((2 : ℝ) ^ finrank ℝ V * ε) := by
  set H : Submodule ℝ V := (ℝ ∙ u₀)ᗮ
  have h1 : finrank ℝ (ℝ ∙ u₀) = 1 := finrank_span_singleton (by intro h; simp [h] at hu₀)
  have hH_add : 1 + finrank ℝ H = finrank ℝ V := by
    have hsum := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ u₀)
    rwa [h1] at hsum
  have hdim_VH : finrank ℝ (WithLp 2 (ℝ × H)) = finrank ℝ V := by
    rw [(WithLp.linearEquiv 2 ℝ (ℝ × H)).finrank_eq, Module.finrank_prod, Module.finrank_self,
      hH_add]
  -- Cover the `ε * r`-slab inside `closedBall x r` by the affine image of a `WithLp 2 (ℝ × H)` ball
  -- under `F = (2 * ε) • u₀ ⊕ 2 • id_H`, whose Jacobian is at most `2 ^ dim V * ε`.
  let A : ℝ →ₗ[ℝ] V := (2 * ε) • LinearMap.toSpanSingleton ℝ V u₀
  let B : H →ₗ[ℝ] V := (2 : ℝ) • H.subtype
  let F : WithLp 2 (ℝ × H) →ₗ[ℝ] V :=
    A.coprod B ∘ₗ (WithLp.linearEquiv 2 ℝ (ℝ × H)).toLinearMap
  have horth : ∀ t y, ⟪A t, B y⟫ = 0 := fun t y => by
    simp only [A, B, LinearMap.smul_apply, LinearMap.toSpanSingleton_apply,
      Submodule.subtype_apply, smul_smul, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real, Submodule.mem_orthogonal_singleton_iff_inner_right.mp y.2, mul_zero]
  have hF_le : F.normDet ≤ (2 : ℝ) ^ finrank ℝ V * ε := by
    rw [LinearMap.normDet_coprod_of_orthogonal A B horth, LinearMap.normDet_smul,
      LinearMap.normDet_eq_norm_apply_one, LinearMap.toSpanSingleton_apply, one_smul, hu₀,
      mul_one, Module.finrank_self, pow_one, Real.norm_of_nonneg (by positivity),
      LinearMap.normDet_smul, LinearMap.normDet_subtype, mul_one,
      Real.norm_of_nonneg zero_le_two, ← hH_add, add_comm 1, pow_succ]
    linarith
  have hinc : {z ∈ closedBall x r | infDist (z - x) (H : Set V) ≤ ε * r} ⊆
      (IsometryEquiv.vaddConst x) '' (F '' closedBall (0 : WithLp 2 (ℝ × H)) r) := by
    rintro z ⟨hzB, hzH⟩
    refine ⟨z - x, ?_, by simp [IsometryEquiv.vaddConst]⟩
    have hw_norm : ‖z - x‖ ≤ r := by simpa [dist_eq_norm] using mem_closedBall.mp hzB
    have hproj_H : H.starProjection (z - x) = (z - x) - ⟪u₀, z - x⟫ • u₀ := by
      rw [Submodule.starProjection_orthogonal, _root_.sub_apply,
        ContinuousLinearMap.id_apply, Submodule.starProjection_unit_singleton ℝ hu₀]
    have hinner_le : |⟪u₀, z - x⟫| ≤ ε * r := by
      have hdist := H.dist_starProjection_eq_infDist (z - x)
      rw [dist_eq_norm, hproj_H, sub_sub_cancel, norm_smul, hu₀, mul_one,
        Real.norm_eq_abs] at hdist
      exact hdist.le.trans hzH
    let p : WithLp 2 (ℝ × H) := WithLp.toLp 2 ((2 * ε)⁻¹ * ⟪u₀, z - x⟫,
      ⟨(2 : ℝ)⁻¹ • H.starProjection (z - x),
        H.smul_mem _ (Submodule.starProjection_apply_mem H _)⟩)
    refine ⟨p, ?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      have hp_sq : ‖p‖ ^ 2 ≤ r ^ 2 := by
        rw [WithLp.prod_norm_sq_eq_of_L2]
        have hp1 : ‖p.fst‖ ≤ r / 2 := by
          have hpos : (0 : ℝ) < 2 * ε := by positivity
          have heq : p.fst = (2 * ε)⁻¹ * ⟪u₀, z - x⟫ := rfl
          rw [heq, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hpos]
          exact (mul_le_mul_of_nonneg_left hinner_le (by positivity)).trans_eq (by field_simp)
        have hp2 : ‖p.snd‖ ≤ r / 2 := by
          have heq : ‖p.snd‖ = ‖(2 : ℝ)⁻¹ • H.starProjection (z - x)‖ := rfl
          rw [heq, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2⁻¹)]
          exact (mul_le_mul_of_nonneg_left
            ((H.norm_starProjection_apply_le (z - x)).trans hw_norm)
            (by positivity)).trans_eq (by ring)
        have hsq1 : ‖p.fst‖ ^ 2 ≤ (r / 2) ^ 2 := sq_le_sq' (by linarith [norm_nonneg p.fst]) hp1
        have hsq2 : ‖p.snd‖ ^ 2 ≤ (r / 2) ^ 2 := sq_le_sq' (by linarith [norm_nonneg p.snd]) hp2
        nlinarith
      exact le_of_sq_le_sq hp_sq hr.le
    · have hFp : F p = (2 * ε * ((2 * ε)⁻¹ * ⟪u₀, z - x⟫)) • u₀ +
          ((2 : ℝ) * 2⁻¹) • H.starProjection (z - x) := by
        simp [F, A, B, p, smul_smul]
      have hc1 : 2 * ε * ((2 * ε)⁻¹ * ⟪u₀, z - x⟫) = ⟪u₀, z - x⟫ := by field_simp
      have hc2 : (2 : ℝ) * 2⁻¹ = 1 := by norm_num
      rw [hFp, hc1, hc2, one_smul, hproj_H]
      abel
  have hvol_pos : 0 < volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ V))) r) :=
    measure_closedBall_pos volume 0 hr
  have hvol_top : volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ V))) r) ≠ ∞ :=
    measure_closedBall_lt_top.ne
  have hvol_eq : volume (closedBall (0 : WithLp 2 (ℝ × H)) r) =
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ V))) r) := by
    let e : WithLp 2 (ℝ × H) ≃ₗᵢ[ℝ] V :=
      (stdOrthonormalBasis ℝ (WithLp 2 (ℝ × H))).equiv (stdOrthonormalBasis ℝ V)
        (finCongr hdim_VH)
    have himg : (e : WithLp 2 (ℝ × H) → V) '' closedBall 0 r = closedBall 0 r := by simp
    rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
      ← e.isometry.euclideanHausdorffMeasure_image, himg, hdim_VH,
      InnerProductSpace.euclideanHausdorffMeasure_eq_volume, volume_closedBall_eq_euclidean]
  have hmeas_le : μHE[finrank ℝ V] {z ∈ closedBall x r | infDist (z - x) (H : Set V) ≤ ε * r} ≤
      ENNReal.ofReal ((2 : ℝ) ^ finrank ℝ V * ε) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ V))) r) := by
    calc μHE[finrank ℝ V] {z ∈ closedBall x r | infDist (z - x) (H : Set V) ≤ ε * r}
        ≤ μHE[finrank ℝ V]
            ((IsometryEquiv.vaddConst x) '' (F '' closedBall (0 : WithLp 2 (ℝ × H)) r)) :=
          measure_mono hinc
      _ = ENNReal.ofReal F.normDet * volume (closedBall (0 : WithLp 2 (ℝ × H)) r) := by
          rw [(IsometryEquiv.vaddConst x).isometry.euclideanHausdorffMeasure_image, ← hdim_VH,
            F.euclideanHausdorffMeasure_image_eq_normDet_mul_volume]
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ finrank ℝ V * ε) *
          volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ V))) r) := by
          rw [hvol_eq]; gcongr
  exact (ENNReal.div_le_div_right hmeas_le _).trans_eq
    (ENNReal.mul_div_cancel_right hvol_pos.ne' hvol_top)

/-- In a finite-dimensional inner product space `V`, no proper submodule `K₀ < ⊤` can satisfy the
top-dimensional cone-density-zero condition at a point `x` of positive upper Lebesgue density. -/
private lemma not_tendsto_outside_cone_top_of_lt_top {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {E : Set V} {x : V} {K₀ : Submodule ℝ V} (hK₀ : K₀ < ⊤)
    (hpos : 0 < limsup (fun r =>
      μHE[finrank ℝ V] (E ∩ closedBall x r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ V))) r)) (𝓝[>] 0))
    (hcone : ∀ ε > (0 : ℝ), Tendsto (fun r =>
      μHE[finrank ℝ V] {z ∈ E ∩ closedBall x r |
        ε * dist z x < infDist (z - x) (K₀ : Set V)} /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ V))) r)) (𝓝[>] 0) (𝓝 0)) :
    False := by
  have hK₀_orth_ne : K₀ᗮ ≠ ⊥ :=
    fun hbot => hK₀.ne (by simpa using congrArg Submodule.orthogonal hbot)
  obtain ⟨v₀, hv₀K, hv₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK₀_orth_ne
  let u₀ : V := ‖v₀‖⁻¹ • v₀
  have hu₀ : ‖u₀‖ = 1 := norm_smul_inv_norm hv₀0
  have hu₀K : u₀ ∈ K₀ᗮ := K₀ᗮ.smul_mem _ hv₀K
  have hK₀_le_H : K₀ ≤ (ℝ ∙ u₀)ᗮ := fun k hk =>
    Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
      (Submodule.inner_right_of_mem_orthogonal hk hu₀K)
  have hlimsup_le (ε : ℝ) (hε : 0 < ε) :
      limsup (fun r => μHE[finrank ℝ V] (E ∩ closedBall x r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ V))) r)) (𝓝[>] 0) ≤
        ENNReal.ofReal ((2 : ℝ) ^ finrank ℝ V * ε) := by
    calc limsup (fun r => μHE[finrank ℝ V] (E ∩ closedBall x r) /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ V))) r)) (𝓝[>] 0)
        ≤ limsup (fun r =>
            μHE[finrank ℝ V] {z ∈ closedBall x r |
              infDist (z - x) ((ℝ ∙ u₀)ᗮ : Set V) ≤ ε * r} /
              volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ V))) r) +
            μHE[finrank ℝ V] {z ∈ E ∩ closedBall x r |
              ε * dist z x < infDist (z - x) (K₀ : Set V)} /
              volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ V))) r)) (𝓝[>] 0) := by
          refine limsup_le_limsup (Eventually.of_forall fun r => ?_)
          rw [← ENNReal.add_div]
          have hsub_u : E ∩ closedBall x r ⊆
              {z ∈ closedBall x r | infDist (z - x) ((ℝ ∙ u₀)ᗮ : Set V) ≤ ε * r} ∪
              {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (K₀ : Set V)} := by
            rintro z ⟨hzE, hzr⟩
            by_cases hz : ε * dist z x < infDist (z - x) (K₀ : Set V)
            · exact Or.inr ⟨⟨hzE, hzr⟩, hz⟩
            · refine Or.inl ⟨hzr, ((infDist_le_infDist_of_subset
                (SetLike.coe_subset_coe.mpr hK₀_le_H) ⟨0, K₀.zero_mem⟩).trans
                (not_lt.mp hz)).trans ?_⟩
              exact mul_le_mul_of_nonneg_left (mem_closedBall.mp hzr) hε.le
          exact ENNReal.div_le_div_right ((measure_mono hsub_u).trans (measure_union_le _ _)) _
      _ = limsup (fun r =>
            μHE[finrank ℝ V] {z ∈ closedBall x r |
              infDist (z - x) ((ℝ ∙ u₀)ᗮ : Set V) ≤ ε * r} /
              volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ V))) r)) (𝓝[>] 0) :=
          ENNReal.limsup_add_of_right_tendsto_zero (hcone ε hε) _
      _ ≤ limsup (fun _ : ℝ => ENNReal.ofReal ((2 : ℝ) ^ finrank ℝ V * ε)) (𝓝[>] 0) :=
          limsup_le_limsup (eventually_mem_nhdsWithin.mono fun r hr =>
            slab_measure_div_le hu₀ hε hr)
      _ = ENNReal.ofReal ((2 : ℝ) ^ finrank ℝ V * ε) := limsup_const _
  have htend : Tendsto (fun ε : ℝ => ENNReal.ofReal ((2 : ℝ) ^ finrank ℝ V * ε))
      (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun ε : ℝ => ENNReal.ofReal ((2 : ℝ) ^ finrank ℝ V * ε) :=
      ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact not_le_of_gt hpos
    (ge_of_tendsto htend (eventually_mem_nhdsWithin.mono fun ε hε => hlimsup_le ε hε))

/-- When `K₀ < P` inside `V` with `finrank ℝ P = k < finrank ℝ V`, rotating a hyperplane of `P`
containing `K₀` into `Pᗮ` yields a `k`-plane `Q ≠ P` still containing `K₀`. -/
private lemma exists_orthogonal_hyperplane_rotation {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {P K₀ : Submodule ℝ V} {k : ℕ}
    (hK₀_lt : K₀ < P) (hP_dim : finrank ℝ P = k) (hcodim : k < finrank ℝ V) :
    ∃ Q : Submodule ℝ V, finrank ℝ Q = k ∧ K₀ ≤ Q ∧ Q ≠ P := by
  have hP_orth_ne : Pᗮ ≠ ⊥ := by
    intro hbot
    have hsum := Submodule.finrank_add_finrank_orthogonal P
    rw [hP_dim, hbot, finrank_bot, add_zero] at hsum
    exact hcodim.ne hsum
  obtain ⟨n, hnP, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP_orth_ne
  let M : Submodule ℝ V := P ⊓ K₀ᗮ
  have hM_ne : M ≠ ⊥ := by
    intro hbot
    apply hK₀_lt.ne
    refine le_antisymm hK₀_lt.le fun p hp => ?_
    have hm0 : p - K₀.starProjection p = 0 :=
      (Submodule.mem_bot ℝ).mp (hbot ▸ ⟨P.sub_mem hp (hK₀_lt.le
        (Submodule.starProjection_apply_mem K₀ p)),
        Submodule.sub_starProjection_mem_orthogonal p⟩)
    rw [sub_eq_zero.mp hm0]
    exact Submodule.starProjection_apply_mem K₀ p
  obtain ⟨u₀, ⟨hu₀P, hu₀K⟩, hu₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM_ne
  let H : Submodule ℝ V := P ⊓ (ℝ ∙ u₀)ᗮ
  have hK₀_le_H : K₀ ≤ H := le_inf hK₀_lt.le fun x hx =>
    Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
      (Submodule.inner_right_of_mem_orthogonal hx hu₀K)
  have hu₀_le_P : ℝ ∙ u₀ ≤ P := (Submodule.span_singleton_le_iff_mem u₀ P).mpr hu₀P
  have hH_sup_u : H ⊔ (ℝ ∙ u₀) = P := by
    refine le_antisymm (sup_le inf_le_left hu₀_le_P) fun p hp => ?_
    have hproj_mem := Submodule.starProjection_apply_mem (ℝ ∙ u₀) p
    have hdiff_H : p - (ℝ ∙ u₀).starProjection p ∈ H :=
      ⟨P.sub_mem hp (hu₀_le_P hproj_mem), Submodule.sub_starProjection_mem_orthogonal p⟩
    simpa using Submodule.add_mem_sup hdiff_H hproj_mem
  have hH_inf_u : H ⊓ (ℝ ∙ u₀) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_right (ℝ ∙ u₀) inf_le_right).trans
      (by rw [inf_comm, Submodule.inf_orthogonal_eq_bot]))
  let Q : Submodule ℝ V := H ⊔ (ℝ ∙ n)
  have hH_inf_n : H ⊓ (ℝ ∙ n) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf inf_le_left
      ((Submodule.span_singleton_le_iff_mem n Pᗮ).mpr hnP)).trans
      (Submodule.inf_orthogonal_eq_bot P).le)
  have hQ_dim : finrank ℝ Q = k := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq H (ℝ ∙ u₀)
    rw [hH_sup_u, hH_inf_u, finrank_bot, add_zero, finrank_span_singleton hu₀0, hP_dim] at h1
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq H (ℝ ∙ n)
    rw [hH_inf_n, finrank_bot, add_zero, finrank_span_singleton hn0] at h2
    exact h2.trans h1.symm
  refine ⟨Q, hQ_dim, hK₀_le_H.trans le_sup_left, fun hQP => hn0 ?_⟩
  have hnQ : n ∈ Q := Submodule.mem_sup_right (Submodule.mem_span_singleton_self n)
  have hn_bot : n ∈ P ⊓ Pᗮ := ⟨hQP ▸ hnQ, hnP⟩
  rw [Submodule.inf_orthogonal_eq_bot] at hn_bot
  exact (Submodule.mem_bot ℝ).mp hn_bot

/-! ### Approximate tangential derivative and tangential Jacobian -/

section Defs

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  {k : ℕ} {E E₁ E₂ : Set V} {g g₁ g₂ : V → W} {L L₁ L₂ : V →L[ℝ] W} {x : V}

/-- A function `g : V → W` has **approximate tangential derivative** `L : V →L[ℝ] W` along `E`
at `x` (in dimension `k`) if `E` admits a unique approximate tangent `k`-plane `P` at `x`, `L`
factors through the orthogonal projection onto `P`, and `E` has `k`-dimensional density zero
outside every superlevel error cone `{z ∈ E | ε * dist z x < ‖g z - g x - L (z - x)‖}` at `x`. -/
structure HasTangentialFDerivAt (k : ℕ) (E : Set V) (g : V → W) (L : V →L[ℝ] W) (x : V) :
    Prop where
  /-- `E` has a unique approximate tangent `k`-plane at `x`. -/
  existsUnique_plane : ∃! P : Submodule ℝ V, IsApproximateTangentPlane k E x P
  /-- `L` vanishes on the orthogonal complement of `approximateTangentPlane k E x`. -/
  comp_projection : L ∘L approximateTangentProjection k E x = L
  /-- Outside every relative-error cone, `E` has `k`-dimensional density zero at `x`. -/
  tendsto_outside_error : ∀ ε > (0 : ℝ), Tendsto (fun r =>
    μHE[k] {z ∈ E ∩ closedBall x r | ε * dist z x < ‖g z - g x - L (z - x)‖} /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)

namespace HasTangentialFDerivAt

/-- If `HasTangentialFDerivAt k E g L x` holds, then `approximateTangentPlane k E x` is an
approximate tangent `k`-plane to `E` at `x`. -/
theorem isApproximateTangentPlane (h : HasTangentialFDerivAt k E g L x) :
    IsApproximateTangentPlane k E x (approximateTangentPlane k E x) :=
  isApproximateTangentPlane_approximateTangentPlane h.existsUnique_plane.exists

/-- If `HasTangentialFDerivAt k E g L x` holds, then `approximateTangentPlane k E x` is the unique
approximate tangent `k`-plane to `E` at `x`. -/
theorem eq_approximateTangentPlane (h : HasTangentialFDerivAt k E g L x) {Q : Submodule ℝ V}
    (hQ : IsApproximateTangentPlane k E x Q) :
    Q = approximateTangentPlane k E x := by
  obtain ⟨P, hP, hPuniq⟩ := h.existsUnique_plane
  rw [hP.approximateTangentPlane_eq hPuniq]
  exact hPuniq Q hQ

/-- If `L₁ ≠ L₂` satisfy `HasTangentialFDerivAt`, `E` has `k`-density zero outside every cone
around the proper subspace `P ⊓ ker (L₁ - L₂)` of `P`. -/
private lemma tendsto_outside_cone_inf_ker_sub (h₁ : HasTangentialFDerivAt k E g L₁ x)
    (h₂ : HasTangentialFDerivAt k E g L₂ x) (hne : L₁ ≠ L₂) :
    (approximateTangentPlane k E x ⊓ LinearMap.ker (L₁ - L₂).toLinearMap) <
      approximateTangentPlane k E x ∧
    ∀ ε > (0 : ℝ), Tendsto (fun r =>
      μHE[k] {z ∈ E ∩ closedBall x r | ε * dist z x <
        infDist (z - x)
          ((approximateTangentPlane k E x ⊓ LinearMap.ker (L₁ - L₂).toLinearMap :
            Submodule ℝ V) : Set V)} /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) := by
  let P : Submodule ℝ V := approximateTangentPlane k E x
  have hP : IsApproximateTangentPlane k E x P := h₁.isApproximateTangentPlane
  set D : V →L[ℝ] W := L₁ - L₂
  have hD_proj : D ∘L P.starProjection = D := by
    rw [← approximateTangentProjection_eq, ContinuousLinearMap.sub_comp,
      h₁.comp_projection, h₂.comp_projection]
  have hD_ne : ∃ p ∈ P, D p ≠ 0 := by
    by_contra! hall
    have hD0 : D = 0 := by
      ext v
      have hv := congrArg (fun T : V →L[ℝ] W => T v) hD_proj
      simp only [ContinuousLinearMap.comp_apply] at hv
      rw [← hv]
      exact hall (P.starProjection v) (Submodule.starProjection_apply_mem P v)
    exact hne (sub_eq_zero.mp hD0)
  obtain ⟨p₀, hp₀P, hp₀D⟩ := hD_ne
  let K₀ : Submodule ℝ V := P ⊓ LinearMap.ker D.toLinearMap
  have hK₀_lt : K₀ < P := lt_of_le_of_ne inf_le_left fun h =>
    hp₀D (LinearMap.mem_ker.mp ((h.symm ▸ hp₀P : p₀ ∈ K₀).2))
  -- `D := L₁ - L₂` is injective on `M := P ⊓ K₀ᗮ`, giving `infDist w K₀ ≤ infDist w P + c * ‖D w‖`.
  let M : Submodule ℝ V := P ⊓ K₀ᗮ
  have hM_inj : LinearMap.ker (D.toLinearMap.comp M.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    rintro ⟨m, hmP, hmK⟩ ⟨n, hnP, hnK⟩ hmn
    ext
    have hsub : m - n ∈ K₀ ⊓ K₀ᗮ :=
      ⟨⟨P.sub_mem hmP hnP, LinearMap.mem_ker.mpr (by simpa [map_sub, sub_eq_zero] using hmn)⟩,
        K₀ᗮ.sub_mem hmK hnK⟩
    rw [Submodule.inf_orthogonal_eq_bot] at hsub
    exact sub_eq_zero.mp ((Submodule.mem_bot ℝ).mp hsub)
  obtain ⟨c, hc0, hc_anti⟩ := (D.toLinearMap.comp M.subtype).exists_antilipschitzWith hM_inj
  have hinf_K₀ (w : V) : infDist w (K₀ : Set V) ≤ infDist w (P : Set V) + c * ‖D w‖ := by
    let p : V := P.starProjection w
    let q : V := K₀.starProjection p
    have hqK : q ∈ K₀ := Submodule.starProjection_apply_mem K₀ p
    have hmM : p - q ∈ M :=
      ⟨P.sub_mem (Submodule.starProjection_apply_mem P w) (hK₀_lt.le hqK),
        Submodule.sub_starProjection_mem_orthogonal p⟩
    have hDq : D q = 0 := hqK.2
    have hDw : D (p - q) = D w := by
      rw [map_sub, hDq, sub_zero, ← ContinuousLinearMap.comp_apply, hD_proj]
    have hnorm_m : ‖p - q‖ ≤ c * ‖D w‖ := by
      simpa [Subtype.dist_eq, hDw] using hc_anti.le_mul_dist ⟨p - q, hmM⟩ 0
    calc infDist w (K₀ : Set V) ≤ dist w q := infDist_le_dist_of_mem hqK
      _ ≤ dist w p + dist p q := dist_triangle w p q
      _ = infDist w (P : Set V) + ‖p - q‖ := by
          rw [P.dist_starProjection_eq_infDist w, dist_eq_norm]
      _ ≤ infDist w (P : Set V) + c * ‖D w‖ := by gcongr
  refine ⟨hK₀_lt, fun ε hε => ?_⟩
  have hsum := ((hP.tendsto_outside_cone (ε / 2) (by positivity)).add
    (h₁.tendsto_outside_error (ε / (4 * c)) (by positivity))).add
    (h₂.tendsto_outside_error (ε / (4 * c)) (by positivity))
  simp only [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun r => ?_)
  rw [← ENNReal.add_div, ← ENNReal.add_div]
  have hsub_u : {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (K₀ : Set V)} ⊆
      ({z ∈ E ∩ closedBall x r | (ε / 2) * dist z x < infDist (z - x) (P : Set V)} ∪
        {z ∈ E ∩ closedBall x r | (ε / (4 * c)) * dist z x < ‖g z - g x - L₁ (z - x)‖}) ∪
      {z ∈ E ∩ closedBall x r | (ε / (4 * c)) * dist z x < ‖g z - g x - L₂ (z - x)‖} := by
    rintro z ⟨hzB, hzK⟩
    by_cases hP_out : (ε / 2) * dist z x < infDist (z - x) (P : Set V)
    · exact Or.inl (Or.inl ⟨hzB, hP_out⟩)
    by_cases h1_out : (ε / (4 * c)) * dist z x < ‖g z - g x - L₁ (z - x)‖
    · exact Or.inl (Or.inr ⟨hzB, h1_out⟩)
    refine Or.inr ⟨hzB, ?_⟩
    have hDeq : D (z - x) = (g z - g x - L₂ (z - x)) - (g z - g x - L₁ (z - x)) := by simp [D]
    have hD_le : ‖D (z - x)‖ ≤ ‖g z - g x - L₁ (z - x)‖ + ‖g z - g x - L₂ (z - x)‖ := by
      rw [hDeq]; exact (norm_sub_le _ _).trans_eq (add_comm _ _)
    have hK_le := (hinf_K₀ (z - x)).trans
      (add_le_add_right (mul_le_mul_of_nonneg_left hD_le c.coe_nonneg) _)
    by_contra! h2_le
    have hprod : (c : ℝ) * ((ε / (4 * c)) * dist z x) = (ε / 4) * dist z x := by field_simp
    have hc1 := (mul_le_mul_of_nonneg_left (not_lt.mp h1_out) c.coe_nonneg).trans_eq hprod
    have hc2 := (mul_le_mul_of_nonneg_left h2_le c.coe_nonneg).trans_eq hprod
    linarith [not_lt.mp hP_out]
  exact ENNReal.div_le_div_right ((measure_mono hsub_u).trans
    ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))) _

/-- **Unconditional uniqueness of the approximate tangential derivative.** At any point `x`, a
function `g : V → W` has at most one approximate tangential derivative along `E`. -/
theorem unique (h₁ : HasTangentialFDerivAt k E g L₁ x)
    (h₂ : HasTangentialFDerivAt k E g L₂ x) : L₁ = L₂ := by
  by_contra hne
  have hP : IsApproximateTangentPlane k E x (approximateTangentPlane k E x) :=
    h₁.isApproximateTangentPlane
  obtain ⟨hK₀_lt, hK₀_cone⟩ := h₁.tendsto_outside_cone_inf_ker_sub h₂ hne
  by_cases hcodim : k < finrank ℝ V
  · obtain ⟨Q, hQ_dim, hK₀_le_Q, hQP⟩ :=
      exists_orthogonal_hyperplane_rotation hK₀_lt hP.finrank_eq hcodim
    have hQ_cone : ∀ ε > (0 : ℝ), Tendsto (fun r =>
        μHE[k] {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (Q : Set V)} /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) := by
      intro ε hε
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hK₀_cone ε hε)
        (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun r => ?_)
      have hsub_Q : {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (Q : Set V)} ⊆
          {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x)
            ((approximateTangentPlane k E x ⊓ LinearMap.ker (L₁ - L₂).toLinearMap :
              Submodule ℝ V) : Set V)} := by
        rintro z ⟨hzB, hzQ⟩
        exact ⟨hzB, hzQ.trans_le (infDist_le_infDist_of_subset
          (SetLike.coe_subset_coe.mpr hK₀_le_Q) ⟨0, Submodule.zero_mem _⟩)⟩
      exact ENNReal.div_le_div_right (measure_mono hsub_Q) _
    exact hQP (h₁.eq_approximateTangentPlane ⟨hQ_dim, hP.limsup_pos, hQ_cone⟩)
  · have hk_eq : k = finrank ℝ V :=
      le_antisymm (hP.finrank_eq ▸ Submodule.finrank_le _) (not_lt.mp hcodim)
    subst hk_eq
    have hP_top : approximateTangentPlane (finrank ℝ V) E x = ⊤ :=
      Submodule.eq_top_of_finrank_eq hP.finrank_eq
    exact not_tendsto_outside_cone_top_of_lt_top (hP_top ▸ hK₀_lt) hP.limsup_pos hK₀_cone

/-- Modifying `E` by a `μHE[k]`-null set preserves `HasTangentialFDerivAt` at every point `x`. -/
theorem congr_ae_set (h : E₁ =ᵐ[μHE[k]] E₂) :
    HasTangentialFDerivAt k E₁ g L x ↔ HasTangentialFDerivAt k E₂ g L x := by
  have hnull : μHE[k] (E₁ ∆ E₂) = 0 := measure_symmDiff_eq_zero_iff.mpr h
  have herr_eq (ε r : ℝ) :
      μHE[k] {z ∈ E₁ ∩ closedBall x r | ε * dist z x < ‖g z - g x - L (z - x)‖} =
        μHE[k] {z ∈ E₂ ∩ closedBall x r | ε * dist z x < ‖g z - g x - L (z - x)‖} := by
    apply measure_congr
    rw [← measure_symmDiff_eq_zero_iff]
    exact measure_mono_null (fun z hz => by
      simp only [mem_symmDiff, mem_ofPred_eq, mem_inter_iff] at hz ⊢; tauto) hnull
  have hex_iff : (∃! P, IsApproximateTangentPlane k E₁ x P) ↔
      ∃! P, IsApproximateTangentPlane k E₂ x P :=
    existsUnique_congr fun _ => IsApproximateTangentPlane.congr_ae h
  constructor <;> rintro ⟨hu, hp, he⟩ <;> refine ⟨?_, ?_, fun ε hε => ?_⟩
  · exact hex_iff.mp hu
  · rwa [← approximateTangentProjection_congr_ae h]
  · simpa only [herr_eq] using he ε hε
  · exact hex_iff.mpr hu
  · rwa [approximateTangentProjection_congr_ae h]
  · simpa only [← herr_eq] using he ε hε

/-- `HasTangentialFDerivAt` depends only on the germ of `E` at `x`. -/
theorem congr_nhds_set (h : E₁ =ᶠ[𝓝 x] E₂) :
    HasTangentialFDerivAt k E₁ g L x ↔ HasTangentialFDerivAt k E₂ g L x := by
  obtain ⟨δ, hδ, hδeq⟩ := Metric.eventually_nhds_iff.mp h
  have hinter (r : ℝ) (hr : r < δ) : E₁ ∩ closedBall x r = E₂ ∩ closedBall x r := by
    ext z
    simp only [mem_inter_iff, mem_closedBall]
    exact and_congr_left fun hzr => by simpa using hδeq (hzr.trans_lt hr)
  have hex_iff : (∃! P, IsApproximateTangentPlane k E₁ x P) ↔
      ∃! P, IsApproximateTangentPlane k E₂ x P :=
    existsUnique_congr fun _ => IsApproximateTangentPlane.congr_nhds h
  constructor <;> rintro ⟨hu, hp, he⟩ <;> refine ⟨?_, ?_, fun ε hε => ?_⟩
  · exact hex_iff.mp hu
  · rwa [← approximateTangentProjection_congr_nhds h]
  · refine (he ε hε).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with r ⟨_, hr⟩
    simp only [hinter r hr]
  · exact hex_iff.mpr hu
  · rwa [approximateTangentProjection_congr_nhds h]
  · refine (he ε hε).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with r ⟨_, hr⟩
    simp only [hinter r hr]

/-- At `x ∈ E`, `HasTangentialFDerivAt k E g L x` depends only on the values of `g` on `E`. -/
theorem congr_of_eqOn (hg : EqOn g₁ g₂ E) (hx : x ∈ E) :
    HasTangentialFDerivAt k E g₁ L x ↔ HasTangentialFDerivAt k E g₂ L x := by
  have hset (ε r : ℝ) :
      {z ∈ E ∩ closedBall x r | ε * dist z x < ‖g₁ z - g₁ x - L (z - x)‖} =
        {z ∈ E ∩ closedBall x r | ε * dist z x < ‖g₂ z - g₂ x - L (z - x)‖} := by
    ext z
    simp only [mem_ofPred_eq, mem_inter_iff]
    exact and_congr_right fun ⟨hzE, _⟩ => by rw [hg hzE, hg hx]
  constructor <;> rintro ⟨hu, hp, he⟩ <;> refine ⟨hu, hp, fun ε hε => ?_⟩
  · simpa only [hset] using he ε hε
  · simpa only [← hset] using he ε hε

/-- Modifying `g` on a `μHE[k].restrict E`-null set preserves `HasTangentialFDerivAt` at every
`x ∈ E` where `g₁ x = g₂ x`. -/
theorem congr_ae_fun (hg : g₁ =ᵐ[μHE[k].restrict E] g₂) (hx_eq : g₁ x = g₂ x) :
    HasTangentialFDerivAt k E g₁ L x ↔ HasTangentialFDerivAt k E g₂ L x := by
  let N := {z ∈ E | g₁ z ≠ g₂ z}
  have hN : μHE[k] N = 0 := by
    have h0 : μHE[k].restrict E {z | g₁ z ≠ g₂ z} = 0 := ae_iff.mp hg
    have hle := (le_restrict_apply E {z | g₁ z ≠ g₂ z}).trans_eq h0
    exact measure_mono_null (t := {z | g₁ z ≠ g₂ z} ∩ E) (fun _ hz => ⟨hz.2, hz.1⟩)
      (nonpos_iff_eq_zero.mp hle)
  have herr_eq (ε r : ℝ) :
      μHE[k] {z ∈ E ∩ closedBall x r | ε * dist z x < ‖g₁ z - g₁ x - L (z - x)‖} =
        μHE[k] {z ∈ E ∩ closedBall x r | ε * dist z x < ‖g₂ z - g₂ x - L (z - x)‖} := by
    apply measure_congr
    rw [← measure_symmDiff_eq_zero_iff]
    refine measure_mono_null ?_ hN
    rintro z (⟨⟨⟨hzE, _⟩, h1⟩, h2⟩ | ⟨⟨⟨hzE, _⟩, h2⟩, h1⟩) <;>
      refine ⟨hzE, fun hzeq => ?_⟩
    · exact h2 ⟨⟨hzE, ‹_›⟩, by rwa [← hzeq, ← hx_eq]⟩
    · exact h1 ⟨⟨hzE, ‹_›⟩, by rwa [hzeq, hx_eq]⟩
  constructor <;> rintro ⟨hu, hp, he⟩ <;> refine ⟨hu, hp, fun ε hε => ?_⟩
  · simpa only [herr_eq] using he ε hε
  · simpa only [← herr_eq] using he ε hε

/-- Classical differentiability within `E` at a point admitting a unique approximate tangent
`k`-plane implies approximate tangential differentiability, with tangential derivative
`L ∘L approximateTangentProjection k E x`. -/
theorem of_hasFDerivWithinAt (hu : ∃! P : Submodule ℝ V, IsApproximateTangentPlane k E x P)
    (hg : HasFDerivWithinAt g L E x) :
    HasTangentialFDerivAt k E g (L ∘L approximateTangentProjection k E x) x := by
  let P : Submodule ℝ V := approximateTangentPlane k E x
  have hP : IsApproximateTangentPlane k E x P :=
    isApproximateTangentPlane_approximateTangentPlane hu.exists
  refine ⟨hu, ?_, fun ε hε => ?_⟩
  · ext v
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, approximateTangentProjection_eq]
    congr 1
    exact Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem P v)
  · obtain ⟨δ, hδ, hδb⟩ := eventually_nhds_iff_ball.mp
      (eventually_nhdsWithin_iff.mp (hg.isLittleO.bound (half_pos hε)))
    have hcone := hP.tendsto_outside_cone (ε / (2 * (‖L‖ + 1))) (by positivity)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcone
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with r ⟨_, hrδ⟩
    have hsub_c :
        {z ∈ E ∩ closedBall x r |
          ε * dist z x < ‖g z - g x - (L ∘L approximateTangentProjection k E x) (z - x)‖} ⊆
        {z ∈ E ∩ closedBall x r |
          (ε / (2 * (‖L‖ + 1))) * dist z x < infDist (z - x) (P : Set V)} := by
      rintro z ⟨⟨hzE, hzr⟩, hzerr⟩
      refine ⟨⟨hzE, hzr⟩, ?_⟩
      have herr := hδb z (mem_ball.mpr ((mem_closedBall.mp hzr).trans_lt hrδ)) hzE
      have hdecomp : g z - g x - (L ∘L approximateTangentProjection k E x) (z - x) =
          (g z - g x - L (z - x)) + L ((z - x) - P.starProjection (z - x)) := by
        simp only [ContinuousLinearMap.comp_apply, approximateTangentProjection_eq, map_sub]
        abel
      rw [hdecomp] at hzerr
      have hnorm := hzerr.trans_le ((norm_add_le _ _).trans (add_le_add herr (L.le_opNorm _)))
      rw [← dist_eq_norm (z - x), P.dist_starProjection_eq_infDist] at hnorm
      rw [dist_eq_norm] at hnorm ⊢
      by_contra! hle
      have hL_le : ‖L‖ * infDist (z - x) (P : Set V) ≤ (ε / 2) * ‖z - x‖ := by
        calc ‖L‖ * infDist (z - x) (P : Set V)
            ≤ (‖L‖ + 1) * ((ε / (2 * (‖L‖ + 1))) * ‖z - x‖) :=
              mul_le_mul (by linarith) hle infDist_nonneg (by positivity)
          _ = (ε / 2) * ‖z - x‖ := by field_simp
      linarith
    exact ENNReal.div_le_div_right (measure_mono hsub_c) _

/-- Sum rule for approximate tangential derivatives. -/
theorem add (h₁ : HasTangentialFDerivAt k E g₁ L₁ x)
    (h₂ : HasTangentialFDerivAt k E g₂ L₂ x) :
    HasTangentialFDerivAt k E (fun z => g₁ z + g₂ z) (L₁ + L₂) x := by
  refine ⟨h₁.existsUnique_plane, ?_, fun ε hε => ?_⟩
  · rw [ContinuousLinearMap.add_comp, h₁.comp_projection, h₂.comp_projection]
  · have hsum := (h₁.tendsto_outside_error (ε / 2) (half_pos hε)).add
      (h₂.tendsto_outside_error (ε / 2) (half_pos hε))
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun r => ?_)
    rw [← ENNReal.add_div]
    have hsub_u :
        {z ∈ E ∩ closedBall x r |
          ε * dist z x < ‖(g₁ z + g₂ z) - (g₁ x + g₂ x) - (L₁ + L₂) (z - x)‖} ⊆
        {z ∈ E ∩ closedBall x r | (ε / 2) * dist z x < ‖g₁ z - g₁ x - L₁ (z - x)‖} ∪
        {z ∈ E ∩ closedBall x r | (ε / 2) * dist z x < ‖g₂ z - g₂ x - L₂ (z - x)‖} := by
      rintro z ⟨hzB, hz⟩
      by_cases h1 : (ε / 2) * dist z x < ‖g₁ z - g₁ x - L₁ (z - x)‖
      · exact Or.inl ⟨hzB, h1⟩
      refine Or.inr ⟨hzB, ?_⟩
      have hdecomp : (g₁ z + g₂ z) - (g₁ x + g₂ x) - (L₁ + L₂) (z - x) =
          (g₁ z - g₁ x - L₁ (z - x)) + (g₂ z - g₂ x - L₂ (z - x)) := by
        simp only [add_apply]; abel
      rw [hdecomp] at hz
      linarith [hz.trans_le (norm_add_le _ _), not_lt.mp h1]
    exact ENNReal.div_le_div_right ((measure_mono hsub_u).trans (measure_union_le _ _)) _

/-- Scalar multiplication rule for approximate tangential derivatives. -/
theorem const_smul (c : ℝ) (h : HasTangentialFDerivAt k E g L x) :
    HasTangentialFDerivAt k E (fun z => c • g z) (c • L) x := by
  refine ⟨h.existsUnique_plane, ?_, fun ε hε => ?_⟩
  · rw [ContinuousLinearMap.smul_comp, h.comp_projection]
  · by_cases hc : c = 0
    · subst hc
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun r => ?_)
      have hempty :
          {z ∈ E ∩ closedBall x r |
            ε * dist z x < ‖(0 : ℝ) • g z - (0 : ℝ) • g x - ((0 : ℝ) • L) (z - x)‖} = ∅ := by
        ext z
        simp only [zero_smul, sub_self, zero_apply, norm_zero, mem_ofPred_eq,
          mem_empty_iff_false, iff_false, not_and]
        intro _
        exact not_lt.mpr (mul_nonneg hε.le dist_nonneg)
      dsimp only
      rw [hempty, measure_empty, ENNReal.zero_div]
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (h.tendsto_outside_error (ε / |c|) (div_pos hε (abs_pos.mpr hc)))
        (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun r => ?_)
      have hsub_c :
          {z ∈ E ∩ closedBall x r |
            ε * dist z x < ‖c • g z - c • g x - (c • L) (z - x)‖} ⊆
          {z ∈ E ∩ closedBall x r | (ε / |c|) * dist z x < ‖g z - g x - L (z - x)‖} := by
        rintro z ⟨hzB, hz⟩
        refine ⟨hzB, ?_⟩
        have hdecomp : c • g z - c • g x - (c • L) (z - x) =
            c • (g z - g x - L (z - x)) := by simp [smul_sub]
        rw [hdecomp, norm_smul, Real.norm_eq_abs] at hz
        rwa [div_mul_eq_mul_div, div_lt_iff₀' (abs_pos.mpr hc)]
      exact ENNReal.div_le_div_right (measure_mono hsub_c) _

/-- Negation rule for approximate tangential derivatives. -/
theorem neg (h : HasTangentialFDerivAt k E g L x) :
    HasTangentialFDerivAt k E (fun z => -g z) (-L) x := by
  simpa using h.const_smul (-1)

/-- Subtraction rule for approximate tangential derivatives. -/
theorem sub (h₁ : HasTangentialFDerivAt k E g₁ L₁ x)
    (h₂ : HasTangentialFDerivAt k E g₂ L₂ x) :
    HasTangentialFDerivAt k E (fun z => g₁ z - g₂ z) (L₁ - L₂) x := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

end HasTangentialFDerivAt

open Classical in
/-- The **approximate tangential derivative** of `g : V → W` along `E` at `x` in dimension `k`:
the unique `L : V →L[ℝ] W` satisfying `HasTangentialFDerivAt k E g L x` when one exists, and `0`
otherwise. -/
noncomputable def tangentialFDeriv (k : ℕ) (E : Set V) (g : V → W) (x : V) : V →L[ℝ] W :=
  if h : ∃ L : V →L[ℝ] W, HasTangentialFDerivAt k E g L x then h.choose else 0

/-- If `HasTangentialFDerivAt k E g L x` holds, then `tangentialFDeriv k E g x = L`. -/
theorem HasTangentialFDerivAt.tangentialFDeriv_eq (h : HasTangentialFDerivAt k E g L x) :
    tangentialFDeriv k E g x = L := by
  have hex : ∃ L', HasTangentialFDerivAt k E g L' x := ⟨L, h⟩
  simp only [tangentialFDeriv, hex, ↓reduceDIte]
  exact hex.choose_spec.unique h

/-- When `g` is tangentially differentiable along `E` at `x`, `tangentialFDeriv k E g x` satisfies
`HasTangentialFDerivAt`. -/
theorem hasTangentialFDerivAt_tangentialFDeriv
    (h : ∃ L : V →L[ℝ] W, HasTangentialFDerivAt k E g L x) :
    HasTangentialFDerivAt k E g (tangentialFDeriv k E g x) x := by
  simp only [tangentialFDeriv, h, ↓reduceDIte]
  exact h.choose_spec

/-- `tangentialFDeriv k E g x` always vanishes on `(approximateTangentPlane k E x)ᗮ`. -/
@[simp]
theorem tangentialFDeriv_comp_approximateTangentProjection (k : ℕ) (E : Set V) (g : V → W)
    (x : V) :
    tangentialFDeriv k E g x ∘L approximateTangentProjection k E x =
      tangentialFDeriv k E g x := by
  by_cases h : ∃ L : V →L[ℝ] W, HasTangentialFDerivAt k E g L x
  · exact (hasTangentialFDerivAt_tangentialFDeriv h).comp_projection
  · simp [tangentialFDeriv, h]

/-- In dimension zero, `tangentialFDeriv 0 E g x` is always `0`. -/
@[simp]
theorem tangentialFDeriv_zero (E : Set V) (g : V → W) (x : V) :
    tangentialFDeriv 0 E g x = 0 := by
  rw [← tangentialFDeriv_comp_approximateTangentProjection 0 E g x,
    approximateTangentProjection_zero, ContinuousLinearMap.comp_zero]

/-- Modifying `E` by a `μHE[k]`-null set leaves `tangentialFDeriv k E g x` unchanged at every
point `x`. -/
theorem tangentialFDeriv_congr_ae_set (h : E₁ =ᵐ[μHE[k]] E₂) (g : V → W) (x : V) :
    tangentialFDeriv k E₁ g x = tangentialFDeriv k E₂ g x := by
  have hpred : (HasTangentialFDerivAt k E₁ g · x) = (HasTangentialFDerivAt k E₂ g · x) :=
    funext fun _ => propext (HasTangentialFDerivAt.congr_ae_set h)
  exact congrArg (fun p : (V →L[ℝ] W) → Prop =>
    by classical exact if h : ∃ L, p L then h.choose else 0) hpred

/-- `tangentialFDeriv k E g x` depends only on the germ of `E` at `x`. -/
theorem tangentialFDeriv_congr_nhds_set (h : E₁ =ᶠ[𝓝 x] E₂) (g : V → W) :
    tangentialFDeriv k E₁ g x = tangentialFDeriv k E₂ g x := by
  have hpred : (HasTangentialFDerivAt k E₁ g · x) = (HasTangentialFDerivAt k E₂ g · x) :=
    funext fun _ => propext (HasTangentialFDerivAt.congr_nhds_set h)
  exact congrArg (fun p : (V →L[ℝ] W) → Prop =>
    by classical exact if h : ∃ L, p L then h.choose else 0) hpred

/-- At `x ∈ E`, `tangentialFDeriv k E g x` depends only on the values of `g` on `E`. -/
theorem tangentialFDeriv_congr_of_eqOn (hg : EqOn g₁ g₂ E) (hx : x ∈ E) :
    tangentialFDeriv k E g₁ x = tangentialFDeriv k E g₂ x := by
  have hpred : (HasTangentialFDerivAt k E g₁ · x) = (HasTangentialFDerivAt k E g₂ · x) :=
    funext fun _ => propext (HasTangentialFDerivAt.congr_of_eqOn hg hx)
  exact congrArg (fun p : (V →L[ℝ] W) → Prop =>
    by classical exact if h : ∃ L, p L then h.choose else 0) hpred

/-- Modifying `g` on a `μHE[k].restrict E`-null set leaves `tangentialFDeriv k E g` unchanged
`μHE[k].restrict E`-almost everywhere. -/
theorem tangentialFDeriv_congr_ae_fun (hg : g₁ =ᵐ[μHE[k].restrict E] g₂) :
    tangentialFDeriv k E g₁ =ᵐ[μHE[k].restrict E] tangentialFDeriv k E g₂ := by
  filter_upwards [hg] with x hx_eq
  have hpred : (HasTangentialFDerivAt k E g₁ · x) = (HasTangentialFDerivAt k E g₂ · x) :=
    funext fun _ => propext (HasTangentialFDerivAt.congr_ae_fun hg hx_eq)
  exact congrArg (fun p : (V →L[ℝ] W) → Prop =>
    by classical exact if h : ∃ L, p L then h.choose else 0) hpred

end Defs

section Jacobian

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {k : ℕ} {E E₁ E₂ : Set V} {g g₁ g₂ : V → W} {L : V →L[ℝ] W} {x : V}

open Classical in
/-- The **`k`-dimensional tangential Jacobian** of `g : V → W` along `E` at `x`: the geometric
Jacobian `LinearMap.normDet` of `tangentialFDeriv k E g x` restricted to
`approximateTangentPlane k E x` when `g` is tangentially differentiable along `E` at `x`, and `0`
otherwise. -/
noncomputable def tangentialJacobian (k : ℕ) (E : Set V) (g : V → W) (x : V) : ℝ :=
  if ∃ L : V →L[ℝ] W, HasTangentialFDerivAt k E g L x then
    ((tangentialFDeriv k E g x).toLinearMap.domRestrict (approximateTangentPlane k E x)).normDet
  else
    0

/-- The tangential Jacobian is nonnegative everywhere. -/
theorem tangentialJacobian_nonneg (k : ℕ) (E : Set V) (g : V → W) (x : V) :
    0 ≤ tangentialJacobian k E g x := by
  unfold tangentialJacobian
  split_ifs
  · exact LinearMap.normDet_nonneg _
  · exact le_rfl

/-- Explicit formula for `tangentialJacobian` when `HasTangentialFDerivAt k E g L x` holds. -/
theorem HasTangentialFDerivAt.tangentialJacobian_eq (h : HasTangentialFDerivAt k E g L x) :
    tangentialJacobian k E g x =
      (L.toLinearMap.domRestrict (approximateTangentPlane k E x)).normDet := by
  have hex : ∃ L', HasTangentialFDerivAt k E g L' x := ⟨L, h⟩
  simp only [tangentialJacobian, hex, ↓reduceIte, h.tangentialFDeriv_eq]

/-- Bound `tangentialJacobian k E g x ≤ ‖L‖ ^ k` when `HasTangentialFDerivAt k E g L x`. -/
theorem HasTangentialFDerivAt.tangentialJacobian_le_opNorm_pow
    (h : HasTangentialFDerivAt k E g L x) :
    tangentialJacobian k E g x ≤ ‖L‖ ^ k := by
  let P := approximateTangentPlane k E x
  have hdim : finrank ℝ P = k := h.isApproximateTangentPlane.finrank_eq
  have heq : L.toLinearMap.domRestrict P = (L.comp P.subtypeL).toLinearMap := by ext y; rfl
  rw [h.tangentialJacobian_eq, heq]
  conv_rhs => rw [← hdim]
  have h1 : ((L.comp P.subtypeL).toLinearMap).normDet ≤ ‖L.comp P.subtypeL‖ ^ finrank ℝ P :=
    normDet_le_opNorm_pow (L.comp P.subtypeL)
  have hsub_norm : ‖P.subtypeL‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by simp
  have hnorm : ‖L.comp P.subtypeL‖ ≤ ‖L‖ :=
    (L.opNorm_comp_le P.subtypeL).trans (mul_le_of_le_one_right (norm_nonneg L) hsub_norm)
  exact h1.trans (pow_le_pow_left₀ (norm_nonneg (L.comp P.subtypeL)) hnorm _)

/-- When the tangential derivative at `x` has range of dimension strictly less than `k`, the
`k`-dimensional tangential Jacobian at `x` vanishes. -/
theorem tangentialJacobian_eq_zero_of_finrank_range_lt
    (hrank : finrank ℝ (LinearMap.range (tangentialFDeriv k E g x).toLinearMap) < k) :
    tangentialJacobian k E g x = 0 := by
  by_cases h : ∃ L : V →L[ℝ] W, HasTangentialFDerivAt k E g L x
  · have htan := hasTangentialFDerivAt_tangentialFDeriv h
    simp only [tangentialJacobian, h, ↓reduceIte]
    apply ((tangentialFDeriv k E g x).toLinearMap.domRestrict
      (approximateTangentPlane k E x)).normDet_eq_zero_iff_rank_range_ne.mpr
    rw [htan.isApproximateTangentPlane.finrank_eq]
    refine ne_of_lt (lt_of_le_of_lt (Submodule.finrank_mono ?_) hrank)
    rintro _ ⟨v, rfl⟩
    exact ⟨v, rfl⟩
  · simp [tangentialJacobian, h]

/-- Modifying `E` by a `μHE[k]`-null set leaves `tangentialJacobian k E g x` unchanged at every
point `x`. -/
theorem tangentialJacobian_congr_ae_set (h : E₁ =ᵐ[μHE[k]] E₂) (g : V → W) (x : V) :
    tangentialJacobian k E₁ g x = tangentialJacobian k E₂ g x := by
  have hex : (∃ L, HasTangentialFDerivAt k E₁ g L x) ↔
      ∃ L, HasTangentialFDerivAt k E₂ g L x :=
    exists_congr fun _ => HasTangentialFDerivAt.congr_ae_set h
  by_cases h₁ : ∃ L, HasTangentialFDerivAt k E₁ g L x
  · have h₂ := hex.mp h₁
    simp only [tangentialJacobian, h₁, h₂, ↓reduceIte, tangentialFDeriv_congr_ae_set h]
    exact congrArg
      (fun S : Submodule ℝ V => ((tangentialFDeriv k E₂ g x).toLinearMap.domRestrict S).normDet)
      (approximateTangentPlane_congr_ae h x)
  · have h₂ : ¬ ∃ L, HasTangentialFDerivAt k E₂ g L x := fun hc => h₁ (hex.mpr hc)
    simp [tangentialJacobian, h₁, h₂]

/-- `tangentialJacobian k E g x` depends only on the germ of `E` at `x`. -/
theorem tangentialJacobian_congr_nhds_set (h : E₁ =ᶠ[𝓝 x] E₂) (g : V → W) :
    tangentialJacobian k E₁ g x = tangentialJacobian k E₂ g x := by
  have hex : (∃ L, HasTangentialFDerivAt k E₁ g L x) ↔
      ∃ L, HasTangentialFDerivAt k E₂ g L x :=
    exists_congr fun _ => HasTangentialFDerivAt.congr_nhds_set h
  by_cases h₁ : ∃ L, HasTangentialFDerivAt k E₁ g L x
  · have h₂ := hex.mp h₁
    simp only [tangentialJacobian, h₁, h₂, ↓reduceIte, tangentialFDeriv_congr_nhds_set h]
    exact congrArg
      (fun S : Submodule ℝ V => ((tangentialFDeriv k E₂ g x).toLinearMap.domRestrict S).normDet)
      (approximateTangentPlane_congr_nhds h)
  · have h₂ : ¬ ∃ L, HasTangentialFDerivAt k E₂ g L x := fun hc => h₁ (hex.mpr hc)
    simp [tangentialJacobian, h₁, h₂]

/-- At `x ∈ E`, `tangentialJacobian k E g x` depends only on the values of `g` on `E`. -/
theorem tangentialJacobian_congr_of_eqOn (hg : EqOn g₁ g₂ E) (hx : x ∈ E) :
    tangentialJacobian k E g₁ x = tangentialJacobian k E g₂ x := by
  have hex : (∃ L, HasTangentialFDerivAt k E g₁ L x) ↔
      ∃ L, HasTangentialFDerivAt k E g₂ L x :=
    exists_congr fun _ => HasTangentialFDerivAt.congr_of_eqOn hg hx
  by_cases h₁ : ∃ L, HasTangentialFDerivAt k E g₁ L x
  · have h₂ := hex.mp h₁
    simp [tangentialJacobian, h₁, h₂, tangentialFDeriv_congr_of_eqOn hg hx]
  · have h₂ : ¬ ∃ L, HasTangentialFDerivAt k E g₂ L x := fun hc => h₁ (hex.mpr hc)
    simp [tangentialJacobian, h₁, h₂]

/-- Modifying `g` on a `μHE[k].restrict E`-null set leaves `tangentialJacobian k E g` unchanged
`μHE[k].restrict E`-almost everywhere. -/
theorem tangentialJacobian_congr_ae_fun (hg : g₁ =ᵐ[μHE[k].restrict E] g₂) :
    tangentialJacobian k E g₁ =ᵐ[μHE[k].restrict E] tangentialJacobian k E g₂ := by
  filter_upwards [hg, tangentialFDeriv_congr_ae_fun (k := k) hg] with x hx_eq hfd
  have hex : (∃ L, HasTangentialFDerivAt k E g₁ L x) ↔
      ∃ L, HasTangentialFDerivAt k E g₂ L x :=
    exists_congr fun _ => HasTangentialFDerivAt.congr_ae_fun hg hx_eq
  by_cases h₁ : ∃ L, HasTangentialFDerivAt k E g₁ L x
  · have h₂ := hex.mp h₁
    simp [tangentialJacobian, h₁, h₂, hfd]
  · have h₂ : ¬ ∃ L, HasTangentialFDerivAt k E g₂ L x := fun hc => h₁ (hex.mpr hc)
    simp [tangentialJacobian, h₁, h₂]

end Jacobian

end TauCeti

/-! ### Deterministic parametrization chain rule and sharp Lipschitz bounds -/

namespace HasFDerivWithinAt

open TauCeti

variable {U V W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] in
/-- For injective `A : U →L[ℝ] V`, `Ring.inverse (A† ∘L A)` is a left inverse to `A† ∘L A`. -/
private lemma ringInverse_adjoint_comp_self {A : U →L[ℝ] V} (hinj : Injective A) :
    Ring.inverse (A.adjoint ∘L A) ∘L (A.adjoint ∘L A) = ContinuousLinearMap.id ℝ U := by
  let G : U →L[ℝ] U := A.adjoint ∘L A
  have hG_det : G.det ≠ 0 := by
    have hsq := A.normDet_sq
    simp only [RCLike.ofReal_real_eq_id, id_eq] at hsq
    rw [← hsq]
    exact pow_ne_zero 2 ((A.toLinearMap.normDet_ne_zero_tfae.out 5 1).mp hinj)
  let eG := G.toContinuousLinearEquivOfDetNeZero hG_det
  have hcoe : (eG : U →L[ℝ] U) = G := G.coe_toContinuousLinearEquivOfDetNeZero hG_det
  have hmul1 : G * (eG.symm : U →L[ℝ] U) = 1 := by
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def, ← hcoe]
    exact eG.coe_comp_coe_symm
  have hmul2 : (eG.symm : U →L[ℝ] U) * G = 1 := by
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def, ← hcoe]
    exact eG.coe_symm_comp_coe
  exact Ring.inverse_mul_cancel G ⟨⟨G, eG.symm, hmul1, hmul2⟩, rfl⟩

section NormedTarget

variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Parametrization chain rule for approximate tangential derivatives.** Let `f : U → V` have
injective derivative `A` within `s` at a Lebesgue density-one point `u₀ ∈ s`, with
`AntilipschitzWith L_f (s.domRestrict f)`, `f '' s ⊆ E`, and `(dim U)`-density zero of
`E \ f '' s` at `f u₀`. If `g ∘ f` has derivative `B` within `s` at `u₀`, then `g` has
approximate tangential derivative `B ∘L Ring.inverse (A† ∘L A) ∘L A†` along `E` at `f u₀`. -/
theorem hasTangentialFDerivAt_of_comp {f : U → V} {s : Set U} {A : U →L[ℝ] V} {u₀ : U}
    {L_f : ℝ≥0} {E : Set V} {g : V → W} {B : U →L[ℝ] W}
    (hf : HasFDerivWithinAt f A s u₀) (hinj : Injective A)
    (hi : AntilipschitzWith L_f (s.domRestrict f)) (hu₀ : u₀ ∈ s) (hsub : f '' s ⊆ E)
    (hdens : Tendsto (fun r => volume (s ∩ closedBall u₀ r) / volume (closedBall (0 : U) r))
      (𝓝[>] 0) (𝓝 1))
    (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f u₀) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0))
    (hgf : HasFDerivWithinAt (g ∘ f) B s u₀) :
    HasTangentialFDerivAt (finrank ℝ U) E g
      (B ∘L Ring.inverse (A.adjoint ∘L A) ∘L A.adjoint) (f u₀) := by
  let P : Submodule ℝ V := LinearMap.range A.toLinearMap
  have htan_iff := fun Q => hf.isApproximateTangentPlane_iff hinj hi hu₀ hsub hdens hdiff (Q := Q)
  have hu : ∃! Q : Submodule ℝ V, IsApproximateTangentPlane (finrank ℝ U) E (f u₀) Q :=
    ⟨P, (htan_iff P).mpr rfl, fun Q hQ => (htan_iff Q).mp hQ⟩
  have hP_eq : approximateTangentPlane (finrank ℝ U) E (f u₀) = P :=
    hf.approximateTangentPlane_eq_range hinj hi hu₀ hsub hdens hdiff
  let L : V →L[ℝ] W := B ∘L Ring.inverse (A.adjoint ∘L A) ∘L A.adjoint
  have hLA (u : U) : L (A u) = B u := by
    have h1 := congrArg (fun T : U →L[ℝ] U => T u) (ringInverse_adjoint_comp_self hinj)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h1
    simp only [L, ContinuousLinearMap.comp_apply, h1]
  have hAadj_proj (v : V) : A.adjoint (P.starProjection v) = A.adjoint v := by
    symm
    refine sub_eq_zero.mp (ext_inner_left ℝ fun u => ?_)
    rw [inner_zero_right, ← map_sub, A.adjoint_inner_right]
    have hmem : A u ∈ P := ⟨u, rfl⟩
    exact Submodule.inner_right_of_mem_orthogonal hmem (P.sub_starProjection_mem_orthogonal v)
  refine ⟨hu, ?_, fun ε hε => ?_⟩
  · ext v
    simp only [ContinuousLinearMap.comp_apply, approximateTangentProjection_eq, hP_eq, hAadj_proj]
  · have hLf1 : (0 : ℝ) < (L_f : ℝ) + 1 := by positivity
    set η₁ : ℝ := ε / (2 * ((L_f : ℝ) + 1))
    set η₂ : ℝ := ε / (2 * (‖L‖ + 1) * ((L_f : ℝ) + 1))
    obtain ⟨δ₁, hδ₁, hδ₁b⟩ := eventually_nhds_iff_ball.mp
      (eventually_nhdsWithin_iff.mp (hgf.isLittleO.bound (by positivity : 0 < η₁)))
    obtain ⟨δ₂, hδ₂, hδ₂b⟩ := eventually_nhds_iff_ball.mp
      (eventually_nhdsWithin_iff.mp (hf.isLittleO.bound (by positivity : 0 < η₂)))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdiff
      (Eventually.of_forall fun _ => zero_le) ?_
    -- For `r` small enough, `AntilipschitzWith` keeps parameters of `f '' s ∩ closedBall (f u₀) r`
    -- inside both error balls, forcing the superlevel error set into `E \ f '' s`.
    filter_upwards [Ioo_mem_nhdsGT (div_pos (lt_min hδ₁ hδ₂) hLf1)] with r ⟨_, hrδ⟩
    have hsub_e :
        {z ∈ E ∩ closedBall (f u₀) r |
          ε * dist z (f u₀) < ‖g z - g (f u₀) - L (z - f u₀)‖} ⊆
        (E \ f '' s) ∩ closedBall (f u₀) r := by
      rintro z ⟨⟨hzE, hzr⟩, hzerr⟩
      refine ⟨⟨hzE, ?_⟩, hzr⟩
      rintro ⟨u, hus, rfl⟩
      have hdu : dist u u₀ ≤ L_f * dist (f u) (f u₀) := by
        simpa [Subtype.dist_eq] using hi.le_mul_dist ⟨u, hus⟩ ⟨u₀, hu₀⟩
      have hdu_r : (L_f : ℝ) * dist (f u) (f u₀) ≤ ((L_f : ℝ) + 1) * r := by
        have hfur : dist (f u) (f u₀) ≤ r := mem_closedBall.mp hzr
        nlinarith [L_f.coe_nonneg, dist_nonneg (x := f u) (y := f u₀)]
      have hu_lt : dist u u₀ < min δ₁ δ₂ :=
        (hdu.trans hdu_r).trans_lt ((lt_div_iff₀' hLf1).mp hrδ)
      have herr₁ := hδ₁b u (mem_ball.mpr (hu_lt.trans_le (min_le_left _ _))) hus
      have herr₂ := hδ₂b u (mem_ball.mpr (hu_lt.trans_le (min_le_right _ _))) hus
      have hdecomp : g (f u) - g (f u₀) - L (f u - f u₀) =
          (g (f u) - g (f u₀) - B (u - u₀)) - L (f u - f u₀ - A (u - u₀)) := by
        simp only [← hLA (u - u₀), map_sub]
        abel
      have hnorm_u : ‖u - u₀‖ ≤ ((L_f : ℝ) + 1) * dist (f u) (f u₀) := by
        rw [← dist_eq_norm]
        nlinarith [L_f.coe_nonneg, dist_nonneg (x := f u) (y := f u₀)]
      have htot : ‖g (f u) - g (f u₀) - L (f u - f u₀)‖ ≤ ε * dist (f u) (f u₀) := by
        calc ‖g (f u) - g (f u₀) - L (f u - f u₀)‖
            ≤ ‖g (f u) - g (f u₀) - B (u - u₀)‖ + ‖L (f u - f u₀ - A (u - u₀))‖ := by
              rw [hdecomp]; exact norm_sub_le _ _
          _ ≤ η₁ * ‖u - u₀‖ + ‖L‖ * (η₂ * ‖u - u₀‖) := by
              gcongr
              · simpa only [comp_apply] using herr₁
              · exact (L.le_opNorm _).trans (by gcongr)
          _ ≤ η₁ * (((L_f : ℝ) + 1) * dist (f u) (f u₀)) +
              (‖L‖ + 1) * (η₂ * (((L_f : ℝ) + 1) * dist (f u) (f u₀))) := by
              gcongr; linarith
          _ = ε * dist (f u) (f u₀) := by dsimp [η₁, η₂]; field_simp; ring
      exact hzerr.not_ge htot
    exact ENNReal.div_le_div_right (measure_mono hsub_e) _

/-- Under the hypotheses of `HasFDerivWithinAt.hasTangentialFDerivAt_of_comp`, composing
`tangentialFDeriv` at `f u₀` with `A` recovers the parameter derivative `B`. -/
theorem tangentialFDeriv_comp_eq {f : U → V} {s : Set U} {A : U →L[ℝ] V} {u₀ : U}
    {L_f : ℝ≥0} {E : Set V} {g : V → W} {B : U →L[ℝ] W}
    (hf : HasFDerivWithinAt f A s u₀) (hinj : Injective A)
    (hi : AntilipschitzWith L_f (s.domRestrict f)) (hu₀ : u₀ ∈ s) (hsub : f '' s ⊆ E)
    (hdens : Tendsto (fun r => volume (s ∩ closedBall u₀ r) / volume (closedBall (0 : U) r))
      (𝓝[>] 0) (𝓝 1))
    (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f u₀) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0))
    (hgf : HasFDerivWithinAt (g ∘ f) B s u₀) :
    tangentialFDeriv (finrank ℝ U) E g (f u₀) ∘L A = B := by
  rw [(hf.hasTangentialFDerivAt_of_comp hinj hi hu₀ hsub hdens hdiff hgf).tangentialFDeriv_eq]
  ext u
  have h1 := congrArg (fun T : U →L[ℝ] U => T u) (ringInverse_adjoint_comp_self hinj)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h1 ⊢
  rw [h1]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- At a Lebesgue density-one point `u₀ ∈ s`, if `g` is `K`-Lipschitz on `E`, `f '' s ⊆ E`,
`f` has derivative `A` within `s` at `u₀`, and `g ∘ f` has derivative `B` within `s` at `u₀`,
then `‖B v‖ ≤ K * ‖A v‖` for all `v : U`. -/
theorem norm_comp_le_of_lipschitzOnWith {f : U → V} {s : Set U} {A : U →L[ℝ] V} {u₀ : U}
    {E : Set V} {g : V → W} {B : U →L[ℝ] W} {K : ℝ≥0}
    (hf : HasFDerivWithinAt f A s u₀) (hu₀ : u₀ ∈ s) (hsub : f '' s ⊆ E)
    (hdens : Tendsto (fun r => volume (s ∩ closedBall u₀ r) / volume (closedBall (0 : U) r))
      (𝓝[>] 0) (𝓝 1))
    (hgf : HasFDerivWithinAt (g ∘ f) B s u₀) (hg : LipschitzOnWith K g E) (v : U) :
    ‖B v‖ ≤ K * ‖A v‖ := by
  by_cases hv0 : v = 0
  · simp [hv0]
  let w : U := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := norm_smul_inv_norm hv0
  suffices h : ‖B w‖ ≤ K * ‖A w‖ by
    have hv_eq : ‖v‖ • w = v := by simp [w, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0)]
    have hBv : ‖B v‖ = ‖v‖ * ‖B w‖ := by
      conv_lhs => rw [← hv_eq]
      rw [map_smul, norm_smul, Real.norm_of_nonneg (norm_nonneg v)]
    have hAv : ‖A v‖ = ‖v‖ * ‖A w‖ := by
      conv_lhs => rw [← hv_eq]
      rw [map_smul, norm_smul, Real.norm_of_nonneg (norm_nonneg v)]
    calc ‖B v‖ = ‖v‖ * ‖B w‖ := hBv
      _ ≤ ‖v‖ * (K * ‖A w‖) := mul_le_mul_of_nonneg_left h (norm_nonneg v)
      _ = K * ‖A v‖ := by rw [hAv]; ring
  -- If `‖B w‖ > K * ‖A w‖`, Lebesgue density `1` at `u₀` produces `u ∈ s` in a small shifted ball
  -- around `u₀ + (ρ / 2) • w` where `‖g (f u) - g (f u₀)‖ > K * ‖f u - f u₀‖`, contradicting `hg`.
  by_contra! hgt
  set ε : ℝ := ‖B w‖ - K * ‖A w‖
  have hε0 : 0 < ε := sub_pos.mpr hgt
  set M : ℝ := ‖B‖ + (K : ℝ) * ‖A‖ + 1
  have hM0 : 0 < M := by positivity
  set η : ℝ := min (1 / 2) (ε / (2 * M))
  have hη0 : 0 < η := lt_min (by norm_num) (div_pos hε0 (by positivity))
  have hη_half : η ≤ 1 / 2 := min_le_left _ _
  have hηM : η * M ≤ ε / 2 :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _) hM0.le).trans_eq (by field_simp)
  obtain ⟨δ₁, hδ₁, hδ₁b⟩ := eventually_nhds_iff_ball.mp
    (eventually_nhdsWithin_iff.mp (hgf.isLittleO.bound (by positivity : 0 < ε / 16)))
  obtain ⟨δ₂, hδ₂, hδ₂b⟩ := eventually_nhds_iff_ball.mp
    (eventually_nhdsWithin_iff.mp (hf.isLittleO.bound
      (by positivity : 0 < ε / (16 * ((K : ℝ) + 1)))))
  obtain ⟨ρ, ⟨hρ0, hρδ⟩, u, hus, huD⟩ :=
    exists_mem_inter_shifted_closedBall_of_tendsto hdens hw hη0 hη_half (lt_min hδ₁ hδ₂)
  have hy : ‖u - (u₀ + (ρ / 2) • w)‖ ≤ (η / 4) * ρ := by simpa [dist_eq_norm] using huD
  have hu_norm : ‖u - u₀‖ ≤ ρ := by
    calc ‖u - u₀‖ = ‖(u - (u₀ + (ρ / 2) • w)) + (ρ / 2) • w‖ := by abel_nf
      _ ≤ ‖u - (u₀ + (ρ / 2) • w)‖ + ‖(ρ / 2) • w‖ := norm_add_le _ _
      _ ≤ (η / 4) * ρ + (ρ / 2) * 1 := by
          gcongr; rw [norm_smul, Real.norm_of_nonneg (by positivity), hw]
      _ ≤ ρ := by nlinarith
  have hu_δ₁ : u ∈ ball u₀ δ₁ := by
    rw [mem_ball, dist_eq_norm]
    exact hu_norm.trans_lt (hρδ.trans_le (min_le_left _ _))
  have hu_δ₂ : u ∈ ball u₀ δ₂ := by
    rw [mem_ball, dist_eq_norm]
    exact hu_norm.trans_lt (hρδ.trans_le (min_le_right _ _))
  have herr_gf := hδ₁b u hu_δ₁ hus
  have herr_f := hδ₂b u hu_δ₂ hus
  have hlip_g : ‖g (f u) - g (f u₀)‖ ≤ K * ‖f u - f u₀‖ := by
    simpa [dist_eq_norm] using
      hg.dist_le_mul (f u) (hsub (mem_image_of_mem f hus))
        (f u₀) (hsub (mem_image_of_mem f hu₀))
  have hB_lower : (ρ / 2) * ‖B w‖ - ((ε / 16) * ρ + ‖B‖ * ((η / 4) * ρ)) ≤
      ‖g (f u) - g (f u₀)‖ := by
    have hdecomp : (ρ / 2) • B w = (g (f u) - g (f u₀)) -
        ((g ∘ f) u - (g ∘ f) u₀ - B (u - u₀)) - B (u - (u₀ + (ρ / 2) • w)) := by
      simp only [comp_apply, map_sub, map_add, map_smul]
      abel
    have h0 : ‖(ρ / 2) • B w‖ = (ρ / 2) * ‖B w‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have ha := norm_sub_le
      ((g (f u) - g (f u₀)) - ((g ∘ f) u - (g ∘ f) u₀ - B (u - u₀)))
      (B (u - (u₀ + (ρ / 2) • w)))
    have hb := norm_sub_le (g (f u) - g (f u₀)) ((g ∘ f) u - (g ∘ f) u₀ - B (u - u₀))
    rw [← hdecomp, h0] at ha
    have h1 := herr_gf.trans (mul_le_mul_of_nonneg_left hu_norm (by positivity))
    have h2 := (B.le_opNorm _).trans (mul_le_mul_of_nonneg_left hy (norm_nonneg B))
    linarith
  have hA_upper : ‖f u - f u₀‖ ≤
      (ρ / 2) * ‖A w‖ + (ε / (16 * ((K : ℝ) + 1))) * ρ + ‖A‖ * ((η / 4) * ρ) := by
    have hdecomp : f u - f u₀ =
        (ρ / 2) • A w + (f u - f u₀ - A (u - u₀)) + A (u - (u₀ + (ρ / 2) • w)) := by
      simp only [map_sub, map_add, map_smul]
      abel
    rw [hdecomp]
    have h1 := herr_f.trans (mul_le_mul_of_nonneg_left hu_norm (by positivity))
    have h2 := (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left hy (norm_nonneg A))
    have h3 : ‖(ρ / 2) • A w‖ = (ρ / 2) * ‖A w‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    linarith [norm_add_le ((ρ / 2) • A w + (f u - f u₀ - A (u - u₀)))
      (A (u - (u₀ + (ρ / 2) • w))),
      norm_add_le ((ρ / 2) • A w) (f u - f u₀ - A (u - u₀))]
  have hKA : (K : ℝ) * ((ε / (16 * ((K : ℝ) + 1))) * ρ) ≤ (ε / 16) * ρ := by
    calc (K : ℝ) * ((ε / (16 * ((K : ℝ) + 1))) * ρ)
        ≤ ((K : ℝ) + 1) * ((ε / (16 * ((K : ℝ) + 1))) * ρ) := by gcongr; linarith
      _ = (ε / 16) * ρ := by field_simp
  have hη_sum : (‖B‖ + (K : ℝ) * ‖A‖) * ((η / 4) * ρ) ≤ (ε / 8) * ρ := by
    calc (‖B‖ + (K : ℝ) * ‖A‖) * ((η / 4) * ρ)
        ≤ (η * M) * (ρ / 4) := by
          have hring : (‖B‖ + (K : ℝ) * ‖A‖) * ((η / 4) * ρ) =
              (η * (‖B‖ + (K : ℝ) * ‖A‖)) * (ρ / 4) := by ring
          rw [hring]; gcongr; dsimp [M]; linarith
      _ ≤ (ε / 2) * (ρ / 4) := by gcongr
      _ = (ε / 8) * ρ := by ring
  have hcomb : (K : ℝ) * ‖f u - f u₀‖ ≤
      (ρ / 2) * ((K : ℝ) * ‖A w‖) + (ε / 16) * ρ + (K : ℝ) * ‖A‖ * ((η / 4) * ρ) := by
    have := mul_le_mul_of_nonneg_left hA_upper K.coe_nonneg
    linarith
  nlinarith [K.coe_nonneg, mul_pos hε0 hρ0]

/-- **Sharp operator-norm bound on `tangentialFDeriv`.** Under the hypotheses of
`HasFDerivWithinAt.hasTangentialFDerivAt_of_comp`, if `g` is `K`-Lipschitz on `E`, then
`‖tangentialFDeriv (finrank ℝ U) E g (f u₀)‖ ≤ K`. -/
theorem norm_tangentialFDeriv_le_of_lipschitzOnWith {f : U → V} {s : Set U} {A : U →L[ℝ] V}
    {u₀ : U} {L_f : ℝ≥0} {E : Set V} {g : V → W} {B : U →L[ℝ] W} {K : ℝ≥0}
    (hf : HasFDerivWithinAt f A s u₀) (hinj : Injective A)
    (hi : AntilipschitzWith L_f (s.domRestrict f)) (hu₀ : u₀ ∈ s) (hsub : f '' s ⊆ E)
    (hdens : Tendsto (fun r => volume (s ∩ closedBall u₀ r) / volume (closedBall (0 : U) r))
      (𝓝[>] 0) (𝓝 1))
    (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f u₀) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0))
    (hgf : HasFDerivWithinAt (g ∘ f) B s u₀) (hg : LipschitzOnWith K g E) :
    ‖tangentialFDeriv (finrank ℝ U) E g (f u₀)‖ ≤ K := by
  refine ContinuousLinearMap.opNorm_le_bound _ K.coe_nonneg fun z => ?_
  have hcomp := hf.tangentialFDeriv_comp_eq hinj hi hu₀ hsub hdens hdiff hgf
  have hP_eq := hf.approximateTangentPlane_eq_range hinj hi hu₀ hsub hdens hdiff
  let P := approximateTangentPlane (finrank ℝ U) E (f u₀)
  have hzP : P.starProjection z ∈ LinearMap.range A.toLinearMap :=
    hP_eq ▸ Submodule.starProjection_apply_mem P z
  obtain ⟨u, hu⟩ := hzP
  calc ‖tangentialFDeriv (finrank ℝ U) E g (f u₀) z‖
      = ‖tangentialFDeriv (finrank ℝ U) E g (f u₀) (P.starProjection z)‖ := by
        rw [← approximateTangentProjection_eq, ← ContinuousLinearMap.comp_apply,
          tangentialFDeriv_comp_approximateTangentProjection]
    _ = ‖B u‖ := by
        rw [← hu, ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.comp_apply, hcomp]
    _ ≤ K * ‖A u‖ := hf.norm_comp_le_of_lipschitzOnWith hu₀ hsub hdens hgf hg u
    _ = K * ‖P.starProjection z‖ := by rw [← ContinuousLinearMap.coe_coe, hu]
    _ ≤ K * ‖z‖ := by gcongr; exact P.norm_starProjection_apply_le z

end NormedTarget

section InnerProductTarget

variable [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- **Parametrization chain rule for the tangential Jacobian.** Under the hypotheses of
`HasFDerivWithinAt.hasTangentialFDerivAt_of_comp`,
`tangentialJacobian (finrank ℝ U) E g (f u₀) * A.normDet = B.normDet`. -/
theorem tangentialJacobian_mul_normDet {f : U → V} {s : Set U} {A : U →L[ℝ] V} {u₀ : U}
    {L_f : ℝ≥0} {E : Set V} {g : V → W} {B : U →L[ℝ] W}
    (hf : HasFDerivWithinAt f A s u₀) (hinj : Injective A)
    (hi : AntilipschitzWith L_f (s.domRestrict f)) (hu₀ : u₀ ∈ s) (hsub : f '' s ⊆ E)
    (hdens : Tendsto (fun r => volume (s ∩ closedBall u₀ r) / volume (closedBall (0 : U) r))
      (𝓝[>] 0) (𝓝 1))
    (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f u₀) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0))
    (hgf : HasFDerivWithinAt (g ∘ f) B s u₀) :
    tangentialJacobian (finrank ℝ U) E g (f u₀) * A.toLinearMap.normDet =
      B.toLinearMap.normDet := by
  have htan := hf.hasTangentialFDerivAt_of_comp hinj hi hu₀ hsub hdens hdiff hgf
  have hcomp : (tangentialFDeriv (finrank ℝ U) E g (f u₀)).toLinearMap ∘ₗ A.toLinearMap =
      B.toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap
      (hf.tangentialFDeriv_comp_eq hinj hi hu₀ hsub hdens hdiff hgf)
  have hP_eq := hf.approximateTangentPlane_eq_range hinj hi hu₀ hsub hdens hdiff
  rw [← hcomp, LinearMap.normDet_comp, htan.tangentialJacobian_eq, ← htan.tangentialFDeriv_eq]
  exact congrArg (· * A.toLinearMap.normDet) (congrArg
    (fun S : Submodule ℝ V =>
      ((tangentialFDeriv (finrank ℝ U) E g (f u₀)).toLinearMap.domRestrict S).normDet) hP_eq)

/-- **Sharp Lipschitz bound on `tangentialJacobian`.** Under the hypotheses of
`HasFDerivWithinAt.hasTangentialFDerivAt_of_comp`, if `g` is `K`-Lipschitz on `E`, then
`tangentialJacobian (finrank ℝ U) E g (f u₀) ≤ K ^ finrank ℝ U`. -/
theorem tangentialJacobian_le_of_lipschitzOnWith {f : U → V} {s : Set U} {A : U →L[ℝ] V}
    {u₀ : U} {L_f : ℝ≥0} {E : Set V} {g : V → W} {B : U →L[ℝ] W} {K : ℝ≥0}
    (hf : HasFDerivWithinAt f A s u₀) (hinj : Injective A)
    (hi : AntilipschitzWith L_f (s.domRestrict f)) (hu₀ : u₀ ∈ s) (hsub : f '' s ⊆ E)
    (hdens : Tendsto (fun r => volume (s ∩ closedBall u₀ r) / volume (closedBall (0 : U) r))
      (𝓝[>] 0) (𝓝 1))
    (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f u₀) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0))
    (hgf : HasFDerivWithinAt (g ∘ f) B s u₀) (hg : LipschitzOnWith K g E) :
    tangentialJacobian (finrank ℝ U) E g (f u₀) ≤ (K : ℝ) ^ finrank ℝ U := by
  have htan := hf.hasTangentialFDerivAt_of_comp hinj hi hu₀ hsub hdens hdiff hgf
  have hnorm := hf.norm_tangentialFDeriv_le_of_lipschitzOnWith hinj hi hu₀ hsub hdens hdiff hgf hg
  rw [htan.tangentialFDeriv_eq] at hnorm
  exact htan.tangentialJacobian_le_opNorm_pow.trans (pow_le_pow_left₀ (norm_nonneg _) hnorm _)

end InnerProductTarget

end HasFDerivWithinAt
