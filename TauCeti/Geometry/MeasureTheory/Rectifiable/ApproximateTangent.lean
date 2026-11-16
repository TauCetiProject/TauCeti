/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.MeasurableTangent
public import Mathlib.Order.LiminfLimsup
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import TauCeti.Geometry.MeasureTheory.Rectifiable.Density
import TauCeti.Geometry.Euclidean.Volume.Density
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Function.AreaFormula.Lipschitz

/-!
# Approximate tangent planes of rectifiable sets

Approximate tangent planes (Mattila 15.17): uniqueness, a.e. existence, and measurability.
-/

public section

open Filter Function Metric MeasureTheory Measure Module Set
open scoped ENNReal NNReal Topology symmDiff
local notation "ω[" d "](" r ")" => volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) r)
local notation "𝓝₊" => 𝓝[>] (0 : ℝ)
local notation "cb" => Metric.closedBall

namespace TauCeti
/-- Volume of a closed ball in `U` agrees with that in `EuclideanSpace ℝ (Fin (finrank ℝ U))`. -/
theorem volume_closedBall_eq_euclidean {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] (x : U) (r : ℝ) : volume (cb x r) =
    volume (cb (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r) := by
  let e : U ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ U)) := (stdOrthonormalBasis ℝ U).repr
  have himg : e '' cb x r = cb (e x) r := e.toIsometryEquiv.image_closedBall x r
  rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume, ←
    e.isometry.euclideanHausdorffMeasure_image, himg,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume, addHaar_closedBall_center]
/-- Bound `volume t ≤ L ^ dim U * μHE[dim U] (f '' t)` along an `L`-antilipschitz restriction. -/
theorem volume_le_mul_euclideanHausdorffMeasure_image_of_antilipschitzWith {U V : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [MeasurableSpace U]
    [BorelSpace U] [MetricSpace V] [MeasurableSpace V] [BorelSpace V] {f : U → V} {s t : Set U} {L :
    ℝ≥0} (hi : AntilipschitzWith L (s.domRestrict f)) (hts : t ⊆ s) : volume t ≤ (L : ℝ≥0∞) ^
    finrank ℝ U * μHE[finrank ℝ U] (f '' t) := by
  rcases t.eq_empty_or_nonempty with rfl | ⟨x₀, _⟩
  · simp
  classical have : Nonempty U := ⟨x₀⟩
  have hφ : LipschitzOnWith L (invFunOn f s) (f '' s) := lipschitzOnWith_iff_restrict.2
    (hi.to_rightInvOn' (fun _ hy => invFunOn_mem hy) fun _ hy => invFunOn_eq hy)
  calc volume t = μHE[finrank ℝ U] (invFunOn f s '' (f '' t)) := by
        rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
          (injOn_iff_injective.2 hi.injective).leftInvOn_invFunOn.image_image' hts]
    _ ≤ (L : ℝ≥0∞) ^ finrank ℝ U * μHE[finrank ℝ U] (f '' t) :=
        (hφ.mono (image_mono hts)).euclideanHausdorffMeasure_image_le (finrank ℝ U)
/-- At a Lebesgue density-one point `x₀` of `s`, shifted balls have non-vanishing density. -/
theorem not_tendsto_volume_inter_shifted_closedBall_div_zero {U : Type*} [NormedAddCommGroup U]
    [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] {s : Set U}
    {x₀ u : U} {η : ℝ} (hdens : Tendsto (fun r => volume (s ∩ cb x₀ r) / volume (cb (0 : U) r)) 𝓝₊
    (𝓝 1)) (hu : ‖u‖ = 1) (hη0 : 0 < η) (hη_half : η ≤ 1 / 2) : ¬ Tendsto (fun ρ => volume (s ∩ cb
    (x₀ + (ρ / 2) • u) ((η / 4) * ρ)) / volume (cb (0 : U) ρ)) 𝓝₊ (𝓝 0) := by
  intro hD0; have : Nontrivial U := ⟨⟨u, 0, fun h => by simp [h] at hu⟩⟩
  set D : ℝ → Set U := fun ρ => cb (x₀ + (ρ / 2) • u) ((η / 4) * ρ)
  let V₀ (ρ : ℝ) := volume (cb (0 : U) ρ)
  set α : ℝ≥0∞ := ENNReal.ofReal (η / 4) ^ finrank ℝ U
  have hα0 : 0 < α := ENNReal.pow_pos (ENNReal.ofReal_pos.mpr (by positivity)) _
  have hineq : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), volume (s ∩ cb x₀ ρ) / V₀ ρ + α ≤ volume (s ∩ D ρ) / V₀ ρ + 1
    := by
    filter_upwards [eventually_mem_nhdsWithin] with ρ (hρ0 : 0 < ρ)
    have hD_sub : D ρ ⊆ cb x₀ ρ := fun x hx => mem_closedBall.mpr <| by
      have h2 : dist (x₀ + (ρ / 2) • u) x₀ = ρ / 2 := by
        simp [dist_eq_norm, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ ρ / 2), hu]
      linarith [mem_closedBall.mp hx, h2, dist_triangle x (x₀ + (ρ / 2) • u) x₀,
        mul_le_mul_of_nonneg_right hη_half hρ0.le]
    have hV_pos : 0 < V₀ ρ := measure_closedBall_pos volume 0 hρ0
    have hV_top : V₀ ρ ≠ ∞ := measure_closedBall_lt_top.ne
    have hvolD : volume (D ρ) = α * V₀ ρ := by
      rw [addHaar_closedBall_center, addHaar_closedBall_mul volume 0 (by positivity) hρ0.le,
        ENNReal.ofReal_pow (by positivity)]
    have hcov : s ∩ cb x₀ ρ ⊆ (s ∩ D ρ) ∪ (cb x₀ ρ \ D ρ) := fun x ⟨hxs, hxB⟩ => by_cases (fun hxD :
      x ∈ D ρ => Or.inl ⟨hxs, hxD⟩) fun hxD => Or.inr ⟨hxB, hxD⟩
    have hadd : volume (s ∩ cb x₀ ρ) + α * V₀ ρ ≤ volume (s ∩ D ρ) + V₀ ρ := calc
      volume (s ∩ cb x₀ ρ) + α * V₀ ρ
          ≤ (volume (s ∩ D ρ) + volume (cb x₀ ρ \ D ρ)) + volume (D ρ) := by
            rw [hvolD]; gcongr; exact (measure_mono hcov).trans (measure_union_le _ _)
      _ = volume (s ∩ D ρ) + V₀ ρ := by
            rw [add_assoc, ← measure_union disjoint_sdiff_self_left measurableSet_closedBall,
              sdiff_union_of_subset hD_sub, addHaar_closedBall_center]
    have hdiv := ENNReal.div_le_div_right hadd (V₀ ρ)
    rwa [ENNReal.add_div, ENNReal.add_div, ENNReal.mul_div_cancel_right hV_pos.ne' hV_top,
      ENNReal.div_self hV_pos.ne' hV_top] at hdiv
  exact hα0.not_ge <| (ENNReal.add_le_add_iff_left ENNReal.one_ne_top).mp <| by
    simpa only [zero_add, add_zero] using le_of_tendsto_of_tendsto (hdens.add tendsto_const_nhds)
      (hD0.add tendsto_const_nhds) hineq
private lemma tendsto_volume_div_zero_of_antilipschitzWith {U V : Type*} [NormedAddCommGroup U]
    [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] [MetricSpace
    V] [MeasurableSpace V] [BorelSpace V] {f : U → V} {s : Set U} {L C : ℝ≥0} (hi :
    AntilipschitzWith L (s.domRestrict f)) (hC : 0 < C) {A : ℝ → Set U} {T : ℝ → Set V} (hT :
    Tendsto (fun r => μHE[finrank ℝ U] (T r) / ω[finrank ℝ U](r)) 𝓝₊ (𝓝 0)) (hinc : ∀ᶠ ρ in 𝓝[>] (0
    : ℝ), f '' (s ∩ A ρ) ⊆ T (C * ρ)) : Tendsto (fun ρ => volume (s ∩ A ρ) / volume (cb (0 : U) ρ))
    𝓝₊ (𝓝 0) := by
  have hmul := ENNReal.Tendsto.const_mul (hT.comp (tendsto_iff_comap.2 (comap_mulLeft_nhdsGT_zero
    (NNReal.coe_pos.2 hC)).ge)) (Or.inr (ENNReal.pow_ne_top (ENNReal.coe_ne_top (r := L * C)) (n :=
    finrank ℝ U)))
  rw [mul_zero] at hmul
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmul (Eventually.of_forall
    fun _ => zero_le) ?_
  filter_upwards [eventually_mem_nhdsWithin, hinc] with ρ (hρ0 : 0 < ρ) hsub
  rw [volume_closedBall_eq_euclidean (0 : U) ρ]
  have hle : volume (s ∩ A ρ) ≤ (L : ℝ≥0∞) ^ finrank ℝ U * μHE[finrank ℝ U] (T (C * ρ)) :=
    (volume_le_mul_euclideanHausdorffMeasure_image_of_antilipschitzWith hi inter_subset_left).trans
    (by gcongr)
  refine (ENNReal.div_le_div_right hle _).trans_eq ?_
  rw [mul_div_assoc, div_volume_closedBall_eq_mul (finrank ℝ U) _ hC hρ0.le, ← mul_assoc, ←
    mul_pow, ← ENNReal.coe_mul]; rfl
end TauCeti
namespace HasFDerivWithinAt
open TauCeti
variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace U]
    [BorelSpace U] [MeasurableSpace V] [BorelSpace V] {f : U → V} {s : Set U} {A : U →L[ℝ] V} {x₀ :
    U} {L : ℝ≥0} {E : Set V} {Q : Submodule ℝ V}
/-- Patchwise lower bound `range A ≤ Q` on any cone-density-zero subspace `Q ≤ V`. -/
theorem range_le_of_tendsto_outside_cone (hf : HasFDerivWithinAt f A s x₀) (hi : AntilipschitzWith L
    (s.domRestrict f)) (hsub : f '' s ⊆ E) (hdens : Tendsto (fun r => volume (s ∩ cb x₀ r) / volume
    (cb (0 : U) r)) 𝓝₊ (𝓝 1)) (hQ : ∀ ε > (0 : ℝ), Tendsto (fun r => μHE[finrank ℝ U] {z ∈ E ∩ cb (f
    x₀) r | ε * dist z (f x₀) < infDist (z - f x₀) (Q : Set V)} / ω[finrank ℝ U](r)) 𝓝₊ (𝓝 0)) :
    LinearMap.range A.toLinearMap ≤ Q := by
  by_contra hnot; obtain ⟨_, ⟨v, rfl⟩, hvQ⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hv0 : v ≠ 0 := fun h => hvQ (by simp [h])
  let u : U := ‖v‖⁻¹ • v; have hu : ‖u‖ = 1 := norm_smul_inv_norm hv0
  have hAu : A u ∉ Q := fun h => hvQ <| by
    have : v = ‖v‖ • u := by simp [u, smul_smul, norm_ne_zero_iff.mpr hv0]
    rw [this, ContinuousLinearMap.coe_coe, map_smul]; exact Q.smul_mem _ h
  set d := infDist (A u) (Q : Set V) with hd_def
  have hd0 : 0 < d := (Q.isClosed_of_finiteDimensional.notMem_iff_infDist_pos ⟨0, Q.zero_mem⟩).mp
    hAu
  set η : ℝ := min (1 / 2) (d / (2 * (‖A‖ + 1)))
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hηA : η * ‖A‖ ≤ d / 2 := (mul_le_mul (min_le_right _ _) (le_add_of_nonneg_right zero_le_one)
    (norm_nonneg A) (by positivity)).trans_eq (by field_simp)
  let C : ℝ≥0 := ⟨‖A‖ + 1, by positivity⟩; have hC : (C : ℝ) = ‖A‖ + 1 := rfl
  have hC0 : 0 < C := Subtype.mk_lt_mk.mpr (by positivity)
  obtain ⟨δ, hδ, hδb⟩ := eventually_nhds_iff_ball.mp <| eventually_nhdsWithin_iff.mp <|
    hf.isLittleO.bound (by positivity : (0 : ℝ) < min 1 (d / 16))
  refine not_tendsto_volume_inter_shifted_closedBall_div_zero hdens hu hη0 (min_le_left _ _) <|
    tendsto_volume_div_zero_of_antilipschitzWith hi hC0 (hQ (d / (16 * C)) (div_pos hd0 (mul_pos (by
    norm_num) (NNReal.coe_pos.2 hC0)))) ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with ρ ⟨hρ0, hρδ⟩
  rintro _ ⟨x, ⟨hxs, hxD⟩, rfl⟩
  have hy : ‖x - (x₀ + (ρ / 2) • u)‖ ≤ (η / 4) * ρ := by simpa [dist_eq_norm] using hxD
  have hdist_x : ‖x - x₀‖ ≤ ρ := calc
    ‖x - x₀‖ = ‖(x - (x₀ + (ρ / 2) • u)) + (ρ / 2) • u‖ := by abel_nf
    _ ≤ (η / 4) * ρ + (ρ / 2) * 1 := (norm_add_le _ _).trans (add_le_add hy
        (by rw [norm_smul, Real.norm_of_nonneg (by positivity), hu]))
    _ ≤ ρ := by nlinarith [min_le_left (1 / 2) (d / (2 * (‖A‖ + 1)))]
  have herr := hδb x (mem_ball.mpr (by simpa [dist_eq_norm] using hdist_x.trans_lt hρδ)) hxs
  have herr1 : ‖f x - f x₀ - A (x - x₀)‖ ≤ 1 * ‖x - x₀‖ := herr.trans (mul_le_mul_of_nonneg_right
    (min_le_left _ _) (norm_nonneg _))
  have herr2 : ‖f x - f x₀ - A (x - x₀)‖ ≤ (d / 16) * ρ := herr.trans ((mul_le_mul_of_nonneg_right
    (min_le_right _ _) (norm_nonneg _)).trans (by gcongr))
  have hfx_dist : dist (f x) (f x₀) ≤ C * ρ := by
    rw [dist_eq_norm, hC]
    calc ‖f x - f x₀‖ = ‖(f x - f x₀ - A (x - x₀)) + A (x - x₀)‖ := by abel_nf
      _ ≤ 1 * ‖x - x₀‖ + ‖A‖ * ‖x - x₀‖ :=
        (norm_add_le _ _).trans (add_le_add herr1 (A.le_opNorm _))
      _ ≤ (‖A‖ + 1) * ρ := by nlinarith [norm_nonneg A]
  refine ⟨⟨hsub (mem_image_of_mem f hxs), mem_closedBall.mpr hfx_dist⟩, ?_⟩
  have hAy : ‖A (x - (x₀ + (ρ / 2) • u))‖ ≤ (d / 8) * ρ := (A.le_opNorm _).trans <|
    (mul_le_mul_of_nonneg_left hy (norm_nonneg A)).trans (by nlinarith)
  have hdiff : ‖(f x - f x₀) - (ρ / 2) • A u‖ ≤ (3 / 16) * d * ρ := by
    have hdecomp : (f x - f x₀) - (ρ / 2) • A u = (f x - f x₀ - A (x - x₀)) + A (x - (x₀ + (ρ / 2) •
      u)) := by
      simp [map_sub, map_add, map_smul]; abel
    exact hdecomp ▸ (norm_add_le _ _).trans (by linarith)
  have hsmul : infDist ((ρ / 2) • A u) (Q : Set V) = (ρ / 2) * d := by
    rw [hd_def, ← Q.dist_starProjection_eq_infDist, ← Q.dist_starProjection_eq_infDist,
      dist_eq_norm, dist_eq_norm, Q.starProjection.map_smul (ρ / 2), ← smul_sub, norm_smul,
      Real.norm_of_nonneg (by positivity)]
  have hlip := (lipschitz_infDist_pt (Q : Set V)).dist_le_mul (f x - f x₀) ((ρ / 2) • A u)
  rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm, hsmul] at hlip
  have : (0 : ℝ) < C := NNReal.coe_pos.2 hC0
  have hcone_lhs : (d / (16 * C)) * dist (f x) (f x₀) ≤ (d / 16) * ρ := (mul_le_mul_of_nonneg_left
    hfx_dist (by positivity)).trans_eq (by field_simp)
  linarith [neg_le_of_abs_le hlip, mul_pos hd0 hρ0]
/-- Patchwise uniqueness `Q = range A` when `A` is injective and `finrank ℝ Q ≤ finrank ℝ U`. -/
theorem eq_range_of_tendsto_outside_cone (hf : HasFDerivWithinAt f A s x₀) (hinj : Injective A) (hi
    : AntilipschitzWith L (s.domRestrict f)) (hsub : f '' s ⊆ E) (hdens : Tendsto (fun r => volume
    (s ∩ cb x₀ r) / volume (cb (0 : U) r)) 𝓝₊ (𝓝 1)) (hQdim : finrank ℝ Q ≤ finrank ℝ U) (hQ : ∀ ε >
    (0 : ℝ), Tendsto (fun r => μHE[finrank ℝ U] {z ∈ E ∩ cb (f x₀) r | ε * dist z (f x₀) < infDist
    (z - f x₀) (Q : Set V)} / ω[finrank ℝ U](r)) 𝓝₊ (𝓝 0)) : Q = LinearMap.range A.toLinearMap :=
    (Submodule.eq_of_le_of_finrank_le (hf.range_le_of_tendsto_outside_cone hi hsub hdens hQ)
    (hQdim.trans_eq (LinearMap.finrank_range_of_inj hinj).symm)).symm
omit [FiniteDimensional ℝ V] in
/-- Positive upper `(dim U)`-density of `E` at `f x₀` on an inverse-Lipschitz patch. -/
theorem limsup_euclideanHausdorffMeasure_inter_closedBall_div_pos (hf : HasFDerivWithinAt f A s x₀)
    (hi : AntilipschitzWith L (s.domRestrict f)) (hsub : f '' s ⊆ E) (hdens : Tendsto (fun r =>
    volume (s ∩ cb x₀ r) / volume (cb (0 : U) r)) 𝓝₊ (𝓝 1)) : 0 < limsup (fun r => μHE[finrank ℝ U]
    (E ∩ cb (f x₀) r) / ω[finrank ℝ U](r)) 𝓝₊ := by
  by_contra! hle
  have htend0 := tendsto_of_le_liminf_of_limsup_le zero_le (nonpos_iff_eq_zero.mp hle).le
  let C : ℝ≥0 := ⟨‖A‖ + 1, by positivity⟩; have hC0 : 0 < C := Subtype.mk_lt_mk.mpr (by positivity)
  obtain ⟨δ, hδ, hδb⟩ := eventually_nhds_iff_ball.mp <| eventually_nhdsWithin_iff.mp <|
    hf.isLittleO.bound zero_lt_one
  refine one_ne_zero <| tendsto_nhds_unique hdens <| tendsto_volume_div_zero_of_antilipschitzWith hi
    hC0 htend0 ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with ρ ⟨_, hρδ⟩
  rintro _ ⟨x, ⟨hxs, hxB⟩, rfl⟩; refine ⟨hsub (mem_image_of_mem f hxs), mem_closedBall.mpr ?_⟩
  have herr := hδb x (mem_ball.mpr ((mem_closedBall.mp hxB).trans_lt hρδ)) hxs; rw [dist_eq_norm]
  calc ‖f x - f x₀‖ = ‖(f x - f x₀ - A (x - x₀)) + A (x - x₀)‖ := by abel_nf
    _ ≤ 1 * ‖x - x₀‖ + ‖A‖ * ‖x - x₀‖ := (norm_add_le _ _).trans (add_le_add herr (A.le_opNorm _))
    _ ≤ C * ρ := by
      have : ‖x - x₀‖ ≤ ρ := by simpa [dist_eq_norm] using mem_closedBall.mp hxB
      change _ ≤ (‖A‖ + 1) * ρ; nlinarith [norm_nonneg A]
omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V] [MeasurableSpace U] [BorelSpace U] in
/-- Zero `(dim U)`-density outside every cone around `range A` on an inverse-Lipschitz patch. -/
theorem tendsto_outside_cone_range (hf : HasFDerivWithinAt f A s x₀) (hi : AntilipschitzWith L
    (s.domRestrict f)) (hx₀ : x₀ ∈ s) (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ cb
    (f x₀) r) / ω[finrank ℝ U](r)) 𝓝₊ (𝓝 0)) : ∀ ε > (0 : ℝ), Tendsto (fun r => μHE[finrank ℝ U] {z
    ∈ E ∩ cb (f x₀) r | ε * dist z (f x₀) < infDist (z - f x₀) (LinearMap.range A.toLinearMap : Set
    V)} / ω[finrank ℝ U](r)) 𝓝₊ (𝓝 0) := by
  intro ε hε
  have hL1 : 0 < (L : ℝ) + 1 := by positivity
  obtain ⟨δ, hδ, hδb⟩ := eventually_nhds_iff_ball.mp <| eventually_nhdsWithin_iff.mp <|
    hf.isLittleO.bound (div_pos hε hL1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdiff (Eventually.of_forall
    fun _ => zero_le) ?_
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hL1)] with r ⟨_, hrδ⟩
  gcongr; rintro z ⟨⟨hzE, hzr⟩, hzcone⟩; refine ⟨⟨hzE, ?_⟩, hzr⟩; rintro ⟨x, hxs, rfl⟩
  have hdx : dist x x₀ ≤ ((L : ℝ) + 1) * dist (f x) (f x₀) := by
    have : dist x x₀ ≤ L * dist (f x) (f x₀) := by
      simpa [Subtype.dist_eq] using hi.le_mul_dist ⟨x, hxs⟩ ⟨x₀, hx₀⟩
    nlinarith [L.coe_nonneg, dist_nonneg (x := f x) (y := f x₀)]
  have hxδ : x ∈ ball x₀ δ := mem_ball.mpr <| (hdx.trans (mul_le_mul_of_nonneg_left
    (mem_closedBall.mp hzr) hL1.le)).trans_lt ((lt_div_iff₀' hL1).mp hrδ)
  refine hzcone.not_ge <| (infDist_le_dist_of_mem (⟨x - x₀, rfl⟩ : A (x - x₀) ∈ (LinearMap.range
    A.toLinearMap : Set V))).trans ?_
  rw [dist_eq_norm]
  exact (hδb x hxδ hxs).trans <|
    (mul_le_mul_of_nonneg_left (dist_eq_norm x x₀ ▸ hdx) (div_nonneg hε.le hL1.le)).trans_eq <|
      by rw [← mul_assoc, div_mul_cancel₀ _ hL1.ne']
end HasFDerivWithinAt
namespace TauCeti
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {k : ℕ} {E E₁ E₂ : Set V}
/-- `P` is an approximate tangent `k`-plane to `E` at `x` (Mattila, Definition 15.17). -/
structure IsApproximateTangentPlane (k : ℕ) (E : Set V) (x : V) (P : Submodule ℝ V) : Prop where
  /-- `P` has dimension `k`. -/
  finrank_eq : finrank ℝ P = k
  /-- `E` has positive upper `k`-dimensional density at `x`. -/
  limsup_pos : 0 < limsup (fun r => μHE[k] (E ∩ cb x r) / ω[k](r)) 𝓝₊
  /-- Outside every cone around `P`, `E` has `k`-dimensional density zero at `x`. -/
  tendsto_outside_cone : ∀ ε > (0 : ℝ), Tendsto (fun r =>
    μHE[k] {z ∈ E ∩ cb x r | ε * dist z x < infDist (z - x) (P : Set V)} /
      ω[k](r)) 𝓝₊ (𝓝 0)
namespace IsApproximateTangentPlane
/-- In dimension zero, any approximate tangent plane is `⊥`. -/
theorem eq_bot {x : V} {P : Submodule ℝ V} (h : IsApproximateTangentPlane 0 E x P) : P = ⊥ := by
  have := finrank_zero_iff.mp h.finrank_eq; exact Submodule.eq_bot_of_subsingleton
omit [FiniteDimensional ℝ V] in
private lemma of_eventually_eq_measure {x : V} {P : Submodule ℝ V} (hb : ∀ᶠ r in 𝓝[>] (0 : ℝ),
    μHE[k] (E₁ ∩ cb x r) = μHE[k] (E₂ ∩ cb x r)) (hc : ∀ ε, ∀ᶠ r in 𝓝[>] (0 : ℝ), μHE[k] {z ∈ E₁ ∩
    cb x r | ε * dist z x < infDist (z - x) (P : Set V)} = μHE[k] {z ∈ E₂ ∩ cb x r | ε * dist z x <
    infDist (z - x) (P : Set V)}) (h : IsApproximateTangentPlane k E₁ x P) :
    IsApproximateTangentPlane k E₂ x P := by
  have hb' : (fun r => μHE[k] (E₁ ∩ cb x r) / ω[k](r)) =ᶠ[𝓝[>] 0]
      (fun r => μHE[k] (E₂ ∩ cb x r) / ω[k](r)) :=
    hb.mono fun r hr => by dsimp only; rw [hr]
  exact ⟨h.1, by simpa only [limsup_congr hb'] using h.2,
    fun ε hε => (h.3 ε hε).congr' ((hc ε).mono fun r hr => by rw [hr])⟩
omit [FiniteDimensional ℝ V] in
/-- Modifying `E` by a `μHE[k]`-null set preserves approximate tangent planes at `x`. -/
theorem congr_ae (h : E₁ =ᵐ[μHE[k]] E₂) {x : V} {P : Submodule ℝ V} : IsApproximateTangentPlane k E₁
    x P ↔ IsApproximateTangentPlane k E₂ x P := by
  have hnull : μHE[k] (E₁ ∆ E₂) = 0 := measure_symmDiff_eq_zero_iff.mpr h
  have hb (r : ℝ) : μHE[k] (E₁ ∩ cb x r) = μHE[k] (E₂ ∩ cb x r) :=
    measure_congr <| measure_symmDiff_eq_zero_iff.mp <| measure_mono_null
      (fun z hz => by simp only [mem_symmDiff, mem_inter_iff] at hz ⊢; tauto) hnull
  have hc (ε r : ℝ) :
      μHE[k] {z ∈ E₁ ∩ cb x r | ε * dist z x < infDist (z - x) (P : Set V)} =
        μHE[k] {z ∈ E₂ ∩ cb x r | ε * dist z x < infDist (z - x) (P : Set V)} :=
    measure_congr <| measure_symmDiff_eq_zero_iff.mp <| measure_mono_null
      (fun z hz => by simp only [mem_symmDiff, mem_ofPred_eq, mem_inter_iff] at hz ⊢; tauto) hnull
  exact ⟨of_eventually_eq_measure (.of_forall hb) (fun ε => .of_forall (hc ε)),
    of_eventually_eq_measure (.of_forall fun r => (hb r).symm) (fun ε => .of_forall fun r => (hc ε
    r).symm)⟩
omit [FiniteDimensional ℝ V] in
/-- Approximate tangent planes depend only on the germ of `E` at `x`. -/
theorem congr_nhds {x : V} (h : E₁ =ᶠ[𝓝 x] E₂) {P : Submodule ℝ V} : IsApproximateTangentPlane k E₁
    x P ↔ IsApproximateTangentPlane k E₂ x P := by
  obtain ⟨δ, hδ, hδeq⟩ := Metric.eventually_nhds_iff.mp h
  have hinter : ∀ᶠ r in 𝓝[>] (0 : ℝ), E₁ ∩ cb x r = E₂ ∩ cb x r := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with r ⟨_, hr⟩
    ext z; simp only [mem_inter_iff, mem_closedBall]
    exact and_congr_left fun hzr => by simpa using hδeq (hzr.trans_lt hr)
  exact ⟨of_eventually_eq_measure (hinter.mono fun _ hr => by rw [hr])
      (fun _ => hinter.mono fun _ hr => by simp only [hr]),
    of_eventually_eq_measure (hinter.mono fun _ hr => by rw [hr])
      (fun _ => hinter.mono fun _ hr => by simp only [hr])⟩
end IsApproximateTangentPlane
open Classical in
/-- Canonical approximate tangent `k`-plane to `E` at `x` (`⊥` if none exists). -/
noncomputable def approximateTangentPlane (k : ℕ) (E : Set V) (x : V) : Submodule ℝ V := if h : ∃ P
    : Submodule ℝ V, IsApproximateTangentPlane k E x P then h.choose else ⊥
/-- Orthogonal projection onto `TauCeti.approximateTangentPlane k E x`. -/
noncomputable def approximateTangentProjection (k : ℕ) (E : Set V) (x : V) : V →L[ℝ] V :=
    (approximateTangentPlane k E x).starProjection
/-- Unfolding lemma for `approximateTangentProjection k E x`. -/
theorem approximateTangentProjection_eq (k : ℕ) (E : Set V) (x : V) :
    approximateTangentProjection k E x = (approximateTangentPlane k E x).starProjection := by rfl
omit [FiniteDimensional ℝ V] in
/-- Uniqueness identifies `approximateTangentPlane k E x` with `P`. -/
theorem IsApproximateTangentPlane.approximateTangentPlane_eq {x : V} {P : Submodule ℝ V} (hP :
    IsApproximateTangentPlane k E x P) (huniq : ∀ Q, IsApproximateTangentPlane k E x Q → Q = P) :
    approximateTangentPlane k E x = P := by
  have hex : ∃ Q, IsApproximateTangentPlane k E x Q := ⟨P, hP⟩
  simp only [approximateTangentPlane, hex, ↓reduceDIte]; exact huniq _ hex.choose_spec
/-- Uniqueness identifies `approximateTangentProjection k E x` with `P.starProjection`. -/
theorem IsApproximateTangentPlane.approximateTangentProjection_eq {x : V} {P : Submodule ℝ V} (hP :
    IsApproximateTangentPlane k E x P) (huniq : ∀ Q, IsApproximateTangentPlane k E x Q → Q = P) :
    approximateTangentProjection k E x = P.starProjection := by
  simp only [approximateTangentProjection, hP.approximateTangentPlane_eq huniq]
omit [FiniteDimensional ℝ V] in
/-- Specification of `approximateTangentPlane k E x` when a plane exists. -/
theorem isApproximateTangentPlane_approximateTangentPlane {x : V} (h : ∃ P : Submodule ℝ V,
    IsApproximateTangentPlane k E x P) : IsApproximateTangentPlane k E x (approximateTangentPlane k
    E x) := by
  simp only [approximateTangentPlane, h, ↓reduceDIte]; exact h.choose_spec
/-- In dimension zero, `approximateTangentPlane 0 E x = ⊥`. -/
@[simp] theorem approximateTangentPlane_zero (E : Set V) (x : V) : approximateTangentPlane 0 E x = ⊥
    := by
  by_cases h : ∃ P : Submodule ℝ V, IsApproximateTangentPlane 0 E x P
  · exact (isApproximateTangentPlane_approximateTangentPlane h).eq_bot
  · simp [approximateTangentPlane, h]
/-- In dimension zero, `approximateTangentProjection 0 E x = 0`. -/
@[simp] theorem approximateTangentProjection_zero (E : Set V) (x : V) :
    approximateTangentProjection 0 E x = 0 := by simp [approximateTangentProjection]
omit [FiniteDimensional ℝ V] in
/-- Null-set invariance of `approximateTangentPlane`. -/
theorem approximateTangentPlane_congr_ae (h : E₁ =ᵐ[μHE[k]] E₂) (x : V) :
    approximateTangentPlane k E₁ x = approximateTangentPlane k E₂ x :=
  congrArg (fun p : Submodule ℝ V → Prop => by classical exact if h : ∃ P, p P then h.choose else ⊥)
    (funext fun _ => propext (IsApproximateTangentPlane.congr_ae h))
/-- Null-set invariance of `approximateTangentProjection`. -/
theorem approximateTangentProjection_congr_ae (h : E₁ =ᵐ[μHE[k]] E₂) (x : V) :
    approximateTangentProjection k E₁ x = approximateTangentProjection k E₂ x := by
  simp only [approximateTangentProjection, approximateTangentPlane_congr_ae h]
omit [FiniteDimensional ℝ V] in
/-- Germ invariance of `approximateTangentPlane`. -/
theorem approximateTangentPlane_congr_nhds {x : V} (h : E₁ =ᶠ[𝓝 x] E₂) :
    approximateTangentPlane k E₁ x = approximateTangentPlane k E₂ x :=
  congrArg (fun p : Submodule ℝ V → Prop => by classical exact if h : ∃ P, p P then h.choose else ⊥)
    (funext fun _ => propext (IsApproximateTangentPlane.congr_nhds h))
/-- Germ invariance of `approximateTangentProjection`. -/
theorem approximateTangentProjection_congr_nhds {x : V} (h : E₁ =ᶠ[𝓝 x] E₂) :
    approximateTangentProjection k E₁ x = approximateTangentProjection k E₂ x := by
  simp only [approximateTangentProjection, approximateTangentPlane_congr_nhds h]
section Rectifiable
variable (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure
    (μHE[k].restrict E)]
include hE hEm
/-- Almost-everywhere existence of a cone-density-zero `k`-plane on a rectifiable set. -/
theorem CountablyRectifiable.ae_exists_submodule_tendsto_measure_outside_cone_div : ∀ᵐ x ∂μHE[k], x
    ∈ E → ∃ P : Submodule ℝ V, finrank ℝ P = k ∧ ∀ ε > (0 : ℝ), Tendsto (fun r => μHE[k] {z ∈ E ∩ cb
    x r | ε * dist z x < infDist (z - x) (P : Set V)} / ω[k](r)) 𝓝₊ (𝓝 0) := by
  obtain ⟨Q, _, hQ⟩ := hE.exists_measurable_approximate_tangent_projection hEm
  exact hQ.mono fun _ hx hxE => let ⟨P, hdim, _, hP⟩ := hx hxE; ⟨P, hdim, hP⟩
/-- Almost-everywhere existence and uniqueness of the cone-density-zero `k`-plane. -/
theorem CountablyRectifiable.ae_existsUnique_submodule_tendsto_measure_outside_cone_div : ∀ᵐ x
    ∂μHE[k], x ∈ E → ∃! P : Submodule ℝ V, finrank ℝ P = k ∧ ∀ ε > (0 : ℝ), Tendsto (fun r => μHE[k]
    {z ∈ E ∩ cb x r | ε * dist z x < infDist (z - x) (P : Set V)} / ω[k](r)) 𝓝₊ (𝓝 0) := by
  let U := EuclideanSpace ℝ (Fin k); obtain ⟨A, f, _, hbi, hcover⟩ := hE.exists_bilipschitz_cover
  choose K L hLip hAnti using hbi; let s (n : ℕ) : Set U := A n ∩ (f n) ⁻¹' E
  have hs_anti (n : ℕ) : AntilipschitzWith (L n) ((s n).domRestrict (f n)) := fun u v => hAnti n ⟨u,
    u.2.1⟩ ⟨v, v.2.1⟩
  have hs_sub (n : ℕ) : f n '' s n ⊆ E := by rintro _ ⟨_, hu, rfl⟩; exact hu.2
  have hpatch (n : ℕ) : ∀ᵐ x ∂μHE[k], x ∈ f n '' s n → ∃ u ∈ s n, f n u = x ∧ DifferentiableAt ℝ (f
    n) u ∧ Injective (fderiv ℝ (f n) u) ∧ Tendsto (fun r => volume (s n ∩ cb u r) / volume (cb (0 :
    U) r)) 𝓝₊ (𝓝 1) := by
    let S := {u | ¬ Tendsto (fun r => volume (s n ∩ cb u r) / volume (cb u r)) (𝓝[>]
      0) (𝓝 1)}
    have hbadD_vol : volume (S ∩ s n) = 0 := nonpos_iff_eq_zero.mp <| (le_restrict_apply (s n) S
      ).trans_eq (ae_iff.mp (Besicovitch.ae_tendsto_measure_inter_div volume (s n)))
    have hbadD_img : μHE[k] (f n '' (S ∩ s n)) = 0 := by
      simpa only [U, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hbadD_vol, mul_zero,
        nonpos_iff_eq_zero] using (hLip n).lipschitzOnWith.euclideanHausdorffMeasure_image_le k (s
        := S ∩ s n)
    have hreg : μHE[k] (f n '' {u | DifferentiableAt ℝ (f n) u ∧ (fderiv ℝ (f n)
      u).toLinearMap.normDet ≠ 0}ᶜ) = 0 := by
      simpa only [finrank_euclideanSpace_fin] using (hLip
        n).euclideanHausdorffMeasure_image_compl_setOf_regular
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hbadD_img, measure_eq_zero_iff_ae_notMem.mp
      hreg] with x hxD hxR
    rintro ⟨u, hu, rfl⟩; obtain ⟨hd, hdet⟩ := not_not.mp fun h => hxR ⟨u, h, rfl⟩
    exact ⟨u, hu, rfl, hd, ((fderiv ℝ (f n) u).toLinearMap.normDet_ne_zero_tfae.out 1 5).mp hdet,
      by simpa only [addHaar_closedBall_center] using not_not.mp fun h => hxD ⟨u, ⟨h, hu⟩, rfl⟩⟩
  filter_upwards [hE.ae_exists_submodule_tendsto_measure_outside_cone_div hEm,
    measure_eq_zero_iff_ae_notMem.mp hcover, ae_all_iff.mpr hpatch] with x hex hcov hxpatch hxE
  obtain ⟨P, hPdim, hPcone⟩ := hex hxE
  obtain ⟨n, u, huA, rfl⟩ := mem_iUnion.mp (not_not.mp fun h => hcov ⟨hxE, h⟩)
  obtain ⟨u', _, hfu', hdiff, hinj, hdens⟩ := hxpatch n ⟨u, ⟨huA, hxE⟩, rfl⟩
  refine ⟨P, ⟨hPdim, hPcone⟩, fun Q ⟨hQdim, hQcone⟩ => ?_⟩
  have hconv {S : Submodule ℝ V} (hc : ∀ ε > (0 : ℝ), Tendsto (fun r =>
      μHE[k] {z ∈ E ∩ cb (f n u') r | ε * dist z (f n u') < infDist (z - f n u') S} /
        volume (cb (0 : U) r)) 𝓝₊ (𝓝 0)) :
      ∀ ε > (0 : ℝ), Tendsto (fun r =>
        μHE[finrank ℝ U] {z ∈ E ∩ cb (f n u') r |
          ε * dist z (f n u') < infDist (z - f n u') S} / ω[finrank ℝ U](r)) 𝓝₊ (𝓝 0) :=
    fun ε hε => by simpa only [U, finrank_euclideanSpace_fin,
      ← volume_closedBall_eq_euclidean (0 : EuclideanSpace ℝ (Fin k))] using hc ε hε
  exact (hdiff.hasFDerivAt.hasFDerivWithinAt.eq_range_of_tendsto_outside_cone hinj (hs_anti n)
    (hs_sub n) hdens (by simpa only [U, finrank_euclideanSpace_fin] using hQdim.le) (hconv
    (hfu'.symm ▸ hQcone))).trans
    (hdiff.hasFDerivAt.hasFDerivWithinAt.eq_range_of_tendsto_outside_cone hinj (hs_anti n) (hs_sub
    n) hdens (by simpa only [U, finrank_euclideanSpace_fin] using hPdim.le) (hconv (hfu'.symm ▸
    hPcone))).symm
/-- Almost-everywhere existence and uniqueness of approximate tangent `k`-planes. -/
theorem CountablyRectifiable.ae_existsUnique_isApproximateTangentPlane : ∀ᵐ x ∂μHE[k], x ∈ E → ∃! P
    : Submodule ℝ V, IsApproximateTangentPlane k E x P := by
  filter_upwards [hE.ae_existsUnique_submodule_tendsto_measure_outside_cone_div hEm,
    hE.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div hEm] with x huniq hdens hxE
  obtain ⟨P, ⟨hPdim, hPcone⟩, hPuniq⟩ := huniq hxE
  exact ⟨P, ⟨hPdim, by rw [(hdens hxE).limsup_eq]; exact zero_lt_one, hPcone⟩,
    fun Q hQ => hPuniq Q ⟨hQ.finrank_eq, hQ.tendsto_outside_cone⟩⟩
/-- Almost everywhere on `E`, `approximateTangentPlane k E x` is an approximate tangent plane. -/
theorem CountablyRectifiable.ae_isApproximateTangentPlane_approximateTangentPlane : ∀ᵐ x ∂μHE[k], x
    ∈ E → IsApproximateTangentPlane k E x (approximateTangentPlane k E x) :=
    (hE.ae_existsUnique_isApproximateTangentPlane hEm).mono fun _ hx hxE =>
    isApproximateTangentPlane_approximateTangentPlane (hx hxE).exists
/-- `μHE[k].restrict E`-a.e. measurability of `approximateTangentProjection k E`. -/
theorem CountablyRectifiable.aemeasurable_approximateTangentProjection : AEMeasurable
    (approximateTangentProjection k E) (μHE[k].restrict E) := by
  obtain ⟨Q, hQm, hQ⟩ := hE.exists_measurable_approximate_tangent_projection hEm
  refine hQm.aemeasurable.congr <| (ae_restrict_iff'₀ hEm).mpr ?_
  filter_upwards [hQ, hE.ae_existsUnique_isApproximateTangentPlane hEm] with x hxQ huniq hxE
  obtain ⟨P, hPdim, hQP, hPcone⟩ := hxQ hxE; obtain ⟨P₀, hP₀, hP₀uniq⟩ := huniq hxE
  rw [hP₀.approximateTangentProjection_eq hP₀uniq, ← hP₀uniq P ⟨hPdim, hP₀.limsup_pos, hPcone⟩, hQP]
end Rectifiable
end TauCeti
namespace HasFDerivWithinAt
open TauCeti
variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace U]
    [BorelSpace U] [MeasurableSpace V] [BorelSpace V] {f : U → V} {s : Set U} {A : U →L[ℝ] V} {x₀ :
    U} {L : ℝ≥0} {E : Set V} {Q : Submodule ℝ V} (hf : HasFDerivWithinAt f A s x₀) (hinj : Injective
    A) (hi : AntilipschitzWith L (s.domRestrict f)) (hx₀ : x₀ ∈ s)
include hf hinj hi hx₀
section WithSub
variable (hsub : f '' s ⊆ E) (hdens : Tendsto (fun r => volume (s ∩ cb x₀ r) / volume (cb (0 : U)
    r)) 𝓝₊ (𝓝 1)) (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ cb (f x₀) r) /
    ω[finrank ℝ U](r)) 𝓝₊ (𝓝 0))
include hsub hdens hdiff
/-- Characterization `IsApproximateTangentPlane (dim U) E (f x₀) Q ↔ Q = range A` on a patch. -/
theorem isApproximateTangentPlane_iff : IsApproximateTangentPlane (finrank ℝ U) E (f x₀) Q ↔ Q =
    LinearMap.range A.toLinearMap := ⟨fun hQ => hf.eq_range_of_tendsto_outside_cone hinj hi hsub
    hdens hQ.finrank_eq.le hQ.tendsto_outside_cone, fun h => h ▸ ⟨LinearMap.finrank_range_of_inj
    hinj, hf.limsup_euclideanHausdorffMeasure_inter_closedBall_div_pos hi hsub hdens,
    hf.tendsto_outside_cone_range hi hx₀ hdiff⟩⟩
/-- Formula `approximateTangentPlane (dim U) E (f x₀) = range A` on an inverse-Lipschitz patch. -/
theorem approximateTangentPlane_eq_range : approximateTangentPlane (finrank ℝ U) E (f x₀) =
    LinearMap.range A.toLinearMap := by
  have hiff := fun Q => hf.isApproximateTangentPlane_iff hinj hi hx₀ hsub hdens hdiff (Q := Q)
  exact ((hiff _).mpr rfl).approximateTangentPlane_eq fun Q hQ => (hiff Q).mp hQ
end WithSub
section ImageOnly
variable (hdens : Tendsto (fun r => volume (s ∩ cb x₀ r) / volume (cb (0 : U) r)) 𝓝₊ (𝓝 1))
include hdens
/-- Characterization of approximate tangent planes to `f '' s` at `f x₀`. -/
theorem isApproximateTangentPlane_image_iff : IsApproximateTangentPlane (finrank ℝ U) (f '' s) (f
    x₀) Q ↔ Q = LinearMap.range A.toLinearMap := hf.isApproximateTangentPlane_iff hinj hi hx₀
    Subset.rfl hdens (by simp)
/-- Formula `approximateTangentPlane (dim U) (f '' s) (f x₀) = range A`. -/
theorem approximateTangentPlane_image_eq_range : approximateTangentPlane (finrank ℝ U) (f '' s) (f
    x₀) = LinearMap.range A.toLinearMap := hf.approximateTangentPlane_eq_range hinj hi hx₀
    Subset.rfl hdens (by simp)
end ImageOnly
end HasFDerivWithinAt
