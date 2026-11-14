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

Let `E` be a subset of a finite-dimensional real inner product space `V`. Following Mattila
(Definition 15.17), a `k`-dimensional subspace `P ≤ V` is an **approximate tangent `k`-plane** to
`E` at `x` (`TauCeti.IsApproximateTangentPlane k E x P`) if `E` has positive upper `k`-dimensional
density at `x` and the portion of `E` outside every cone around `P` has `k`-dimensional density
zero at `x`.

This file establishes existence, uniqueness, canonical selection, measurability, and invariance of
approximate tangent planes:

* **Deterministic uniqueness on inverse-Lipschitz patches.** If `f : U → V` has an
  inverse-Lipschitz restriction to `s ⊆ U`, `f` has derivative `A` within `s` at a Lebesgue
  density-one point `x₀`, and `f '' s ⊆ E`, then every subspace `Q` outside whose cones `E` has
  `(dim U)`-density zero at `f x₀` contains `range A`
  (`HasFDerivWithinAt.range_le_of_tendsto_outside_cone`). No forward Lipschitz bound on `f` or
  measurability of `s` is required. When `A` is injective and `dim Q ≤ dim U`, this forces
  `Q = range A`.
* **Almost-everywhere existence and uniqueness on rectifiable sets.** A null-measurable, countably
  `k`-rectifiable set `E` with locally finite `μHE[k]` measure has a unique approximate tangent
  `k`-plane at `μHE[k]`-almost every `x ∈ E`
  (`TauCeti.CountablyRectifiable.ae_existsUnique_isApproximateTangentPlane`), and in fact a unique
  `k`-plane satisfying the cone-density-zero condition alone
  (`TauCeti.CountablyRectifiable.ae_existsUnique_submodule_tendsto_measure_outside_cone_div`).
* **Canonical plane and measurable projection field.** `TauCeti.approximateTangentPlane k E x`
  selects the approximate tangent `k`-plane when one exists (and `⊥` otherwise), and
  `TauCeti.approximateTangentProjection k E x` is its orthogonal projection. Both are invariant
  under `μHE[k]`-null modifications (`TauCeti.approximateTangentPlane_congr_ae`) and neighborhood
  localization (`TauCeti.approximateTangentPlane_congr_nhds`), and the projection field is
  `μHE[k].restrict E`-almost everywhere measurable on null-measurable countably `k`-rectifiable
  sets with locally finite `μHE[k]` measure
  (`TauCeti.CountablyRectifiable.aemeasurable_approximateTangentProjection`).

All densities use `μHE[k]` and the volume of a ball in `EuclideanSpace ℝ (Fin k)`. Dimension zero
is included throughout.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11 (approximate tangents).
* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Definition 15.17 and
  Theorem 15.19.
* H. Federer, *Geometric Measure Theory*, 3.2.16 and 3.2.19.
-/

public section

open Filter Function Metric MeasureTheory Measure Module Set
open scoped ENNReal NNReal Topology symmDiff

namespace TauCeti

/-- Volume of a closed ball in any finite-dimensional real inner product space `U` agrees with the
volume of the closed ball of the same radius in `EuclideanSpace ℝ (Fin (finrank ℝ U))`. -/
theorem volume_closedBall_eq_euclidean {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] (x : U) (r : ℝ) :
    volume (closedBall x r) =
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r) := by
  let e : U ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ U)) := (stdOrthonormalBasis ℝ U).repr
  have himg : (e : U → _) '' closedBall x r = closedBall (e x) r :=
    e.toIsometryEquiv.image_closedBall x r
  rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
    ← e.isometry.euclideanHausdorffMeasure_image, himg,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume, addHaar_closedBall_center]

/-- Rescaling the radius in a `k`-dimensional density quotient. -/
theorem div_volume_closedBall_eq_pow_mul (k : ℕ) (m : ℝ≥0∞) {c : ℝ≥0} (hc : 0 < c) {r : ℝ}
    (hr : 0 ≤ r) :
    m / volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) =
      (c : ℝ≥0∞) ^ k * (m / volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) (c * r))) := by
  rw [addHaar_closedBall_mul volume 0 c.coe_nonneg hr, finrank_euclideanSpace_fin,
    ENNReal.ofReal_pow c.coe_nonneg, ENNReal.ofReal_coe_nnreal, ← mul_div_assoc,
    ENNReal.mul_div_mul_left _ _ (pow_ne_zero _ (ENNReal.coe_ne_zero.2 hc.ne'))
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)]

/-- If `f` has `L`-Lipschitz inverse on `s`, then `volume` on any subset `t ⊆ s` is bounded by
`L ^ dim U` times the normalized Hausdorff measure of `f '' t`. -/
theorem volume_le_mul_euclideanHausdorffMeasure_image_of_antilipschitzWith {U V : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [MeasurableSpace U] [BorelSpace U] [MetricSpace V] [MeasurableSpace V] [BorelSpace V]
    {f : U → V} {s t : Set U} {L : ℝ≥0} (hi : AntilipschitzWith L (s.domRestrict f))
    (hts : t ⊆ s) :
    volume t ≤ (L : ℝ≥0∞) ^ finrank ℝ U * μHE[finrank ℝ U] (f '' t) := by
  rcases t.eq_empty_or_nonempty with rfl | ⟨x₀, _⟩
  · simp
  classical
  have : Nonempty U := ⟨x₀⟩
  have hinj : InjOn f s := injOn_iff_injective.2 hi.injective
  have hφ : LipschitzOnWith L (invFunOn f s) (f '' s) :=
    lipschitzOnWith_iff_restrict.2
      (hi.to_rightInvOn' (fun _ hy => invFunOn_mem hy) fun _ hy => invFunOn_eq hy)
  rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  calc μHE[finrank ℝ U] t = μHE[finrank ℝ U] (invFunOn f s '' (f '' t)) := by
        rw [hinj.leftInvOn_invFunOn.image_image' hts]
    _ ≤ (L : ℝ≥0∞) ^ finrank ℝ U * μHE[finrank ℝ U] (f '' t) :=
        (hφ.mono (image_mono hts)).euclideanHausdorffMeasure_image_le (finrank ℝ U)

/-- Scaling distance to a submodule by a nonnegative real scalar. -/
private lemma infDist_smul_of_nonneg {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (Q : Submodule ℝ V) {c : ℝ} (hc : 0 ≤ c) (v : V) :
    infDist (c • v) (Q : Set V) = c * infDist v (Q : Set V) := by
  rw [← Q.dist_starProjection_eq_infDist, ← Q.dist_starProjection_eq_infDist,
    dist_eq_norm, dist_eq_norm, map_smul, ← smul_sub, norm_smul, Real.norm_of_nonneg hc]

end TauCeti

/-! ### Deterministic uniqueness and positive upper density on inverse-Lipschitz patches -/

namespace HasFDerivWithinAt

open TauCeti

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
  [MeasurableSpace V] [BorelSpace V] in
/-- Near a point `x₀ ∈ s` where `f` has derivative `A` within `s` and `A u ∉ Q` (`‖u‖ = 1`),
small shifted parameter balls in direction `u` map into the complement of a cone around `Q`. -/
private lemma image_inter_shiftedBall_subset_outside_cone {f : U → V} {s : Set U} {A : U →L[ℝ] V}
    {x₀ u : U} {E : Set V} {Q : Submodule ℝ V} {d η : ℝ} (hf : HasFDerivWithinAt f A s x₀)
    (hsub : f '' s ⊆ E) (hu : ‖u‖ = 1) (hd0 : 0 < d) (hd : d = infDist (A u) (Q : Set V))
    (hη_half : η ≤ 1 / 2) (hηA : η * ‖A‖ ≤ d / 2) :
    let C : ℝ≥0 := ⟨‖A‖ + 1, by positivity⟩
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      f '' (s ∩ closedBall (x₀ + (ρ / 2) • u) ((η / 4) * ρ)) ⊆
        {z ∈ E ∩ closedBall (f x₀) (C * ρ) |
          (d / (16 * C)) * dist z (f x₀) < infDist (z - f x₀) (Q : Set V)} := by
  intro C
  have hC : (C : ℝ) = ‖A‖ + 1 := rfl
  have hbound := hf.isLittleO.bound (by positivity : (0 : ℝ) < min 1 (d / 16))
  obtain ⟨δ, hδ, hδb⟩ := eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp hbound)
  filter_upwards [Ioo_mem_nhdsGT hδ] with ρ ⟨hρ0, hρδ⟩
  rintro _ ⟨x, ⟨hxs, hxD⟩, rfl⟩
  have hdist_x : ‖x - x₀‖ ≤ ρ := by
    have h1 : ‖x - (x₀ + (ρ / 2) • u)‖ ≤ (η / 4) * ρ := by simpa [dist_eq_norm] using hxD
    calc ‖x - x₀‖ = ‖(x - (x₀ + (ρ / 2) • u)) + (ρ / 2) • u‖ := by abel_nf
      _ ≤ ‖x - (x₀ + (ρ / 2) • u)‖ + ‖(ρ / 2) • u‖ := norm_add_le _ _
      _ ≤ (η / 4) * ρ + (ρ / 2) * 1 := by
          gcongr; rw [norm_smul, Real.norm_of_nonneg (by positivity), hu]
      _ ≤ ρ := by nlinarith
  have hxδ : x ∈ ball x₀ δ := mem_ball.mpr (by simpa [dist_eq_norm] using hdist_x.trans_lt hρδ)
  have herr := hδb x hxδ hxs
  have herr1 : ‖f x - f x₀ - A (x - x₀)‖ ≤ 1 * ‖x - x₀‖ :=
    herr.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _))
  have herr2 : ‖f x - f x₀ - A (x - x₀)‖ ≤ (d / 16) * ρ :=
    herr.trans ((mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)).trans
      (by gcongr))
  have hfx_dist : dist (f x) (f x₀) ≤ C * ρ := by
    rw [dist_eq_norm, hC]
    calc ‖f x - f x₀‖ = ‖(f x - f x₀ - A (x - x₀)) + A (x - x₀)‖ := by abel_nf
      _ ≤ ‖f x - f x₀ - A (x - x₀)‖ + ‖A (x - x₀)‖ := norm_add_le _ _
      _ ≤ 1 * ‖x - x₀‖ + ‖A‖ * ‖x - x₀‖ := by gcongr; exact A.le_opNorm _
      _ = (‖A‖ + 1) * ‖x - x₀‖ := by ring
      _ ≤ (‖A‖ + 1) * ρ := by gcongr
  refine ⟨⟨hsub (mem_image_of_mem f hxs), mem_closedBall.mpr hfx_dist⟩, ?_⟩
  have hAy : ‖A (x - (x₀ + (ρ / 2) • u))‖ ≤ (d / 8) * ρ := by
    have hy : ‖x - (x₀ + (ρ / 2) • u)‖ ≤ (η / 4) * ρ := by simpa [dist_eq_norm] using hxD
    calc ‖A (x - (x₀ + (ρ / 2) • u))‖ ≤ ‖A‖ * ((η / 4) * ρ) :=
          (A.le_opNorm _).trans (by gcongr)
      _ = (η * ‖A‖) * (ρ / 4) := by ring
      _ ≤ (d / 2) * (ρ / 4) := by gcongr
      _ = (d / 8) * ρ := by ring
  have hdiff : ‖(f x - f x₀) - (ρ / 2) • A u‖ ≤ (3 / 16) * d * ρ := by
    have hdecomp : (f x - f x₀) - (ρ / 2) • A u =
        (f x - f x₀ - A (x - x₀)) + A (x - (x₀ + (ρ / 2) • u)) := by
      simp [map_sub, map_add, map_smul]; abel
    rw [hdecomp]
    exact (norm_add_le _ _).trans (by linarith)
  have hlip := (lipschitz_infDist_pt (Q : Set V)).dist_le_mul (f x - f x₀) ((ρ / 2) • A u)
  rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm,
    infDist_smul_of_nonneg Q (by positivity), ← hd] at hlip
  have hinf : (5 / 16) * d * ρ ≤ infDist (f x - f x₀) (Q : Set V) := by
    have := neg_le_of_abs_le hlip
    linarith
  have hC0 : (0 : ℝ) < C := by rw [hC]; positivity
  have hcone_lhs : (d / (16 * C)) * dist (f x) (f x₀) ≤ (d / 16) * ρ := by
    calc (d / (16 * C)) * dist (f x) (f x₀) ≤ (d / (16 * C)) * (C * ρ) := by gcongr
      _ = (d / 16) * ρ := by field_simp
  linarith [mul_pos hd0 hρ0]

/-- **Patchwise lower bound on approximate tangent planes.** Let `f : U → V` have derivative `A`
within `s` at `x₀` with `AntilipschitzWith L (s.domRestrict f)` and `f '' s ⊆ E`. If `s` has
Lebesgue density `1` at `x₀` and `E` has `(dim U)`-density zero outside every cone around a
submodule `Q ≤ V` at `f x₀`, then `range A ≤ Q`. Neither measurability of `s` nor a forward
Lipschitz condition on `f` is assumed. -/
theorem range_le_of_tendsto_outside_cone {f : U → V} {s : Set U} {A : U →L[ℝ] V} {x₀ : U}
    {L : ℝ≥0} {E : Set V} {Q : Submodule ℝ V} (hf : HasFDerivWithinAt f A s x₀)
    (hi : AntilipschitzWith L (s.domRestrict f)) (hsub : f '' s ⊆ E)
    (hdens : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall (0 : U) r))
      (𝓝[>] 0) (𝓝 1))
    (hQ : ∀ ε > (0 : ℝ), Tendsto (fun r =>
      μHE[finrank ℝ U] {z ∈ E ∩ closedBall (f x₀) r |
        ε * dist z (f x₀) < infDist (z - f x₀) (Q : Set V)} /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0)) :
    LinearMap.range A.toLinearMap ≤ Q := by
  by_contra hnot
  obtain ⟨_, ⟨v, rfl⟩, hvQ⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hv0 : v ≠ 0 := fun h => hvQ (by simp [h])
  let u : U := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := norm_smul_inv_norm hv0
  have hAu : A u ∉ Q := fun h => hvQ (by
    have : v = ‖v‖ • u := by simp [u, smul_smul, norm_ne_zero_iff.mpr hv0]
    rw [this, ContinuousLinearMap.coe_coe, map_smul]
    exact Q.smul_mem _ h)
  have : Nontrivial U := ⟨⟨u, 0, fun h => by simp [h] at hu⟩⟩
  set d := infDist (A u) (Q : Set V) with hd_def
  have hd0 : 0 < d :=
    (Q.isClosed_of_finiteDimensional.notMem_iff_infDist_pos ⟨0, Q.zero_mem⟩).mp hAu
  set η : ℝ := min (1 / 2) (d / (2 * (‖A‖ + 1)))
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hη_half : η ≤ 1 / 2 := min_le_left _ _
  have hηA : η * ‖A‖ ≤ d / 2 := by
    calc η * ‖A‖ ≤ (d / (2 * (‖A‖ + 1))) * (‖A‖ + 1) := by
          gcongr
          · exact min_le_right _ _
          · linarith
      _ = d / 2 := by field_simp
  let C : ℝ≥0 := ⟨‖A‖ + 1, by positivity⟩
  have hC : (C : ℝ) = ‖A‖ + 1 := rfl
  have hC0 : 0 < C := NNReal.coe_pos.mp (by positivity : (0 : ℝ) < ‖A‖ + 1)
  let L' : ℝ≥0 := max L 1
  have hi' : AntilipschitzWith L' (s.domRestrict f) := fun x y =>
    (hi x y).trans (by gcongr; exact le_max_left L 1)
  set D : ℝ → Set U := fun ρ => closedBall (x₀ + (ρ / 2) • u) ((η / 4) * ρ)
  set α : ℝ≥0∞ := ENNReal.ofReal (η / 4) ^ finrank ℝ U
  have hα0 : 0 < α := ENNReal.pow_pos (ENNReal.ofReal_pos.mpr (by positivity)) _
  -- First show `volume (s ∩ D ρ) / volume (closedBall 0 ρ) → 0` via the cone-density hypothesis.
  have hD_zero : Tendsto (fun ρ => volume (s ∩ D ρ) / volume (closedBall (0 : U) ρ))
      (𝓝[>] 0) (𝓝 0) := by
    have hcone_C : Tendsto (fun ρ =>
        μHE[finrank ℝ U] {z ∈ E ∩ closedBall (f x₀) (C * ρ) |
          (d / (16 * C)) * dist z (f x₀) < infDist (z - f x₀) (Q : Set V)} /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) (C * ρ)))
        (𝓝[>] 0) (𝓝 0) :=
      (hQ (d / (16 * C)) (by rw [hC]; positivity)).comp
        (tendsto_iff_comap.2 (comap_mulLeft_nhdsGT_zero (NNReal.coe_pos.2 hC0)).ge)
    have hmul := ENNReal.Tendsto.const_mul hcone_C
      (Or.inr (ENNReal.pow_ne_top (ENNReal.coe_ne_top (r := L' * C)) (n := finrank ℝ U)))
    rw [mul_zero] at hmul
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmul
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_mem_nhdsWithin,
      hf.image_inter_shiftedBall_subset_outside_cone hsub hu hd0 hd_def hη_half hηA] with ρ hρ0 hinc
    rw [volume_closedBall_eq_euclidean (0 : U) ρ]
    calc volume (s ∩ D ρ) / volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) ρ)
        ≤ (L' : ℝ≥0∞) ^ finrank ℝ U * μHE[finrank ℝ U] (f '' (s ∩ D ρ)) /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) ρ) := by
          gcongr
          exact volume_le_mul_euclideanHausdorffMeasure_image_of_antilipschitzWith hi'
            inter_subset_left
      _ ≤ (L' : ℝ≥0∞) ^ finrank ℝ U *
          μHE[finrank ℝ U] {z ∈ E ∩ closedBall (f x₀) (C * ρ) |
            (d / (16 * C)) * dist z (f x₀) < infDist (z - f x₀) (Q : Set V)} /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) ρ) := by
          gcongr
      _ = ((L' * C : ℝ≥0) : ℝ≥0∞) ^ finrank ℝ U *
          (μHE[finrank ℝ U] {z ∈ E ∩ closedBall (f x₀) (C * ρ) |
            (d / (16 * C)) * dist z (f x₀) < infDist (z - f x₀) (Q : Set V)} /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) (C * ρ))) := by
          rw [mul_div_assoc, div_volume_closedBall_eq_pow_mul (finrank ℝ U) _ hC0 hρ0.le]
          push_cast
          ring
  -- On the other hand, Lebesgue density `1` at `x₀` forces `1 + α ≤ 0 + 1`.
  have hineq : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      volume (s ∩ closedBall x₀ ρ) / volume (closedBall (0 : U) ρ) + α ≤
        volume (s ∩ D ρ) / volume (closedBall (0 : U) ρ) + 1 := by
    filter_upwards [eventually_mem_nhdsWithin] with ρ (hρ0 : 0 < ρ)
    have hD_sub : D ρ ⊆ closedBall x₀ ρ := fun x hx => by
      rw [mem_closedBall] at hx ⊢
      calc dist x x₀ ≤ dist x (x₀ + (ρ / 2) • u) + dist (x₀ + (ρ / 2) • u) x₀ := dist_triangle _ _ _
        _ ≤ (η / 4) * ρ + (ρ / 2) * 1 := by
            gcongr; simp [dist_eq_norm, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ ρ / 2),
              hu]
        _ ≤ ρ := by nlinarith
    have hV0_pos : 0 < volume (closedBall (0 : U) ρ) := measure_closedBall_pos volume 0 hρ0
    have hV0_top : volume (closedBall (0 : U) ρ) ≠ ∞ := measure_closedBall_lt_top.ne
    have hvolD : volume (D ρ) = α * volume (closedBall (0 : U) ρ) := by
      rw [addHaar_closedBall_center, addHaar_closedBall_mul volume 0 (by positivity) hρ0.le,
        ENNReal.ofReal_pow (by positivity)]
    have hvol_split : volume (closedBall x₀ ρ \ D ρ) + α * volume (closedBall (0 : U) ρ) =
        volume (closedBall (0 : U) ρ) := by
      rw [← hvolD, ← measure_union disjoint_sdiff_self_left measurableSet_closedBall,
        sdiff_union_of_subset hD_sub, addHaar_closedBall_center]
    have hcov : s ∩ closedBall x₀ ρ ⊆ (s ∩ D ρ) ∪ (closedBall x₀ ρ \ D ρ) := fun x ⟨hxs, hxB⟩ =>
      by_cases (fun hxD : x ∈ D ρ => Or.inl ⟨hxs, hxD⟩) (fun hxD => Or.inr ⟨hxB, hxD⟩)
    have hadd : volume (s ∩ closedBall x₀ ρ) + α * volume (closedBall (0 : U) ρ) ≤
        volume (s ∩ D ρ) + volume (closedBall (0 : U) ρ) := by
      calc volume (s ∩ closedBall x₀ ρ) + α * volume (closedBall (0 : U) ρ)
          ≤ (volume (s ∩ D ρ) + volume (closedBall x₀ ρ \ D ρ)) +
              α * volume (closedBall (0 : U) ρ) := by
            gcongr; exact (measure_mono hcov).trans (measure_union_le _ _)
        _ = volume (s ∩ D ρ) + volume (closedBall (0 : U) ρ) := by
            rw [add_assoc, hvol_split]
    have hdiv := ENNReal.div_le_div_right hadd (volume (closedBall (0 : U) ρ))
    rwa [ENNReal.add_div, ENNReal.add_div,
      ENNReal.mul_div_cancel_right hV0_pos.ne' hV0_top,
      ENNReal.div_self hV0_pos.ne' hV0_top] at hdiv
  have h1α : 1 + α ≤ 0 + 1 :=
    le_of_tendsto_of_tendsto (hdens.add tendsto_const_nhds) (hD_zero.add tendsto_const_nhds) hineq
  have hα_le : α ≤ 0 :=
    (ENNReal.add_le_add_iff_left ENNReal.one_ne_top).mp
      (by simpa only [zero_add, add_zero] using h1α)
  exact not_le_of_gt hα0 hα_le

/-- **Patchwise uniqueness of the cone-density-zero plane.** Under the hypotheses of
`HasFDerivWithinAt.range_le_of_tendsto_outside_cone`, if `A` is injective and
`finrank ℝ Q ≤ finrank ℝ U`, then `Q = range A`. -/
theorem eq_range_of_tendsto_outside_cone {f : U → V} {s : Set U} {A : U →L[ℝ] V} {x₀ : U}
    {L : ℝ≥0} {E : Set V} {Q : Submodule ℝ V} (hf : HasFDerivWithinAt f A s x₀)
    (hinj : Injective A) (hi : AntilipschitzWith L (s.domRestrict f)) (hsub : f '' s ⊆ E)
    (hdens : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall (0 : U) r))
      (𝓝[>] 0) (𝓝 1))
    (hQdim : finrank ℝ Q ≤ finrank ℝ U)
    (hQ : ∀ ε > (0 : ℝ), Tendsto (fun r =>
      μHE[finrank ℝ U] {z ∈ E ∩ closedBall (f x₀) r |
        ε * dist z (f x₀) < infDist (z - f x₀) (Q : Set V)} /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0)) :
    Q = LinearMap.range A.toLinearMap :=
  (Submodule.eq_of_le_of_finrank_le (hf.range_le_of_tendsto_outside_cone hi hsub hdens hQ)
    (hQdim.trans_eq (LinearMap.finrank_range_of_inj hinj).symm)).symm

omit [FiniteDimensional ℝ V] in
/-- On an inverse-Lipschitz patch `f '' s ⊆ E`, relative differentiability at a Lebesgue
density-one parameter `x₀` guarantees positive upper `(dim U)`-density of `E` at `f x₀`. No forward
Lipschitz condition on `f` or measurability of `s` is needed. -/
theorem limsup_euclideanHausdorffMeasure_inter_closedBall_div_pos {f : U → V} {s : Set U}
    {A : U →L[ℝ] V} {x₀ : U} {L : ℝ≥0} {E : Set V} (hf : HasFDerivWithinAt f A s x₀)
    (hi : AntilipschitzWith L (s.domRestrict f)) (hsub : f '' s ⊆ E)
    (hdens : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall (0 : U) r))
      (𝓝[>] 0) (𝓝 1)) :
    0 < limsup (fun r => μHE[finrank ℝ U] (E ∩ closedBall (f x₀) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) := by
  by_contra! hle
  rw [nonpos_iff_eq_zero] at hle
  have htend0 : Tendsto (fun r => μHE[finrank ℝ U] (E ∩ closedBall (f x₀) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_of_le_liminf_of_limsup_le zero_le hle.le
  let C : ℝ≥0 := ⟨‖A‖ + 1, by positivity⟩
  have hC : (C : ℝ) = ‖A‖ + 1 := rfl
  have hC0 : 0 < C := NNReal.coe_pos.mp (by positivity : (0 : ℝ) < ‖A‖ + 1)
  let L' : ℝ≥0 := max L 1
  have hi' : AntilipschitzWith L' (s.domRestrict f) := fun x y =>
    (hi x y).trans (by gcongr; exact le_max_left L 1)
  have hbound := hf.isLittleO.bound zero_lt_one
  obtain ⟨δ, hδ, hδb⟩ := eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp hbound)
  have hcomp := ENNReal.Tendsto.const_mul
    (htend0.comp (tendsto_iff_comap.2 (comap_mulLeft_nhdsGT_zero (NNReal.coe_pos.2 hC0)).ge))
    (Or.inr (ENNReal.pow_ne_top (ENNReal.coe_ne_top (r := L' * C)) (n := finrank ℝ U)))
  rw [mul_zero] at hcomp
  have hdens0 : Tendsto (fun ρ => volume (s ∩ closedBall x₀ ρ) / volume (closedBall (0 : U) ρ))
      (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcomp
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with ρ ⟨hρ0, hρδ⟩
    have hinc : f '' (s ∩ closedBall x₀ ρ) ⊆ E ∩ closedBall (f x₀) (C * ρ) := by
      rintro _ ⟨x, ⟨hxs, hxB⟩, rfl⟩
      refine ⟨hsub (mem_image_of_mem f hxs), mem_closedBall.mpr ?_⟩
      have hxδ : x ∈ ball x₀ δ := mem_ball.mpr ((mem_closedBall.mp hxB).trans_lt hρδ)
      have herr := hδb x hxδ hxs
      rw [dist_eq_norm]
      calc ‖f x - f x₀‖ = ‖(f x - f x₀ - A (x - x₀)) + A (x - x₀)‖ := by abel_nf
        _ ≤ ‖f x - f x₀ - A (x - x₀)‖ + ‖A (x - x₀)‖ := norm_add_le _ _
        _ ≤ 1 * ‖x - x₀‖ + ‖A‖ * ‖x - x₀‖ := by gcongr; exact A.le_opNorm _
        _ = C * dist x x₀ := by rw [hC, dist_eq_norm]; ring
        _ ≤ C * ρ := by gcongr; exact mem_closedBall.mp hxB
    rw [volume_closedBall_eq_euclidean (0 : U) ρ]
    calc volume (s ∩ closedBall x₀ ρ) /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) ρ)
        ≤ (L' : ℝ≥0∞) ^ finrank ℝ U * μHE[finrank ℝ U] (f '' (s ∩ closedBall x₀ ρ)) /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) ρ) := by
          gcongr
          exact volume_le_mul_euclideanHausdorffMeasure_image_of_antilipschitzWith hi'
            inter_subset_left
      _ ≤ (L' : ℝ≥0∞) ^ finrank ℝ U * μHE[finrank ℝ U] (E ∩ closedBall (f x₀) (C * ρ)) /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) ρ) := by
          gcongr
      _ = ((L' * C : ℝ≥0) : ℝ≥0∞) ^ finrank ℝ U *
          (μHE[finrank ℝ U] (E ∩ closedBall (f x₀) (C * ρ)) /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) (C * ρ))) := by
          rw [mul_div_assoc, div_volume_closedBall_eq_pow_mul (finrank ℝ U) _ hC0 hρ0.le]
          push_cast
          ring
  exact one_ne_zero (tendsto_nhds_unique hdens hdens0)

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V] [MeasurableSpace U] [BorelSpace U] in
/-- On an inverse-Lipschitz patch `f '' s`, if `f` has derivative `A` within `s` at `x₀ ∈ s` and
`E \ f '' s` has `(dim U)`-density zero at `f x₀`, then `E` has `(dim U)`-density zero outside
every cone around `range A` at `f x₀`. -/
theorem tendsto_outside_cone_range {f : U → V} {s : Set U} {A : U →L[ℝ] V} {x₀ : U}
    {L : ℝ≥0} {E : Set V} (hf : HasFDerivWithinAt f A s x₀)
    (hi : AntilipschitzWith L (s.domRestrict f)) (hx₀ : x₀ ∈ s)
    (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f x₀) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0)) :
    ∀ ε > (0 : ℝ), Tendsto (fun r =>
      μHE[finrank ℝ U] {z ∈ E ∩ closedBall (f x₀) r |
        ε * dist z (f x₀) < infDist (z - f x₀) (LinearMap.range A.toLinearMap : Set V)} /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0) := by
  intro ε hε
  have hL1 : 0 < (L : ℝ) + 1 := by positivity
  set η : ℝ := ε / ((L : ℝ) + 1)
  obtain ⟨δ, hδ, hδb⟩ := eventually_nhds_iff_ball.mp
    (eventually_nhdsWithin_iff.mp (hf.isLittleO.bound (div_pos hε hL1)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdiff
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hL1)] with r ⟨_, hrδ⟩
  gcongr
  rintro z ⟨⟨hzE, hzr⟩, hzcone⟩
  refine ⟨⟨hzE, ?_⟩, hzr⟩
  rintro ⟨x, hxs, rfl⟩
  have hdx : dist x x₀ ≤ L * dist (f x) (f x₀) := by
    simpa [Subtype.dist_eq] using hi.le_mul_dist ⟨x, hxs⟩ ⟨x₀, hx₀⟩
  have hxδ : x ∈ ball x₀ δ := by
    rw [mem_ball]
    have hfxr : dist (f x) (f x₀) ≤ r := mem_closedBall.mp hzr
    calc dist x x₀ ≤ L * dist (f x) (f x₀) := hdx
      _ ≤ ((L : ℝ) + 1) * r := by nlinarith [L.coe_nonneg, dist_nonneg (x := f x) (y := f x₀)]
      _ < δ := (lt_div_iff₀' hL1).mp hrδ
  have herr := hδb x hxδ hxs
  have hinf : infDist (f x - f x₀) (LinearMap.range A.toLinearMap : Set V) ≤
      ε * dist (f x) (f x₀) :=
    calc infDist (f x - f x₀) (LinearMap.range A.toLinearMap : Set V)
        ≤ dist (f x - f x₀) (A (x - x₀)) := infDist_le_dist_of_mem ⟨x - x₀, rfl⟩
      _ = ‖f x - f x₀ - A (x - x₀)‖ := by rw [dist_eq_norm]
      _ ≤ η * ‖x - x₀‖ := herr
      _ ≤ η * (L * dist (f x) (f x₀)) := by gcongr; rwa [← dist_eq_norm]
      _ ≤ η * (((L : ℝ) + 1) * dist (f x) (f x₀)) := by gcongr; linarith
      _ = ε * dist (f x) (f x₀) := by
          dsimp [η]
          rw [← mul_assoc, div_mul_cancel₀ _ hL1.ne']
  exact hzcone.not_ge hinf

end HasFDerivWithinAt

/-! ### Approximate tangent planes, canonical plane and projection, and rectifiable uniqueness -/

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {k : ℕ} {E E₁ E₂ : Set V}

/-- A `k`-dimensional subspace `P ≤ V` is an **approximate tangent `k`-plane** to `E` at `x`
(Mattila, Definition 15.17) if `E` has positive upper `k`-dimensional density at `x` and the
portion of `E` outside every cone around `P` has `k`-dimensional density zero at `x`. -/
structure IsApproximateTangentPlane (k : ℕ) (E : Set V) (x : V) (P : Submodule ℝ V) : Prop where
  /-- `P` has dimension `k`. -/
  finrank_eq : finrank ℝ P = k
  /-- `E` has positive upper `k`-dimensional density at `x`. -/
  limsup_pos : 0 < limsup (fun r =>
    μHE[k] (E ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0)
  /-- Outside every cone around `P`, `E` has `k`-dimensional density zero at `x`. -/
  tendsto_outside_cone : ∀ ε > (0 : ℝ), Tendsto (fun r =>
    μHE[k] {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)

namespace IsApproximateTangentPlane

/-- In dimension zero, any approximate tangent plane is `⊥`. -/
theorem eq_bot {x : V} {P : Submodule ℝ V} (h : IsApproximateTangentPlane 0 E x P) : P = ⊥ := by
  have := finrank_zero_iff.mp h.finrank_eq
  exact Submodule.eq_bot_of_subsingleton

omit [FiniteDimensional ℝ V] in
/-- Modifying `E` by a `μHE[k]`-null set preserves approximate tangent planes at every point `x`. -/
theorem congr_ae (h : E₁ =ᵐ[μHE[k]] E₂) {x : V} {P : Submodule ℝ V} :
    IsApproximateTangentPlane k E₁ x P ↔ IsApproximateTangentPlane k E₂ x P := by
  have hnull : μHE[k] (E₁ ∆ E₂) = 0 := measure_symmDiff_eq_zero_iff.mpr h
  have hmeas_eq (S : Set V) : μHE[k] (E₁ ∩ S) = μHE[k] (E₂ ∩ S) := by
    apply measure_congr
    rw [← measure_symmDiff_eq_zero_iff]
    exact measure_mono_null (fun z hz => by
      simp only [mem_symmDiff, mem_inter_iff] at hz ⊢; tauto) hnull
  have hcone_eq (ε r : ℝ) :
      μHE[k] {z ∈ E₁ ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} =
        μHE[k] {z ∈ E₂ ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} := by
    apply measure_congr
    rw [← measure_symmDiff_eq_zero_iff]
    exact measure_mono_null (fun z hz => by
      simp only [mem_symmDiff, mem_ofPred_eq, mem_inter_iff] at hz ⊢; tauto) hnull
  constructor <;> rintro ⟨hd, hl, hc⟩ <;> refine ⟨hd, ?_, fun ε hε => ?_⟩
  · simpa only [hmeas_eq] using hl
  · simpa only [hcone_eq] using hc ε hε
  · simpa only [← hmeas_eq] using hl
  · simpa only [← hcone_eq] using hc ε hε

omit [FiniteDimensional ℝ V] in
/-- Approximate tangent planes depend only on the germ of `E` at `x`. -/
theorem congr_nhds {x : V} (h : E₁ =ᶠ[𝓝 x] E₂) {P : Submodule ℝ V} :
    IsApproximateTangentPlane k E₁ x P ↔ IsApproximateTangentPlane k E₂ x P := by
  obtain ⟨δ, hδ, hδeq⟩ := Metric.eventually_nhds_iff.mp h
  have hinter (r : ℝ) (hr : r < δ) : E₁ ∩ closedBall x r = E₂ ∩ closedBall x r := by
    ext z
    simp only [mem_inter_iff, mem_closedBall]
    exact and_congr_left fun hzr => by simpa using hδeq (hzr.trans_lt hr)
  have hev_ball :
      (fun r => μHE[k] (E₁ ∩ closedBall x r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) =ᶠ[𝓝[>] 0]
      (fun r => μHE[k] (E₂ ∩ closedBall x r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with r ⟨_, hr⟩
    rw [hinter r hr]
  have hev_cone (ε : ℝ) :
      (fun r => μHE[k] {z ∈ E₁ ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) =ᶠ[𝓝[>] 0]
      (fun r => μHE[k] {z ∈ E₂ ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with r ⟨_, hr⟩
    simp only [hinter r hr]
  constructor <;> rintro ⟨hd, hl, hc⟩ <;> refine ⟨hd, ?_, fun ε hε => ?_⟩
  · rwa [← limsup_congr hev_ball]
  · exact (hc ε hε).congr' (hev_cone ε)
  · rwa [limsup_congr hev_ball]
  · exact (hc ε hε).congr' (hev_cone ε).symm

end IsApproximateTangentPlane

open Classical in
/-- The canonical approximate tangent `k`-plane to `E` at `x`: the chosen plane when one exists,
and `⊥` otherwise. When the approximate tangent `k`-plane is unique (in particular, `μHE[k]`-almost
everywhere on a null-measurable countably `k`-rectifiable set with locally finite `μHE[k]` measure),
this equals that unique plane. -/
noncomputable def approximateTangentPlane (k : ℕ) (E : Set V) (x : V) : Submodule ℝ V :=
  if h : ∃ P : Submodule ℝ V, IsApproximateTangentPlane k E x P then h.choose else ⊥

/-- The orthogonal projection onto `TauCeti.approximateTangentPlane k E x`. -/
noncomputable def approximateTangentProjection (k : ℕ) (E : Set V) (x : V) : V →L[ℝ] V :=
  (approximateTangentPlane k E x).starProjection

/-- `approximateTangentProjection k E x` is the orthogonal projection onto
`approximateTangentPlane k E x`. -/
theorem approximateTangentProjection_eq (k : ℕ) (E : Set V) (x : V) :
    approximateTangentProjection k E x = (approximateTangentPlane k E x).starProjection := by
  unfold approximateTangentProjection; rfl

omit [FiniteDimensional ℝ V] in
/-- If `P` is the unique approximate tangent `k`-plane to `E` at `x`, then
`approximateTangentPlane k E x = P`. -/
theorem IsApproximateTangentPlane.approximateTangentPlane_eq {x : V} {P : Submodule ℝ V}
    (hP : IsApproximateTangentPlane k E x P)
    (huniq : ∀ Q, IsApproximateTangentPlane k E x Q → Q = P) :
    approximateTangentPlane k E x = P := by
  have hex : ∃ Q, IsApproximateTangentPlane k E x Q := ⟨P, hP⟩
  simp only [approximateTangentPlane, hex, ↓reduceDIte]
  exact huniq _ hex.choose_spec

/-- If `P` is the unique approximate tangent `k`-plane to `E` at `x`, then
`approximateTangentProjection k E x = P.starProjection`. -/
theorem IsApproximateTangentPlane.approximateTangentProjection_eq {x : V} {P : Submodule ℝ V}
    (hP : IsApproximateTangentPlane k E x P)
    (huniq : ∀ Q, IsApproximateTangentPlane k E x Q → Q = P) :
    approximateTangentProjection k E x = P.starProjection := by
  simp only [approximateTangentProjection, hP.approximateTangentPlane_eq huniq]

omit [FiniteDimensional ℝ V] in
/-- When an approximate tangent `k`-plane to `E` at `x` exists, `approximateTangentPlane k E x`
satisfies `IsApproximateTangentPlane`. -/
theorem isApproximateTangentPlane_approximateTangentPlane {x : V}
    (h : ∃ P : Submodule ℝ V, IsApproximateTangentPlane k E x P) :
    IsApproximateTangentPlane k E x (approximateTangentPlane k E x) := by
  simp only [approximateTangentPlane, h, ↓reduceDIte]
  exact h.choose_spec

/-- In dimension zero, `approximateTangentPlane 0 E x` is always `⊥`. -/
@[simp]
theorem approximateTangentPlane_zero (E : Set V) (x : V) :
    approximateTangentPlane 0 E x = ⊥ := by
  by_cases h : ∃ P : Submodule ℝ V, IsApproximateTangentPlane 0 E x P
  · exact (isApproximateTangentPlane_approximateTangentPlane h).eq_bot
  · simp [approximateTangentPlane, h]

/-- In dimension zero, `approximateTangentProjection 0 E x` is always `0`. -/
@[simp]
theorem approximateTangentProjection_zero (E : Set V) (x : V) :
    approximateTangentProjection 0 E x = 0 := by
  simp [approximateTangentProjection]

omit [FiniteDimensional ℝ V] in
/-- Modifying `E` by a `μHE[k]`-null set leaves `approximateTangentPlane k E x` unchanged at every
point `x`. -/
theorem approximateTangentPlane_congr_ae (h : E₁ =ᵐ[μHE[k]] E₂) (x : V) :
    approximateTangentPlane k E₁ x = approximateTangentPlane k E₂ x := by
  have hpred : IsApproximateTangentPlane k E₁ x = IsApproximateTangentPlane k E₂ x :=
    funext fun _ => propext (IsApproximateTangentPlane.congr_ae h)
  exact congrArg (fun p : Submodule ℝ V → Prop =>
    by classical exact if h : ∃ P, p P then h.choose else ⊥) hpred

/-- Modifying `E` by a `μHE[k]`-null set leaves `approximateTangentProjection k E x` unchanged at
every point `x`. -/
theorem approximateTangentProjection_congr_ae (h : E₁ =ᵐ[μHE[k]] E₂) (x : V) :
    approximateTangentProjection k E₁ x = approximateTangentProjection k E₂ x := by
  simp only [approximateTangentProjection, approximateTangentPlane_congr_ae h]

omit [FiniteDimensional ℝ V] in
/-- `approximateTangentPlane k E x` depends only on the germ of `E` at `x`. -/
theorem approximateTangentPlane_congr_nhds {x : V} (h : E₁ =ᶠ[𝓝 x] E₂) :
    approximateTangentPlane k E₁ x = approximateTangentPlane k E₂ x := by
  have hpred : IsApproximateTangentPlane k E₁ x = IsApproximateTangentPlane k E₂ x :=
    funext fun _ => propext (IsApproximateTangentPlane.congr_nhds h)
  exact congrArg (fun p : Submodule ℝ V → Prop =>
    by classical exact if h : ∃ P, p P then h.choose else ⊥) hpred

/-- `approximateTangentProjection k E x` depends only on the germ of `E` at `x`. -/
theorem approximateTangentProjection_congr_nhds {x : V} (h : E₁ =ᶠ[𝓝 x] E₂) :
    approximateTangentProjection k E₁ x = approximateTangentProjection k E₂ x := by
  simp only [approximateTangentProjection, approximateTangentPlane_congr_nhds h]

/-- **Existence of approximate tangent planes.** At almost every point of a null-measurable,
countably `k`-rectifiable set with locally finite `μHE[k]` measure, there is a `k`-plane such
that the part of the set outside every cone about that plane has `k`-dimensional density zero. -/
theorem CountablyRectifiable.ae_exists_submodule_tendsto_measure_outside_cone_div
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∀ᵐ x ∂μHE[k], x ∈ E → ∃ P : Submodule ℝ V, finrank ℝ P = k ∧
      ∀ ε > (0 : ℝ), Tendsto (fun r =>
        μHE[k] {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨Q, _, hQ⟩ := hE.exists_measurable_approximate_tangent_projection hEm
  filter_upwards [hQ] with x hx hxE
  obtain ⟨P, hdim, _, hP⟩ := hx hxE
  exact ⟨P, hdim, hP⟩

/-- **Almost-everywhere existence and uniqueness of the cone-density-zero `k`-plane.** At
`μHE[k]`-almost every point of a null-measurable, countably `k`-rectifiable set `E` with locally
finite `μHE[k]` measure, there is a unique `k`-plane outside whose every cone `E` has
`k`-dimensional density zero. -/
theorem CountablyRectifiable.ae_existsUnique_submodule_tendsto_measure_outside_cone_div
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∀ᵐ x ∂μHE[k], x ∈ E → ∃! P : Submodule ℝ V, finrank ℝ P = k ∧
      ∀ ε > (0 : ℝ), Tendsto (fun r =>
        μHE[k] {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨A, f, _, hbi, hcover⟩ := hE.exists_bilipschitz_cover
  choose K L hLip hAnti using hbi
  let s (n : ℕ) : Set (EuclideanSpace ℝ (Fin k)) := A n ∩ (f n) ⁻¹' E
  have hs_anti (n : ℕ) : AntilipschitzWith (L n) ((s n).domRestrict (f n)) := fun u v =>
    (hAnti n) ⟨u, u.2.1⟩ ⟨v, v.2.1⟩
  have hs_sub (n : ℕ) : f n '' s n ⊆ E := by rintro _ ⟨u, hu, rfl⟩; exact hu.2
  -- Stage 1: on each bi-Lipschitz patch `f n '' s n`, almost every image point comes from a
  -- regular parameter `u` at which `s n` has Lebesgue density `1`.
  have hpatch (n : ℕ) : ∀ᵐ x ∂μHE[k], x ∈ f n '' s n →
      ∃ u ∈ s n, f n u = x ∧ DifferentiableAt ℝ (f n) u ∧ Injective (fderiv ℝ (f n) u) ∧
        Tendsto (fun r => volume (s n ∩ closedBall u r) /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1) := by
    let S := {u | ¬ Tendsto (fun r => volume (s n ∩ closedBall u r) /
      volume (closedBall u r)) (𝓝[>] 0) (𝓝 1)}
    let badD := {u ∈ s n | u ∈ S}
    have hbadD_vol : volume badD = 0 := by
      have h : volume.restrict (s n) S = 0 :=
        ae_iff.mp (Besicovitch.ae_tendsto_measure_inter_div volume (s n))
      have hN := nonpos_iff_eq_zero.mp ((le_restrict_apply (s n) S).trans_eq h)
      refine measure_mono_null ?_ hN
      exact fun _ hu => ⟨hu.2, hu.1⟩
    have hbadD_img : μHE[k] (f n '' badD) = 0 := by
      have hle :=
        (LipschitzWith.lipschitzOnWith (hLip n)).euclideanHausdorffMeasure_image_le k (s := badD)
      simpa only [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hbadD_vol, mul_zero,
        nonpos_iff_eq_zero] using hle
    have hreg : μHE[k] (f n '' {u | DifferentiableAt ℝ (f n) u ∧
        (fderiv ℝ (f n) u).toLinearMap.normDet ≠ 0}ᶜ) = 0 := by
      simpa only [finrank_euclideanSpace_fin] using
        LipschitzWith.euclideanHausdorffMeasure_image_compl_setOf_regular (hLip n)
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hbadD_img,
      measure_eq_zero_iff_ae_notMem.mp hreg] with x hxD hxR
    rintro ⟨u, hu, rfl⟩
    have huR : DifferentiableAt ℝ (f n) u ∧ (fderiv ℝ (f n) u).toLinearMap.normDet ≠ 0 :=
      not_not.mp fun h => hxR ⟨u, h, rfl⟩
    have huD : Tendsto (fun r => volume (s n ∩ closedBall u r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1) := by
      have := not_not.mp fun h => hxD ⟨u, ⟨hu, h⟩, rfl⟩
      simpa only [addHaar_closedBall_center] using this
    exact ⟨u, hu, rfl, huR.1,
      ((fderiv ℝ (f n) u).toLinearMap.normDet_ne_zero_tfae.out 1 5).mp huR.2, huD⟩
  -- Stage 2: combine existence with patchwise identification `Q = range (fderiv ℝ (f n) u')`.
  filter_upwards [hE.ae_exists_submodule_tendsto_measure_outside_cone_div hEm,
    measure_eq_zero_iff_ae_notMem.mp hcover, ae_all_iff.mpr hpatch] with x hex hcov hxpatch hxE
  obtain ⟨P, hPdim, hPcone⟩ := hex hxE
  have hxU : x ∈ ⋃ n, f n '' A n := not_not.mp fun h => hcov ⟨hxE, h⟩
  obtain ⟨n, hn⟩ := mem_iUnion.mp hxU
  obtain ⟨u, huA, rfl⟩ := hn
  obtain ⟨u', _, hfu', hdiff, hinj, hdens⟩ := hxpatch n ⟨u, ⟨huA, hxE⟩, rfl⟩
  refine ⟨P, ⟨hPdim, hPcone⟩, fun Q ⟨hQdim, hQcone⟩ => ?_⟩
  have hconv {S : Submodule ℝ V}
      (hc : ∀ ε > (0 : ℝ), Tendsto (fun r =>
        μHE[k] {z ∈ E ∩ closedBall (f n u') r |
          ε * dist z (f n u') < infDist (z - f n u') (S : Set V)} /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)) :
      ∀ ε > (0 : ℝ), Tendsto (fun r =>
        μHE[finrank ℝ (EuclideanSpace ℝ (Fin k))] {z ∈ E ∩ closedBall (f n u') r |
          ε * dist z (f n u') < infDist (z - f n u') (S : Set V)} /
          volume (closedBall (0 : EuclideanSpace ℝ
            (Fin (finrank ℝ (EuclideanSpace ℝ (Fin k))))) r)) (𝓝[>] 0) (𝓝 0) := fun ε hε => by
    simpa only [finrank_euclideanSpace_fin,
      ← volume_closedBall_eq_euclidean (0 : EuclideanSpace ℝ (Fin k))] using hc ε hε
  have hQeq := hdiff.hasFDerivAt.hasFDerivWithinAt.eq_range_of_tendsto_outside_cone hinj
    (hs_anti n) (hs_sub n) hdens
    (by simpa only [finrank_euclideanSpace_fin] using hQdim.le) (hconv (hfu'.symm ▸ hQcone))
  have hPeq := hdiff.hasFDerivAt.hasFDerivWithinAt.eq_range_of_tendsto_outside_cone hinj
    (hs_anti n) (hs_sub n) hdens
    (by simpa only [finrank_euclideanSpace_fin] using hPdim.le) (hconv (hfu'.symm ▸ hPcone))
  exact hQeq.trans hPeq.symm

/-- **Existence and uniqueness of approximate tangent planes.** A null-measurable, countably
`k`-rectifiable set `E` with locally finite `μHE[k]` measure admits a unique approximate tangent
`k`-plane at `μHE[k]`-almost every `x ∈ E`. -/
theorem CountablyRectifiable.ae_existsUnique_isApproximateTangentPlane
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∀ᵐ x ∂μHE[k], x ∈ E → ∃! P : Submodule ℝ V, IsApproximateTangentPlane k E x P := by
  filter_upwards [hE.ae_existsUnique_submodule_tendsto_measure_outside_cone_div hEm,
    hE.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div hEm] with x huniq hdens hxE
  obtain ⟨P, ⟨hPdim, hPcone⟩, hPuniq⟩ := huniq hxE
  have hpos : 0 < limsup (fun r => μHE[k] (E ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) := by
    rw [(hdens hxE).limsup_eq]
    exact zero_lt_one
  exact ⟨P, ⟨hPdim, hpos, hPcone⟩, fun Q hQ => hPuniq Q ⟨hQ.finrank_eq, hQ.tendsto_outside_cone⟩⟩

/-- At `μHE[k]`-almost every point of a null-measurable, countably `k`-rectifiable set `E` with
locally finite `μHE[k]` measure, `approximateTangentPlane k E x` is the unique approximate tangent
`k`-plane to `E` at `x`. -/
theorem CountablyRectifiable.ae_isApproximateTangentPlane_approximateTangentPlane
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∀ᵐ x ∂μHE[k], x ∈ E → IsApproximateTangentPlane k E x (approximateTangentPlane k E x) := by
  filter_upwards [hE.ae_existsUnique_isApproximateTangentPlane hEm] with x hx hxE
  exact isApproximateTangentPlane_approximateTangentPlane (hx hxE).exists

/-- **Measurability of the canonical approximate tangent projection.** For a null-measurable,
countably `k`-rectifiable set `E` with locally finite `μHE[k]` measure,
`approximateTangentProjection k E` is `μHE[k].restrict E`-almost everywhere measurable. -/
theorem CountablyRectifiable.aemeasurable_approximateTangentProjection
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    AEMeasurable (approximateTangentProjection k E) (μHE[k].restrict E) := by
  obtain ⟨Q, hQm, hQ⟩ := hE.exists_measurable_approximate_tangent_projection hEm
  refine hQm.aemeasurable.congr ?_
  rw [EventuallyEq, ae_restrict_iff'₀ hEm]
  filter_upwards [hQ, hE.ae_existsUnique_isApproximateTangentPlane hEm] with x hxQ huniq hxE
  obtain ⟨P, hPdim, hQP, hPcone⟩ := hxQ hxE
  obtain ⟨P₀, hP₀, hP₀uniq⟩ := huniq hxE
  have hPP₀ : P = P₀ := hP₀uniq P ⟨hPdim, hP₀.limsup_pos, hPcone⟩
  rw [hP₀.approximateTangentProjection_eq hP₀uniq, ← hPP₀, hQP]

end TauCeti

namespace HasFDerivWithinAt

open TauCeti

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]

/-- **Characterization of approximate tangent planes on an inverse-Lipschitz patch.** Let
`f : U → V` have injective derivative `A` within `s` at a Lebesgue density-one point `x₀ ∈ s`, with
`AntilipschitzWith L (s.domRestrict f)` and `f '' s ⊆ E`. If `E \ f '' s` has `(dim U)`-density
zero at `f x₀`, then `Q` is an approximate tangent `(dim U)`-plane to `E` at `f x₀` if and only if
`Q = range A`. -/
theorem isApproximateTangentPlane_iff {f : U → V} {s : Set U} {A : U →L[ℝ] V} {x₀ : U}
    {L : ℝ≥0} {E : Set V} {Q : Submodule ℝ V} (hf : HasFDerivWithinAt f A s x₀)
    (hinj : Injective A) (hi : AntilipschitzWith L (s.domRestrict f)) (hx₀ : x₀ ∈ s)
    (hsub : f '' s ⊆ E)
    (hdens : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall (0 : U) r))
      (𝓝[>] 0) (𝓝 1))
    (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f x₀) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0)) :
    IsApproximateTangentPlane (finrank ℝ U) E (f x₀) Q ↔
      Q = LinearMap.range A.toLinearMap := by
  refine ⟨fun hQ => hf.eq_range_of_tendsto_outside_cone hinj hi hsub hdens hQ.finrank_eq.le
    hQ.tendsto_outside_cone, ?_⟩
  rintro rfl
  exact ⟨LinearMap.finrank_range_of_inj hinj,
    hf.limsup_euclideanHausdorffMeasure_inter_closedBall_div_pos hi hsub hdens,
    hf.tendsto_outside_cone_range hi hx₀ hdiff⟩

/-- Under the hypotheses of `HasFDerivWithinAt.isApproximateTangentPlane_iff`, the canonical
approximate tangent `(dim U)`-plane to `E` at `f x₀` is `range A`. -/
theorem approximateTangentPlane_eq_range {f : U → V} {s : Set U} {A : U →L[ℝ] V} {x₀ : U}
    {L : ℝ≥0} {E : Set V} (hf : HasFDerivWithinAt f A s x₀) (hinj : Injective A)
    (hi : AntilipschitzWith L (s.domRestrict f)) (hx₀ : x₀ ∈ s) (hsub : f '' s ⊆ E)
    (hdens : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall (0 : U) r))
      (𝓝[>] 0) (𝓝 1))
    (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f x₀) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0)) :
    approximateTangentPlane (finrank ℝ U) E (f x₀) = LinearMap.range A.toLinearMap := by
  have hiff := fun Q => hf.isApproximateTangentPlane_iff hinj hi hx₀ hsub hdens hdiff (Q := Q)
  exact ((hiff _).mpr rfl).approximateTangentPlane_eq fun Q hQ => (hiff Q).mp hQ

/-- On an inverse-Lipschitz image `f '' s`, at any Lebesgue density-one parameter `x₀ ∈ s` where
`f` has injective derivative `A` within `s`, `range A` is the unique approximate tangent
`(dim U)`-plane at `f x₀`. -/
theorem isApproximateTangentPlane_image_iff {f : U → V} {s : Set U} {A : U →L[ℝ] V} {x₀ : U}
    {L : ℝ≥0} {Q : Submodule ℝ V} (hf : HasFDerivWithinAt f A s x₀) (hinj : Injective A)
    (hi : AntilipschitzWith L (s.domRestrict f)) (hx₀ : x₀ ∈ s)
    (hdens : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall (0 : U) r))
      (𝓝[>] 0) (𝓝 1)) :
    IsApproximateTangentPlane (finrank ℝ U) (f '' s) (f x₀) Q ↔
      Q = LinearMap.range A.toLinearMap :=
  hf.isApproximateTangentPlane_iff hinj hi hx₀ Subset.rfl hdens (by simp)

/-- On an inverse-Lipschitz image `f '' s`, at any Lebesgue density-one parameter `x₀ ∈ s` where
`f` has injective derivative `A` within `s`, `approximateTangentPlane` at `f x₀` is `range A`. -/
theorem approximateTangentPlane_image_eq_range {f : U → V} {s : Set U} {A : U →L[ℝ] V} {x₀ : U}
    {L : ℝ≥0} (hf : HasFDerivWithinAt f A s x₀) (hinj : Injective A)
    (hi : AntilipschitzWith L (s.domRestrict f)) (hx₀ : x₀ ∈ s)
    (hdens : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall (0 : U) r))
      (𝓝[>] 0) (𝓝 1)) :
    approximateTangentPlane (finrank ℝ U) (f '' s) (f x₀) = LinearMap.range A.toLinearMap :=
  hf.approximateTangentPlane_eq_range hinj hi hx₀ Subset.rfl hdens (by simp)

end HasFDerivWithinAt
