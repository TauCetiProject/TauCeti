/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Topology.Instances.Matrix

/-!
# Asymptotic bounds and infinite volume of asymptotically Euclidean ends

For an asymptotically Euclidean end `e` of positive decay order `t > 0`, the pulled-back metric
matrix `e.metricMatrix x` converges to the identity matrix as `‖x‖ → ∞`, and therefore its
determinant converges to `1` and its inverse matrix converges to the identity matrix. Outside a
sufficiently large ball `‖x‖ > R₁`, the metric determinant is uniformly bounded below by `1 / 4`,
the inverse metric entries satisfy `|g⁻¹_ij(x) - δ_ij| ≤ C₁ ‖x‖ ^ (-t)`, and the first and
second derivatives obey the `O(‖x‖ ^ (-t - 1))` and `O(‖x‖ ^ (-t - 2))` bounds with a single
constant.

As a geometric consequence, in positive dimension `1 ≤ n` every asymptotically Euclidean end of
positive order has infinite Riemannian volume (`riemannianVolume_range_eq_top`), and hence no
compact `C¹` manifold with a continuous Riemannian metric admits an asymptotically Euclidean end
of positive order (`not_compactSpace`).

## Main results

* `TauCeti.volume_exteriorBall`: for `1 ≤ n`, every exterior ball in `ℝⁿ` has infinite
  Lebesgue measure.
* `TauCeti.AsymptoticallyEuclideanEnd.tendsto_metricMatrix_one`,
  `TauCeti.AsymptoticallyEuclideanEnd.tendsto_det_metricMatrix_one`,
  `TauCeti.AsymptoticallyEuclideanEnd.tendsto_inv_metricMatrix_one`: asymptotic convergence of the
  metric matrix, its determinant, and its inverse as `‖x‖ → ∞`.
* `TauCeti.AsymptoticallyEuclideanEnd.exists_asymptotic_bounds`: uniform exterior determinant,
  inverse-matrix, and derivative bounds.
* `TauCeti.AsymptoticallyEuclideanEnd.riemannianVolume_range_eq_top`: every asymptotically
  Euclidean end of positive order in dimension `1 ≤ n` has infinite Riemannian volume.
* `TauCeti.AsymptoticallyEuclideanEnd.not_compactSpace`: no compact Riemannian manifold of
  dimension `1 ≤ n` admits an asymptotically Euclidean end of positive order.

## References

* R. Bartnik, *The mass of an asymptotically flat manifold*, Comm. Pure Appl. Math. 39 (1986),
  661–693.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 8.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff ENNReal Manifold Matrix RealInnerProductSpace Topology

namespace TauCeti

/-- For `1 ≤ n`, the exterior of every closed ball in `ℝⁿ` has infinite Lebesgue measure. -/
theorem volume_exteriorBall {n : ℕ} (hn : 1 ≤ n) (R : ℝ) :
    volume (exteriorBall n R : Set (EuclideanSpace ℝ (Fin n))) = ⊤ := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hcoe : (exteriorBall n R : Set (EuclideanSpace ℝ (Fin n))) = (closedBall 0 R)ᶜ := by
    ext x
    simp [mem_exteriorBall, mem_closedBall, dist_zero_right]
  rw [hcoe, measure_compl measurableSet_closedBall measure_closedBall_lt_top.ne,
    measure_univ_of_isAddLeftInvariant volume,
    ENNReal.top_sub measure_closedBall_lt_top.ne]

namespace AsymptoticallyEuclideanEnd

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] {t : ℝ}

/-- For positive decay order `t > 0`, the pulled-back metric matrix approaches the identity matrix
as `‖x‖ → ∞`. -/
theorem tendsto_metricMatrix_one (e : AsymptoticallyEuclideanEnd n M t) (ht : 0 < t) :
    Tendsto e.metricMatrix (comap norm atTop) (𝓝 1) := by
  obtain ⟨C, hC⟩ := e.decay
  simp only [← e.metricCoeff_eq_openPullbackMetricCoeff] at hC
  have hcoeff : Tendsto e.metricCoeff (comap norm atTop)
      (𝓝 fun i j : Fin n ↦ if i = j then (1 : ℝ) else 0) := by
    rw [tendsto_pi_nhds]
    intro i
    rw [tendsto_pi_nhds]
    intro j
    have hzero : Tendsto (fun x : EuclideanSpace ℝ (Fin n) ↦ C * ‖x‖ ^ (-t))
        (comap norm atTop) (𝓝 0) := by
      have h1 : Tendsto (fun r : ℝ ↦ C * r ^ (-t)) atTop (𝓝 (C * 0)) :=
        (tendsto_rpow_neg_atTop ht).const_mul C
      have h2 := h1.comp (tendsto_comap (f := norm (E := EuclideanSpace ℝ (Fin n))))
      simpa only [mul_zero, Function.comp_def] using h2
    rw [Metric.tendsto_nhds] at hzero ⊢
    intro ε hε
    filter_upwards [hzero ε hε, preimage_mem_comap (Ioi_mem_atTop e.radius)] with x hx hrx
    have h1 := (hC x hrx i j).1
    have h0 : 0 ≤ C * ‖x‖ ^ (-t) := (abs_nonneg _).trans h1
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h0] at hx
    rw [Real.dist_eq]
    exact h1.trans_lt hx
  have h1 : Matrix.of (fun i j : Fin n ↦ if i = j then (1 : ℝ) else 0) =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [Matrix.one_apply]
  have hof : Continuous (Matrix.of : (Fin n → Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) :=
    continuous_matrixOf.2 continuous_id
  have hcomp :
      (Matrix.of : (Fin n → Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) ∘ e.metricCoeff =
        e.metricMatrix := by
    funext x
    ext i j
    simp [metricMatrix_apply]
  rw [← hcomp, ← h1]
  exact hof.continuousAt.tendsto.comp hcoeff

/-- For positive decay order `t > 0`, the determinant of the pulled-back metric matrix converges to
`1` as `‖x‖ → ∞`. -/
theorem tendsto_det_metricMatrix_one (e : AsymptoticallyEuclideanEnd n M t) (ht : 0 < t) :
    Tendsto (fun x ↦ (e.metricMatrix x).det) (comap norm atTop) (𝓝 1) := by
  have hc : Tendsto (fun A : Matrix (Fin n) (Fin n) ℝ ↦ A.det) (𝓝 1) (𝓝 1) := by
    simpa only [id_eq, Matrix.det_one] using
      (continuous_id.matrix_det.continuousAt (x := (1 : Matrix (Fin n) (Fin n) ℝ))).tendsto
  exact hc.comp (e.tendsto_metricMatrix_one ht)

/-- For positive decay order `t > 0`, the inverse of the pulled-back metric matrix converges to the
identity matrix as `‖x‖ → ∞`. -/
theorem tendsto_inv_metricMatrix_one (e : AsymptoticallyEuclideanEnd n M t) (ht : 0 < t) :
    Tendsto (fun x ↦ (e.metricMatrix x)⁻¹) (comap norm atTop) (𝓝 1) := by
  have h1 : (1 : Matrix (Fin n) (Fin n) ℝ).det ≠ 0 := by simp
  have hc : Tendsto (fun A : Matrix (Fin n) (Fin n) ℝ ↦ A⁻¹) (𝓝 1) (𝓝 1) := by
    simpa only [id_eq, inv_one] using (continuousAt_id.matrix_inv h1).tendsto
  exact hc.comp (e.tendsto_metricMatrix_one ht)

/-- For `0 < t`, outside a sufficiently large ball of radius `R₁ ≥ max e.radius 1`:
* the metric determinant satisfies `1 / 4 ≤ det (g(x))` (hence `1 / 2 ≤ √(det (g(x)))`);
* the inverse metric entries satisfy `|g⁻¹_ij(x)| ≤ 2` and
  `|g⁻¹_ij(x) - δ_ij| ≤ C₁ ‖x‖ ^ (-t)`;
* the first and second derivatives of `g_ij` are bounded by `C₁ ‖x‖ ^ (-t - 1)` and
  `C₁ ‖x‖ ^ (-t - 2)`. -/
theorem exists_asymptotic_bounds (e : AsymptoticallyEuclideanEnd n M t) (ht : 0 < t) :
    ∃ R₁ C₁ : ℝ, max e.radius 1 ≤ R₁ ∧ 0 ≤ C₁ ∧
      ∀ x : EuclideanSpace ℝ (Fin n), R₁ < ‖x‖ →
        (1 / 4 ≤ (e.metricMatrix x).det ∧ (e.metricMatrix x).det ≠ 0 ∧
          1 / 2 ≤ Real.sqrt (e.metricMatrix x).det) ∧
        (∀ i j : Fin n,
          |(e.metricMatrix x)⁻¹ i j| ≤ 2 ∧
          |(e.metricMatrix x)⁻¹ i j - if i = j then 1 else 0| ≤ C₁ * ‖x‖ ^ (-t) ∧
          ‖fderiv ℝ (fun y ↦ e.metricCoeff y i j) x‖ ≤ C₁ * ‖x‖ ^ (-t - 1) ∧
          ‖fderiv ℝ (fderiv ℝ (fun y ↦ e.metricCoeff y i j)) x‖ ≤
            C₁ * ‖x‖ ^ (-t - 2)) := by
  obtain ⟨C, hC⟩ := e.decay
  simp only [← e.metricCoeff_eq_openPullbackMetricCoeff] at hC
  have hdet_ev : ∀ᶠ x in comap norm atTop, (1 / 4 : ℝ) < (e.metricMatrix x).det :=
    (e.tendsto_det_metricMatrix_one ht).eventually (Ioi_mem_nhds (by norm_num))
  have hinv_ev :
      ∀ᶠ x in comap norm atTop, ∀ i j : Fin n, |(e.metricMatrix x)⁻¹ i j| ≤ 2 := by
    rw [eventually_all]
    intro i
    rw [eventually_all]
    intro j
    have hij : Tendsto (fun x ↦ (e.metricMatrix x)⁻¹ i j) (comap norm atTop)
        (𝓝 ((1 : Matrix (Fin n) (Fin n) ℝ) i j)) :=
      (continuous_apply_apply i j).continuousAt.tendsto.comp (e.tendsto_inv_metricMatrix_one ht)
    filter_upwards [Metric.tendsto_nhds.1 hij 1 one_pos] with x hx
    rw [Real.dist_eq, Matrix.one_apply] at hx
    split_ifs at hx <;> linarith [abs_sub_abs_le_abs_sub ((e.metricMatrix x)⁻¹ i j) 1,
      abs_sub_abs_le_abs_sub ((e.metricMatrix x)⁻¹ i j) 0]
  have hev := (hdet_ev.and hinv_ev).and (preimage_mem_comap (Ioi_mem_atTop (max e.radius 1)))
  rw [Filter.eventually_comap] at hev
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.1 hev
  set R₁ : ℝ := max (max e.radius 1) R₀
  set C₁ : ℝ := max (max C 0) (2 * (n : ℝ) * max C 0)
  refine ⟨R₁, C₁, le_max_left _ _, le_trans (le_max_right C 0) (le_max_left _ _),
    fun x hx ↦ ?_⟩
  have hxR₀ : R₀ ≤ ‖x‖ := (le_max_right _ _).trans hx.le
  have ⟨⟨hdet_gt, hinv_le⟩, hrx_max⟩ := hR₀ ‖x‖ hxR₀ x rfl
  have hrx : e.radius < ‖x‖ := (le_max_left _ _).trans_lt hrx_max
  have hdet_ne : (e.metricMatrix x).det ≠ 0 :=
    ((by norm_num : (0 : ℝ) < 1 / 4).trans hdet_gt).ne'
  have hsqrt : 1 / 2 ≤ Real.sqrt (e.metricMatrix x).det := by
    have h14 : (1 / 2 : ℝ) = Real.sqrt (1 / 4) := by
      have hsq : (1 / 4 : ℝ) = (1 / 2) ^ 2 := by norm_num
      rw [hsq, Real.sqrt_sq (by norm_num)]
    rw [h14]
    exact Real.sqrt_le_sqrt hdet_gt.le
  refine ⟨⟨hdet_gt.le, hdet_ne, hsqrt⟩, fun i j ↦ ?_⟩
  have hC0 : C ≤ max C 0 := le_max_left C 0
  have hC1 : max C 0 ≤ C₁ := le_max_left _ _
  have h2nC : 2 * (n : ℝ) * max C 0 ≤ C₁ := le_max_right _ _
  have hsub_inv :
      (e.metricMatrix x)⁻¹ - 1 = (e.metricMatrix x)⁻¹ * (1 - e.metricMatrix x) := by
    rw [mul_sub, mul_one, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet_ne)]
  have hinv_diff :
      |(e.metricMatrix x)⁻¹ i j - if i = j then 1 else 0| ≤ C₁ * ‖x‖ ^ (-t) := by
    have hentry : (e.metricMatrix x)⁻¹ i j - (if i = j then 1 else 0) =
        ∑ k : Fin n, (e.metricMatrix x)⁻¹ i k *
          ((if k = j then 1 else 0) - e.metricCoeff x k j) := by
      have h := congrFun (congrFun hsub_inv i) j
      simpa only [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply, metricMatrix_apply] using h
    rw [hentry]
    calc |∑ k : Fin n, (e.metricMatrix x)⁻¹ i k *
            ((if k = j then 1 else 0) - e.metricCoeff x k j)|
        ≤ ∑ k : Fin n, |(e.metricMatrix x)⁻¹ i k *
            ((if k = j then 1 else 0) - e.metricCoeff x k j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin n, 2 * (max C 0 * ‖x‖ ^ (-t)) := by
          refine Finset.sum_le_sum fun k _ ↦ ?_
          rw [abs_mul, abs_sub_comm]
          have hk0 : |e.metricCoeff x k j - if k = j then 1 else 0| ≤ max C 0 * ‖x‖ ^ (-t) :=
            (hC x hrx k j).1.trans
              (mul_le_mul_of_nonneg_right hC0 (Real.rpow_nonneg (norm_nonneg x) _))
          exact mul_le_mul (hinv_le i k) hk0 (abs_nonneg _) (by norm_num)
      _ = 2 * (n : ℝ) * max C 0 * ‖x‖ ^ (-t) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ C₁ * ‖x‖ ^ (-t) :=
          mul_le_mul_of_nonneg_right h2nC (Real.rpow_nonneg (norm_nonneg x) _)
  exact ⟨hinv_le i j, hinv_diff,
    (hC x hrx i j).2.1.trans (mul_le_mul_of_nonneg_right (hC0.trans hC1)
      (Real.rpow_nonneg (norm_nonneg x) _)),
    (hC x hrx i j).2.2.trans (mul_le_mul_of_nonneg_right (hC0.trans hC1)
      (Real.rpow_nonneg (norm_nonneg x) _))⟩

/-- In positive dimension `1 ≤ n`, every asymptotically Euclidean end of positive order `t > 0`
has infinite Riemannian volume. -/
theorem riemannianVolume_range_eq_top [IsManifold (𝓡 n) 1 M]
    [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (𝓡 n) x)]
    (hn : 1 ≤ n) (ht : 0 < t) (e : AsymptoticallyEuclideanEnd n M t) :
    riemannianVolume (𝓡 n) M (Set.range e.toFun) = ⊤ := by
  have : Nonempty M := e.nonempty_of_pos hn
  obtain ⟨R₁, _, hR₁, _, hbounds⟩ := e.exists_asymptotic_bounds ht
  have hR₁_ge : e.radius ≤ R₁ := (le_max_left _ _).trans hR₁
  let Φ := e.partialDiffeomorph (k := 1) le_rfl (by simp)
  have hcov := Φ.setLIntegral_riemannianVolume_eq
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis rfl (φ := fun _ ↦ (1 : ℝ≥0∞))
    measurable_const
  simp only [Φ, partialDiffeomorph_target, partialDiffeomorph_source, lintegral_one,
    Measure.restrict_apply_univ, mul_one, (EuclideanSpace.basisFun (Fin n) ℝ).addHaar_eq_volume]
    at hcov
  have hsub : (exteriorBall n R₁ : Set (EuclideanSpace ℝ (Fin n))) ⊆
      (exteriorBall n e.radius : Set (EuclideanSpace ℝ (Fin n))) :=
    exteriorBall_anti hR₁_ge
  have hlower : ENNReal.ofReal (1 / 2) *
        volume (exteriorBall n R₁ : Set (EuclideanSpace ℝ (Fin n))) ≤
      riemannianVolume (𝓡 n) M (Set.range e.toFun) := by
    rw [hcov]
    calc ENNReal.ofReal (1 / 2) * volume (exteriorBall n R₁ : Set (EuclideanSpace ℝ (Fin n)))
        = ∫⁻ _ in (exteriorBall n R₁ : Set (EuclideanSpace ℝ (Fin n))),
            ENNReal.ofReal (1 / 2) ∂volume := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ x in (exteriorBall n R₁ : Set (EuclideanSpace ℝ (Fin n))),
            ENNReal.ofReal (riemannianJacobian (I := 𝓡 n)
              (EuclideanSpace.basisFun (Fin n) ℝ).toBasis Φ x) ∂volume := by
          refine setLIntegral_mono' (exteriorBall n R₁).isOpen.measurableSet fun x hx ↦ ?_
          rw [e.riemannianJacobian_partialDiffeomorph (k := 1) le_rfl (by simp) (hsub hx)]
          exact ENNReal.ofReal_le_ofReal (hbounds x (mem_exteriorBall.1 hx)).1.2.2
      _ ≤ ∫⁻ x in (exteriorBall n e.radius : Set (EuclideanSpace ℝ (Fin n))),
            ENNReal.ofReal (riemannianJacobian (I := 𝓡 n)
              (EuclideanSpace.basisFun (Fin n) ℝ).toBasis Φ x) ∂volume :=
          lintegral_mono_set hsub
  rw [volume_exteriorBall hn R₁, ENNReal.mul_top (by norm_num)] at hlower
  exact top_unique hlower

/-- No compact `C¹` manifold of dimension `1 ≤ n` with a continuous Riemannian metric admits an
asymptotically Euclidean end of positive order `t > 0`. -/
theorem not_compactSpace [IsManifold (𝓡 n) 1 M]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (𝓡 n) x)]
    (hn : 1 ≤ n) (ht : 0 < t) (e : AsymptoticallyEuclideanEnd n M t) :
    ¬ CompactSpace M := by
  intro _
  let _ : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  have htop : riemannianVolume (𝓡 n) M univ = ⊤ :=
    top_unique ((e.riemannianVolume_range_eq_top hn ht).symm.trans_le
      (measure_mono (subset_univ _)))
  exact htop.not_lt isCompact_univ.measure_lt_top

end AsymptoticallyEuclideanEnd

end TauCeti

end
