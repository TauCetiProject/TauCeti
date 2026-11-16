/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Topology.Instances.Matrix

/-!
# Asymptotic bounds and infinite volume of asymptotically Euclidean ends

For an asymptotically Euclidean end `e` of positive decay order `t > 0`, the pulled-back metric
matrix `e.metricMatrix x` converges to the identity matrix along `Bornology.cobounded`, and
therefore its determinant converges to `1` and its inverse matrix converges to the identity matrix.
Outside a sufficiently large ball `‖x‖ > R₁`, the metric determinant is uniformly bounded below by
`1 / 4`, the metric entries `g_ij(x)` and inverse metric entries `g⁻¹_ij(x)` satisfy
`|g_ij(x) - δ_ij| ≤ C₁ ‖x‖ ^ (-t)` and `|g⁻¹_ij(x) - δ_ij| ≤ C₁ ‖x‖ ^ (-t)`, and the first and
second derivatives of `e.metricCoeff` (`g_ij`) obey the `O(‖x‖ ^ (-t - 1))` and
`O(‖x‖ ^ (-t - 2))` bounds with a single constant.

As a geometric consequence, in positive dimension `1 ≤ n` every asymptotically Euclidean end of
positive order has infinite Riemannian volume (`riemannianVolume_range_eq_top`), and hence no
compact `C¹` manifold with a continuous Riemannian metric admits an asymptotically Euclidean end
of positive order (`not_compactSpace`).

## Main results

* `TauCeti.AsymptoticallyEuclideanEnd.tendsto_metricMatrix_one`,
  `TauCeti.AsymptoticallyEuclideanEnd.tendsto_det_metricMatrix_one`,
  `TauCeti.AsymptoticallyEuclideanEnd.tendsto_inv_metricMatrix_one`: asymptotic convergence of the
  metric matrix, its determinant, and its inverse along `Bornology.cobounded`.
* `TauCeti.AsymptoticallyEuclideanEnd.exists_asymptotic_bounds`: uniform exterior determinant,
  metric and inverse-metric decay, and first- and second-derivative bounds on `e.metricCoeff`.
* `TauCeti.AsymptoticallyEuclideanEnd.riemannianVolume_range_eq_top`: every asymptotically
  Euclidean end of positive order in dimension `1 ≤ n` has infinite Riemannian volume.
* `TauCeti.AsymptoticallyEuclideanEnd.not_compactSpace`: no compact `C¹` manifold of dimension
  `1 ≤ n` with a continuous Riemannian metric admits an asymptotically Euclidean end of positive
  order.

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

namespace AsymptoticallyEuclideanEnd

variable {n : ℕ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {t : ℝ}
  (e : AsymptoticallyEuclideanEnd n I M t)

/-- For positive decay order `t > 0`, the pulled-back metric matrix approaches the identity matrix
along `Bornology.cobounded`. -/
theorem tendsto_metricMatrix_one (ht : 0 < t) :
    Tendsto e.metricMatrix (Bornology.cobounded (EuclideanSpace ℝ (Fin n))) (𝓝 1) := by
  obtain ⟨C, hC⟩ := e.decay
  simp only [← e.metricCoeff_eq_openPullbackMetricCoeff] at hC
  have hcoeff : Tendsto e.metricCoeff (Bornology.cobounded (EuclideanSpace ℝ (Fin n)))
      (𝓝 fun i j : Fin n ↦ if i = j then (1 : ℝ) else 0) := by
    rw [tendsto_pi_nhds]; intro i; rw [tendsto_pi_nhds]; intro j
    have hzero : Tendsto (fun x : EuclideanSpace ℝ (Fin n) ↦ C * ‖x‖ ^ (-t))
        (Bornology.cobounded (EuclideanSpace ℝ (Fin n))) (𝓝 0) := by
      simpa only [mul_zero, Function.comp_def] using
        ((tendsto_rpow_neg_atTop ht).const_mul C).comp
          (tendsto_norm_cobounded_atTop (E := EuclideanSpace ℝ (Fin n)))
    rw [Metric.tendsto_nhds] at hzero ⊢
    intro ε hε
    filter_upwards [hzero ε hε,
      tendsto_norm_cobounded_atTop.eventually (Ioi_mem_atTop e.radius)] with x hx hrx
    have h1 := (hC x hrx i j).1
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ((abs_nonneg _).trans h1)] at hx
    exact (Real.dist_eq _ _).trans_lt (h1.trans_lt hx)
  have h1 : Matrix.of (fun i j : Fin n ↦ if i = j then (1 : ℝ) else 0) =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by ext i j; simp [Matrix.one_apply]
  have hcomp : (Matrix.of : (Fin n → Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) ∘ e.metricCoeff =
      e.metricMatrix := funext fun x ↦ by ext i j; simp [metricMatrix_apply]
  rw [← hcomp, ← h1]
  exact (continuous_matrixOf.2 continuous_id).continuousAt.tendsto.comp hcoeff

/-- For positive decay order `t > 0`, the determinant of the pulled-back metric matrix converges to
`1` along `Bornology.cobounded`. -/
theorem tendsto_det_metricMatrix_one (ht : 0 < t) :
    Tendsto (fun x ↦ (e.metricMatrix x).det)
      (Bornology.cobounded (EuclideanSpace ℝ (Fin n))) (𝓝 1) := by
  have hc : Tendsto (fun A : Matrix (Fin n) (Fin n) ℝ ↦ A.det) (𝓝 1) (𝓝 1) := by
    simpa only [id_eq, Matrix.det_one] using
      (continuous_id.matrix_det.continuousAt (x := (1 : Matrix (Fin n) (Fin n) ℝ))).tendsto
  exact hc.comp (e.tendsto_metricMatrix_one ht)

/-- For positive decay order `t > 0`, the inverse of the pulled-back metric matrix converges to the
identity matrix along `Bornology.cobounded`. -/
theorem tendsto_inv_metricMatrix_one (ht : 0 < t) :
    Tendsto (fun x ↦ (e.metricMatrix x)⁻¹)
      (Bornology.cobounded (EuclideanSpace ℝ (Fin n))) (𝓝 1) := by
  have hc : Tendsto (fun A : Matrix (Fin n) (Fin n) ℝ ↦ A⁻¹) (𝓝 1) (𝓝 1) := by
    simpa only [id_eq, inv_one] using
      (continuousAt_id.matrix_inv (by simp : (1 : Matrix (Fin n) (Fin n) ℝ).det ≠ 0)).tendsto
  exact hc.comp (e.tendsto_metricMatrix_one ht)

/-- For positive decay order `t > 0`, the entries of `(e.metricMatrix x)⁻¹` are eventually bounded
in absolute value by `2` along `Bornology.cobounded`. -/
private theorem eventually_abs_inv_metricMatrix_le (ht : 0 < t) :
    ∀ᶠ x in Bornology.cobounded (EuclideanSpace ℝ (Fin n)),
      ∀ i j : Fin n, |(e.metricMatrix x)⁻¹ i j| ≤ 2 := by
  rw [eventually_all]; intro i; rw [eventually_all]; intro j
  have hij : Tendsto (fun x ↦ (e.metricMatrix x)⁻¹ i j)
      (Bornology.cobounded (EuclideanSpace ℝ (Fin n)))
      (𝓝 ((1 : Matrix (Fin n) (Fin n) ℝ) i j)) :=
    (continuous_apply_apply i j).continuousAt.tendsto.comp (e.tendsto_inv_metricMatrix_one ht)
  filter_upwards [Metric.tendsto_nhds.1 hij 1 one_pos] with x hx
  rw [Real.dist_eq, Matrix.one_apply] at hx
  split_ifs at hx <;> linarith [abs_sub_abs_le_abs_sub ((e.metricMatrix x)⁻¹ i j) 1,
    abs_sub_abs_le_abs_sub ((e.metricMatrix x)⁻¹ i j) 0]

/-- Entrywise bound on `(e.metricMatrix x)⁻¹ - 1` via `g⁻¹ - 1 = g⁻¹ * (1 - g)`. -/
private theorem abs_inv_metricMatrix_sub_le {x : EuclideanSpace ℝ (Fin n)}
    (hdet : (e.metricMatrix x).det ≠ 0) {B δ : ℝ} (hB : 0 ≤ B)
    (hinv : ∀ i k : Fin n, |(e.metricMatrix x)⁻¹ i k| ≤ B)
    (hdiff : ∀ k j : Fin n, |e.metricCoeff x k j - if k = j then 1 else 0| ≤ δ) (i j : Fin n) :
    |(e.metricMatrix x)⁻¹ i j - if i = j then 1 else 0| ≤ (n : ℝ) * B * δ := by
  have hsub_inv : (e.metricMatrix x)⁻¹ - 1 = (e.metricMatrix x)⁻¹ * (1 - e.metricMatrix x) := by
    rw [mul_sub, mul_one, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet)]
  have hentry : (e.metricMatrix x)⁻¹ i j - (if i = j then 1 else 0) =
      ∑ k : Fin n, (e.metricMatrix x)⁻¹ i k * ((if k = j then 1 else 0) - e.metricCoeff x k j) := by
    have h := congrFun (congrFun hsub_inv i) j
    simpa only [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply, metricMatrix_apply] using h
  rw [hentry]
  calc |∑ k : Fin n, (e.metricMatrix x)⁻¹ i k * ((if k = j then 1 else 0) - e.metricCoeff x k j)|
      ≤ ∑ k : Fin n,
          |(e.metricMatrix x)⁻¹ i k * ((if k = j then 1 else 0) - e.metricCoeff x k j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, B * δ := Finset.sum_le_sum fun k _ ↦ by
        rw [abs_mul, abs_sub_comm]; exact mul_le_mul (hinv i k) (hdiff k j) (abs_nonneg _) hB
    _ = (n : ℝ) * B * δ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- For `0 < t`, outside a sufficiently large ball of radius `R₁ ≥ max e.radius 1`:
* the metric determinant satisfies `1 / 4 ≤ det (g(x))` (hence `1 / 2 ≤ √(det (g(x)))`);
* the metric entries satisfy `|g_ij(x) - δ_ij| ≤ C₁ ‖x‖ ^ (-t)`;
* the inverse metric entries satisfy `|g⁻¹_ij(x)| ≤ 2` and
  `|g⁻¹_ij(x) - δ_ij| ≤ C₁ ‖x‖ ^ (-t)`;
* the first and second derivatives of `g_ij` are bounded by `C₁ ‖x‖ ^ (-t - 1)` and
  `C₁ ‖x‖ ^ (-t - 2)`. -/
theorem exists_asymptotic_bounds (ht : 0 < t) :
    ∃ R₁ C₁ : ℝ, max e.radius 1 ≤ R₁ ∧ 0 ≤ C₁ ∧
      ∀ x : EuclideanSpace ℝ (Fin n), R₁ < ‖x‖ →
        (1 / 4 ≤ (e.metricMatrix x).det ∧ (e.metricMatrix x).det ≠ 0 ∧
          1 / 2 ≤ Real.sqrt (e.metricMatrix x).det) ∧
        (∀ i j : Fin n,
          |e.metricCoeff x i j - if i = j then 1 else 0| ≤ C₁ * ‖x‖ ^ (-t) ∧
          |(e.metricMatrix x)⁻¹ i j| ≤ 2 ∧
          |(e.metricMatrix x)⁻¹ i j - if i = j then 1 else 0| ≤ C₁ * ‖x‖ ^ (-t) ∧
          ‖fderiv ℝ (fun y ↦ e.metricCoeff y i j) x‖ ≤ C₁ * ‖x‖ ^ (-t - 1) ∧
          ‖fderiv ℝ (fderiv ℝ (fun y ↦ e.metricCoeff y i j)) x‖ ≤ C₁ * ‖x‖ ^ (-t - 2)) := by
  obtain ⟨C, hC⟩ := e.decay
  simp only [← e.metricCoeff_eq_openPullbackMetricCoeff] at hC
  -- Combine eventual determinant positivity, inverse-entry bounds, and the exterior radius.
  have hdet_ev : ∀ᶠ x in Bornology.cobounded (EuclideanSpace ℝ (Fin n)),
      (1 / 4 : ℝ) < (e.metricMatrix x).det :=
    (e.tendsto_det_metricMatrix_one ht).eventually (Ioi_mem_nhds (by norm_num))
  have hev := (hdet_ev.and (e.eventually_abs_inv_metricMatrix_le ht)).and
    (tendsto_norm_cobounded_atTop.eventually (Ioi_mem_atTop (max e.radius 1)))
  obtain ⟨R₀, -, hR₀⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.1 hev
  -- Choose a common exterior radius `R₁` and uniform constant `C₁`.
  set R₁ : ℝ := max (max e.radius 1) R₀
  set C₁ : ℝ := max (max C 0) ((n : ℝ) * 2 * max C 0)
  refine ⟨R₁, C₁, le_max_left _ _, le_trans (le_max_right C 0) (le_max_left _ _), fun x hx ↦ ?_⟩
  have ⟨⟨hdet_gt, hinv_le⟩, hrx_max⟩ := hR₀ ((le_max_right _ _).trans hx.le)
  have hrx : e.radius < ‖x‖ := (le_max_left _ _).trans_lt hrx_max
  have hdet_ne : (e.metricMatrix x).det ≠ 0 := ((by norm_num : (0 : ℝ) < 1 / 4).trans hdet_gt).ne'
  refine ⟨⟨hdet_gt.le, hdet_ne, Real.le_sqrt_of_sq_le (by linarith)⟩, fun i j ↦ ?_⟩
  -- Deduce uniform metric, inverse-metric, and derivative bounds at `x`.
  have hC0 : C ≤ max C 0 := le_max_left C 0
  have hC1 : max C 0 ≤ C₁ := le_max_left _ _
  have h2nC : (n : ℝ) * 2 * max C 0 ≤ C₁ := le_max_right _ _
  have hcoeff0 (k l : Fin n) :
      |e.metricCoeff x k l - if k = l then 1 else 0| ≤ max C 0 * ‖x‖ ^ (-t) :=
    (hC x hrx k l).1.trans (mul_le_mul_of_nonneg_right hC0 (Real.rpow_nonneg (norm_nonneg x) _))
  have hinv_diff : |(e.metricMatrix x)⁻¹ i j - if i = j then 1 else 0| ≤ C₁ * ‖x‖ ^ (-t) :=
    (e.abs_inv_metricMatrix_sub_le hdet_ne (by norm_num) hinv_le hcoeff0 i j).trans <| by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h2nC (Real.rpow_nonneg (norm_nonneg x) _)
  exact ⟨(hcoeff0 i j).trans (mul_le_mul_of_nonneg_right hC1 (Real.rpow_nonneg (norm_nonneg x) _)),
    hinv_le i j, hinv_diff,
    (hC x hrx i j).2.1.trans (mul_le_mul_of_nonneg_right (hC0.trans hC1)
      (Real.rpow_nonneg (norm_nonneg x) _)),
    (hC x hrx i j).2.2.trans (mul_le_mul_of_nonneg_right (hC0.trans hC1)
      (Real.rpow_nonneg (norm_nonneg x) _))⟩

/-- A positive-dimensional asymptotically Euclidean end identifies `ℝⁿ` linearly with the target
model space `E` via the bijective differential at any point of the exterior ball. -/
private def linearEquivModel (hn : 1 ≤ n) (e : AsymptoticallyEuclideanEnd n I M t) :
    EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] E := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let hne := nonempty_exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius
  let x : exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius := ⟨hne.choose, hne.choose_spec⟩
  exact (NormedSpace.fromTangentSpace x.1).symm.toLinearEquiv.trans
    ((TauCeti.Manifold.tangentSpaceOpenEquiv (I := 𝓡 n) x).symm.toLinearEquiv.trans
      (LinearEquiv.ofBijective (mfderiv (𝓡 n) I e.toFun x).toLinearMap (e.mfderiv_bijective x)))

/-- In positive dimension `1 ≤ n`, every asymptotically Euclidean end of positive order `t > 0`
has infinite Riemannian volume. -/
theorem riemannianVolume_range_eq_top [FiniteDimensional ℝ E] [IsManifold I 1 M]
    [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (hn : 1 ≤ n) (ht : 0 < t) : riemannianVolume I M (Set.range e.toFun) = ⊤ := by
  have : Nonempty M := e.nonempty hn
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Module.finrank ℝ E :=
    (e.linearEquivModel hn).finrank_eq
  obtain ⟨R₁, _, hR₁, _, hbounds⟩ := e.exists_asymptotic_bounds ht
  have hR₁_ge : e.radius ≤ R₁ := (le_max_left _ _).trans hR₁
  let Φ := e.partialDiffeomorph (k := 1) le_rfl (by simp)
  have hcov := Φ.setLIntegral_riemannianVolume_eq
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis hdim (φ := fun _ ↦ (1 : ℝ≥0∞)) measurable_const
  simp only [Φ, partialDiffeomorph_target, partialDiffeomorph_source, lintegral_one,
    Measure.restrict_apply_univ, mul_one, (EuclideanSpace.basisFun (Fin n) ℝ).addHaar_eq_volume]
    at hcov
  let U₁ : Set (EuclideanSpace ℝ (Fin n)) := exteriorBall (EuclideanSpace ℝ (Fin n)) R₁
  let U : Set (EuclideanSpace ℝ (Fin n)) := exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius
  have hsub : U₁ ⊆ U := SetLike.coe_subset_coe.2 (exteriorBall_anti hR₁_ge)
  have hlower : ENNReal.ofReal (1 / 2) * volume U₁ ≤ riemannianVolume I M (Set.range e.toFun) := by
    rw [hcov]
    calc ENNReal.ofReal (1 / 2) * volume U₁
        = ∫⁻ _ in U₁, ENNReal.ofReal (1 / 2) ∂volume := by rw [setLIntegral_const]
      _ ≤ ∫⁻ x in U₁, ENNReal.ofReal (riemannianJacobian (I := I)
            (EuclideanSpace.basisFun (Fin n) ℝ).toBasis Φ x) ∂volume := by
          refine setLIntegral_mono'
            (exteriorBall (EuclideanSpace ℝ (Fin n)) R₁).isOpen.measurableSet fun x hx ↦ ?_
          rw [e.riemannianJacobian_partialDiffeomorph (k := 1) le_rfl (by simp) (hsub hx)]
          exact ENNReal.ofReal_le_ofReal (hbounds x (mem_exteriorBall.1 hx)).1.2.2
      _ ≤ ∫⁻ x in U, ENNReal.ofReal (riemannianJacobian (I := I)
            (EuclideanSpace.basisFun (Fin n) ℝ).toBasis Φ x) ∂volume := lintegral_mono_set hsub
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [show U₁ = (closedBall 0 R₁)ᶜ from coe_exteriorBall_eq_compl_closedBall R₁,
    volume.addHaar_compl_closedBall, ENNReal.mul_top (by norm_num)] at hlower
  exact top_unique hlower

/-- No compact `C¹` manifold with a continuous Riemannian metric admits an asymptotically Euclidean
end of positive order `t > 0` in dimension `1 ≤ n`. -/
theorem not_compactSpace [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (hn : 1 ≤ n) (ht : 0 < t) (e : AsymptoticallyEuclideanEnd n I M t) : ¬ CompactSpace M := by
  intro _
  have : FiniteDimensional ℝ E := (e.linearEquivModel hn).finiteDimensional
  let _ : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  have htop : riemannianVolume I M univ = ⊤ :=
    top_unique <| (e.riemannianVolume_range_eq_top hn ht).symm.trans_le
      (measure_mono (subset_univ _))
  exact htop.not_lt isCompact_univ.measure_lt_top

end AsymptoticallyEuclideanEnd

end TauCeti

end
