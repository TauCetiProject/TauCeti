/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Topology.Instances.Matrix

/-!
# Asymptotic bounds and infinite volume of asymptotically Euclidean ends

For an asymptotically Euclidean end `φ` of positive decay order `t > 0` on `(closedBall 0 R)ᶜ`, the
pulled-back metric matrix `pullbackMetricCoeff I φ x` converges to the identity matrix along
`Bornology.cobounded`, and therefore its determinant converges to `1` and its inverse matrix
converges to the identity matrix. Outside a sufficiently large ball `‖x‖ > R₁`, the metric
determinant is uniformly bounded below by `1 / 4`, the metric entries `g_ij(x)` and inverse metric
entries `g⁻¹_ij(x)` satisfy `|g_ij(x) - δ_ij| ≤ C₁ ‖x‖ ^ (-t)` and
`|g⁻¹_ij(x) - δ_ij| ≤ C₁ ‖x‖ ^ (-t)`, and all derivatives of order `k ≤ 2` of `g_ij - δ_ij` obey the
`O(‖x‖ ^ (-t - k))` bounds with a single constant `C₁`.

As a geometric consequence, every asymptotically Euclidean end of positive order has infinite
Riemannian volume (`riemannianVolume_image_eq_top`), and hence no compact `C¹` manifold with a
continuous Riemannian metric admits an asymptotically Euclidean end of positive order
(`not_compactSpace`).

## Main results

* `TauCeti.IsAsymptoticallyEuclideanEnd.tendsto_pullbackMetricCoeff_one`,
  `TauCeti.IsAsymptoticallyEuclideanEnd.tendsto_det_pullbackMetricCoeff_one`,
  `TauCeti.IsAsymptoticallyEuclideanEnd.tendsto_inv_pullbackMetricCoeff_one`: asymptotic convergence
  of the pulled-back metric matrix, its determinant, and its inverse along `Bornology.cobounded`.
* `TauCeti.IsAsymptoticallyEuclideanEnd.exists_asymptotic_bounds`: uniform exterior determinant,
  metric and inverse-metric decay, and derivative bounds of order `k ≤ 2`.
* `TauCeti.riemannianJacobian_eq_sqrt_det_pullbackMetricCoeff`,
  `TauCeti.IsAsymptoticallyEuclideanEnd.riemannianJacobian_toPartialDiffeomorph`: Riemannian
  Jacobian formula in terms of `pullbackMetricCoeff`.
* `TauCeti.IsAsymptoticallyEuclideanEnd.riemannianVolume_image_eq_top`: every asymptotically
  Euclidean end of positive order has infinite Riemannian volume.
* `TauCeti.IsAsymptoticallyEuclideanEnd.not_compactSpace`: no compact `C¹` manifold with a
  continuous Riemannian metric admits an asymptotically Euclidean end of positive order.

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

variable {n : ℕ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- In the standard orthonormal basis of `ℝⁿ`, the Riemannian Jacobian of any map `φ : ℝⁿ → M` is
`√(det (pullbackMetricCoeff I φ x))`. -/
theorem riemannianJacobian_eq_sqrt_det_pullbackMetricCoeff
    (φ : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n)) :
    riemannianJacobian (I := I) (EuclideanSpace.basisFun (Fin n) ℝ).toBasis φ x =
      Real.sqrt (pullbackMetricCoeff I φ x).det := by
  rw [riemannianJacobian_eq_sqrt_det_gram]
  congr 2
  ext i j
  rw [Matrix.gram_apply, OrthonormalBasis.coe_toBasis, pullbackMetricCoeff_apply]

namespace IsAsymptoticallyEuclideanEnd

variable {t R : ℝ} {φ : EuclideanSpace ℝ (Fin n) → M}

/-- For positive decay order `t > 0`, the pulled-back metric matrix approaches the identity matrix
along `Bornology.cobounded`. -/
theorem tendsto_pullbackMetricCoeff_one (h : IsAsymptoticallyEuclideanEnd I t R φ) (ht : 0 < t) :
    Tendsto (pullbackMetricCoeff I φ)
      (Bornology.cobounded (EuclideanSpace ℝ (Fin n))) (𝓝 1) := by
  obtain ⟨C, hC⟩ := h.exists_norm_iteratedFDeriv_le
  have hentry (i j : Fin n) :
      Tendsto (fun x ↦ pullbackMetricCoeff I φ x i j)
        (Bornology.cobounded (EuclideanSpace ℝ (Fin n)))
        (𝓝 ((1 : Matrix (Fin n) (Fin n) ℝ) i j)) := by
    have hzero : Tendsto (fun x : EuclideanSpace ℝ (Fin n) ↦ C * ‖x‖ ^ (-t))
        (Bornology.cobounded (EuclideanSpace ℝ (Fin n))) (𝓝 0) := by
      simpa only [mul_zero, Function.comp_def] using
        ((tendsto_rpow_neg_atTop ht).const_mul C).comp
          (tendsto_norm_cobounded_atTop (E := EuclideanSpace ℝ (Fin n)))
    rw [Metric.tendsto_nhds] at hzero ⊢
    intro ε hε
    filter_upwards [hzero ε hε,
      tendsto_norm_cobounded_atTop.eventually (Ioi_mem_atTop R)] with x hx hrx
    have h1 := hC 0 (Nat.zero_le 2) i j x (by simpa using hrx)
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, Matrix.sub_apply, Nat.cast_zero, sub_zero] at h1
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ((abs_nonneg _).trans h1)] at hx
    exact (Real.dist_eq _ _).trans_lt (h1.trans_lt hx)
  exact tendsto_pi_nhds.2 fun i ↦ tendsto_pi_nhds.2 fun j ↦ hentry i j

/-- For positive decay order `t > 0`, the determinant of the pulled-back metric matrix converges to
`1` along `Bornology.cobounded`. -/
theorem tendsto_det_pullbackMetricCoeff_one (h : IsAsymptoticallyEuclideanEnd I t R φ)
    (ht : 0 < t) :
    Tendsto (fun x ↦ (pullbackMetricCoeff I φ x).det)
      (Bornology.cobounded (EuclideanSpace ℝ (Fin n))) (𝓝 1) := by
  have hc : Tendsto (fun A : Matrix (Fin n) (Fin n) ℝ ↦ A.det) (𝓝 1) (𝓝 1) := by
    simpa only [id_eq, Matrix.det_one] using
      (continuous_id.matrix_det.continuousAt (x := (1 : Matrix (Fin n) (Fin n) ℝ))).tendsto
  exact hc.comp (h.tendsto_pullbackMetricCoeff_one ht)

/-- For positive decay order `t > 0`, the inverse of the pulled-back metric matrix converges to the
identity matrix along `Bornology.cobounded`. -/
theorem tendsto_inv_pullbackMetricCoeff_one (h : IsAsymptoticallyEuclideanEnd I t R φ)
    (ht : 0 < t) :
    Tendsto (fun x ↦ (pullbackMetricCoeff I φ x)⁻¹)
      (Bornology.cobounded (EuclideanSpace ℝ (Fin n))) (𝓝 1) := by
  have hc : Tendsto (fun A : Matrix (Fin n) (Fin n) ℝ ↦ A⁻¹) (𝓝 1) (𝓝 1) := by
    simpa only [id_eq, inv_one] using
      (continuousAt_id.matrix_inv (by simp : (1 : Matrix (Fin n) (Fin n) ℝ).det ≠ 0)).tendsto
  exact hc.comp (h.tendsto_pullbackMetricCoeff_one ht)

/-- For positive decay order `t > 0`, the entries of `(pullbackMetricCoeff I φ x)⁻¹` are eventually
bounded in absolute value by `2` along `Bornology.cobounded`. -/
private theorem eventually_abs_inv_pullbackMetricCoeff_le
    (h : IsAsymptoticallyEuclideanEnd I t R φ) (ht : 0 < t) :
    ∀ᶠ x in Bornology.cobounded (EuclideanSpace ℝ (Fin n)),
      ∀ i j : Fin n, |(pullbackMetricCoeff I φ x)⁻¹ i j| ≤ 2 := by
  rw [eventually_all]; intro i; rw [eventually_all]; intro j
  have hij : Tendsto (fun x ↦ (pullbackMetricCoeff I φ x)⁻¹ i j)
      (Bornology.cobounded (EuclideanSpace ℝ (Fin n)))
      (𝓝 ((1 : Matrix (Fin n) (Fin n) ℝ) i j)) :=
    (continuous_apply_apply i j).continuousAt.tendsto.comp
      (h.tendsto_inv_pullbackMetricCoeff_one ht)
  filter_upwards [Metric.tendsto_nhds.1 hij 1 one_pos] with x hx
  rw [Real.dist_eq, Matrix.one_apply] at hx
  split_ifs at hx <;> linarith [abs_sub_abs_le_abs_sub ((pullbackMetricCoeff I φ x)⁻¹ i j) 1,
    abs_sub_abs_le_abs_sub ((pullbackMetricCoeff I φ x)⁻¹ i j) 0]

/-- Entrywise bound on `(pullbackMetricCoeff I φ x)⁻¹ - 1` via `g⁻¹ - 1 = g⁻¹ * (1 - g)`. -/
private theorem abs_inv_pullbackMetricCoeff_sub_le (φ : EuclideanSpace ℝ (Fin n) → M)
    {x : EuclideanSpace ℝ (Fin n)} (hdet : (pullbackMetricCoeff I φ x).det ≠ 0)
    {B δ : ℝ} (hB : 0 ≤ B)
    (hinv : ∀ i k : Fin n, |(pullbackMetricCoeff I φ x)⁻¹ i k| ≤ B)
    (hdiff : ∀ k j : Fin n, |(pullbackMetricCoeff I φ x - 1) k j| ≤ δ) (i j : Fin n) :
    |((pullbackMetricCoeff I φ x)⁻¹ - 1) i j| ≤ (n : ℝ) * B * δ := by
  have hsub_inv :
      (pullbackMetricCoeff I φ x)⁻¹ - 1 =
        (pullbackMetricCoeff I φ x)⁻¹ * (1 - pullbackMetricCoeff I φ x) := by
    rw [mul_sub, mul_one, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet)]
  have hentry :
      ((pullbackMetricCoeff I φ x)⁻¹ - 1) i j =
        ∑ k : Fin n, (pullbackMetricCoeff I φ x)⁻¹ i k * (1 - pullbackMetricCoeff I φ x) k j := by
    exact congrFun (congrFun hsub_inv i) j
  rw [hentry]
  calc |∑ k : Fin n, (pullbackMetricCoeff I φ x)⁻¹ i k * (1 - pullbackMetricCoeff I φ x) k j|
      ≤ ∑ k : Fin n,
          |(pullbackMetricCoeff I φ x)⁻¹ i k * (1 - pullbackMetricCoeff I φ x) k j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, B * δ := Finset.sum_le_sum fun k _ ↦ by
        rw [abs_mul, show (1 - pullbackMetricCoeff I φ x) k j =
            -(pullbackMetricCoeff I φ x - 1) k j by simp, abs_neg]
        exact mul_le_mul (hinv i k) (hdiff k j) (abs_nonneg _) hB
    _ = (n : ℝ) * B * δ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- For `0 < t`, outside a sufficiently large ball of radius `R₁ ≥ max R 1`:
* the metric determinant satisfies `1 / 4 ≤ det (g(x))` (hence `1 / 2 ≤ √(det (g(x)))`);
* the metric entries satisfy `|g_ij(x) - δ_ij| ≤ C₁ ‖x‖ ^ (-t)`;
* the inverse metric entries satisfy `|g⁻¹_ij(x)| ≤ 2` and
  `|g⁻¹_ij(x) - δ_ij| ≤ C₁ ‖x‖ ^ (-t)`;
* all derivatives of order `k ≤ 2` of `g_ij - δ_ij` are bounded by `C₁ ‖x‖ ^ (-t - k)`. -/
theorem exists_asymptotic_bounds (h : IsAsymptoticallyEuclideanEnd I t R φ) (ht : 0 < t) :
    ∃ R₁ C₁ : ℝ, max R 1 ≤ R₁ ∧ 0 ≤ C₁ ∧
      ∀ x ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) R₁)ᶜ,
        (1 / 4 ≤ (pullbackMetricCoeff I φ x).det ∧ (pullbackMetricCoeff I φ x).det ≠ 0 ∧
          1 / 2 ≤ Real.sqrt (pullbackMetricCoeff I φ x).det) ∧
        (∀ i j : Fin n,
          |(pullbackMetricCoeff I φ x - 1) i j| ≤ C₁ * ‖x‖ ^ (-t) ∧
          |(pullbackMetricCoeff I φ x)⁻¹ i j| ≤ 2 ∧
          |((pullbackMetricCoeff I φ x)⁻¹ - 1) i j| ≤ C₁ * ‖x‖ ^ (-t) ∧
          ∀ k ≤ 2, ‖iteratedFDeriv ℝ k (fun y ↦ (pullbackMetricCoeff I φ y - 1) i j) x‖ ≤
            C₁ * ‖x‖ ^ (-t - k)) := by
  obtain ⟨C, hC⟩ := h.exists_norm_iteratedFDeriv_le
  -- Combine eventual determinant positivity, inverse-entry bounds, and the exterior radius.
  have hdet_ev : ∀ᶠ x in Bornology.cobounded (EuclideanSpace ℝ (Fin n)),
      (1 / 4 : ℝ) < (pullbackMetricCoeff I φ x).det :=
    (h.tendsto_det_pullbackMetricCoeff_one ht).eventually (Ioi_mem_nhds (by norm_num))
  have hev := (hdet_ev.and (h.eventually_abs_inv_pullbackMetricCoeff_le ht)).and
    (tendsto_norm_cobounded_atTop.eventually (Ioi_mem_atTop (max R 1)))
  obtain ⟨R₀, -, hR₀⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.1 hev
  -- Choose a common exterior radius `R₁` and uniform constant `C₁`.
  set R₁ : ℝ := max (max R 1) R₀
  set C₁ : ℝ := max (max C 0) ((n : ℝ) * 2 * max C 0)
  refine ⟨R₁, C₁, le_max_left _ _, le_trans (le_max_right C 0) (le_max_left _ _), fun x hx ↦ ?_⟩
  have hrx₁ : R₁ < ‖x‖ := by simpa using hx
  have ⟨⟨hdet_gt, hinv_le⟩, hrx_max⟩ := hR₀ ((le_max_right _ _).trans hrx₁.le)
  have hrx : x ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ := by
    simpa using (le_max_left R 1).trans_lt hrx_max
  have hdet_ne : (pullbackMetricCoeff I φ x).det ≠ 0 :=
    ((by norm_num : (0 : ℝ) < 1 / 4).trans hdet_gt).ne'
  refine ⟨⟨hdet_gt.le, hdet_ne, Real.le_sqrt_of_sq_le (by linarith)⟩, fun i j ↦ ?_⟩
  -- Deduce uniform metric, inverse-metric, and derivative bounds at `x`.
  have hC0 : C ≤ max C 0 := le_max_left C 0
  have hC1 : max C 0 ≤ C₁ := le_max_left _ _
  have h2nC : (n : ℝ) * 2 * max C 0 ≤ C₁ := le_max_right _ _
  have hcoeff0 (k l : Fin n) :
      |(pullbackMetricCoeff I φ x - 1) k l| ≤ max C 0 * ‖x‖ ^ (-t) := by
    have hk := hC 0 (Nat.zero_le 2) k l x hrx
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, Nat.cast_zero, sub_zero] at hk
    exact hk.trans (mul_le_mul_of_nonneg_right hC0 (Real.rpow_nonneg (norm_nonneg x) _))
  have hinv_diff : |((pullbackMetricCoeff I φ x)⁻¹ - 1) i j| ≤ C₁ * ‖x‖ ^ (-t) :=
    (abs_inv_pullbackMetricCoeff_sub_le φ hdet_ne (by norm_num) hinv_le hcoeff0 i j).trans <| by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h2nC (Real.rpow_nonneg (norm_nonneg x) _)
  refine ⟨(hcoeff0 i j).trans (mul_le_mul_of_nonneg_right hC1 (Real.rpow_nonneg (norm_nonneg x) _)),
    hinv_le i j, hinv_diff, fun k hk ↦ ?_⟩
  exact (hC k hk i j x hrx).trans
    (mul_le_mul_of_nonneg_right (hC0.trans hC1) (Real.rpow_nonneg (norm_nonneg x) _))

/-- At every point, the Riemannian Jacobian of `h.toPartialDiffeomorph k hk1 hk` in the standard
basis of `ℝⁿ` is `√(det (pullbackMetricCoeff I φ x))`. -/
theorem riemannianJacobian_toPartialDiffeomorph (k : ℕ∞ω) [IsManifold I k M] (hk1 : 1 ≤ k)
    (hk : k ≤ (∞ : ℕ∞ω)) (h : IsAsymptoticallyEuclideanEnd I t R φ)
    (x : EuclideanSpace ℝ (Fin n)) :
    riemannianJacobian (I := I) (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (h.toPartialDiffeomorph k hk1 hk) x = Real.sqrt (pullbackMetricCoeff I φ x).det := by
  rw [h.coe_toPartialDiffeomorph k hk1 hk]
  exact riemannianJacobian_eq_sqrt_det_pullbackMetricCoeff φ x

/-- An asymptotically Euclidean end identifies `ℝⁿ` linearly with the target model space `E` via
the invertible differential at a point of `(closedBall 0 R)ᶜ`. -/
private theorem exists_continuousLinearEquiv_model (h : IsAsymptoticallyEuclideanEnd I t R φ) :
    Nonempty (EuclideanSpace ℝ (Fin n) ≃L[ℝ] E) := by
  have : Nonempty (Fin n) := ⟨⟨0, h.dim_pos⟩⟩
  obtain ⟨x, hx⟩ := NormedSpace.exists_lt_norm ℝ (EuclideanSpace ℝ (Fin n)) R
  obtain ⟨e, -⟩ := h.isInvertible_mfderiv x (by simpa using hx)
  exact ⟨e⟩

/-- Every asymptotically Euclidean end of positive order `t > 0` has infinite Riemannian volume. -/
theorem riemannianVolume_image_eq_top [FiniteDimensional ℝ E] [IsManifold I 1 M]
    [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (h : IsAsymptoticallyEuclideanEnd I t R φ) (ht : 0 < t) :
    riemannianVolume I M (φ '' (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ) = ⊤ := by
  have hloc : IsLocalDiffeomorphOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I 1 φ
      (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ :=
    h.isLocalDiffeomorphOn 1 le_rfl (by simp)
  have hcov := hloc.setLIntegral_riemannianVolume_image one_ne_zero
    isClosed_closedBall.isOpen_compl.measurableSet h.injOn
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (fun _ ↦ (1 : ℝ≥0∞))
  simp only [lintegral_one, Measure.restrict_apply_univ, mul_one,
    (EuclideanSpace.basisFun (Fin n) ℝ).addHaar_eq_volume] at hcov
  obtain ⟨R₁, _, hR₁, _, hbounds⟩ := h.exists_asymptotic_bounds ht
  let U₁ : Set (EuclideanSpace ℝ (Fin n)) := (closedBall 0 R₁)ᶜ
  have hsub : U₁ ⊆ (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ :=
    compl_subset_compl.2 (closedBall_subset_closedBall ((le_max_left _ _).trans hR₁))
  have hlower : ENNReal.ofReal (1 / 2) * volume U₁ ≤
      riemannianVolume I M (φ '' (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ) := by
    rw [hcov]
    calc ENNReal.ofReal (1 / 2) * volume U₁
        = ∫⁻ _ in U₁, ENNReal.ofReal (1 / 2) ∂volume := by rw [setLIntegral_const]
      _ ≤ ∫⁻ x in U₁, ENNReal.ofReal (riemannianJacobian (I := I)
            (EuclideanSpace.basisFun (Fin n) ℝ).toBasis φ x) ∂volume := by
          refine setLIntegral_mono' isClosed_closedBall.isOpen_compl.measurableSet fun x hx ↦ ?_
          rw [riemannianJacobian_eq_sqrt_det_pullbackMetricCoeff]
          exact ENNReal.ofReal_le_ofReal (hbounds x hx).1.2.2
      _ ≤ ∫⁻ x in (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ, ENNReal.ofReal
            (riemannianJacobian (I := I) (EuclideanSpace.basisFun (Fin n) ℝ).toBasis φ x)
            ∂volume := lintegral_mono_set hsub
  have : Nonempty (Fin n) := ⟨⟨0, h.dim_pos⟩⟩
  rw [volume.addHaar_compl_closedBall, ENNReal.mul_top (by norm_num)] at hlower
  exact top_unique hlower

/-- No compact `C¹` manifold with a continuous Riemannian metric admits an asymptotically Euclidean
end of positive order `t > 0`. -/
theorem not_compactSpace [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (h : IsAsymptoticallyEuclideanEnd I t R φ) (ht : 0 < t) : ¬ CompactSpace M := by
  intro _
  obtain ⟨e⟩ := h.exists_continuousLinearEquiv_model
  have : FiniteDimensional ℝ E := e.toLinearEquiv.finiteDimensional
  let _ : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  have htop : riemannianVolume I M univ = ⊤ :=
    top_unique <| (h.riemannianVolume_image_eq_top ht).symm.trans_le (measure_mono (subset_univ _))
  exact htop.not_lt isCompact_univ.measure_lt_top

end IsAsymptoticallyEuclideanEnd

end TauCeti

end
