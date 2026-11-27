/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Decay
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Infinite volume of asymptotically Euclidean ends

Every asymptotically Euclidean end `φ` of positive decay order `t > 0` on `(closedBall 0 R)ᶜ` has
infinite Riemannian volume (`riemannianVolume_image_eq_top`), because outside a sufficiently large
ball the pulled-back metric determinant satisfies `1 / 4 ≤ det (g(x))` (and hence
`1 / 2 ≤ √(det (g(x)))` via `IsAsymptoticallyEuclideanEnd.exists_asymptotic_bounds`). As a
consequence, no compact `C¹` manifold with a continuous Riemannian metric admits an asymptotically
Euclidean end of positive order (`not_compactSpace`).

## Main results

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

open Bundle Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff ENNReal Manifold Matrix RealInnerProductSpace Topology

namespace TauCeti

variable {n : ℕ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

namespace IsAsymptoticallyEuclideanEnd

variable {t R : ℝ} {φ : EuclideanSpace ℝ (Fin n) → M}

/-- Every asymptotically Euclidean end of positive order `t > 0` has infinite Riemannian volume. -/
theorem riemannianVolume_image_eq_top [IsManifold I 1 M]
    [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (h : IsAsymptoticallyEuclideanEnd I t R φ) (ht : 0 < t) :
    let _ := h.finiteDimensional
    riemannianVolume I M (φ '' (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ) = ⊤ := by
  have : FiniteDimensional ℝ E := h.finiteDimensional
  have hloc : IsLocalDiffeomorphOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I 1 φ
      (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ :=
    h.isLocalDiffeomorphOn 1 le_rfl (by simp)
  have hcov := hloc.setLIntegral_riemannianVolume_image one_ne_zero
    isClosed_closedBall.isOpen_compl.measurableSet h.injOn
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (fun _ ↦ (1 : ℝ≥0∞))
  simp only [lintegral_one, Measure.restrict_apply_univ, mul_one,
    (EuclideanSpace.basisFun (Fin n) ℝ).addHaar_eq_volume] at hcov
  have hjac (x : EuclideanSpace ℝ (Fin n)) :
      riemannianJacobian (I := I) (EuclideanSpace.basisFun (Fin n) ℝ).toBasis φ x =
        Real.sqrt (pullbackMetricCoeff I φ x).det := by
    rw [riemannianJacobian_eq_sqrt_det_gram]
    congr 2
    ext i j
    rw [Matrix.gram_apply, OrthonormalBasis.coe_toBasis, pullbackMetricCoeff_apply]
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
          rw [hjac x]
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
  have : FiniteDimensional ℝ E := h.finiteDimensional
  let _ : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  have htop : riemannianVolume I M univ = ⊤ :=
    top_unique <| (h.riemannianVolume_image_eq_top ht).symm.trans_le (measure_mono (subset_univ _))
  exact htop.not_lt isCompact_univ.measure_lt_top

end IsAsymptoticallyEuclideanEnd

end TauCeti

end
