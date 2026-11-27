/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Conformal
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Distance

/-!
# Intrinsic ball volume under constant metric scaling

Rescaling a Riemannian metric by `c²`, with `c > 0`, multiplies intrinsic distances by `c`
and volume by `c^dim`. The ball-volume identity retains infinite distances between components.

The scaling arguments are adapted from the formalizations in
[frenzymath/lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
[frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Bundle Manifold MeasureTheory Set TauCeti TauCeti.WithMetric
open scoped ContDiff ENNReal Manifold NNReal

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))

/-- Multiplying a metric by `c²` multiplies the measure of corresponding sets by `c^dim`. -/
theorem riemannianVolume_rescale_const_sq_apply [LindelofSpace M] {c : ℝ} (hc : 0 < c)
    (s : Set (WithMetric (g.rescale (fun _ ↦ c ^ 2) contMDiff_const
      (fun _ ↦ sq_pos_of_pos hc)))) :
    riemannianVolume I _ s =
      ENNReal.ofReal (c ^ Module.finrank ℝ E) * riemannianVolume I (WithMetric g)
        ((fun x : WithMetric g ↦ toWithMetric
          (g.rescale (fun _ ↦ c ^ 2) contMDiff_const (fun _ ↦ sq_pos_of_pos hc))
          x.ofWithMetric) ⁻¹' s) := by
  rw [Bundle.ContMDiffRiemannianMetric.riemannianVolume_eq_map_withDensity_relativeVolumeDensity g
    (g.rescale (fun _ ↦ c ^ 2) contMDiff_const (fun _ ↦ sq_pos_of_pos hc)),
    (measurableEmbedding_toWithMetric_ofWithMetric g _).map_apply]
  simp only [g.relativeVolumeDensity_homothety hc, withDensity_const, smul_apply, smul_eq_mul]

/-- Under `g ↦ c² g`, the volume of an intrinsic ball of radius `r` is `c^dim` times the old
volume at radius `r / c`. The equality holds for every extended radius and every component. -/
theorem riemannianVolume_eball_rescale_const_sq [T3Space M] [LindelofSpace M]
    {c : ℝ} (hc : 0 < c) (x : M) (r : ℝ≥0∞) :
    letI : EMetricSpace (WithMetric g) := .ofRiemannianMetric I (WithMetric g)
    letI : EMetricSpace (WithMetric (g.rescale (fun _ ↦ c ^ 2) contMDiff_const
      (fun _ ↦ sq_pos_of_pos hc))) := .ofRiemannianMetric I _
    riemannianVolume I _
        (Metric.eball (toWithMetric (g.rescale (fun _ ↦ c ^ 2) contMDiff_const
          (fun _ ↦ sq_pos_of_pos hc)) x) r) =
      ENNReal.ofReal (c ^ Module.finrank ℝ E) *
        riemannianVolume I (WithMetric g)
          (Metric.eball (toWithMetric g x) (r / ENNReal.ofReal c)) := by
  let : EMetricSpace (WithMetric g) := .ofRiemannianMetric I (WithMetric g)
  let : EMetricSpace (WithMetric (g.rescale (fun _ ↦ c ^ 2) contMDiff_const
    (fun _ ↦ sq_pos_of_pos hc))) := .ofRiemannianMetric I _
  rw [riemannianVolume_rescale_const_sq_apply g hc]
  congr 2
  ext y
  simp only [mem_preimage, Metric.mem_eball]
  rw [IsRiemannianManifold.out (I := I), IsRiemannianManifold.out (I := I),
    g.riemannianEDist_rescale_const_sq hc,
    ENNReal.lt_div_iff_mul_lt (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr hc))
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]

/-- Under `g ↦ c g`, the volume of an intrinsic ball of radius `r` is `√c^dim` times the old
volume at radius `r / √c`. The equality holds for every extended radius and every component. -/
theorem riemannianVolume_eball_rescale_const [T3Space M] [LindelofSpace M]
    {c : ℝ} (hc : 0 < c) (x : M) (r : ℝ≥0∞) :
    letI : EMetricSpace (WithMetric g) := .ofRiemannianMetric I (WithMetric g)
    letI : EMetricSpace (WithMetric (g.rescale (fun _ ↦ c) contMDiff_const
      (fun _ ↦ hc))) := .ofRiemannianMetric I _
    riemannianVolume I _
        (Metric.eball (toWithMetric (g.rescale (fun _ ↦ c) contMDiff_const
          (fun _ ↦ hc)) x) r) =
      ENNReal.ofReal (Real.sqrt c ^ Module.finrank ℝ E) *
        riemannianVolume I (WithMetric g)
          (Metric.eball (toWithMetric g x) (r / ENNReal.ofReal (Real.sqrt c))) := by
  have h := g.riemannianVolume_eball_rescale_const_sq (Real.sqrt_pos.mpr hc) x r
  rw [g.rescale_const_sqrt_sq hc] at h
  exact h

/-- Under `g ↦ c² g`, a power-law lower bound for intrinsic ball volumes on radii at most `R`
holds on radii at most `c * R`. -/
theorem riemannianVolume_eball_lower_bound_rescale_const_sq [T3Space M] [LindelofSpace M]
    {c : ℝ} (hc : 0 < c) {a : ℝ≥0∞} {R : ℝ}
    (hvol : letI : EMetricSpace (WithMetric g) := .ofRiemannianMetric I (WithMetric g)
      ∀ x : WithMetric g, ∀ r : ℝ, 0 < r → r ≤ R →
        a * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
          riemannianVolume I (WithMetric g) (Metric.eball x (ENNReal.ofReal r))) :
    letI : EMetricSpace (WithMetric (g.rescale (fun _ ↦ c ^ 2) contMDiff_const
      (fun _ ↦ sq_pos_of_pos hc))) := .ofRiemannianMetric I _
    ∀ x : WithMetric (g.rescale (fun _ ↦ c ^ 2) contMDiff_const
      (fun _ ↦ sq_pos_of_pos hc)), ∀ r : ℝ, 0 < r → r ≤ c * R →
      a * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
        riemannianVolume I _ (Metric.eball x (ENNReal.ofReal r)) := by
  let : EMetricSpace (WithMetric g) := .ofRiemannianMetric I (WithMetric g)
  let : EMetricSpace (WithMetric (g.rescale (fun _ ↦ c ^ 2) contMDiff_const
    (fun _ ↦ sq_pos_of_pos hc))) := .ofRiemannianMetric I _
  intro x r hr hrR
  have hsmall : r / c ≤ R := (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using hrR)
  have h := mul_le_mul_right (hvol (toWithMetric g x.ofWithMetric) (r / c)
    (div_pos hr hc) hsmall) (ENNReal.ofReal (c ^ Module.finrank ℝ E))
  have hscale : ENNReal.ofReal (c ^ Module.finrank ℝ E) *
      ENNReal.ofReal (r / c) ^ Module.finrank ℝ E =
        ENNReal.ofReal r ^ Module.finrank ℝ E := by
    rw [← ENNReal.ofReal_pow (div_nonneg hr.le hc.le),
      ← ENNReal.ofReal_mul (pow_nonneg hc.le _), ← mul_pow,
      show c * (r / c) = r by field_simp,
      ENNReal.ofReal_pow hr.le]
  have hball := riemannianVolume_eball_rescale_const_sq g hc x.ofWithMetric (ENNReal.ofReal r)
  rw [toWithMetric_ofWithMetric, ← ENNReal.ofReal_div_of_pos hc] at hball
  rw [hball]
  convert h using 1
  rw [mul_left_comm, hscale]

/-- A power-law lower bound for intrinsic ball volumes on radii at most `R` is preserved by
rescaling the metric by `c > 0`, transferred to radii at most `√c * R`. -/
theorem riemannianVolume_eball_lower_bound_rescale_const [T3Space M] [LindelofSpace M]
    {c : ℝ} (hc : 0 < c) {a : ℝ≥0∞} {R : ℝ}
    (hvol : letI : EMetricSpace (WithMetric g) := .ofRiemannianMetric I (WithMetric g)
      ∀ x : WithMetric g, ∀ r : ℝ, 0 < r → r ≤ R →
        a * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
          riemannianVolume I (WithMetric g) (Metric.eball x (ENNReal.ofReal r))) :
    letI : EMetricSpace (WithMetric (g.rescale (fun _ ↦ c) contMDiff_const
      (fun _ ↦ hc))) := .ofRiemannianMetric I _
    ∀ x : WithMetric (g.rescale (fun _ ↦ c) contMDiff_const (fun _ ↦ hc)),
      ∀ r : ℝ, 0 < r → r ≤ Real.sqrt c * R →
      a * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
        riemannianVolume I _ (Metric.eball x (ENNReal.ofReal r)) := by
  have h := g.riemannianVolume_eball_lower_bound_rescale_const_sq (Real.sqrt_pos.mpr hc) hvol
  rw [g.rescale_const_sqrt_sq hc] at h
  exact h

end Bundle.ContMDiffRiemannianMetric
