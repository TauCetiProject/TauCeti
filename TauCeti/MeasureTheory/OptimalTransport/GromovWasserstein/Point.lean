/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.GromovWasserstein.Space
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# One-point kernels and completeness of the target

The constant one-point kernels form a closed isometric copy of the metric target `Z` inside
`GromovWassersteinSpace p Z`, for every `1 ≤ p ≤ ∞`. In particular, completeness of the
Gromov–Wasserstein space forces completeness of `Z`. Neither separability nor completeness
of the target is assumed in the closedness theorem.

The closedness statement also rules out new nonconstant kernels appearing as limits of
one-point kernels, even when the target is incomplete.

## References

* M. Bauer, F. Mémoli, T. Needham and M. Nishino, *The Z-Gromov–Wasserstein distance*,
  J. Mach. Learn. Res. 26 (2025), Theorem 39, for the characterization of completeness.
  Only the necessary direction is proved here, with the full-distortion convention.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace TauCeti.GromovWassersteinSpace

universe u v

variable {p : ℝ≥0∞} {Z : Type v} [MetricSpace Z] [Fact (1 ≤ p)]

/-- One-point kernels form a closed subset of the Gromov–Wasserstein space, even for an
incomplete or nonseparable target. -/
theorem isClosed_range_point :
    IsClosed (range (point.{u} (p := p) (Z := Z))) := by
  classical
  apply IsSeqClosed.isClosed
  intro Ks L hKs hL
  choose zs hpoint_eq using hKs
  obtain ⟨K, rfl⟩ := mk_surjective L
  have hnorm : Tendsto (fun n ↦
      eLpNorm (fun q ↦ edist (K.kernel q) (zs n)) p (K.measure.prod K.measure)) atTop
      (𝓝 0) := by
    simpa only [← hpoint_eq, edist_comm, edist_mk_point] using
      (tendsto_iff_edist_tendsto_0.1 hL)
  -- Scalar distances let us use convergence in measure without any linear structure on `Z`.
  have hreal : Tendsto (fun n ↦
      eLpNorm (fun q ↦ dist (K.kernel q) (zs n)) p (K.measure.prod K.measure)) atTop
      (𝓝 0) := by
    simp_rw [edist_dist] at hnorm
    exact (tendsto_congr fun n ↦ eLpNorm_ofReal
      (fun q ↦ dist (K.kernel q) (zs n)) (.of_forall fun _ ↦ dist_nonneg)).1 hnorm
  have hmeasure : TendstoInMeasure (K.measure.prod K.measure)
      (fun n q ↦ dist (K.kernel q) (zs n)) atTop 0 :=
    tendstoInMeasure_of_tendsto_eLpNorm
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) (by simpa using hreal)
  obtain ⟨ns, hns, hae⟩ := hmeasure.exists_seq_tendsto_ae
  obtain ⟨q, hq⟩ := hae.exists
  have hzs : Tendsto (zs ∘ ns) atTop (𝓝 (K.kernel q)) := by
    apply tendsto_iff_dist_tendsto_zero.2
    simpa only [Pi.zero_apply, Function.comp_apply, dist_comm] using hq
  have hpoint := ((isometry_point.{u} (p := p)).continuous.tendsto (K.kernel q)).comp hzs
  have hlimit : Tendsto (fun n ↦ point (p := p) (zs (ns n))) atTop (𝓝 (mk K)) := by
    simpa only [Function.comp_def, ← hpoint_eq] using hL.comp hns.tendsto_atTop
  exact ⟨K.kernel q, tendsto_nhds_unique hpoint hlimit⟩

/-- The target embeds as a closed isometric copy through its constant one-point kernels. -/
theorem isClosedEmbedding_point :
    Topology.IsClosedEmbedding (point.{u} (p := p) (Z := Z)) :=
  ⟨isometry_point.isEmbedding, isClosed_range_point⟩

variable (p) in
/-- Completeness of the Gromov–Wasserstein space implies completeness of the metric target.
No global separability hypothesis is required, including at exponent `∞`. -/
theorem completeSpace_of_completeSpace_gromovWassersteinSpace
    [CompleteSpace (GromovWassersteinSpace.{u} p Z)] : CompleteSpace Z :=
  (isometry_point.{u} (p := p) (Z := Z)).isUniformInducing.completeSpace
    (isClosed_range_point (p := p) (Z := Z)).isComplete

end TauCeti.GromovWassersteinSpace
