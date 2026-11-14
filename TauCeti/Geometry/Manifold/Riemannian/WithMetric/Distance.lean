/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Distance

/-!
# Distance and completeness for a dominating metric

If a Riemannian metric `g` uniformly dominates the given tangent norms on `M`, the
identification `ofWithMetric : WithMetric g → M` is Lipschitz for Riemannian extended distance.
When `M` is complete for that distance, the copy carrying `g` is complete as well.
Extended distances allow points in distinct connected components to be infinitely far apart.

The carrier and tangent-norm comparison are provided by `TauCeti.WithMetric`.
See M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §3, Lemma 3.3.
-/

public section

open Bundle Manifold MeasureTheory Set TauCeti.Manifold
open scoped ContDiff ENNReal Manifold NNReal Topology

noncomputable section

namespace TauCeti.WithMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}

section Intrinsic

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}

/-- If the given squared tangent norms are bounded by `C²` times `g`, forgetting the copy
carrying `g` increases Riemannian extended distance by at most the positive factor `C`. -/
theorem riemannianEDist_ofWithMetric_le_mul {C : ℝ≥0} (hC0 : C ≠ 0)
    (hg : ∀ x (v : TangentSpace I x), ‖v‖ ^ 2 ≤ (C : ℝ) ^ 2 * g.inner x v v)
    (x y : WithMetric g) :
    riemannianEDist I x.ofWithMetric y.ofWithMetric ≤ C * riemannianEDist I x y :=
  Manifold.riemannianEDist_le_mul contMDiff_ofWithMetric hC0
    (fun x v ↦ norm_mfderiv_ofWithMetric_le_mul
      (hg x.ofWithMetric (mfderiv I I ofWithMetric x v))) x y

end Intrinsic

section Ambient

variable {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  {g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}

/-- If the given squared tangent norms are bounded by `C²` times `g` and the copy is equipped
with its Riemannian distance, `ofWithMetric` is `C`-Lipschitz for positive `C`. -/
theorem lipschitzWith_ofWithMetric [PseudoEMetricSpace (WithMetric g)]
    [IsRiemannianManifold I (WithMetric g)] {C : ℝ≥0} (hC0 : C ≠ 0)
    (hg : ∀ x (v : TangentSpace I x), ‖v‖ ^ 2 ≤ (C : ℝ) ^ 2 * g.inner x v v) :
    LipschitzWith C (ofWithMetric : WithMetric g → M) := by
  intro x y
  rw [IsRiemannianManifold.out (I := I), IsRiemannianManifold.out (I := I)]
  exact riemannianEDist_ofWithMetric_le_mul hC0 hg x y

/-- A metric uniformly dominating a complete Riemannian metric is complete for its own
Riemannian extended distance. -/
theorem completeSpace_of_sq_norm_le_mul [CompleteSpace M] {C : ℝ≥0} (hC0 : C ≠ 0)
    (hg : ∀ x (v : TangentSpace I x), ‖v‖ ^ 2 ≤ (C : ℝ) ^ 2 * g.inner x v v) :
    letI : PseudoEMetricSpace (WithMetric g) := .ofRiemannianMetric I (WithMetric g)
    CompleteSpace (WithMetric g) := by
  let : PseudoEMetricSpace (WithMetric g) := .ofRiemannianMetric I (WithMetric g)
  exact CompleteSpace.of_comp_eq_id (toWithMetric g) ofWithMetric rfl
    continuous_toWithMetric (lipschitzWith_ofWithMetric hC0 hg).uniformContinuous

end Ambient

end TauCeti.WithMetric

end
