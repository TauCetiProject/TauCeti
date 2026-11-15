/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Completeness

/-!
# A metric dominating a complete metric is geodesically complete

Let `M` be complete for its Riemannian extended distance and let `g` be a smooth Riemannian
metric uniformly dominating the given tangent norms. Then the copy `TauCeti.WithMetric g` is
metrically complete by `TauCeti.WithMetric.completeSpace_of_sq_norm_le_mul`, hence geodesically
complete by `TauCeti.Manifold.isGeodesicallyCompleteAt_of_completeSpace`. Its maximal geodesics,
read in `M`, are Lipschitz with a uniform multiple of their constant `g`-speed as Lipschitz
constant.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §2, Thm. 2.8, and Ch. 7, §3,
  Lemma 3.3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Ch. 6.
-/

public section

open Bundle Manifold TauCeti.Manifold
open scoped ContDiff Manifold NNReal

noncomputable section

namespace TauCeti.WithMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}

/-- **A maximal geodesic of a dominating metric is Lipschitz for the given distance.** If `g`
uniformly dominates the given metric of `M` with positive comparison factor `C`, a maximal
geodesic of `g`, read in `M`, is Lipschitz on its maximal interval for the Riemannian distance
of `M`, with `C` times its `g`-speed as constant. -/
theorem lipschitzOnWith_ofWithMetric_maximalGeodesic
    {C : ℝ≥0} (hC0 : C ≠ 0)
    (hg : ∀ x (v : TangentSpace I x), ‖v‖ ^ 2 ≤ (C : ℝ) ^ 2 * g.inner x v v)
    (p : WithMetric g) (v : TangentSpace I p) :
    LipschitzOnWith (C * ‖v‖₊) (ofWithMetric ∘ maximalGeodesic I (WithMetric g) p v)
      (geodesicInterval I (WithMetric g) p v) := by
  let : EMetricSpace (WithMetric g) := .ofRiemannianMetric I (WithMetric g)
  exact (lipschitzWith_ofWithMetric hC0 hg).comp_lipschitzOnWith
    (lipschitzOnWith_maximalGeodesic (I := I) (p := p) (v := v))

/-- **A metric dominating a complete Riemannian metric is geodesically complete.** If `M` is
complete for its Riemannian distance and `g` is a Riemannian metric on `M` with
`|v|² ≤ C² g(v, v)` for a fixed positive `C` and every tangent vector `v`, then every maximal
geodesic of `g` is defined for all time. -/
theorem isGeodesicallyCompleteAt_of_sq_norm_le_mul [CompleteSpace M]
    {C : ℝ≥0} (hC0 : C ≠ 0)
    (hg : ∀ x (v : TangentSpace I x), ‖v‖ ^ 2 ≤ (C : ℝ) ^ 2 * g.inner x v v)
    (p : WithMetric g) :
    IsGeodesicallyCompleteAt I (WithMetric g) p := by
  let : EMetricSpace (WithMetric g) := .ofRiemannianMetric I (WithMetric g)
  have : CompleteSpace (WithMetric g) := completeSpace_of_sq_norm_le_mul hC0 hg
  exact isGeodesicallyCompleteAt_of_completeSpace p

end TauCeti.WithMetric

end
