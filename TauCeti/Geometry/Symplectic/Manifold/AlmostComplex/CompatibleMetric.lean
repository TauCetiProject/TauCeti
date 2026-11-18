/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Pullback.Average
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Basic

/-!
# Metrics compatible with an almost complex structure

Let `j` be a smooth almost complex structure on a manifold `M`. A Riemannian metric `g` on `M` is
*compatible with* `j` when `j` is a `g`-isometry, `g(j u, j v) = g(u, v)`. Averaging any metric with
its pullback by `j`,

`g'(u, v) = ½ (g(u, v) + g(j u, j v))`,

gives a compatible metric (`TauCeti.SmoothAlmostComplexStructure.compatibleAverage`), so compatible
metrics exist whenever metrics do, for instance over a σ-compact Hausdorff base. No dimension or
orientation hypothesis is needed.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure.compatibleAverage`: the average of a metric and its
  pullback by `j`, compatible with `j`
  (`TauCeti.SmoothAlmostComplexStructure.compatibleAverage_inner_apply_apply`). It is the instance
  `A = j` of `Bundle.ContMDiffRiemannianMetric.pullbackAverage`, and fixes exactly the compatible
  metrics (`TauCeti.SmoothAlmostComplexStructure.compatibleAverage_eq_self_iff`).
* `TauCeti.SmoothAlmostComplexStructure.exists_contMDiffRiemannianMetric_compatible`: compatible
  metrics exist over a σ-compact Hausdorff manifold.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] (j : SmoothAlmostComplexStructure I M)

variable {n : ℕ∞ω} [ENat.LEInfty n]

/-- **The compatible average of a metric.** The mean of a metric `g` and its pullback by `j`,
`½ (g(u, v) + g(j u, j v))`. It is compatible with `j`
(`TauCeti.SmoothAlmostComplexStructure.compatibleAverage_inner_apply_apply`). -/
def compatibleAverage (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) :
    ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x) :=
  g.pullbackAverage j.tangentEquiv j.contMDiff_tangentEquiv

/-- The compatible average is the half-sum of the metric and its pullback by `j`. -/
@[simp]
theorem compatibleAverage_inner
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (x : M)
    (u v : TangentSpace I x) :
    (j.compatibleAverage g).inner x u v = 2⁻¹ * (g.inner x u v + g.inner x (j x u) (j x v)) := by
  simp [compatibleAverage]

/-- The compatible average is compatible with `j`: `j` is an isometry for it. -/
theorem compatibleAverage_inner_apply_apply
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (x : M)
    (u v : TangentSpace I x) :
    (j.compatibleAverage g).inner x (j x u) (j x v) = (j.compatibleAverage g).inner x u v := by
  simpa [compatibleAverage] using g.pullbackAverage_inner_apply_apply _ j.contMDiff_tangentEquiv
    (by simp) x u v

/-- A metric is its own compatible average exactly when it is compatible with `j`. -/
theorem compatibleAverage_eq_self_iff
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) :
    j.compatibleAverage g = g ↔
      ∀ x (u v : TangentSpace I x), g.inner x (j x u) (j x v) = g.inner x u v := by
  simpa [compatibleAverage] using g.pullbackAverage_eq_self_iff _ j.contMDiff_tangentEquiv

/-- Compatible averaging is idempotent. -/
@[simp]
theorem compatibleAverage_compatibleAverage
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) :
    j.compatibleAverage (j.compatibleAverage g) = j.compatibleAverage g :=
  (j.compatibleAverage_eq_self_iff _).2 (j.compatibleAverage_inner_apply_apply g)

/-- The structures `j` and `-j` have the same compatible averages. -/
@[simp]
theorem neg_compatibleAverage
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) :
    (-j).compatibleAverage g = j.compatibleAverage g := by
  ext x u v
  simp

/-- Compatible averaging commutes with lowering the smoothness of the metric. -/
@[simp]
theorem compatibleAverage_ofLE {m : ℕ∞ω} [ENat.LEInfty m]
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hmn : m ≤ n) :
    j.compatibleAverage (g.ofLE hmn) = (j.compatibleAverage g).ofLE hmn := by
  ext x u v
  simp

/-- **Existence of compatible metrics.** A σ-compact Hausdorff manifold modelled on a
finite-dimensional space with a smooth almost complex structure `j` carries a `C^n` Riemannian
metric for which `j` is an isometry. -/
theorem exists_contMDiffRiemannianMetric_compatible [FiniteDimensional ℝ E] [T2Space M]
    [SigmaCompactSpace M] {n : ℕ∞} :
    ∃ g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x),
      ∀ x (u v : TangentSpace I x), g.inner x (j x u) (j x v) = g.inner x u v := by
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := I) (n := n) (F := E)
    (E := fun x : M ↦ TangentSpace I x)
  exact ⟨j.compatibleAverage g, j.compatibleAverage_inner_apply_apply g⟩

end SmoothAlmostComplexStructure

end TauCeti
