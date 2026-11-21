/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Section
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Pullback.Average
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Metric
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Polar
import TauCeti.Geometry.Symplectic.Manifold.Flat

/-!
# Compatible metrics and pullback averaging

A smooth two-form `σ` on a manifold `M` compatible with a smooth almost complex structure `J`
(`TauCeti.SmoothTwoForm.Compatible`: `σ(J u, J w) = σ(u, w)` and `σ(u, J u) > 0` for `u ≠ 0`)
determines the smooth Riemannian metric

`g(u, w) = σ(u, J w)`

(`TauCeti.SmoothTwoForm.Compatible.metric`). It is the unique metric with this property, and once
it is installed as the metric of `M`, `J` is orthogonal and the Kähler two-form `⟪J ·, ·⟫` of `J`
(`TauCeti.SmoothAlmostComplexStructure.kahlerTwoForm`) is `σ`. Conversely, the Kähler two-form of
an orthogonal smooth almost complex structure is compatible with it, and its compatible metric is
the metric one started from. Thus, for a fixed `J`, the compatible two-forms and the smooth
metrics making `J` orthogonal determine each other.

This is how symplectic data, on which pseudoholomorphic curves are defined, become the
almost-Kähler data `(g, J, ω)` on which the Seiberg–Witten equations of a symplectic four-manifold
are set up (for instance `TauCeti.SeibergWitten.complexDeformationOperator`, which takes an
oriented Riemannian four-manifold with an orthogonal `J` satisfying
`TauCeti.SmoothAlmostComplexStructure.IsCompatibleOrientation`). On a Hausdorff σ-compact
four-manifold every nondegenerate smooth two-form `σ` admits a compatible `J`
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_compatible`); with the metric of `(σ, J)`, `J` is
compatible with the symplectic orientation of `σ` and has Kähler two-form `σ`
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_isCompatibleOrientation_and_kahlerTwoForm_eq`).

A given `C^n` Riemannian metric can also be averaged with its pullback by a smooth almost
complex structure `J`. This produces a `J`-invariant metric in arbitrary dimension, without
an orientation hypothesis. Existence of an initial metric is used only in the separate
finite-dimensional Hausdorff σ-compact existence theorem.

## Main definitions

* `TauCeti.SmoothAlmostComplexStructure.compatibleAverage`: the average of a given metric and
  its pullback by `J`, with the same regularity and invariant under `J`.

* `TauCeti.SmoothTwoForm.Compatible.metric`: the smooth Riemannian metric `σ(·, J ·)` of a smooth
  compatible pair `(σ, J)`.

## Main results

* `TauCeti.SmoothTwoForm.Compatible.metric_inner` and
  `TauCeti.SmoothTwoForm.Compatible.eq_metric_iff`: `g(u, w) = σ(u, J w)`, and this characterizes
  the metric.
* `TauCeti.SmoothTwoForm.Compatible.inner_eq_eval₂`: the same identity for the installed metric.
* `TauCeti.SmoothAlmostComplexStructure.metric_compatible_kahlerTwoForm`: the Kähler two-form of an
  orthogonal `J` is compatible with `J`
  (`TauCeti.SmoothAlmostComplexStructure.compatible_kahlerTwoForm`), and its compatible metric is
  the metric of `M`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.exists_isCompatibleOrientation_and_kahlerTwoForm_eq`:
  almost-Kähler data with Kähler form a prescribed nondegenerate two-form on a four-manifold.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford (2017),
  Chapter 4.
* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
-/

public section

noncomputable section

open Bundle Module
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

section CompatiblePair

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}

namespace SmoothTwoForm.Compatible

omit [FiniteDimensional ℝ E] in
/-- The bilinear forms `σ(-J ·, ·)` of a compatible pair are `σ(·, J ·)`. -/
private theorem flatComp_neg_apply (h : σ.Compatible J) (x : M) (u w : TangentSpace I x) :
    σ.flatComp (-J.toEndomorphism) x u w = σ.eval₂ x u (J x w) := by
  rw [flatComp_apply, ← h.invariant.apply x u (J x w), SmoothAlmostComplexStructure.apply_apply,
    SmoothBundleForm.eval₂_neg_right]
  simp [flat_apply]

omit [FiniteDimensional ℝ E] in
/-- The bilinear forms `σ(·, J ·)` of a compatible pair are symmetric and positive definite. -/
private theorem flatComp_neg_mem_positiveDefiniteBilinearSections (h : σ.Compatible J) :
    σ.flatComp (-J.toEndomorphism) ∈ Manifold.positiveDefiniteBilinearSections I ∞ E
      (fun x : M ↦ TangentSpace I x) := by
  refine (Manifold.mem_positiveDefiniteBilinearSections _).2
    ⟨(Manifold.mem_symmetricBilinearSections _).2 fun x u w ↦ ?_, fun x u hu ↦ ?_⟩
  · rw [h.flatComp_neg_apply, h.flatComp_neg_apply, SmoothBundleForm.eval₂_swap,
      ← h.invariant.apply x (J x w) u, SmoothAlmostComplexStructure.apply_apply,
      SmoothBundleForm.eval₂_neg_left, neg_neg]
  · rw [h.flatComp_neg_apply]
    exact tames_iff.1 h.tames x u hu

/-- **The metric of a compatible pair.** A smooth two-form `σ` compatible with a smooth almost
complex structure `J` determines the smooth Riemannian metric `g(u, w) = σ(u, J w)`
(`TauCeti.SmoothTwoForm.Compatible.metric_inner`). -/
def metric (h : σ.Compatible J) :
    ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) :=
  .ofPositiveDefiniteSection (σ.flatComp (-J.toEndomorphism))
    h.flatComp_neg_mem_positiveDefiniteBilinearSections

@[simp]
theorem metric_inner (h : σ.Compatible J) (x : M) (u w : TangentSpace I x) :
    h.metric.inner x u w = σ.eval₂ x u (J x w) := by
  rw [metric, ContMDiffRiemannianMetric.ofPositiveDefiniteSection_inner, h.flatComp_neg_apply]

/-- The metric of a compatible pair `(σ, J)` is the only smooth metric with
`g(u, w) = σ(u, J w)`. -/
theorem eq_metric_iff (h : σ.Compatible J)
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    g = h.metric ↔ ∀ x u w, g.inner x u w = σ.eval₂ x u (J x w) := by
  refine ⟨fun hg x u w ↦ by rw [hg, metric_inner], fun hg ↦ ?_⟩
  ext x u w
  rw [hg, metric_inner]

/-- Once the metric of a compatible pair `(σ, J)` is installed as the metric of `M`, its inner
product is `⟪u, w⟫ = σ(u, J w)`. -/
theorem inner_eq_eval₂ (h : σ.Compatible J) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨h.metric.toRiemannianMetric⟩
    ∀ x u w, ⟪u, w⟫ = σ.eval₂ x u (J x w) :=
  fun x u w ↦ by
    rw [ContMDiffRiemannianMetric.inner_riemannianBundle, metric_inner]

end SmoothTwoForm.Compatible

namespace SmoothAlmostComplexStructure

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The metric of the compatible pair formed by an orthogonal smooth almost complex structure and
its Kähler two-form is the metric of `M`. -/
theorem metric_compatible_kahlerTwoForm
    (hJ : ∀ (x : M) (u w : TangentSpace I x), ⟪J x u, J x w⟫ = ⟪u, w⟫) :
    (compatible_kahlerTwoForm hJ).metric =
      ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := I) (n := ∞) (F := E) := by
  refine (((compatible_kahlerTwoForm hJ).eq_metric_iff _).2 fun x u w ↦ ?_).symm
  rw [ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]
  exact inner_eq_eval₂_kahlerTwoForm hJ x u w

end SmoothAlmostComplexStructure

namespace SmoothTwoForm.IsNondegenerate

/-- **Almost-Kähler data of a nondegenerate two-form on a four-manifold.** Let `σ` be a
nondegenerate smooth two-form, for instance a symplectic form, on a Hausdorff σ-compact
four-manifold oriented by the symplectic orientation of `σ`. Then `σ` has a compatible smooth
almost complex structure `J` such that, for the metric `σ(·, J ·)`, `J` is orthogonal, compatible
with the orientation, and has Kähler two-form `σ`. -/
theorem exists_isCompatibleOrientation_and_kahlerTwoForm_eq [T2Space M] [SigmaCompactSpace M]
    (o : Manifold.Orientation I M (Fin 4)) (hσ : σ.IsNondegenerate)
    (ho : ∀ x : M,
      (letI : Fact (finrank ℝ (TangentSpace I x) = 4) := o.fact_finrank_tangentSpace x
       (hσ.symplecticFormAt x).orientation Fact.out) = o.orientationAt x) :
    ∃ (J : SmoothAlmostComplexStructure I M) (h : σ.Compatible J),
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨h.metric.toRiemannianMetric⟩
      letI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
        Bundle.instIsContMDiffRiemannianBundle h.metric
      J.IsCompatibleOrientation o ∧
        J.kahlerTwoForm
          (SmoothAlmostComplexStructure.inner_apply_apply_of_inner_eq h.inner_eq_eval₂) = σ := by
  obtain ⟨J, h⟩ := hσ.exists_compatible
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨h.metric.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    Bundle.instIsContMDiffRiemannianBundle h.metric
  exact ⟨J, h, SmoothAlmostComplexStructure.isCompatibleOrientation_of_symplectic o hσ
    h.inner_eq_eval₂ ho, SmoothAlmostComplexStructure.kahlerTwoForm_eq_of_inner_eq h.inner_eq_eval₂⟩

end SmoothTwoForm.IsNondegenerate

end CompatiblePair

end TauCeti

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
