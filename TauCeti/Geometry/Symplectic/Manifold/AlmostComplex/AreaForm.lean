/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.PullbackAverage
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Basic
import TauCeti.Geometry.Symplectic.Complex.TwoDim

/-!
# Metrics compatible with an almost complex structure, and the area form of a surface

Let `j` be a smooth almost complex structure on a manifold `M`. A Riemannian metric `g` on `M` is
*compatible with* `j` when `j` is a `g`-isometry, `g(j u, j v) = g(u, v)`. Averaging any metric with
its pullback by `j`,

`g'(u, v) = ½ (g(u, v) + g(j u, j v))`,

gives a compatible metric (`TauCeti.SmoothAlmostComplexStructure.compatibleAverage`), so compatible
metrics exist whenever metrics do, for instance over a σ-compact Hausdorff base.

On a surface, oriented so that every frame `(v, j v)` is positive, the *area form* of a compatible
metric is `dA(u, v) = g(j u, v)`. It is the Riemannian volume form of the metric and the
orientation (`TauCeti.SmoothAlmostComplexStructure.riemannianVolumeForm_apply_eq_inner`), and it is
positive on every frame `(v, j v)`, where it takes the value `|v|²`; positivity alone holds for any
metric. These statements are pointwise: they only ask for compatibility and the orientation
condition at the point considered.
They follow from the linear algebra of an oriented Euclidean plane, where `j` is the rotation by a
right angle (`TauCeti.AlmostComplexStructure.volumeForm_apply_eq_inner`).

Any two metrics compatible with `j` on a surface are conformal: on each tangent plane they are
proportional, because both make every frame `(v, j v)` orthogonal with sides of equal length. More
generally, any symmetric bilinear form `B` on `T_x M` preserved by `j` satisfies
`B(j u, v) = B(w, w) / g(w, w) · dA(u, v)` for any nonzero `w` at `x`
(`TauCeti.SmoothAlmostComplexStructure.bilinForm_apply_left_eq_mul_riemannianVolumeForm`).
Hence the area form of a second compatible metric `g'` is the area form of `g` times the conformal
factor `c(x) = g'(w, w) / g(w, w)`. So, with the bundle metric `h` fixed, the `L²` pairing of
bundle sections over a surface,
`Bundle.ContinuousRiemannianMetric.l2Pairing`, becomes `∫ c(x) h(ξ(x), η(x)) dA` under a change of
compatible metric; it is a scalar multiple of the original pairing only when `c` is constant.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure.compatibleAverage`: the average of a metric and its
  pullback by `j`, compatible with `j`
  (`TauCeti.SmoothAlmostComplexStructure.compatibleAverage_inner_apply_apply`). It is the instance
  `A = j` of `Bundle.ContMDiffRiemannianMetric.pullbackAverage`, and fixes exactly the compatible
  metrics (`TauCeti.SmoothAlmostComplexStructure.compatibleAverage_eq_self_iff`).
* `TauCeti.SmoothAlmostComplexStructure.exists_contMDiffRiemannianMetric_compatible`: compatible
  metrics exist over a σ-compact Hausdorff manifold.
* `TauCeti.SmoothAlmostComplexStructure.riemannianVolumeForm_apply_eq_inner`: on a surface the
  Riemannian volume form of a compatible metric is the area form `dA(u, v) = g(j u, v)`.
* `TauCeti.SmoothAlmostComplexStructure.riemannianVolumeForm_apply_self_apply`: `dA(v, j v) = |v|²`.
* `TauCeti.SmoothAlmostComplexStructure.bilinForm_apply_left_eq_mul_riemannianVolumeForm`: the
  area form `B(j u, v)` of a `j`-invariant symmetric bilinear form, such as another compatible
  metric, is the conformal factor times `dA`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Appendix C.1 (the area form compatible with `j` used for the formal adjoint, Lemma C.1.9).
-/

public section

noncomputable section

open Bundle Module
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

namespace SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] (j : SmoothAlmostComplexStructure I M)

/-! ### Compatible metrics -/

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

/-! ### The area form of a surface -/

section AreaForm

variable [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {o : Manifold.Orientation I M (Fin 2)} {x : M}
  (hg : ∀ u v : TangentSpace I x, ⟪j x u, j x v⟫ = ⟪u, v⟫)
  (ho : ∀ b : Basis (Fin 2) ℝ (TangentSpace I x), b 1 = j x (b 0) →
    b.orientation = o.orientationAt x)
include hg ho

/-- **The area form of a compatible metric.** At a point of a surface where the metric is
compatible with `j` and every frame `(v, j v)` is positive, the Riemannian volume form is the area
form `dA(u, v) = g(j u, v)`. -/
theorem riemannianVolumeForm_apply_eq_inner (u v : TangentSpace I x) :
    riemannianVolumeForm o x ![u, v] = ⟪j x u, v⟫ := by
  let := o.fact_finrank_tangentSpace x
  rw [riemannianVolumeForm_apply]
  simpa only [almostComplexStructureAt_apply] using
    (j.almostComplexStructureAt x).volumeForm_apply_eq_inner _
      (by simpa only [almostComplexStructureAt_apply] using hg)
      (by simpa only [almostComplexStructureAt_apply] using ho) u v

/-- **The area form is positive on complex frames**: `dA(v, j v) = |v|²`. -/
theorem riemannianVolumeForm_apply_self_apply (v : TangentSpace I x) :
    riemannianVolumeForm o x ![v, j x v] = ‖v‖ ^ 2 := by
  rw [riemannianVolumeForm_apply_eq_inner j hg ho, hg, real_inner_self_eq_norm_sq]

omit hg in
/-- The area form is positive on the frame `(v, j v)` of a nonzero tangent vector. This only uses
the orientation condition, not the compatibility of the metric. -/
theorem riemannianVolumeForm_apply_self_apply_pos {v : TangentSpace I x} (hv : v ≠ 0) :
    0 < riemannianVolumeForm o x ![v, j x v] := by
  let := o.fact_finrank_tangentSpace x
  rw [riemannianVolumeForm_apply]
  simpa only [almostComplexStructureAt_apply] using
    (j.almostComplexStructureAt x).volumeForm_apply_self_apply_pos _
      (by simpa only [almostComplexStructureAt_apply] using ho) hv

/-- **Compatible metrics on a surface are conformal.** At a point of a surface as above, a
symmetric bilinear form `B` on the tangent plane preserved by `j`, such as a second compatible
metric, satisfies `B(j u, v) = B(w, w) / |w|² · dA(u, v)` for any nonzero tangent vector `w`. -/
theorem bilinForm_apply_left_eq_mul_riemannianVolumeForm
    {B : LinearMap.BilinForm ℝ (TangentSpace I x)} (hB : B.IsSymm)
    (hBj : ∀ u v : TangentSpace I x, B (j x u) (j x v) = B u v) {w : TangentSpace I x}
    (hw : w ≠ 0) (u v : TangentSpace I x) :
    B (j x u) v = B w w / ‖w‖ ^ 2 * riemannianVolumeForm o x ![u, v] := by
  let := o.fact_finrank_tangentSpace x
  have hk : ‖w‖ ^ 2 * B (j x u) v = B w w * ⟪j x u, v⟫ := by
    simpa using LinearMap.congr_fun₂
      ((j.almostComplexStructureAt x).norm_sq_smul_bilinForm_eq_smul_innerₗ
        (by simpa only [almostComplexStructureAt_apply] using hg) hB
        (by simpa only [almostComplexStructureAt_apply] using hBj) w) (j x u) v
  rw [riemannianVolumeForm_apply_eq_inner j hg ho, div_mul_eq_mul_div, eq_div_iff (by positivity)]
  linear_combination hk

end AreaForm

end SmoothAlmostComplexStructure

end TauCeti
