/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Mean
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Pullback
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Basic
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace

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
positive on every frame `(v, j v)`, where it takes the value `|v|²`. The proof identifies `j` with
the rotation by a right angle of the oriented Euclidean plane `T_x M`
(`Orientation.rightAngleRotation`), whose area form is Mathlib's `Orientation.areaForm`.

Any two metrics compatible with `j` on a surface are conformal: on each tangent plane they are
proportional, because both make every frame `(v, j v)` orthogonal with sides of equal length.
Hence the area form of a second compatible metric `g'` is the area form of `g` times the conformal
factor `g'(w, w) / g(w, w)`, for any nonzero `w`
(`TauCeti.SmoothAlmostComplexStructure.inner_apply_left_eq_mul_riemannianVolumeForm`). So the
`L²` pairing of bundle sections over a surface, `Bundle.ContMDiffRiemannianMetric.l2Pairing`,
changes under a change of compatible metric only by this factor.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure.compatibleAverage`: the average of a metric and its
  pullback by `j`, compatible with `j`
  (`TauCeti.SmoothAlmostComplexStructure.compatibleAverage_inner_apply_apply`).
* `TauCeti.SmoothAlmostComplexStructure.exists_contMDiffRiemannianMetric_compatible`: compatible
  metrics exist over a σ-compact Hausdorff manifold.
* `TauCeti.SmoothAlmostComplexStructure.riemannianVolumeForm_apply_eq_inner`: on a surface the
  Riemannian volume form of a compatible metric is the area form `dA(u, v) = g(j u, v)`.
* `TauCeti.SmoothAlmostComplexStructure.riemannianVolumeForm_apply_self_apply`: `dA(v, j v) = |v|²`.
* `TauCeti.SmoothAlmostComplexStructure.inner_apply_left_eq_mul_riemannianVolumeForm`: the area
  form of another compatible metric is the conformal factor times `dA`.

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
  meanRiemannianMetric (fun b : Bool ↦
    if b then g.pullbackBundleEquiv j.tangentEquiv j.contMDiff_tangentEquiv else g)

/-- The compatible average is the half-sum of the metric and its pullback by `j`. -/
theorem compatibleAverage_inner
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (x : M)
    (u v : TangentSpace I x) :
    (j.compatibleAverage g).inner x u v = 2⁻¹ * (g.inner x u v + g.inner x (j x u) (j x v)) := by
  simp [compatibleAverage, meanRiemannianMetric_inner, add_comm,
    ContMDiffRiemannianMetric.pullbackBundleEquiv_inner]

/-- The compatible average is compatible with `j`: `j` is an isometry for it. -/
theorem compatibleAverage_inner_apply_apply
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (x : M)
    (u v : TangentSpace I x) :
    (j.compatibleAverage g).inner x (j x u) (j x v) = (j.compatibleAverage g).inner x u v := by
  rw [compatibleAverage_inner, compatibleAverage_inner, apply_apply, apply_apply, map_neg,
    ContinuousLinearMap.map_neg₂]
  ring

/-- A metric compatible with `j` is its own compatible average. -/
theorem compatibleAverage_eq_self
    {g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}
    (hg : ∀ x (u v : TangentSpace I x), g.inner x (j x u) (j x v) = g.inner x u v) :
    j.compatibleAverage g = g := by
  ext x u v
  rw [compatibleAverage_inner, hg]
  ring

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
  {o : Manifold.Orientation I M (Fin 2)}

/-- At a point of a surface where every frame `(v, j v)` is positive, `j` is the rotation by a
right angle of the oriented Euclidean tangent plane. -/
private theorem apply_eq_rightAngleRotation
    (hg : ∀ x (u v : TangentSpace I x), ⟪j x u, j x v⟫ = ⟪u, v⟫)
    (ho : ∀ x (b : Basis (Fin 2) ℝ (TangentSpace I x)), b 1 = j x (b 0) →
      b.orientation = o.orientationAt x)
    (x : M) (v : TangentSpace I x) :
    letI := o.fact_finrank_tangentSpace x
    j x v = (o.orientationAt x).rightAngleRotation v := by
  let := o.fact_finrank_tangentSpace x
  set ox := o.orientationAt x
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  -- The frame `(v, j v)` is a positive basis.
  set b := basisOfLinearIndependentOfCardEqFinrank
    ((j.almostComplexStructureAt x).linearIndependent_pair hv)
    (by simpa using (o.finrank_tangentSpace_eq x).symm)
  have hb : ⇑b = ![v, j x v] := by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank, almostComplexStructureAt_apply]
  have hpos : 0 < ox.areaForm v (j x v) := by
    rw [Orientation.areaForm_to_volumeForm, ← hb]
    exact Orientation.volumeForm_apply_pos_iff.2 (ho x b (by simp [hb]))
  -- Since `j v ⟂ v` and `|j v| = |v|`, the area `ω(v, j v)` is `|v|²`.
  have hjx : ∀ u v, ⟪j.almostComplexStructureAt x u, j.almostComplexStructureAt x v⟫ = ⟪u, v⟫ :=
    fun u v ↦ by simpa only [almostComplexStructureAt_apply] using hg x u v
  have hnorm : ‖j x v‖ = ‖v‖ := by
    simpa only [almostComplexStructureAt_apply] using AlmostComplexStructure.norm_apply hjx v
  have hperp : ⟪v, j x v⟫ = 0 := by
    simpa only [almostComplexStructureAt_apply, real_inner_comm v] using
      AlmostComplexStructure.inner_apply_self hjx v
  have harea : ox.areaForm v (j x v) = ‖v‖ ^ 2 := by
    have h := ox.inner_sq_add_areaForm_sq v (j x v)
    rw [hperp, hnorm] at h
    nlinarith [sq_nonneg (ox.areaForm v (j x v) - ‖v‖ ^ 2),
      sq_nonneg (ox.areaForm v (j x v) + ‖v‖ ^ 2), sq_nonneg ‖v‖]
  -- Equality in Cauchy–Schwarz for `⟪J v, j v⟫ = ω(v, j v) = |J v| |j v|`.
  have hJ : ‖ox.rightAngleRotation v‖ = ‖v‖ := by simp
  have heq : ⟪ox.rightAngleRotation v, j x v⟫ = ‖ox.rightAngleRotation v‖ * ‖j x v‖ := by
    rw [Orientation.inner_rightAngleRotation_left, harea, hJ, hnorm, sq]
  rw [inner_eq_norm_mul_iff_real, hJ, hnorm] at heq
  exact (smul_right_injective _ (norm_ne_zero_iff.2 hv) heq).symm

variable (hg : ∀ x (u v : TangentSpace I x), ⟪j x u, j x v⟫ = ⟪u, v⟫)
  (ho : ∀ x (b : Basis (Fin 2) ℝ (TangentSpace I x)), b 1 = j x (b 0) →
    b.orientation = o.orientationAt x)
include hg ho

/-- **The area form of a compatible metric.** On a surface with a metric compatible with `j`,
oriented so that every frame `(v, j v)` is positive, the Riemannian volume form is the area form
`dA(u, v) = g(j u, v)`. -/
theorem riemannianVolumeForm_apply_eq_inner (x : M) (u v : TangentSpace I x) :
    riemannianVolumeForm o x ![u, v] = ⟪j x u, v⟫ := by
  let := o.fact_finrank_tangentSpace x
  rw [riemannianVolumeForm_apply, ← Orientation.areaForm_to_volumeForm,
    apply_eq_rightAngleRotation j hg ho, Orientation.inner_rightAngleRotation_left]

/-- **The area form is positive on complex frames**: `dA(v, j v) = |v|²`. -/
theorem riemannianVolumeForm_apply_self_apply (x : M) (v : TangentSpace I x) :
    riemannianVolumeForm o x ![v, j x v] = ‖v‖ ^ 2 := by
  rw [riemannianVolumeForm_apply_eq_inner j hg ho, hg, real_inner_self_eq_norm_sq]

/-- The area form is positive on the frame `(v, j v)` of a nonzero tangent vector. -/
theorem riemannianVolumeForm_apply_self_apply_pos (x : M) {v : TangentSpace I x} (hv : v ≠ 0) :
    0 < riemannianVolumeForm o x ![v, j x v] := by
  rw [riemannianVolumeForm_apply_self_apply j hg ho]
  positivity

omit [ENat.LEInfty n] in
/-- **Compatible metrics on a surface are conformal.** If `g'` is a second metric compatible with
`j`, its area form `g'(j u, v)` is the area form of the metric of `M` times the conformal factor
`g'(w, w) / |w|²`, for any nonzero tangent vector `w` at the same point. -/
theorem inner_apply_left_eq_mul_riemannianVolumeForm
    (g' : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (hg' : ∀ x (u v : TangentSpace I x), g'.inner x (j x u) (j x v) = g'.inner x u v)
    (x : M) {w : TangentSpace I x} (hw : w ≠ 0) (u v : TangentSpace I x) :
    g'.inner x (j x u) v = g'.inner x w w / ‖w‖ ^ 2 * riemannianVolumeForm o x ![u, v] := by
  let := o.fact_finrank_tangentSpace x
  -- Both metrics are determined by their values on the frame `(w, j w)`, which both make
  -- orthogonal with sides of equal length.
  set b := basisOfLinearIndependentOfCardEqFinrank
    ((j.almostComplexStructureAt x).linearIndependent_pair hw)
    (by simpa using (o.finrank_tangentSpace_eq x).symm)
  have hb : ⇑b = ![w, j x w] := by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank, almostComplexStructureAt_apply]
  have h₀ : g'.inner x w (j x w) = 0 := by
    simpa only [almostComplexStructureAt_apply, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]
      using (j.almostComplexStructureAt x).bilinForm_apply_apply_self_eq_zero
        (g := (g'.inner x).toLinearMap₁₂) ⟨fun u v ↦ g'.symm x u v⟩
        (fun u v ↦ by
          simpa only [almostComplexStructureAt_apply,
            ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply] using hg' x u v) w
  have hjx : ∀ u v, ⟪j.almostComplexStructureAt x u, j.almostComplexStructureAt x v⟫ = ⟪u, v⟫ :=
    fun u v ↦ by simpa only [almostComplexStructureAt_apply] using hg x u v
  have h₁ : ⟪w, j x w⟫ = 0 := by
    simpa only [almostComplexStructureAt_apply, real_inner_comm w] using
      AlmostComplexStructure.inner_apply_self hjx w
  have h₂ : ‖j x w‖ = ‖w‖ := by
    simpa only [almostComplexStructureAt_apply] using AlmostComplexStructure.norm_apply hjx w
  have key : ‖w‖ ^ 2 • (g'.inner x).toLinearMap₁₂ = g'.inner x w w • innerₗ (TangentSpace I x) := by
    refine LinearMap.ext_basis b b fun i k ↦ ?_
    fin_cases i <;> fin_cases k <;>
      simp [hb, h₀, h₁, g'.symm x (j x w) w, real_inner_comm w, hg', mul_comm, h₂]
  have hk : ‖w‖ ^ 2 * g'.inner x (j x u) v = g'.inner x w w * ⟪j x u, v⟫ := by
    simpa using LinearMap.congr_fun₂ key (j x u) v
  rw [riemannianVolumeForm_apply_eq_inner j hg ho, div_mul_eq_mul_div, eq_div_iff (by positivity)]
  linear_combination hk

end AreaForm

end SmoothAlmostComplexStructure

end TauCeti
