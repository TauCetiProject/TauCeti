/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Topology.VectorBundle.FiniteDimensional
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# Smooth nondegenerate metrics on a manifold

This file bundles a smooth field of symmetric nondegenerate real bilinear forms on the tangent
bundle. Positivity is not required.

The metric is stored as a native `ContMDiffSection` of the bundle of continuous bilinear forms.
When the model space is finite-dimensional, its pointwise nondegeneracy produces flat and sharp
musical isomorphisms through `LinearMap.BilinForm.toDual`. Every smooth Riemannian metric gives
such a nondegenerate metric, which connects this general carrier to Mathlib's positive-definite
Riemannian carrier.

These objects are the algebraic and smooth carrier needed to state the Koszul construction of the
Levi-Civita connection for an indefinite metric.

## Main definitions and results

* `TauCeti.Manifold.ContMDiffNondegenerateMetric`: a smooth symmetric nondegenerate tangent
  bilinear form.
* `TauCeti.Manifold.ContMDiffNondegenerateMetric.inCoordinates`: the metric read in a
  tangent-bundle trivialization, with its symmetry, nondegeneracy and smoothness on the base set.
* `TauCeti.Manifold.ContMDiffNondegenerateMetric.chartMetric`: the metric read in the chart at a
  point, a field of symmetric nondegenerate bilinear forms on the chart target, smooth there.
* `TauCeti.Manifold.ContMDiffNondegenerateMetric.flat`: its fibrewise flat musical equivalence,
  for a finite-dimensional model space.
* `TauCeti.Manifold.ContMDiffNondegenerateMetric.sharp`: the inverse musical equivalence, for a
  finite-dimensional model space.
* `TauCeti.Manifold.ContMDiffNondegenerateMetric.ofRiemannianBundle`: the metric of a smooth
  Riemannian bundle instance on the tangent bundle, as a smooth nondegenerate metric.
* `Bundle.ContMDiffRiemannianMetric.toNondegenerateMetric`: the positive-definite specialization.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapters 2 and 5.
-/

public section

noncomputable section

open Bundle FiberBundle
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A smooth field of symmetric nondegenerate real bilinear forms on the tangent bundle.

The form is a native smooth section of the continuous-bilinear-form bundle. Nondegeneracy is the
native algebraic predicate on its underlying `LinearMap.BilinForm`; it does not impose positivity
or choose any signature. -/
structure ContMDiffNondegenerateMetric where
  /-- The smooth section of continuous bilinear forms. -/
  toContMDiffSection :
    Cₛ^∞⟮I; E →L[ℝ] E →L[ℝ] ℝ,
      fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ⟯
  /-- The bilinear form in every tangent fibre is symmetric. -/
  symm (x : M) : (toContMDiffSection x).toBilinForm.IsSymm
  /-- The bilinear form in every tangent fibre is nondegenerate. -/
  nondegenerate (x : M) : (toContMDiffSection x).toBilinForm.Nondegenerate

namespace ContMDiffNondegenerateMetric

instance : CoeFun (ContMDiffNondegenerateMetric (I := I) (M := M)) fun _ ↦
    (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ where
  coe g := g.toContMDiffSection

/-- The underlying field of bilinear forms is smooth. -/
theorem contMDiff (g : ContMDiffNondegenerateMetric (I := I) (M := M)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (g x)) :=
  g.toContMDiffSection.contMDiff

/-- Pairing two differentiable vector fields with a smooth nondegenerate metric is
differentiable. -/
theorem mdifferentiableAt_apply (g : ContMDiffNondegenerateMetric (I := I) (M := M))
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    MDiffAt (fun y ↦ g y (Y y) (Z y)) x := by
  have h := (g.contMDiff.mdifferentiable (by simp)).mdifferentiableAt.clm_bundle_apply₂ hY hZ
  simpa [mdifferentiableAt_section] using h

/-- Evaluation of a smooth nondegenerate metric is symmetric in its tangent arguments. -/
theorem apply_comm (g : ContMDiffNondegenerateMetric (I := I) (M := M))
    (x : M) (v w : TangentSpace I x) : g x v w = g x w v :=
  (g.symm x).eq v w

/-- Smooth nondegenerate metrics are equal when all their fibrewise pairings agree. -/
@[ext]
theorem ext {g h : ContMDiffNondegenerateMetric (I := I) (M := M)}
    (heq : ∀ x v w, g x v w = h x v w) : g = h := by
  cases g with
  | mk gs gsymm gnond =>
    cases h with
    | mk hs hsymm hnond =>
      congr 1
      apply ContMDiffSection.ext
      intro x
      ext v w
      exact heq x v w

/-! ### The metric read in a trivialization -/

/-- The metric `g` at `x`, read in the trivialization of the tangent bundle at `a`: a continuous
bilinear form on the model space. It is meaningful for `x` in the base set of that
trivialization. -/
def inCoordinates (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (a x : M) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ContinuousLinearMap.inCoordinates E (fun y : M ↦ TangentSpace I y)
    (E →L[ℝ] ℝ) (fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) a x a x (g x)

/-- On the base set of the trivialization at `a`, the metric read in that trivialization pairs two
vectors of the model space as `g` pairs the tangent vectors with these coordinates. -/
theorem inCoordinates_apply
    (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (a : M) {x : M}
    (hx : x ∈ (trivializationAt E (fun y : M ↦ TangentSpace I y) a).baseSet) (v w : E) :
    g.inCoordinates a x v w =
      g x ((trivializationAt E (fun y : M ↦ TangentSpace I y) a).symm x v)
        ((trivializationAt E (fun y : M ↦ TangentSpace I y) a).symm x w) := by
  simpa only [inCoordinates, Trivial.fiberBundle_trivializationAt',
    Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq] using
    (inCoordinates_apply_eq₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := fun y : M ↦ TangentSpace I y) (E₂ := fun y : M ↦ TangentSpace I y)
      (E₃ := Bundle.Trivial M ℝ) (x₀ := a) (x := x)
      (ϕ := g x) hx hx (by simp) (v := v) (w := w))

/-- On the base set of the trivialization at `a`, the metric read in that trivialization is the
congruence of the metric by the trivialization's linear equivalence. -/
theorem inCoordinates_toBilinForm
    (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (a : M) {x : M}
    (hx : x ∈ (trivializationAt E (fun y : M ↦ TangentSpace I y) a).baseSet) :
    (g.inCoordinates a x).toBilinForm =
      LinearMap.BilinForm.congr
        ((trivializationAt E (fun y : M ↦ TangentSpace I y) a).continuousLinearEquivAt ℝ x hx
          |>.toLinearEquiv) (g x).toBilinForm := by
  ext v w
  rw [ContinuousLinearMap.toBilinForm_apply, LinearMap.BilinForm.congr_apply,
    inCoordinates_apply g a hx, ContinuousLinearMap.toBilinForm_apply,
    ContinuousLinearEquiv.coe_symm_toLinearEquiv,
    Trivialization.continuousLinearEquivAt_symm_apply]

/-- The metric read in a trivialization is symmetric on its base set. -/
theorem isSymm_inCoordinates
    (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (a : M) {x : M}
    (hx : x ∈ (trivializationAt E (fun y : M ↦ TangentSpace I y) a).baseSet) :
    (g.inCoordinates a x).toBilinForm.IsSymm := by
  constructor
  intro v w
  simp only [ContinuousLinearMap.toBilinForm_apply, inCoordinates_apply g a hx]
  exact g.apply_comm x _ _

/-- The metric read in a trivialization is nondegenerate on its base set. -/
theorem nondegenerate_inCoordinates
    (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (a : M) {x : M}
    (hx : x ∈ (trivializationAt E (fun y : M ↦ TangentSpace I y) a).baseSet) :
    (g.inCoordinates a x).toBilinForm.Nondegenerate := by
  rw [inCoordinates_toBilinForm g a hx]
  exact (g.nondegenerate x).congr _

/-- The metric read in the trivialization at `a` is smooth at every point of its base set. -/
theorem contMDiffAt_inCoordinates
    (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (a : M) {x : M}
    (hx : x ∈ (trivializationAt E (fun y : M ↦ TangentSpace I y) a).baseSet) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ (g.inCoordinates a) x := by
  have hsec := ((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) a).contMDiffAt_section_iff
      (IB := I) (n := ∞) (s := fun y ↦ g y) (by simpa using hx)).1 (g.contMDiff x)
  simp only [hom_trivializationAt_apply] at hsec
  exact hsec

/-! ### The metric read in a chart -/

section Chart

variable (g : ContMDiffNondegenerateMetric (I := I) (M := M)) {x₀ y : M}

/-- The metric `g` read in the chart at `x₀`: at a point `z` of the model space, the bilinear form
on `E` obtained by reading `g` at `(extChartAt I x₀).symm z` in the trivialization of the tangent
bundle at `x₀`. It is meaningful on the chart target `(extChartAt I x₀).target`. -/
def chartMetric (x₀ : M) (z : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  g.inCoordinates x₀ ((extChartAt I x₀).symm z)

/-- At a point `z` of the chart target, the chart metric pairs two vectors of the model space as
`g` pairs the tangent vectors at `(extChartAt I x₀).symm z` with these coordinates. -/
theorem chartMetric_apply {z : E} (hz : z ∈ (extChartAt I x₀).target) (u w : E) :
    g.chartMetric x₀ z u w =
      g ((extChartAt I x₀).symm z)
        ((trivializationAt E (TangentSpace I) x₀).symm ((extChartAt I x₀).symm z) u)
        ((trivializationAt E (TangentSpace I) x₀).symm ((extChartAt I x₀).symm z) w) :=
  g.inCoordinates_apply x₀ (by simpa using (extChartAt I x₀).map_target hz) u w

/-- At the chart image of a point `y` of the chart domain, the chart metric pairs two vectors of
the model space as `g` pairs the tangent vectors at `y` with these coordinates. -/
theorem chartMetric_extChartAt_apply (hy : y ∈ (extChartAt I x₀).source) (u w : E) :
    g.chartMetric x₀ (extChartAt I x₀ y) u w =
      g y ((trivializationAt E (TangentSpace I) x₀).symm y u)
        ((trivializationAt E (TangentSpace I) x₀).symm y w) := by
  rw [chartMetric, (extChartAt I x₀).left_inv hy]
  exact g.inCoordinates_apply x₀ (by simpa using hy) u w

/-- At the chart image of a point `y` of the chart domain, the chart metric pairs two vectors of a
basis `b` of the model space as `g` pairs the corresponding vectors at `y` of the coordinate frame
of `b`. -/
theorem chartMetric_extChartAt_apply_basis {ι : Type*} (b : Module.Basis ι ℝ E)
    (hy : y ∈ (extChartAt I x₀).source) (i j : ι) :
    g.chartMetric x₀ (extChartAt I x₀ y) (b i) (b j) =
      g y ((trivializationAt E (TangentSpace I) x₀).localFrame b i y)
        ((trivializationAt E (TangentSpace I) x₀).localFrame b j y) := by
  have hbase : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by simpa using hy
  simp only [g.chartMetric_extChartAt_apply hy, ← symmL_basis_eq_localFrame b hbase,
    Trivialization.symmL_apply _ hbase]

/-- The chart metric is symmetric at every point of the chart target. -/
theorem isSymm_chartMetric {z : E} (hz : z ∈ (extChartAt I x₀).target) :
    LinearMap.IsSymm (g.chartMetric x₀ z).toBilinForm :=
  LinearMap.BilinForm.isSymm_iff.1 <|
    g.isSymm_inCoordinates x₀ (by simpa using (extChartAt I x₀).map_target hz)

/-- The chart metric is nondegenerate at every point of the chart target. -/
theorem nondegenerate_chartMetric {z : E} (hz : z ∈ (extChartAt I x₀).target) :
    (g.chartMetric x₀ z).toBilinForm.Nondegenerate :=
  g.nondegenerate_inCoordinates x₀ (by simpa using (extChartAt I x₀).map_target hz)

/-- The chart metric is smooth on the chart target. -/
theorem contDiffOn_chartMetric (x₀ : M) :
    ContDiffOn ℝ ∞ (g.chartMetric x₀) (extChartAt I x₀).target := by
  rw [← contMDiffOn_iff_contDiffOn]
  intro z hz
  exact (g.contMDiffAt_inCoordinates x₀ (by simpa using (extChartAt I x₀).map_target hz))
    |>.comp_contMDiffWithinAt z (contMDiffOn_extChartAt_symm x₀ z hz)

/-- The chart metric is smooth at the chart image of every point of the chart domain lying in the
interior of the model. -/
theorem contDiffAt_chartMetric (hy : y ∈ (extChartAt I x₀).source)
    (hint : extChartAt I x₀ y ∈ interior (Set.range I)) :
    ContDiffAt ℝ ∞ (g.chartMetric x₀) (extChartAt I x₀ y) := by
  refine (g.contDiffOn_chartMetric x₀).contDiffAt ?_
  rw [← nhdsWithin_eq_nhds.2 (mem_interior_iff_mem_nhds.1 hint)]
  exact extChartAt_target_mem_nhdsWithin' hy

end Chart

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- The flat musical isomorphism induced by a smooth nondegenerate metric at `x`. Its inverse is
the sharp musical isomorphism. -/
noncomputable def flat (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (x : M) :
    TangentSpace I x ≃ₗ[ℝ] Module.Dual ℝ (TangentSpace I x) :=
  (g x).toBilinForm.toDual (g.nondegenerate x)

/-- The flat musical isomorphism is Mathlib's dual equivalence of the fibrewise bilinear form. -/
theorem flat_eq_toDual (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (x : M) :
    g.flat x = (g x).toBilinForm.toDual (g.nondegenerate x) := by
  rw [flat]

/-- The sharp musical isomorphism induced by a smooth nondegenerate metric at `x`. -/
noncomputable def sharp (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (x : M) :
    Module.Dual ℝ (TangentSpace I x) ≃ₗ[ℝ] TangentSpace I x :=
  (g.flat x).symm

/-- The inverse of the flat musical isomorphism is the sharp musical isomorphism. -/
@[simp]
theorem flat_symm (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (x : M) :
    (g.flat x).symm = g.sharp x := by
  rw [sharp]

/-- Flat undoes sharp. -/
@[simp]
theorem flat_sharp_apply (g : ContMDiffNondegenerateMetric (I := I) (M := M))
    (x : M) (f : Module.Dual ℝ (TangentSpace I x)) : g.flat x (g.sharp x f) = f :=
  (g.flat x).apply_symm_apply f

/-- Sharp undoes flat. -/
@[simp]
theorem sharp_flat_apply (g : ContMDiffNondegenerateMetric (I := I) (M := M))
    (x : M) (v : TangentSpace I x) : g.sharp x (g.flat x v) = v :=
  (g.flat x).symm_apply_apply v

/-- The flat musical isomorphism evaluates as the metric pairing. -/
@[simp]
theorem flat_apply_apply (g : ContMDiffNondegenerateMetric (I := I) (M := M))
    (x : M) (v w : TangentSpace I x) : g.flat x v w = g x v w := by
  rw [flat_eq_toDual, LinearMap.BilinForm.toDual_def, ContinuousLinearMap.toBilinForm_apply]

/-- The sharp representative of a covector pairs against every vector to give that covector. -/
@[simp]
theorem apply_sharp_apply (g : ContMDiffNondegenerateMetric (I := I) (M := M))
    (x : M) (f : Module.Dual ℝ (TangentSpace I x)) (w : TangentSpace I x) :
    g x (g.sharp x f) w = f w := by
  rw [← g.flat_apply_apply, flat_sharp_apply]

/-- By symmetry, the sharp representative also represents a covector in the second argument. -/
@[simp]
theorem apply_apply_sharp (g : ContMDiffNondegenerateMetric (I := I) (M := M))
    (x : M) (f : Module.Dual ℝ (TangentSpace I x)) (w : TangentSpace I x) :
    g x w (g.sharp x f) = f w := by
  rw [g.apply_comm, g.apply_sharp_apply]

/-- A vector is the sharp representative of a covector exactly when contraction with the metric
gives that covector. -/
theorem eq_sharp_iff (g : ContMDiffNondegenerateMetric (I := I) (M := M))
    (x : M) (v : TangentSpace I x) (f : Module.Dual ℝ (TangentSpace I x)) :
    v = g.sharp x f ↔ ∀ w, g x v w = f w := by
  constructor
  · rintro rfl w
    exact g.apply_sharp_apply x f w
  · intro h
    apply (g.flat x).injective
    ext w
    rw [g.flat_apply_apply, h, flat_sharp_apply]

end FiniteDimensional

end ContMDiffNondegenerateMetric

end TauCeti.Manifold

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A smooth positive-definite Riemannian metric, viewed as a smooth symmetric nondegenerate
metric without forgetting its fibrewise values. -/
def toNondegenerateMetric
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    Manifold.ContMDiffNondegenerateMetric (I := I) (M := M) where
  toContMDiffSection := ⟨g.inner, g.contMDiff⟩
  symm x := ⟨g.symm x⟩
  nondegenerate x := by
    constructor <;>
    · intro v hv
      by_contra hv0
      exact (g.pos x v hv0).ne' (hv v)

/-- Viewing a Riemannian metric as a nondegenerate metric preserves its pointwise pairing. -/
@[simp]
theorem toNondegenerateMetric_apply
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (x : M) (v w : TangentSpace I x) :
    g.toNondegenerateMetric x v w = g.inner x v w :=
  (rfl)

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti.Manifold.ContMDiffNondegenerateMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section RiemannianBundle

variable (I M) [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The metric of a smooth Riemannian bundle structure on the tangent bundle, viewed as a smooth
symmetric nondegenerate metric. -/
def ofRiemannianBundle : ContMDiffNondegenerateMetric (I := I) (M := M) :=
  (Bundle.ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)).toNondegenerateMetric

/-- The metric of a Riemannian bundle structure pairs tangent vectors by their inner product. -/
@[simp]
theorem ofRiemannianBundle_apply (x : M) (v w : TangentSpace I x) :
    ofRiemannianBundle I M x v w = inner ℝ v w := by
  simp only [ofRiemannianBundle,
    Bundle.ContMDiffRiemannianMetric.toNondegenerateMetric_apply,
    Bundle.ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]
  rfl

end RiemannianBundle

end TauCeti.Manifold.ContMDiffNondegenerateMetric
