/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# Smooth nondegenerate metrics on a manifold

This file bundles a smooth field of symmetric nondegenerate real bilinear forms on the tangent
bundle. Positivity is not required.

The metric is stored as a native `ContMDiffSection` of the bundle of continuous bilinear forms.
Its pointwise nondegeneracy produces flat and sharp musical isomorphisms through
`LinearMap.BilinForm.toDual`. Every smooth Riemannian metric gives such a nondegenerate metric,
which connects this general carrier to Mathlib's positive-definite Riemannian carrier.

These objects are the algebraic and smooth carrier needed to state the Koszul construction of the
Levi-Civita connection for an indefinite metric.

## Main definitions and results

* `TauCeti.Manifold.ContMDiffNondegenerateMetric`: a smooth symmetric nondegenerate tangent
  bilinear form.
* `TauCeti.Manifold.ContMDiffNondegenerateMetric.flat`: its fibrewise flat musical equivalence.
* `TauCeti.Manifold.ContMDiffNondegenerateMetric.sharp`: the inverse musical equivalence.
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

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- The flat musical isomorphism induced by a smooth nondegenerate metric at `x`. Its inverse is
the sharp musical isomorphism. -/
noncomputable def flat (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (x : M) :
    TangentSpace I x ≃ₗ[ℝ] Module.Dual ℝ (TangentSpace I x) := by
  let _ : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  exact (g x).toBilinForm.toDual (g.nondegenerate x)

/-- The sharp musical isomorphism induced by a smooth nondegenerate metric at `x`. -/
noncomputable abbrev sharp (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (x : M) :
    Module.Dual ℝ (TangentSpace I x) ≃ₗ[ℝ] TangentSpace I x :=
  (g.flat x).symm

/-- The flat musical isomorphism evaluates as the metric pairing. -/
@[simp]
theorem flat_apply_apply (g : ContMDiffNondegenerateMetric (I := I) (M := M))
    (x : M) (v w : TangentSpace I x) : g.flat x v w = g x v w := by
  let _ : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  change (g x).toBilinForm.toDual (g.nondegenerate x) v w = g x v w
  rw [LinearMap.BilinForm.toDual_def]
  rfl

/-- The sharp representative of a covector pairs against every vector to give that covector. -/
@[simp]
theorem apply_sharp_apply (g : ContMDiffNondegenerateMetric (I := I) (M := M))
    (x : M) (f : Module.Dual ℝ (TangentSpace I x)) (w : TangentSpace I x) :
    g x (g.sharp x f) w = f w := by
  let _ : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  change (g x).toBilinForm
      (((g x).toBilinForm.toDual (g.nondegenerate x)).symm f) w = f w
  exact LinearMap.BilinForm.apply_toDual_symm_apply f w

/-- By symmetry, the sharp representative also represents a covector in the first argument. -/
@[simp]
theorem apply_sharp_apply_left (g : ContMDiffNondegenerateMetric (I := I) (M := M))
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
    rw [g.flat_apply_apply, h, LinearEquiv.apply_symm_apply]

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
    constructor
    · intro v hv
      by_contra hv0
      exact (ne_of_gt (g.pos x v hv0)) (hv v)
    · intro v hv
      by_contra hv0
      exact (ne_of_gt (g.pos x v hv0)) (hv v)

/-- Viewing a Riemannian metric as a nondegenerate metric preserves its pointwise pairing. -/
@[simp]
theorem toNondegenerateMetric_apply
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (x : M) (v w : TangentSpace I x) :
    g.toNondegenerateMetric x v w = g.inner x v w :=
  (rfl)

end Bundle.ContMDiffRiemannianMetric
