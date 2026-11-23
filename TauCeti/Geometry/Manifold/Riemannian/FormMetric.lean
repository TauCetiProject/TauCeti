/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.AlternatingForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Regularity of the pointwise metric on differential forms

The Gram pairing of real differential forms has the regularity of the forms and the
Riemannian metric. This is a scalar function on the manifold, without an orientation
hypothesis. In particular, smooth forms have smooth pointwise squared lengths, as needed
for their geometric integral pairing.

The pairing is `TauCeti.alternatingFormInner` on the existing alternating tangent fibres.
On a manifold with a continuous Riemannian metric it is a continuous fibre metric on the bundle
of forms, `TauCeti.formMetric`; this is data, not an instance, so no new norm is installed on
those fibres.

## Main definitions

* `TauCeti.formMetric I M k`: the Gram inner product of `k`-forms as a continuous fibre metric.
-/

public section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {k : ℕ}

section Continuous

variable [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable (I M k) in
/-- The Gram inner product `TauCeti.alternatingFormInner` of real `k`-forms on a manifold with a
continuous Riemannian metric, as a continuous fibre metric on the bundle of `k`-forms. -/
noncomputable def formMetric : ContinuousRiemannianMetric (E [⋀^Fin k]→L[ℝ] ℝ)
    (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :=
  haveI : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
  letI : ContMDiffVectorBundle 0 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  letI : IsContMDiffRiemannianBundle I 0 E (TangentSpace I : M → Type _) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  (alternatingFormRiemannianMetric E I (TangentSpace I : M → Type _) 0
    k).toContinuousRiemannianMetric

/-- The metric `TauCeti.formMetric` is the Gram inner product of forms. -/
@[simp]
theorem formMetric_inner (x : M) (v w : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :
    (formMetric I M k).inner x v w = alternatingFormInner (TangentSpace I x) k v w := by
  have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
  have : ContMDiffVectorBundle 0 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  have : IsContMDiffRiemannianBundle I 0 E (TangentSpace I : M → Type _) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  exact alternatingFormRiemannianMetric_inner (I := I) (V := (TangentSpace I : M → Type _)) x v w

end Continuous

variable {n : ℕ∞ω} [IsManifold I (n + 1) M]
  [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]

/-- The Gram pairing of `C^n` real forms on a manifold with a `C^n` Riemannian metric
is `C^n`, without requiring orientability. -/
theorem IsSmoothForm.contMDiff_alternatingFormInner {α β : RoughForm I M ℝ k}
    (hα : IsSmoothForm I n α) (hβ : IsSmoothForm I n β) :
    ContMDiff I 𝓘(ℝ) n
      (fun x ↦ alternatingFormInner (TangentSpace I x) k (α x) (β x)) := by
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact hα.contMDiff.alternatingFormInner_bundle hβ.contMDiff

end TauCeti
