/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.Restriction

/-!
# Curvature of a metric restricted to an open submanifold

Let `g` be a smooth Riemannian metric on `M` and `U ⊆ M` an open set. The inclusion
`U → M` is a local Riemannian isometry from the restricted metric `g|_U`
(`Bundle.ContMDiffRiemannianMetric.restrictOpenTangentSpace`) to `g`, so every curvature quantity
of `g|_U` at `x ∈ U` is that of `g` at `x`. In particular `Scal(g|_U) = Scal(g)` on `U`.

Consequently scalar curvature is local in the metric: two metrics that agree on a neighbourhood of
`x` have the same scalar curvature at `x`, and two metrics that agree on an open set have the same
scalar curvature there. This is what lets constructions that modify a metric only away from a set,
such as gluing along collars or interpolating in a tube, keep the scalar curvature unchanged
where the metric is unchanged.

## Main results

* `Bundle.ContMDiffRiemannianMetric.isLocalRiemannianIsometry_restrictOpenTangentSpace`: the
  inclusion of an open submanifold is a local Riemannian isometry from the restricted metric.
* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_restrictOpenTangentSpace`: the scalar
  curvature of the restricted metric is the scalar curvature of the metric.
* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_eq_of_eventually_inner_eq`: metrics that agree
  near a point have the same scalar curvature there.
* `Bundle.ContMDiffRiemannianMetric.eqOn_scalarCurvature`: metrics that agree on an open set have
  the same scalar curvature on it.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (local isometries) and Proposition 7.6 (naturality of the curvature tensor).
-/

public section

open Bundle Manifold Filter TopologicalSpace
open scoped ContDiff Manifold Topology

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The inclusion of an open submanifold `U ⊆ M` is a local Riemannian isometry from the
restriction of a metric `g` to `U` to the metric `g` itself. -/
theorem isLocalRiemannianIsometry_restrictOpenTangentSpace [IsManifold I 1 M] {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (U : Opens M) :
    letI : RiemannianBundle (fun x : U ↦ TangentSpace I x) :=
      ⟨(g.restrictOpenTangentSpace U).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    TauCeti.IsLocalRiemannianIsometry I I (Subtype.val : U → M) :=
  letI : RiemannianBundle (fun x : U ↦ TangentSpace I x) :=
    ⟨(g.restrictOpenTangentSpace U).toRiemannianMetric⟩
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  { contMDiff := contMDiff_subtype_val
    isInvertible_mfderiv := fun x ↦
      ⟨TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x,
        (TauCeti.Manifold.mfderiv_subtype_val x).symm⟩
    inner_mfderiv := fun x v w ↦ by
      have h := g.toRiemannianMetric.restrictOpenTangentSpace_inner_mfderiv_subtype_val U x v w
      rw [← restrictOpenTangentSpace_toRiemannianMetric] at h
      rw [inner_riemannianBundle g, inner_riemannianBundle (g.restrictOpenTangentSpace U)]
      exact h.symm }

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]

/-- **Scalar curvature is local.** The scalar curvature of the restriction of a metric `g` to an
open submanifold `U` is the scalar curvature of `g` at each point of `U`. -/
@[simp]
theorem scalarCurvature_restrictOpenTangentSpace
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (U : Opens M) (x : U) :
    (g.restrictOpenTangentSpace U).scalarCurvature x = g.scalarCurvature x := by
  let _ : RiemannianBundle (fun x : U ↦ TangentSpace I x) :=
    ⟨(g.restrictOpenTangentSpace U).toRiemannianMetric⟩
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [scalarCurvature_def, scalarCurvature_def,
    (g.isLocalRiemannianIsometry_restrictOpenTangentSpace U).scalarCurvature_map x]

/-- **Locality of scalar curvature.** Two metrics that agree on a neighbourhood of `x` have the
same scalar curvature at `x`. -/
theorem scalarCurvature_eq_of_eventually_inner_eq
    {g₁ g₂ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {x : M}
    (h : ∀ᶠ y in 𝓝 x, g₁.inner y = g₂.inner y) :
    g₁.scalarCurvature x = g₂.scalarCurvature x := by
  obtain ⟨U, hU, hUo, hxU⟩ := eventually_nhds_iff.1 h
  have hres := restrictOpenTangentSpace_eq_of_inner_eq ⟨U, hUo⟩ hU
  rw [← scalarCurvature_restrictOpenTangentSpace g₁ ⟨U, hUo⟩ ⟨x, hxU⟩, hres,
    scalarCurvature_restrictOpenTangentSpace]

/-- Two metrics that agree on an open set have the same scalar curvature on it. -/
theorem eqOn_scalarCurvature
    {g₁ g₂ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {U : Set M}
    (hU : IsOpen U) (h : ∀ x ∈ U, g₁.inner x = g₂.inner x) :
    Set.EqOn g₁.scalarCurvature g₂.scalarCurvature U := fun _ hx ↦
  scalarCurvature_eq_of_eventually_inner_eq (eventually_of_mem (hU.mem_nhds hx) h)

end Bundle.ContMDiffRiemannianMetric
