/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Basic
public import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Smoothness of the musical isomorphisms of a nondegenerate metric

A smooth nondegenerate metric `g` on a manifold with finite-dimensional model space is, read as a
section of `Hom(TM, T*M)`, its own flat musical map, so the flat map is smooth by definition.
This file proves that the inverse sharp map is smooth as well: the fibrewise inverses of `g` form
a smooth section of `Hom(T*M, TM)`. In a bundle chart this is the smoothness of the inverse of
the metric matrix, obtained from smoothness of inversion of continuous linear maps. No positivity
is assumed.

Consequently the sharp of a `C^n` covector field is a `C^n` vector field. This is the regularity
input needed to turn the Koszul functional of an indefinite metric into a covariant derivative.
For a Riemannian metric, the corresponding statement for the Riesz dual is
`Riemannian.Tensor.contMDiffOn_rieszDual`.

## Main results

* `TauCeti.Manifold.ContMDiffNondegenerateMetric.isInvertible`: each fibre map `g x` is invertible.
* `TauCeti.Manifold.ContMDiffNondegenerateMetric.inverse_apply`: its inverse is the sharp map.
* `TauCeti.Manifold.ContMDiffNondegenerateMetric.contMDiff_inverse`: the fibrewise inverses form a
  smooth section of `Hom(T*M, TM)`.
* `TauCeti.Manifold.ContMDiffNondegenerateMetric.contMDiffWithinAt_sharp` and its variants: the
  sharp of a `C^n` covector field is a `C^n` vector field, for `n ≤ ∞`.

## References

* B. O'Neill, *Semi-Riemannian Geometry*, Academic Press, 1983, Chapter 3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 2.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti.Manifold.ContMDiffNondegenerateMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (g : ContMDiffNondegenerateMetric (I := I) (M := M))

/-- The flat map `g x : T_x M →L[ℝ] T_x^* M` of a nondegenerate metric is invertible. -/
theorem isInvertible (x : M) : (g x).IsInvertible :=
  -- The tangent fibre is the model space `E`, where the normed structure is available.
  ContinuousLinearMap.isInvertible_of_separatingLeft (E := E) (g.nondegenerate x).1

/-- The inverse of the flat map `g x` is the sharp musical isomorphism. -/
@[simp]
theorem inverse_apply (x : M) (φ : TangentSpace I x →L[ℝ] ℝ) :
    (g x).inverse φ = g.sharp x φ := by
  rw [g.eq_sharp_iff]
  intro w
  rw [(g.isInvertible x).self_apply_inverse, ContinuousLinearMap.coe_coe]

/-- The fibrewise inverses of a smooth nondegenerate metric form a smooth section of the bundle
`Hom(T*M, TM)`. Equivalently, the sharp musical isomorphism is smooth in bundle charts. -/
theorem contMDiff_inverse :
    ContMDiff I (I.prod 𝓘(ℝ, (E →L[ℝ] ℝ) →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' ((E →L[ℝ] ℝ) →L[ℝ] E)
        (E := fun x : M ↦ (TangentSpace I x →L[ℝ] ℝ) →L[ℝ] TangentSpace I x) x (g x).inverse) :=
  ContMDiff.clm_bundle_inverse (b := fun x ↦ x) (ϕ := fun x ↦ g x) g.contMDiff g.isInvertible

variable {n : WithTop ℕ∞} {Φ : (x : M) → TangentSpace I x →L[ℝ] ℝ} {s : Set M} {x : M}

/-- The sharp of a `C^n` covector field is a `C^n` vector field, for `n ≤ ∞`.

We give here a version of this statement within a set at a point. -/
theorem contMDiffWithinAt_sharp (hn : n ≤ ∞)
    (hΦ : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) y (Φ y))
      s x) :
    ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) n
      (fun y ↦ TotalSpace.mk' E y (g.sharp y (Φ y))) s x := by
  simp_rw [← g.inverse_apply]
  exact ((g.contMDiff_inverse.of_le hn).contMDiffAt.contMDiffWithinAt).clm_bundle_apply hΦ

/-- The sharp of a `C^n` covector field is a `C^n` vector field, for `n ≤ ∞`.

We give here a version of this statement at a point. -/
theorem contMDiffAt_sharp (hn : n ≤ ∞)
    (hΦ : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) y (Φ y))
      x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) n (fun y ↦ TotalSpace.mk' E y (g.sharp y (Φ y))) x :=
  g.contMDiffWithinAt_sharp hn hΦ

/-- The sharp of a `C^n` covector field is a `C^n` vector field, for `n ≤ ∞`.

We give here a version of this statement on a set. -/
theorem contMDiffOn_sharp (hn : n ≤ ∞)
    (hΦ : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) y (Φ y))
      s) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) n (fun y ↦ TotalSpace.mk' E y (g.sharp y (Φ y))) s :=
  fun x hx ↦ g.contMDiffWithinAt_sharp hn (hΦ x hx)

/-- The sharp of a `C^n` covector field is a `C^n` vector field, for `n ≤ ∞`. -/
theorem contMDiff_sharp (hn : n ≤ ∞)
    (hΦ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) y (Φ y))) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) n (fun y ↦ TotalSpace.mk' E y (g.sharp y (Φ y))) :=
  fun x ↦ g.contMDiffAt_sharp hn (hΦ x)

end TauCeti.Manifold.ContMDiffNondegenerateMetric
