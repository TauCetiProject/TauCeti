/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic

/-!
# Local Riemannian isometry of `WithMetric.ofWithMetric`

For a `C^n` Riemannian metric `g` on `M`, the tautological map
`WithMetric.ofWithMetric : WithMetric g → M` is a smooth diffeomorphism whose differential is the
identity and pulls `g` back to the installed metric on `WithMetric g`. Consequently, when `g` is
installed as the `RiemannianBundle` instance on `M`, `WithMetric.ofWithMetric` is a local
Riemannian isometry (`TauCeti.WithMetric.isLocalRiemannianIsometry_ofWithMetric`).

## Main results

* `TauCeti.WithMetric.isLocalRiemannianIsometry_ofWithMetric`: `WithMetric.ofWithMetric` is a local
  Riemannian isometry from `WithMetric g` to `(M, g)`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (local isometries and pullback metrics).
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.WithMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- When `g` is installed as the Riemannian metric on `M`, the tautological map
`ofWithMetric : WithMetric g → M` is a local Riemannian isometry. -/
theorem isLocalRiemannianIsometry_ofWithMetric
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    IsLocalRiemannianIsometry I I (ofWithMetric : WithMetric g → M) :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  { contMDiff := contMDiff_ofWithMetric
    isInvertible_mfderiv := fun z ↦ by
      rw [mfderiv_ofWithMetric]
      exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
    inner_mfderiv := fun z u v ↦ (inner_def z u v).symm }

end TauCeti.WithMetric

end
