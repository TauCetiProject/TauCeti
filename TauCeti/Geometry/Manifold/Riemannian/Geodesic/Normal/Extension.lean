/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Coordinates
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Distortion
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Global vector fields parallel at a point

On a boundaryless Riemannian manifold, every tangent vector `v ∈ T_p M` is the value at `p` of a
smooth vector field `X` on all of `M` whose Levi-Civita covariant derivative vanishes at `p`
(`TauCeti.Manifold.exists_contMDiff_apply_eq_and_leviCivitaConnection_eq_zero`).

The normal coordinate field of `v` on a normal neighbourhood of `p` has these properties near `p`
(`TauCeti.Manifold.IsNormalDomain.leviCivitaConnection_normalCoordinateField_self`). Extending it
from a neighbourhood of `p` to a global smooth section
(`ContMDiffSection.exists_eventuallyEq_isCompact_tsupport_subset`) keeps both, since the
covariant derivative at `p` only depends on the germ there.

Such fields are the test sections of the maximum principle for tensors. For an endomorphism
field `A`, a field `X` with `∇X (p) = 0` kills the first-order terms `(∇A)(∇X)` and `|∇X|²` in
`Δ ⟪A X, X⟫ (p)` and `Δ |X|² (p)`. If moreover `X p` is an eigenvector of a symmetric `A p` of
eigenvalue `c`, the remaining terms in `∇*∇X` cancel in `Δ (⟪A X, X⟫ - c |X|²) (p)`, leaving
`-⟪(∇*∇A) X, X⟫ (p)`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 5
  (normal coordinates and geodesic frames).
-/

public section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **A global vector field parallel at a point.** On a boundaryless Riemannian manifold, every
tangent vector `v ∈ T_p M` extends to a smooth vector field `X` on `M` with `X p = v` and
`∇X (p) = 0` for the Levi-Civita connection. -/
theorem exists_contMDiff_apply_eq_and_leviCivitaConnection_eq_zero (p : M)
    (v : TangentSpace I p) :
    ∃ X : Π q : M, TangentSpace I q, CMDiff ∞ (T% X) ∧ X p = v ∧
      leviCivitaConnection I M X p = 0 := by
  obtain ⟨r, -, hN, -⟩ := exists_isNormalDomain_ball_norm_mfderiv_bounds (I := I) (M := M) p
    one_lt_two
  set N := normalCoordinateField I M p (Metric.ball 0 r) v
  -- A global smooth section equal to the normal coordinate field near `p`.
  obtain ⟨X, hXN, -, -⟩ := ContMDiffSection.exists_eventuallyEq_isCompact_tsupport_subset
    isCompact_singleton (hN.isOpen_image.mem_nhdsSet.2 (singleton_subset_iff.2 hN.self_mem_image))
    (hN.contMDiffOn_normalCoordinateField v)
  rw [nhdsSet_singleton] at hXN
  refine ⟨X, X.contMDiff, by simp [hXN.self_of_nhds, hN.normalCoordinateField_self], ?_⟩
  -- Near `p` the field is the normal coordinate field, which is parallel at `p`.
  rw [(leviCivitaConnection I M).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    ((X.contMDiff p).mdifferentiableAt (by simp))
    (hN.mdifferentiableAt_normalCoordinateField v hN.self_mem_image) Filter.univ_mem hXN]
  exact hN.leviCivitaConnection_normalCoordinateField_self v

end TauCeti.Manifold
