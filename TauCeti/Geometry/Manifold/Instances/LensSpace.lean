/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.LensSpace.Basic
public import TauCeti.Analysis.InnerProductSpace.Euclidean.Space
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Manifold.Instances.Quotient

/-!
# Lens spaces are analytic manifolds

The lens space `TauCeti.LensSpace m ℓ` is the orbit space of the unit sphere `S²ᵏ⁺¹ ⊆ ℂᵏ⁺¹` under
the free action of the finite lens group `TauCeti.lensGroup m ℓ`
(`TauCeti.AlgebraicTopology.UniversalCover.LensSpace.Basic`). The lens group consists of linear
isometries, so it acts on the sphere by analytic diffeomorphisms, and the orbit space is an
analytic manifold of dimension `2k + 1` by `TauCeti.instIsManifoldQuotient`. The projection from
the sphere is an analytic local diffeomorphism.

As for Mathlib's spheres (`EuclideanSpace.instChartedSpaceSphere`), the manifold structure is
stated for any `n` with `Fact (finrank ℝ (EuclideanSpace ℂ (Fin (k + 1))) = n + 1)`, and the
instance `TauCeti.factFinrankEuclideanSpaceComplex`
(`TauCeti.Analysis.InnerProductSpace.Euclidean.Space`) supplies `n = 2k + 1`. This lets instance
search find the structure for a concrete model such as `𝓡 3`, where it could not solve
`2 * k + 1 = 3` for `k`.

## Main results

* `TauCeti.LensSpace.instIsManifold`: the lens space is an analytic manifold modelled on
  `ℝ²ᵏ⁺¹`.
* `TauCeti.LensSpace.isLocalDiffeomorph_mk`: the projection from the sphere is an analytic local
  diffeomorphism.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Example 2.43 (lens spaces
  as quotients of odd-dimensional spheres).
-/

public section

open Metric Module
open scoped Manifold ContDiff

namespace TauCeti

noncomputable section

section Smooth

variable (m : ℕ) [NeZero m] {k : ℕ} (ℓ : Fin (k + 1) → (ZMod m)ˣ) {n : ℕ}
  [Fact (finrank ℝ (EuclideanSpace ℂ (Fin (k + 1))) = n + 1)]

/-- The lens group acts on the unit sphere of `ℂᵏ⁺¹` by analytic diffeomorphisms. -/
instance : ContMDiffConstSMul (𝓡 n) ω (lensGroup m ℓ)
    (sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1) :=
  IsScalarTower.contMDiffConstSMul
    (EuclideanSpace ℂ (Fin (k + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin (k + 1)))

end Smooth

namespace LensSpace

variable (m : ℕ) [NeZero m] {k : ℕ} (ℓ : Fin (k + 1) → (ZMod m)ˣ) {n : ℕ}
  [Fact (finrank ℝ (EuclideanSpace ℂ (Fin (k + 1))) = n + 1)]

/-- The charts of a lens space, pushed forward from the sphere along the orbit projection. -/
instance instChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin n)) (LensSpace m ℓ) :=
  inferInstanceAs (ChartedSpace (EuclideanSpace ℝ (Fin n))
    (MulAction.orbitRel.Quotient (lensGroup m ℓ) (sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1)))

/-- **A lens space is an analytic manifold** of dimension `2k + 1`. -/
instance instIsManifold : IsManifold (𝓡 n) ω (LensSpace m ℓ) :=
  inferInstanceAs (IsManifold (𝓡 n) ω (MulAction.orbitRel.Quotient (lensGroup m ℓ)
    (sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1)))

/-- The projection from the sphere to a lens space is an analytic local diffeomorphism. -/
theorem isLocalDiffeomorph_mk : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ω (mk m ℓ) :=
  mk_def m ℓ ▸ isLocalDiffeomorph_quotientMk

end LensSpace

end

end TauCeti
