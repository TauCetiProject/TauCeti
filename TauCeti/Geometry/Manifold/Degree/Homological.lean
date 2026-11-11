/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.Geometry.Manifold.Degree.Basic
public import TauCeti.Geometry.Manifold.RegularValue.Fibre

/-!
# The smooth degree is the homological degree

Let `M` and `N` be boundaryless `C¹` manifolds of dimension `n + 1`, modelled on possibly
different finite-dimensional real normed spaces `F` and `F'`, with orientations `o` of `M` and `o'`
of `N` (`TauCeti.Manifold.Orientation`). Through their local homology generators
(`TauCeti.Manifold.Orientation.toHomologicalOrientation`) these are homological orientations,
for which a continuous map `f : M → N` has a local index at every point
(`TauCeti.HomologicalOrientation.localIndex`) and, when it is proper and `N` is preconnected, a
degree (`TauCeti.HomologicalOrientation.degree`) characterized by `f_*[M] = deg f • [N]` for
compact `M` and `N`.

At a point where the manifold derivative of `f` is invertible, the local index of `f` is the
orientation sign of `f` (`TauCeti.Manifold.Orientation.localIndex_toHomologicalOrientation`).
The fibre of a proper map over a regular value `y` is compact and discrete, hence finite
(`TauCeti.IsRegularValue.finite_preimage_of_isProperMap`). Summing over it, the homological degree
of a proper map onto a preconnected manifold is the signed count of preimages
`degreeAtRegularValue o o' f y` (`TauCeti.Manifold.Orientation.degree_toHomologicalOrientation`).
For a map between compact manifolds, with `N` preconnected, this reads
`f_*[M] = (degreeAtRegularValue o o' f y) • [N]` in `Hₙ₊₁(N; ℤ)`
(`TauCeti.Manifold.Orientation.mapFundamentalClass_eq_degreeAtRegularValue_smul`), so a degree
computed by counting preimages with signs computes the image of the fundamental class. The models
need not be inner product spaces: a product of spheres, modelled on a product of Euclidean spaces
with the sup norm, is covered.

## Main results

* `TauCeti.Manifold.Orientation.degree_toHomologicalOrientation`: the degree of a proper map onto
  a preconnected manifold is the signed count of preimages of any regular value.
* `TauCeti.Manifold.Orientation.mapFundamentalClass_eq_degreeAtRegularValue_smul`: for a map
  between compact manifolds, with preconnected target, `f_*[M]` is the signed count of preimages
  of a regular value times `[N]`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Proposition 2.30 (the degree as a sum of local degrees).
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5 (the degree as a signed count of preimages).
-/

public section

noncomputable section

open Module
open scoped Manifold

namespace TauCeti

namespace Manifold.Orientation

variable {M N F F' : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  [TopologicalSpace M] [T2Space M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) 1 M]
  [TopologicalSpace N] [T2Space N] [ChartedSpace F' N] [IsManifold 𝓘(ℝ, F') 1 N]
  {n : ℕ} (hF : finrank ℝ F = n + 1) (hF' : finrank ℝ F' = n + 1)
  (o : Manifold.Orientation 𝓘(ℝ, F) M (Fin (n + 1)))
  (o' : Manifold.Orientation 𝓘(ℝ, F') N (Fin (n + 1)))

/-- **The homological degree is the signed count of preimages.** For a proper map `f : M → N`
onto a preconnected manifold and a regular value `y` of `f`, the degree of `f` with respect to the
homological orientations of `o` and `o'` is `degreeAtRegularValue o o' f y`. -/
theorem degree_toHomologicalOrientation [PreconnectedSpace N] {f : C(M, N)} (hf : IsProperMap f)
    {y : N} (hy : IsRegularValue 𝓘(ℝ, F) 𝓘(ℝ, F') f y) :
    (o.toHomologicalOrientation hF).degree (o'.toHomologicalOrientation hF') hF f =
      degreeAtRegularValue o o' f y := by
  have hfin := hy.finite_preimage_of_isProperMap (hF.trans hF'.symm) hf
  rw [HomologicalOrientation.degree_eq_sum_localIndex _ _ hF hF' hf hfin,
    degreeAtRegularValue_eq_sum_of_finite hfin]
  exact Finset.sum_congr rfl fun x hx ↦ localIndex_toHomologicalOrientation hF hF' o o' f
    ((isRegularPoint_iff_isInvertible_mfderiv (hF.trans hF'.symm)).1
      (hy.isRegularPoint (hfin.mem_toFinset.1 hx)))

/-- **The signed count of preimages computes the image of the fundamental class.** For a continuous
map `f : M → N` between compact manifolds, with `N` preconnected, and a regular value `y` of `f`,
`f_*[M] = (degreeAtRegularValue o o' f y) • [N]` in `Hₙ₊₁(N; ℤ)`, for the fundamental classes of
the homological orientations of `o` and `o'`. -/
theorem mapFundamentalClass_eq_degreeAtRegularValue_smul [CompactSpace M] [CompactSpace N]
    [PreconnectedSpace N] {f : C(M, N)} {y : N} (hy : IsRegularValue 𝓘(ℝ, F) 𝓘(ℝ, F') f y) :
    (o.toHomologicalOrientation hF).mapFundamentalClass hF f =
      degreeAtRegularValue o o' f y • (o'.toHomologicalOrientation hF').fundamentalClass hF' := by
  rw [HomologicalOrientation.mapFundamentalClass_eq_degree_smul _ _ hF hF',
    degree_toHomologicalOrientation hF hF' o o' f.continuous.isProperMap hy]

end Manifold.Orientation

end TauCeti
