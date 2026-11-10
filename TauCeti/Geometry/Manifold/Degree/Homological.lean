/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LocalIndex
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.Geometry.Manifold.Degree.Basic
public import TauCeti.Geometry.Manifold.RegularValue.Fibre
import TauCeti.Geometry.Manifold.MFDeriv.LocalInjectivity

/-!
# The smooth degree is the homological degree

Let `M` and `N` be boundaryless `C¹` manifolds modelled on the same real inner product space `E`
of dimension `n + 1`, with orientations `o` of `M` and `o'` of `N`
(`TauCeti.Manifold.Orientation`). Through their local homology generators
(`TauCeti.Manifold.Orientation.toHomologicalOrientation`) these are homological orientations,
for which a continuous map `f : M → N` has a local index at every point
(`TauCeti.HomologicalOrientation.localIndex`) and, when it is proper and `N` is preconnected, a
degree (`TauCeti.HomologicalOrientation.degree`) characterized by `f_*[M] = deg f • [N]` for
compact `M` and `N`.

At a point `x` where the manifold derivative of `f` is invertible, the local index of `f` is the
orientation sign of `f` at `x` (`TauCeti.Manifold.Orientation.localIndex_toHomologicalOrientation`):
`1` where `f` preserves the orientations and `-1` where it reverses them. In the preferred charts
at `x` and `f x`, the derivative of `f` is that of `χ ∘ f ∘ φ.symm`, which acts on the local
homology of the model by the sign of its Jacobian
(`OpenPartialHomeomorph.localHomologyMap_restrict_localOrientationOfOrientedChart`). Only
differentiability at `x` is used; it already makes `x` isolated in its fibre
(`TauCeti.eventually_ne_of_mfderiv_injective`).

The fibre of a proper map over a regular value `y` is compact and, by this isolation, discrete,
hence finite (`TauCeti.IsRegularValue.finite_preimage_of_isProperMap`). Summing over it, the
homological degree of a proper map onto a preconnected manifold is the signed count of preimages
`degreeAtRegularValue o o' f y` (`TauCeti.Manifold.Orientation.degree_toHomologicalOrientation`).
For a map between compact manifolds, with `N` preconnected, this reads
`f_*[M] = (degreeAtRegularValue o o' f y) • [N]` in `Hₙ₊₁(N; ℤ)`
(`TauCeti.Manifold.Orientation.mapFundamentalClass_eq_degreeAtRegularValue_smul`), so a degree
computed by counting preimages with signs computes the image of the fundamental class.

## Main results

* `TauCeti.Manifold.Orientation.localIndex_toHomologicalOrientation`: at a point of invertible
  derivative the local index is the orientation sign.
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

open Filter Module Set Topology
open scoped Manifold

namespace TauCeti

namespace Manifold.Orientation

variable {M N E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace E N]
  {n : ℕ} (hE : finrank ℝ E = n + 1)

variable [T2Space M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space N] [IsManifold 𝓘(ℝ, E) 1 N]
  (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1)))
  (o' : Manifold.Orientation 𝓘(ℝ, E) N (Fin (n + 1)))

/-- The local index at a point of invertible derivative, when the tangent orientations at `x` and
`f x` are the same orientation of the model: both sides are the sign of the Jacobian. -/
private theorem localIndex_toHomologicalOrientation_of_orientationAt_eq (f : C(M, N)) {x : M}
    (hf : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x).IsInvertible)
    (ho : o'.orientationAt (f x) = o.orientationAt x) :
    (o.toHomologicalOrientation hE).localIndex (o'.toHomologicalOrientation hE) f x =
      orientationSign o o' f x := by
  -- In the preferred charts at `x` and `f x`, `f` has derivative `f'` at `x`, which isolates `x`
  -- in its fibre; on an isolating neighbourhood, `f` carries the local orientation selected by the
  -- tangent orientation `ω` at `x` to `sign (det f')` times the one selected by `ω` at `f x`.
  set f' : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x
  set ω : _root_.Orientation ℝ E (Fin (n + 1)) := o.orientationAt x
  have hcard : Fintype.card (Fin (n + 1)) = finrank ℝ E := by simp [hE]
  have hfd : HasFDerivAt (chartAt E (f x) ∘ f ∘ (chartAt E x).symm) f' (chartAt E x x) := by
    have h := (mdifferentiableAt_of_isInvertible_mfderiv hf).hasMFDerivAt.2
    simp only [writtenInExtChartAt, hasFDerivWithinAt_univ, ModelWithCorners.range_eq_univ] at h
    exact h
  -- An open neighbourhood `U` of `x`, in the domains of the preferred charts at `x` and `f x`,
  -- meets the fibre only in `x`.
  obtain ⟨t, htne, hto, hxt⟩ := eventually_nhds_iff.1
    (eventually_nhdsWithin_iff.1 (eventually_ne_of_mfderiv_injective hf.injective))
  set U : Set M := ((chartAt E x).source ∩ t) ∩ f ⁻¹' (chartAt E (f x)).source
  have hUo : IsOpen U := ((chartAt E x).open_source.inter hto).inter
    ((chartAt E (f x)).open_source.preimage f.continuous)
  have hxU : x ∈ U := ⟨⟨mem_chart_source E x, hxt⟩, mem_chart_source E (f x)⟩
  have hU (z : M) (hz : z ∈ U) (hfz : f z = f x) : z = x := by
    by_contra hzx
    exact htne z hz.1.2 hzx hfz
  obtain ⟨e, he⟩ := hf
  -- The tangent spaces are the model `E`, on which `e` is an equivalence.
  let e' : E ≃L[ℝ] E := e
  have he' : (e' : E →L[ℝ] E) = f' := he
  have hdet : f'.det ≠ 0 := by
    rw [← he']
    exact (LinearEquiv.isUnit_det' e'.toLinearEquiv).ne_zero
  have key := (chartAt E x).localHomologyMap_restrict_localOrientationOfOrientedChart ω hE
    (chartAt E (f x)) f (mem_chart_source E x) (mem_chart_source E (f x)) hUo hxU hU hfd hdet
  rw [← localOrientationOfManifoldOrientation_eq, ← ho, ← localOrientationOfManifoldOrientation_eq,
    ← toHomologicalOrientation_apply, ← toHomologicalOrientation_apply] at key
  rw [(HomologicalOrientation.localIndex_eq_iff _ _ hE f rfl hUo hxU hU).2 key]
  -- The orientation sign is the sign of the Jacobian too.
  rcases hdet.lt_or_gt with h | h
  · have hmap : _root_.Orientation.map (Fin (n + 1)) e'.toLinearEquiv ω = -ω :=
      (_root_.Orientation.map_eq_neg_iff_det_neg _ _ hcard).2 (by rwa [← he'] at h)
    rw [sign_neg h, SignType.coe_neg_one, orientationSign_of_isOrientationReversingAt
      ((isOrientationReversingAt_iff o o' f x).2 ⟨e, he, by rw [ho]; exact hmap⟩)]
  · have hmap : _root_.Orientation.map (Fin (n + 1)) e'.toLinearEquiv ω = ω :=
      (_root_.Orientation.map_eq_iff_det_pos _ _ hcard).2 (by rwa [← he'] at h)
    rw [sign_pos h, SignType.coe_one, orientationSign_of_isOrientationPreservingAt
      ((isOrientationPreservingAt_iff o o' f x).2 ⟨e, he, by rw [ho]; exact hmap⟩)]

/-- **The local index at a point of invertible derivative is the orientation sign.** For a
continuous map `f : M → N` whose manifold derivative at `x` is invertible, the local index of `f`
at `x` with respect to the homological orientations of `o` and `o'` is `1` if `f` preserves the
orientations at `x` and `-1` if it reverses them. -/
theorem localIndex_toHomologicalOrientation (f : C(M, N)) {x : M}
    (hf : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x).IsInvertible) :
    (o.toHomologicalOrientation hE).localIndex (o'.toHomologicalOrientation hE) f x =
      orientationSign o o' f x := by
  -- Reversing `o'` if necessary, the tangent orientations at `x` and `f x` agree.
  rcases _root_.Orientation.eq_or_eq_neg (o'.orientationAt (f x)) (o.orientationAt x)
    (by simp [hE]) with ho | ho
  · exact localIndex_toHomologicalOrientation_of_orientationAt_eq hE o o' f hf ho
  · have h := localIndex_toHomologicalOrientation_of_orientationAt_eq hE o (-o') f hf
      (by rw [orientationAt_neg, ho]; exact neg_neg (o.orientationAt x))
    rwa [toHomologicalOrientation_neg, HomologicalOrientation.localIndex_neg_right,
      orientationSign_neg_right, neg_inj] at h

/-- **The homological degree is the signed count of preimages.** For a proper map `f : M → N`
onto a preconnected manifold and a regular value `y` of `f`, the degree of `f` with respect to the
homological orientations of `o` and `o'` is `degreeAtRegularValue o o' f y`. -/
theorem degree_toHomologicalOrientation [PreconnectedSpace N] {f : C(M, N)} (hf : IsProperMap f)
    {y : N} (hy : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, E) f y) :
    (o.toHomologicalOrientation hE).degree (o'.toHomologicalOrientation hE) hE f =
      degreeAtRegularValue o o' f y := by
  have hfin := hy.finite_preimage_of_isProperMap rfl hf
  rw [HomologicalOrientation.degree_eq_sum_localIndex _ _ hE hE hf hfin,
    degreeAtRegularValue_eq_sum_of_finite hfin]
  exact Finset.sum_congr rfl fun x hx ↦ localIndex_toHomologicalOrientation hE o o' f
    ((isRegularPoint_iff_isInvertible_mfderiv rfl).1
      (hy.isRegularPoint (hfin.mem_toFinset.1 hx)))

/-- **The signed count of preimages computes the image of the fundamental class.** For a continuous
map `f : M → N` between compact manifolds, with `N` preconnected, and a regular value `y` of `f`,
`f_*[M] = (degreeAtRegularValue o o' f y) • [N]` in `Hₙ₊₁(N; ℤ)`, for the fundamental classes of
the homological orientations of `o` and `o'`. -/
theorem mapFundamentalClass_eq_degreeAtRegularValue_smul [CompactSpace M] [CompactSpace N]
    [PreconnectedSpace N] {f : C(M, N)} {y : N} (hy : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, E) f y) :
    (o.toHomologicalOrientation hE).mapFundamentalClass hE f =
      degreeAtRegularValue o o' f y • (o'.toHomologicalOrientation hE).fundamentalClass hE := by
  rw [HomologicalOrientation.mapFundamentalClass_eq_degree_smul _ _ hE hE,
    degree_toHomologicalOrientation hE o o' f.continuous.isProperMap hy]

end Manifold.Orientation

end TauCeti
