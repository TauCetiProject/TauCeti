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

All of this holds, with the same proofs, for manifolds `M` and `N` modelled on boundaryless models
`I` and `J` in finite-dimensional spaces `E` and `E'` whose charts are carried to the same
`(n + 1)`-dimensional inner product space `F` by linear equivalences `L` and `L'`
(`TauCeti.HasLinearModelCharts`): the derivative of `f` read in these charts is
`L' ∘ mfderiv f x ∘ L⁻¹`. This covers products of manifolds, such as products of spheres, whose
model `ℝᵐ × ℝⁿ` carries no inner product. The statements for a common inner product model are the
case of identity maps `L` and `L'`.

## Main results

* `TauCeti.Manifold.Orientation.localIndex_toHomologicalOrientation`: at a point of invertible
  derivative the local index is the orientation sign.
* `TauCeti.Manifold.Orientation.degree_toHomologicalOrientation`: the degree of a proper map onto
  a preconnected manifold is the signed count of preimages of any regular value.
* `TauCeti.Manifold.Orientation.mapFundamentalClass_eq_degreeAtRegularValue_smul`: for a map
  between compact manifolds, with preconnected target, `f_*[M]` is the signed count of preimages
  of a regular value times `[N]`.
* `TauCeti.Manifold.Orientation.localIndex_toHomologicalOrientationOfLinearModel`,
  `TauCeti.Manifold.Orientation.degree_toHomologicalOrientationOfLinearModel`,
  `TauCeti.Manifold.Orientation.mapFundamentalClass_eq_degreeAtRegularValue_smul_of_linearModel`:
  the same for manifolds whose charts are carried to a common inner product space by linear
  equivalences.

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

section LinearModel

variable {M N E E' H H' F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {L : E ≃L[ℝ] F} {L' : E' ≃L[ℝ] F}
  [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [ChartedSpace F M] [IsManifold I 1 M]
  [TopologicalSpace N] [T2Space N] [ChartedSpace H' N] [ChartedSpace F N] [IsManifold J 1 N]
  {n : ℕ} (hF : finrank ℝ F = n + 1) (hc : HasLinearModelCharts I L M)
  (hc' : HasLinearModelCharts J L' N)
  (o : Manifold.Orientation I M (Fin (n + 1))) (o' : Manifold.Orientation J N (Fin (n + 1)))

include hc hc' in
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [FiniteDimensional ℝ F] [T2Space M]
  [IsManifold I 1 M] [T2Space N] [IsManifold J 1 N] in
/-- Read in the charts in `F`, a map `f : M → N` differentiable at `x` has derivative
`L' ∘ f' ∘ L⁻¹` at `x`, where `f'` is its manifold derivative. -/
private theorem hasFDerivAt_chartAt_comp_of_linearModel {f : M → N} {x : M}
    (hf : MDifferentiableAt I J f x) :
    HasFDerivAt (chartAt F (f x) ∘ f ∘ (chartAt F x).symm)
      ((L' : E' →L[ℝ] F).comp ((mfderiv I J f x).comp (L.symm : F →L[ℝ] E)))
      (chartAt F x x) := by
  have h := hf.hasMFDerivAt.2
  simp only [hasFDerivWithinAt_univ, ModelWithCorners.range_eq_univ] at h
  have heq : chartAt F (f x) ∘ f ∘ (chartAt F x).symm =
      L' ∘ writtenInExtChartAt I J x f ∘ L.symm := by
    ext z
    simp [hc.chartAt_eq x, hc'.chartAt_eq (f x), writtenInExtChartAt]
  have hx : chartAt F x x = L (extChartAt I x x) := by simp [hc.chartAt_eq x]
  rw [heq, hx]
  refine L'.hasFDerivAt.comp _ (HasFDerivAt.comp _ ?_ L.symm.hasFDerivAt)
  rwa [L.symm_apply_apply]

include hF in
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- For orientations `ω` of `E` and `ω'` of `E'` carried by `L` and `L'` to the same orientation of
`F`, a linear equivalence `e : E ≃ E'` carries `ω` to `ω'` or to `-ω'` according to the sign of
the determinant of `e` read in `F`. -/
private theorem map_eq_of_det_pos_of_map_eq {ω : _root_.Orientation ℝ E (Fin (n + 1))}
    {ω' : _root_.Orientation ℝ E' (Fin (n + 1))}
    (hω : ω'.map _ L'.toLinearEquiv = ω.map _ L.toLinearEquiv) (e : E ≃L[ℝ] E') :
    (0 < ((L' : E' →L[ℝ] F).comp ((e : E →L[ℝ] E').comp (L.symm : F →L[ℝ] E))).det →
      ω.map _ e.toLinearEquiv = ω') ∧
    (((L' : E' →L[ℝ] F).comp ((e : E →L[ℝ] E').comp (L.symm : F →L[ℝ] E))).det < 0 →
      ω.map _ e.toLinearEquiv = -ω') := by
  -- Read in `F`, `e` is the automorphism `g = L⁻¹ ≫ e ≫ L'`.
  set g : F ≃L[ℝ] F := L.symm.trans (e.trans L')
  have hcard : Fintype.card (Fin (n + 1)) = finrank ℝ F := by simp [hF]
  -- The determinant of a continuous linear map is that of its underlying linear map, here `g`.
  have hg : ((L' : E' →L[ℝ] F).comp ((e : E →L[ℝ] E').comp (L.symm : F →L[ℝ] E))).det =
      LinearMap.det (g.toLinearEquiv : F →ₗ[ℝ] F) := rfl
  have hmap : (ω.map _ e.toLinearEquiv).map _ L'.toLinearEquiv =
      (ω.map _ L.toLinearEquiv).map _ g.toLinearEquiv := by
    have hL : e.toLinearEquiv.trans L'.toLinearEquiv = L.toLinearEquiv.trans g.toLinearEquiv := by
      ext v
      simp [g]
    rw [← Orientation.map_trans, ← Orientation.map_trans, hL]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · apply (Orientation.map (Fin (n + 1)) L'.toLinearEquiv).injective
    rw [hmap, hω]
    exact (Orientation.map_eq_iff_det_pos _ _ hcard).2 (by rwa [hg] at h)
  · apply (Orientation.map (Fin (n + 1)) L'.toLinearEquiv).injective
    rw [hmap, Orientation.map_neg, hω]
    exact (Orientation.map_eq_neg_iff_det_neg _ _ hcard).2 (by rwa [hg] at h)

include hc hc' in
/-- The local index at a point of invertible derivative, when the tangent orientations at `x` and
`f x`, carried to `F`, are the same orientation of `F`: both sides are the sign of the Jacobian
read in the charts in `F`. -/
private theorem localIndex_toHomologicalOrientationOfLinearModel_of_map_eq (f : C(M, N)) {x : M}
    (hf : (mfderiv I J f x).IsInvertible)
    (ho : (o'.orientationAt (f x)).map _ L'.toLinearEquiv =
      (o.orientationAt x).map _ L.toLinearEquiv) :
    (o.toHomologicalOrientationOfLinearModel hF hc).localIndex
        (o'.toHomologicalOrientationOfLinearModel hF hc') f x =
      orientationSign o o' f x := by
  -- In the charts in `F` at `x` and `f x`, `f` has derivative `f'` at `x`, which isolates `x`
  -- in its fibre; on an isolating neighbourhood, `f` carries the local orientation selected by
  -- `ω` at `x` to `sign (det f')` times the one selected by `ω` at `f x`.
  set f' : F →L[ℝ] F := (L' : E' →L[ℝ] F).comp ((mfderiv I J f x).comp (L.symm : F →L[ℝ] E))
  set ω : _root_.Orientation ℝ F (Fin (n + 1)) := (o.orientationAt x).map _ L.toLinearEquiv
  have hfd : HasFDerivAt (chartAt F (f x) ∘ f ∘ (chartAt F x).symm) f' (chartAt F x x) :=
    hasFDerivAt_chartAt_comp_of_linearModel hc hc' (mdifferentiableAt_of_isInvertible_mfderiv hf)
  -- An open neighbourhood `U` of `x`, in the domains of the charts at `x` and `f x`, meets the
  -- fibre only in `x`.
  obtain ⟨t, htne, hto, hxt⟩ := eventually_nhds_iff.1
    (eventually_nhdsWithin_iff.1 (eventually_ne_of_mfderiv_injective hf.injective))
  set U : Set M := ((chartAt F x).source ∩ t) ∩ f ⁻¹' (chartAt F (f x)).source
  have hUo : IsOpen U := ((chartAt F x).open_source.inter hto).inter
    ((chartAt F (f x)).open_source.preimage f.continuous)
  have hxU : x ∈ U := ⟨⟨mem_chart_source F x, hxt⟩, mem_chart_source F (f x)⟩
  have hU (z : M) (hz : z ∈ U) (hfz : f z = f x) : z = x := by
    by_contra hzx
    exact htne z hz.1.2 hzx hfz
  obtain ⟨e₀, he⟩ := hf
  -- The tangent spaces are the models `E` and `E'`.
  let e : E ≃L[ℝ] E' := e₀
  have hf'e : f' = (L' : E' →L[ℝ] F).comp ((e : E →L[ℝ] E').comp (L.symm : F →L[ℝ] E)) := by
    simp only [f', ← he]
    rfl
  have hdet : f'.det ≠ 0 := by
    rw [hf'e]
    exact (LinearEquiv.isUnit_det' (L.symm.trans (e.trans L')).toLinearEquiv).ne_zero
  have key := (chartAt F x).localHomologyMap_restrict_localOrientationOfOrientedChart ω hF
    (chartAt F (f x)) f (mem_chart_source F x) (mem_chart_source F (f x)) hUo hxU hU hfd hdet
  rw [← toHomologicalOrientationOfLinearModel_apply hF hc, ← ho,
    ← toHomologicalOrientationOfLinearModel_apply hF hc'] at key
  rw [(HomologicalOrientation.localIndex_eq_iff _ _ hF f rfl hUo hxU hU).2 key]
  -- The orientation sign is the sign of the Jacobian too.
  have hmap := map_eq_of_det_pos_of_map_eq hF ho e
  rcases hdet.lt_or_gt with h | h
  · rw [sign_neg h, SignType.coe_neg_one, orientationSign_of_isOrientationReversingAt
      ((isOrientationReversingAt_iff o o' f x).2 ⟨e₀, he, hmap.2 (hf'e ▸ h)⟩)]
  · rw [sign_pos h, SignType.coe_one, orientationSign_of_isOrientationPreservingAt
      ((isOrientationPreservingAt_iff o o' f x).2 ⟨e₀, he, hmap.1 (hf'e ▸ h)⟩)]

include hc hc' in
/-- **The local index at a point of invertible derivative is the orientation sign**, for manifolds
`M` and `N` modelled on boundaryless models whose charts are carried to the same inner product
space `F` by linear equivalences. The local index of a continuous map `f : M → N` at `x`, with
respect to the homological orientations of `o` and `o'`, is `1` if `f` preserves the orientations
at `x` and `-1` if it reverses them. -/
theorem localIndex_toHomologicalOrientationOfLinearModel (f : C(M, N)) {x : M}
    (hf : (mfderiv I J f x).IsInvertible) :
    (o.toHomologicalOrientationOfLinearModel hF hc).localIndex
        (o'.toHomologicalOrientationOfLinearModel hF hc') f x =
      orientationSign o o' f x := by
  -- Reversing `o'` if necessary, the tangent orientations at `x` and `f x` agree in `F`.
  rcases _root_.Orientation.eq_or_eq_neg ((o'.orientationAt (f x)).map _ L'.toLinearEquiv)
      ((o.orientationAt x).map _ L.toLinearEquiv) (by simp [hF]) with ho | ho
  · exact localIndex_toHomologicalOrientationOfLinearModel_of_map_eq hF hc hc' o o' f hf ho
  · have h := localIndex_toHomologicalOrientationOfLinearModel_of_map_eq hF hc hc' o (-o') f hf
      (by
        rw [orientationAt_neg]
        erw [Orientation.map_neg]
        rw [ho]
        exact neg_neg ((o.orientationAt x).map _ L.toLinearEquiv))
    rwa [toHomologicalOrientationOfLinearModel_neg, HomologicalOrientation.localIndex_neg_right,
      orientationSign_neg_right, neg_inj] at h

include hc hc' in
/-- **The homological degree is the signed count of preimages**, for manifolds modelled on
boundaryless models whose charts are carried to the same inner product space by linear
equivalences. For a proper map `f : M → N` onto a preconnected manifold and a regular value `y`
of `f`, the degree of `f` with respect to the homological orientations of `o` and `o'` is
`degreeAtRegularValue o o' f y`. -/
theorem degree_toHomologicalOrientationOfLinearModel [PreconnectedSpace N] {f : C(M, N)}
    (hf : IsProperMap f) {y : N} (hy : IsRegularValue I J f y) :
    (o.toHomologicalOrientationOfLinearModel hF hc).degree
        (o'.toHomologicalOrientationOfLinearModel hF hc') hF f =
      degreeAtRegularValue o o' f y := by
  have hdim : finrank ℝ E = finrank ℝ E' :=
    L.toLinearEquiv.finrank_eq.trans L'.toLinearEquiv.finrank_eq.symm
  have hfin := hy.finite_preimage_of_isProperMap hdim hf
  rw [HomologicalOrientation.degree_eq_sum_localIndex _ _ hF hF hf hfin,
    degreeAtRegularValue_eq_sum_of_finite hfin]
  exact Finset.sum_congr rfl fun x hx ↦ localIndex_toHomologicalOrientationOfLinearModel hF hc hc'
    o o' f ((isRegularPoint_iff_isInvertible_mfderiv hdim).1
      (hy.isRegularPoint (hfin.mem_toFinset.1 hx)))

include hc hc' in
/-- **The signed count of preimages computes the image of the fundamental class**, for manifolds
modelled on boundaryless models whose charts are carried to the same inner product space by
linear equivalences, such as products of spheres. For a continuous map `f : M → N` between
compact manifolds, with `N` preconnected, and a regular value `y` of `f`,
`f_*[M] = (degreeAtRegularValue o o' f y) • [N]` in `Hₙ₊₁(N; ℤ)`, for the fundamental classes of
the homological orientations of `o` and `o'`. -/
theorem mapFundamentalClass_eq_degreeAtRegularValue_smul_of_linearModel [CompactSpace M]
    [CompactSpace N] [PreconnectedSpace N] {f : C(M, N)} {y : N} (hy : IsRegularValue I J f y) :
    (o.toHomologicalOrientationOfLinearModel hF hc).mapFundamentalClass hF f =
      degreeAtRegularValue o o' f y •
        (o'.toHomologicalOrientationOfLinearModel hF hc').fundamentalClass hF := by
  rw [HomologicalOrientation.mapFundamentalClass_eq_degree_smul _ _ hF hF,
    degree_toHomologicalOrientationOfLinearModel hF hc hc' o o' f.continuous.isProperMap hy]

end LinearModel

variable {M N E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace E N]
  {n : ℕ} (hE : finrank ℝ E = n + 1)

variable [T2Space M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space N] [IsManifold 𝓘(ℝ, E) 1 N]
  (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1)))
  (o' : Manifold.Orientation 𝓘(ℝ, E) N (Fin (n + 1)))

/-- **The local index at a point of invertible derivative is the orientation sign.** For a
continuous map `f : M → N` whose manifold derivative at `x` is invertible, the local index of `f`
at `x` with respect to the homological orientations of `o` and `o'` is `1` if `f` preserves the
orientations at `x` and `-1` if it reverses them. -/
theorem localIndex_toHomologicalOrientation (f : C(M, N)) {x : M}
    (hf : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x).IsInvertible) :
    (o.toHomologicalOrientation hE).localIndex (o'.toHomologicalOrientation hE) f x =
      orientationSign o o' f x := by
  rw [← toHomologicalOrientationOfLinearModel_refl, ← toHomologicalOrientationOfLinearModel_refl]
  exact localIndex_toHomologicalOrientationOfLinearModel hE (hasLinearModelCharts_refl M)
    (hasLinearModelCharts_refl N) o o' f hf

/-- **The homological degree is the signed count of preimages.** For a proper map `f : M → N`
onto a preconnected manifold and a regular value `y` of `f`, the degree of `f` with respect to the
homological orientations of `o` and `o'` is `degreeAtRegularValue o o' f y`. -/
theorem degree_toHomologicalOrientation [PreconnectedSpace N] {f : C(M, N)} (hf : IsProperMap f)
    {y : N} (hy : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, E) f y) :
    (o.toHomologicalOrientation hE).degree (o'.toHomologicalOrientation hE) hE f =
      degreeAtRegularValue o o' f y := by
  rw [← toHomologicalOrientationOfLinearModel_refl, ← toHomologicalOrientationOfLinearModel_refl]
  exact degree_toHomologicalOrientationOfLinearModel hE (hasLinearModelCharts_refl M)
    (hasLinearModelCharts_refl N) o o' hf hy

/-- **The signed count of preimages computes the image of the fundamental class.** For a continuous
map `f : M → N` between compact manifolds, with `N` preconnected, and a regular value `y` of `f`,
`f_*[M] = (degreeAtRegularValue o o' f y) • [N]` in `Hₙ₊₁(N; ℤ)`, for the fundamental classes of
the homological orientations of `o` and `o'`. -/
theorem mapFundamentalClass_eq_degreeAtRegularValue_smul [CompactSpace M] [CompactSpace N]
    [PreconnectedSpace N] {f : C(M, N)} {y : N} (hy : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, E) f y) :
    (o.toHomologicalOrientation hE).mapFundamentalClass hE f =
      degreeAtRegularValue o o' f y • (o'.toHomologicalOrientation hE).fundamentalClass hE := by
  rw [← toHomologicalOrientationOfLinearModel_refl, ← toHomologicalOrientationOfLinearModel_refl]
  exact mapFundamentalClass_eq_degreeAtRegularValue_smul_of_linearModel hE
    (hasLinearModelCharts_refl M) (hasLinearModelCharts_refl N) o o' hy

end Manifold.Orientation

end TauCeti
