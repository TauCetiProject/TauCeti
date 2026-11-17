/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LocalIndex
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.Geometry.Manifold.Degree.Global
public import TauCeti.Geometry.Manifold.RegularValue.Fibre
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass
import TauCeti.Geometry.Manifold.MFDeriv.LocalInjectivity
import TauCeti.Geometry.Manifold.ModelTransport.Boundaryless
import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.LinearEquiv
import TauCeti.Geometry.Manifold.Orientation.Pullback
import TauCeti.Topology.Maps.Proper.Basic

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

The same holds for compact connected boundaryless manifolds modelled on any finite-dimensional real
normed spaces, such as products, read through copies charted in `ℝⁿ⁺¹`
(`TauCeti.BoundarylessModel`) with the orientations pulled back along the identities. Without a
common chart there is no preferred fundamental class, and the formula holds up to sign for any
integral fundamental classes (`TauCeti.IsFundamentalClass`) of `M` and `N`
(`TauCeti.Manifold.Orientation.exists_singularHomologyMap_eq_degreeAtRegularValue_smul`).

When `N` is moreover σ-compact, a proper `C¹` map has a regular value by Sard's theorem, so its
homological degree is the mapping degree `TauCeti.degree o o' f`
(`TauCeti.Manifold.Orientation.degree_toHomologicalOrientation_eq_degree`). For a proper smooth
map onto a connected σ-compact manifold, the degree formula of
`TauCeti.Geometry.Manifold.Degree.Global` then computes the integrals of pulled-back compactly
supported top forms through the homological degree, the integer `deg f` with
`f_*[M]_{f⁻¹(K)} = deg f • [N]_K` for every compact `K ⊆ N`:
$$\int_M f^*\varphi = \deg(f) \int_N \varphi$$
(`TauCeti.Manifold.Orientation.integralTopForm_mpullback_eq_degree_toHomologicalOrientation_mul`).
Neither manifold need be compact; for instance `f` may be a proper smooth self-map of an open
disc.

## Main results

* `TauCeti.Manifold.Orientation.localIndex_toHomologicalOrientation`: at a point of invertible
  derivative the local index is the orientation sign.
* `TauCeti.Manifold.Orientation.degree_toHomologicalOrientation`: the degree of a proper map onto
  a preconnected manifold is the signed count of preimages of any regular value.
* `TauCeti.Manifold.Orientation.mapFundamentalClass_eq_degreeAtRegularValue_smul`: for a map
  between compact manifolds, with preconnected target, `f_*[M]` is the signed count of preimages
  of a regular value times `[N]`.
* `TauCeti.Manifold.Orientation.exists_singularHomologyMap_eq_degreeAtRegularValue_smul`: for a
  `C¹` map between compact connected boundaryless manifolds with any models, `f_* μ` is `±` the
  signed count of preimages of a regular value times `ν`, for any integral fundamental classes `μ`
  and `ν`.
* `TauCeti.Manifold.Orientation.degree_toHomologicalOrientation_eq_degree`: the homological
  degree of a proper `C¹` map onto a preconnected σ-compact manifold is its mapping degree.
* `TauCeti.Manifold.Orientation.integralTopForm_mpullback_eq_degree_toHomologicalOrientation_mul`:
  `∫_M f^*φ = deg(f) ∫_N φ` for a proper smooth map, with the homological degree.

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

/-- **The homological degree is the mapping degree.** For a proper `C¹` map `f : M → N` onto a
preconnected σ-compact manifold, the degree of `f` with respect to the homological orientations of
`o` and `o'` is the mapping degree `TauCeti.degree o o' f`, the signed count of preimages of a
regular value. -/
theorem degree_toHomologicalOrientation_eq_degree [SigmaCompactSpace N] [PreconnectedSpace N]
    {f : C(M, N)} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 f) (hfp : IsProperMap f) :
    (o.toHomologicalOrientation hE).degree (o'.toHomologicalOrientation hE) hE f =
      degree o o' f := by
  rcases isEmpty_or_nonempty N with hN | hN
  · rw [HomologicalOrientation.degree_of_isEmpty, degree_of_isEmpty]
  -- The domain of a proper map to a σ-compact space is σ-compact, so Sard's theorem applies.
  have := hfp.sigmaCompactSpace
  have h : ∃ y, IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, E) f y :=
    (dense_isRegularValue rfl (hf.mdifferentiable one_ne_zero)).nonempty
  rw [degree_eq_degreeAtRegularValue_choose h]
  exact degree_toHomologicalOrientation hE o o' hfp h.choose_spec

open scoped ContDiff in
/-- **The degree formula for the homological degree.** For a proper smooth map `f : M → N` onto a
connected σ-compact manifold and a compactly supported smooth top form `φ` on `N`,
`∫_M f^*φ = deg(f) ∫_N φ`, where `deg(f)` is the degree of `f` with respect to the homological
orientations of `o` and `o'`, so that `f_*[M]_{f⁻¹(K)} = deg(f) • [N]_K` for every compact
`K ⊆ N`. -/
theorem integralTopForm_mpullback_eq_degree_toHomologicalOrientation_mul
    [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E) ∞ N] [SigmaCompactSpace N] [ConnectedSpace N]
    {f : C(M, N)} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ f) (hfp : IsProperMap f)
    {φ : RoughForm 𝓘(ℝ, E) N ℝ (n + 1)} (hφ : IsSmoothForm 𝓘(ℝ, E) ∞ φ)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin (n + 1)]→L[ℝ] ℝ) φ)) :
    integralTopForm o (mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) f φ) =
      (o.toHomologicalOrientation hE).degree (o'.toHomologicalOrientation hE) hE f *
        integralTopForm o' φ := by
  rw [degree_toHomologicalOrientation_eq_degree hE o o' (hf.of_le (by simp)) hfp]
  exact integralTopForm_mpullback_eq_degree_mul o o' hf hfp hφ hc

section AnyModel

open AlgebraicTopology

variable {W W' H H' M N : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W'] [TopologicalSpace H]
  [TopologicalSpace H'] {I : ModelWithCorners ℝ W H} [I.Boundaryless]
  {J : ModelWithCorners ℝ W' H'} [J.Boundaryless]
  [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I 1 M] [CompactSpace M]
  [ConnectedSpace M]
  [TopologicalSpace N] [T2Space N] [ChartedSpace H' N] [IsManifold J 1 N] [CompactSpace N]
  [ConnectedSpace N]

omit [I.Boundaryless] [J.Boundaryless] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [T2Space N] [CompactSpace N] [ConnectedSpace N] in
/-- The degree formula of
`TauCeti.Manifold.Orientation.exists_singularHomologyMap_eq_degreeAtRegularValue_smul`, given `C¹`
diffeomorphisms `ιM : M' → M` and `ιN : N' → N` from compact connected manifolds charted
in one inner product space `V`: on these, `f` is read as `ιN⁻¹ ∘ f ∘ ιM`, whose degree is that of
`f` for the pulled-back orientations, and the inner-product formula applies. -/
private theorem exists_singularHomologyMap_eq_degreeAtRegularValue_smul_of_diffeomorph
    {V M' N' : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {k : ℕ} (hV : finrank ℝ V = k + 1)
    [TopologicalSpace M'] [T2Space M'] [ChartedSpace V M'] [IsManifold 𝓘(ℝ, V) 1 M']
    [CompactSpace M'] [ConnectedSpace M']
    [TopologicalSpace N'] [T2Space N'] [ChartedSpace V N'] [IsManifold 𝓘(ℝ, V) 1 N']
    [CompactSpace N'] [ConnectedSpace N']
    (ιM : M' ≃ₘ^1⟮𝓘(ℝ, V), I⟯ M) (ιN : N' ≃ₘ^1⟮𝓘(ℝ, V), J⟯ N)
    (o : Manifold.Orientation I M (Fin (k + 1))) (o' : Manifold.Orientation J N (Fin (k + 1)))
    {f : C(M, N)} (hf : ContMDiff I J 1 f) {y : N} (hy : IsRegularValue I J f y)
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) (k + 1) :
      ModuleCat.{0} ℤ)} (hμ : IsFundamentalClass μ)
    {ν : ((TopCat.toSSet.obj (TopCat.of N)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) (k + 1) :
      ModuleCat.{0} ℤ)} (hν : IsFundamentalClass ν) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) (k + 1)).obj
          (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom f)).hom μ =
        (s * degreeAtRegularValue o o' f y) • ν := by
  have hιM (x) : (mfderiv 𝓘(ℝ, V) I ιM x).IsInvertible := ιM.isInvertible_mfderiv one_ne_zero
  have hιN (x) : (mfderiv 𝓘(ℝ, V) J ιN x).IsInvertible := ιN.isInvertible_mfderiv one_ne_zero
  let oM := o.pullback ιM.contMDiff hιM (by simp [hV])
  let oN := o'.pullback ιN.contMDiff hιN (by simp [hV])
  -- Read on the copies, `f` is `g = ιN⁻¹ ∘ f ∘ ιM`, with the same degree at `ιN⁻¹ y`.
  let g : C(M', N') :=
    (ιN.symm.toHomeomorph : C(N, N')).comp
      (f.comp (ιM.toHomeomorph : C(M', M)))
  have hιg : ⇑ιN ∘ ⇑g = ⇑f ∘ ⇑ιM := funext fun x ↦ by simp [g]
  have hg : MDifferentiable 𝓘(ℝ, V) 𝓘(ℝ, V) g :=
    (ιN.symm.contMDiff.comp (hf.comp ιM.contMDiff)).mdifferentiable one_ne_zero
  have hgdeg : degreeAtRegularValue oM oN g (ιN.symm y) = degreeAtRegularValue o o' f y := by
    rw [← degreeAtRegularValue_comp_left (e := ιN) (fun _ hz ↦ ιN.injective hz)
      (o'.isOrientationPreservingAt_pullback _ hιN _ _) fun x _ ↦ hg x, hιg, ιN.apply_symm_apply,
      degreeAtRegularValue_comp_of_bijective (e := ιM) ιM.toHomeomorph.bijective
        (o.isOrientationPreservingAt_pullback _ hιM _) (hf.mdifferentiable one_ne_zero)]
  have hreg : IsRegularValue 𝓘(ℝ, V) 𝓘(ℝ, V) g (ιN.symm y) := by
    refine isRegularValue_iff.2 fun x hx ↦ ?_
    have hx' : f (ιM x) = y := by simpa [g] using congrArg ιN hx
    exact (isRegularPoint_iff.2 (ιN.symm.isInvertible_mfderiv one_ne_zero).surjective).comp
      ((hy.isRegularPoint hx').comp (isRegularPoint_iff.2 (hιM x).surjective))
  have key := mapFundamentalClass_eq_degreeAtRegularValue_smul hV oM oN hreg
  rw [hgdeg] at key
  -- Compare `μ` and `ν` with the images of the fundamental classes of the copies.
  obtain ⟨s₁, hs₁, rfl⟩ :=
    (oM.toHomologicalOrientation hV).exists_eq_smul_mapFundamentalClass_of_isFundamentalClass hV
      ιM.toHomeomorph hμ
  obtain ⟨s₂, hs₂, rfl⟩ :=
    (oN.toHomologicalOrientation hV).exists_eq_smul_mapFundamentalClass_of_isFundamentalClass hV
      ιN.toHomeomorph hν
  refine ⟨s₁ * s₂, ?_, ?_⟩
  · rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl <;> simp
  -- `f ∘ ιM = ιN ∘ g` carries `±[M']` to `±deg • ιN_*[N']`.
  have hcomp : f.comp (ιM.toHomeomorph : C(M', M)) =
      (ιN.toHomeomorph : C(N', N)).comp g :=
    ContinuousMap.ext fun x ↦ (congrFun hιg x).symm
  rw [map_zsmul, ← HomologicalOrientation.mapFundamentalClass_comp, hcomp,
    HomologicalOrientation.mapFundamentalClass_comp, key]
  -- The fundamental class of `N'` is read in the homology functor's object.
  erw [map_zsmul]
  rw [← HomologicalOrientation.mapFundamentalClass_def, smul_smul]
  -- The right-hand side lives in the homology of `N`, read as `SSet.homology`.
  erw [smul_smul]
  congr 1
  have h₂ : s₂ * s₂ = 1 := by rcases hs₂ with rfl | rfl <;> rfl
  linear_combination (-(s₁ * degreeAtRegularValue o o' f y)) * h₂


/-- **The smooth degree is the homological degree, for any models.** Let `f : M → N` be a `C¹`
map between compact connected boundaryless manifolds of dimension `k + 1`, modelled on any
finite-dimensional real normed spaces, with orientations `o` and `o'`, and let `y` be a regular
value of `f`. Then `f` sends any integral fundamental class `μ` of `M` to `±` the signed count of
preimages `degreeAtRegularValue o o' f y` times any integral fundamental class `ν` of `N`. Here the
fundamental classes are those of `TauCeti.IsFundamentalClass`, which need no orientation datum;
for manifolds charted in one inner product space, with the fundamental classes of `o` and `o'`, the
sign is `1` (`TauCeti.Manifold.Orientation.mapFundamentalClass_eq_degreeAtRegularValue_smul`). -/
theorem exists_singularHomologyMap_eq_degreeAtRegularValue_smul {k : ℕ}
    (hW : finrank ℝ W = k + 1) (hW' : finrank ℝ W' = k + 1)
    (o : Manifold.Orientation I M (Fin (k + 1))) (o' : Manifold.Orientation J N (Fin (k + 1)))
    {f : C(M, N)} (hf : ContMDiff I J 1 f) {y : N} (hy : IsRegularValue I J f y)
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) (k + 1) :
      ModuleCat.{0} ℤ)} (hμ : IsFundamentalClass μ)
    {ν : ((TopCat.toSSet.obj (TopCat.of N)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) (k + 1) :
      ModuleCat.{0} ℤ)} (hν : IsFundamentalClass ν) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) (k + 1)).obj
          (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom f)).hom μ =
        (s * degreeAtRegularValue o o' f y) • ν := by
  -- Copies `M'` and `N'` of `M` and `N` charted in `V = ℝᵏ⁺¹`, with the identities `ιM`, `ιN`.
  let V := EuclideanSpace ℝ (Fin (k + 1))
  have hV : finrank ℝ V = k + 1 := finrank_euclideanSpace_fin
  let IM := I.transContinuousLinearEquiv (ContinuousLinearEquiv.ofFinrankEq (hW.trans hV.symm))
  let IN := J.transContinuousLinearEquiv (ContinuousLinearEquiv.ofFinrankEq (hW'.trans hV.symm))
  let ιM : BoundarylessModel IM M ≃ₘ^1⟮𝓘(ℝ, V), I⟯ M :=
    ((ContinuousLinearEquiv.toTransContinuousLinearEquiv I M _).trans
      (BoundarylessModel.diffeomorph IM 1)).symm
  let ιN : BoundarylessModel IN N ≃ₘ^1⟮𝓘(ℝ, V), J⟯ N :=
    ((ContinuousLinearEquiv.toTransContinuousLinearEquiv J N _).trans
      (BoundarylessModel.diffeomorph IN 1)).symm
  exact exists_singularHomologyMap_eq_degreeAtRegularValue_smul_of_diffeomorph hV ιM ιN o o' hf
    hy hμ hν

end AnyModel

end Manifold.Orientation

end TauCeti
