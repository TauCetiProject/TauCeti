/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LocalIndex
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.Geometry.Manifold.Degree.Basic
public import TauCeti.Geometry.Manifold.IsManifold.Prod
public import TauCeti.Geometry.Manifold.RegularValue.Fibre
import TauCeti.Geometry.Manifold.MFDeriv.LocalInjectivity

/-!
# The smooth degree is the homological degree

Let `M` and `N` be boundaryless `C¹` manifolds modelled on real normed spaces `E` and `F` of the
same dimension `n + 1`, with orientations `o` of `M` and `o'` of `N`
(`TauCeti.Manifold.Orientation`). Through their local homology generators
(`TauCeti.Manifold.Orientation.toHomologicalOrientation`) these are homological orientations,
for which a continuous map `f : M → N` has a local index at every point
(`TauCeti.HomologicalOrientation.localIndex`) and, when it is proper and `N` is preconnected, a
degree (`TauCeti.HomologicalOrientation.degree`) characterized by `f_*[M] = deg f • [N]` for
compact `M` and `N`.

At a point `x` where the manifold derivative of `f` is invertible, the local index of `f` is the
orientation sign of `f` at `x` (`TauCeti.Manifold.Orientation.localIndex_toHomologicalOrientation`):
`1` where `f` preserves the orientations and `-1` where it reverses them. Reading the preferred
charts at `x` and `f x` in the Euclidean model `ℝⁿ⁺¹` along linear equivalences matching the
tangent orientations, the derivative of `f` acts on the local homology of the model by the sign of
its Jacobian (`OpenPartialHomeomorph.localHomologyMap_restrict_localOrientationOfOrientedChart`).
Only differentiability at `x` is used; it already makes `x` isolated in its fibre
(`TauCeti.eventually_ne_of_mfderiv_injective`).

The fibre of a proper map over a regular value `y` is compact and, by this isolation, discrete,
hence finite (`TauCeti.IsRegularValue.finite_preimage_of_isProperMap`). Summing over it, the
homological degree of a proper map onto a preconnected manifold is the signed count of preimages
`degreeAtRegularValue o o' f y` (`TauCeti.Manifold.Orientation.degree_toHomologicalOrientation`).
For a map between compact manifolds, with `N` preconnected, this reads
`f_*[M] = (degreeAtRegularValue o o' f y) • [N]` in `Hₙ₊₁(N; ℤ)`
(`TauCeti.Manifold.Orientation.mapFundamentalClass_eq_degreeAtRegularValue_smul`), so a degree
computed by counting preimages with signs computes the image of the fundamental class. For a map out
of a product `M₁ × M₂` carrying an orientation for the product model `𝓘(ℝ, E₁).prod 𝓘(ℝ, E₂)`,
`TauCeti.Manifold.Orientation.mapFundamentalClass_prod_eq_degreeAtRegularValue_smul` records the
same identity with respect to `TauCeti.chartedSpaceProd`.

## Main results

* `TauCeti.Manifold.Orientation.localIndex_toHomologicalOrientation`: at a point of invertible
  derivative the local index is the orientation sign.
* `TauCeti.Manifold.Orientation.degree_toHomologicalOrientation`: the degree of a proper map onto
  a preconnected manifold is the signed count of preimages of any regular value.
* `TauCeti.Manifold.Orientation.mapFundamentalClass_eq_degreeAtRegularValue_smul`: for a map
  between compact manifolds, with preconnected target, `f_*[M]` is the signed count of preimages
  of a regular value times `[N]`.
* `TauCeti.Manifold.Orientation.toHomologicalOrientationProd` and
  `TauCeti.Manifold.Orientation.mapFundamentalClass_prod_eq_degreeAtRegularValue_smul`:
  the homological orientation and fundamental-class pushforward for a product manifold
  `M₁ × M₂` oriented over `𝓘(ℝ, E₁).prod 𝓘(ℝ, E₂)`.

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

/-- `o.orientationAt x`, typed in the model space `E` (`TangentSpace 𝓘(ℝ, E) x = E`
definitionally) so `rw` matches `_root_.Orientation.map` at `implicit` transparency. -/
private def modelOrientationAt {X G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace X] [ChartedSpace G X] [IsManifold 𝓘(ℝ, G) 1 X]
    {k : ℕ} (ω : Manifold.Orientation 𝓘(ℝ, G) X (Fin (k + 1))) (p : X) :
    _root_.Orientation ℝ G (Fin (k + 1)) :=
  ω.orientationAt p

private theorem modelOrientationAt_neg {X G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace X] [ChartedSpace G X] [IsManifold 𝓘(ℝ, G) 1 X]
    {k : ℕ} (ω : Manifold.Orientation 𝓘(ℝ, G) X (Fin (k + 1))) (p : X) :
    modelOrientationAt (-ω) p = -modelOrientationAt ω p :=
  orientationAt_neg ω p

section General

variable {M N E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]
  {n : ℕ} (hE : finrank ℝ E = n + 1) (hF : finrank ℝ F = n + 1)

variable [T2Space M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space N] [IsManifold 𝓘(ℝ, F) 1 N]
  (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1)))
  (o' : Manifold.Orientation 𝓘(ℝ, F) N (Fin (n + 1)))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [T2Space M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space N] [IsManifold 𝓘(ℝ, F) 1 N] in
/-- Reading `f` in the preferred charts at `x` and `f x` postcomposed with continuous linear
equivalences `L_E` and `L_F` conjugates the chart derivative `f' : E →L[ℝ] F`. -/
private theorem hasFDerivAt_transHomeomorph_chartAt {G₁ G₂ : Type}
    [NormedAddCommGroup G₁] [NormedSpace ℝ G₁] [NormedAddCommGroup G₂] [NormedSpace ℝ G₂]
    {f : C(M, N)} {x : M} {f' : E →L[ℝ] F}
    (hfd : HasFDerivAt (chartAt F (f x) ∘ f ∘ (chartAt E x).symm) f' (chartAt E x x))
    (L_E : E ≃L[ℝ] G₁) (L_F : F ≃L[ℝ] G₂) :
    HasFDerivAt
      (((chartAt F (f x)).transHomeomorph L_F.toHomeomorph) ∘ f ∘
        ((chartAt E x).transHomeomorph L_E.toHomeomorph).symm)
      (L_F.toContinuousLinearMap ∘L f' ∘L L_E.symm.toContinuousLinearMap)
      (((chartAt E x).transHomeomorph L_E.toHomeomorph) x) := by
  have hLsymm : ⇑L_E.toHomeomorph.symm = ⇑L_E.symm := rfl
  have hcomp : ((chartAt F (f x)).transHomeomorph L_F.toHomeomorph) ∘ f ∘
        ((chartAt E x).transHomeomorph L_E.toHomeomorph).symm =
      L_F ∘ (chartAt F (f x) ∘ f ∘ (chartAt E x).symm) ∘ L_E.symm := by
    ext z
    simp [hLsymm]
  rw [hcomp]
  have h₁ : HasFDerivAt ((chartAt F (f x) ∘ f ∘ (chartAt E x).symm) ∘ L_E.symm)
      (f' ∘L L_E.symm.toContinuousLinearMap)
      (((chartAt E x).transHomeomorph L_E.toHomeomorph) x) := by
    refine HasFDerivAt.comp _ ?_ L_E.symm.hasFDerivAt
    simpa using hfd
  simpa [ContinuousLinearMap.comp_assoc] using L_F.hasFDerivAt.comp _ h₁

omit [T2Space M] [T2Space N] in
/-- When `L_E` and `L_F` transport the tangent orientations at `x` and `f x` to the same
orientation of `ℝⁿ⁺¹`, the Jacobian sign of `L_F ∘ e ∘ L_E.symm` equals `orientationSign o o' f x`.
-/
private theorem coe_sign_det_conj_eq_orientationSign (f : C(M, N)) {x : M}
    (e : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] TangentSpace 𝓘(ℝ, F) (f x))
    (he : (e : TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, F) (f x)) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)
    (L_E : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (L_F : F ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (ho : (modelOrientationAt o' (f x)).map (Fin (n + 1)) L_F.toLinearEquiv =
      (modelOrientationAt o x).map (Fin (n + 1)) L_E.toLinearEquiv) :
    let e' : E ≃L[ℝ] F := e
    let g : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
      L_E.symm.trans (e'.trans L_F)
    (SignType.sign (g : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
        EuclideanSpace ℝ (Fin (n + 1))).det : ℤ) =
      orientationSign o o' f x := by
  intro e' g
  have hcard : Fintype.card (Fin (n + 1)) = finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    simp
  set ω₀ := (modelOrientationAt o x).map (Fin (n + 1)) L_E.toLinearEquiv with hω₀
  have hωg : ω₀.map (Fin (n + 1)) g.toLinearEquiv =
      ((modelOrientationAt o x).map (Fin (n + 1)) e'.toLinearEquiv).map (Fin (n + 1))
        L_F.toLinearEquiv := by
    have hL : L_E.toLinearEquiv.trans g.toLinearEquiv =
        e'.toLinearEquiv.trans L_F.toLinearEquiv := by
      ext z
      simp [g]
    rw [hω₀, ← _root_.Orientation.map_trans, ← _root_.Orientation.map_trans, hL]
  have hdet : (g : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1))).det ≠ 0 :=
    (LinearEquiv.isUnit_det' g.toLinearEquiv).ne_zero
  rcases hdet.lt_or_gt with h | h
  · have hmap₀ : _root_.Orientation.map (Fin (n + 1)) g.toLinearEquiv ω₀ = -ω₀ :=
      (_root_.Orientation.map_eq_neg_iff_det_neg _ _ hcard).2 h
    have hmap : _root_.Orientation.map (Fin (n + 1)) e'.toLinearEquiv (modelOrientationAt o x) =
        -modelOrientationAt o' (f x) :=
      (_root_.Orientation.map (Fin (n + 1)) L_F.toLinearEquiv).injective
        (by rw [← hωg, hmap₀, ← ho, _root_.Orientation.map_neg])
    rw [sign_neg h, SignType.coe_neg_one, orientationSign_of_isOrientationReversingAt
      ((isOrientationReversingAt_iff o o' f x).2 ⟨e, he, hmap⟩)]
  · have hmap₀ : _root_.Orientation.map (Fin (n + 1)) g.toLinearEquiv ω₀ = ω₀ :=
      (_root_.Orientation.map_eq_iff_det_pos _ _ hcard).2 h
    have hmap : _root_.Orientation.map (Fin (n + 1)) e'.toLinearEquiv (modelOrientationAt o x) =
        modelOrientationAt o' (f x) :=
      (_root_.Orientation.map (Fin (n + 1)) L_F.toLinearEquiv).injective
        (by rw [← hωg, hmap₀, ← ho])
    rw [sign_pos h, SignType.coe_one, orientationSign_of_isOrientationPreservingAt
      ((isOrientationPreservingAt_iff o o' f x).2 ⟨e, he, hmap⟩)]

/-- The local index at a point of invertible derivative, when linear equivalences `L_E` and `L_F`
to `ℝⁿ⁺¹` match the tangent orientations at `x` and `f x`: both sides are the sign of the Jacobian
in the induced Euclidean charts. -/
private theorem localIndex_toHomologicalOrientation_of_map_orientationAt_eq (f : C(M, N)) {x : M}
    (hf : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).IsInvertible)
    (L_E : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (L_F : F ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (ho : (modelOrientationAt o' (f x)).map (Fin (n + 1)) L_F.toLinearEquiv =
      (modelOrientationAt o x).map (Fin (n + 1)) L_E.toLinearEquiv) :
    (o.toHomologicalOrientation hE).localIndex (o'.toHomologicalOrientation hF) f x =
      orientationSign o o' f x := by
  set M₀ := EuclideanSpace ℝ (Fin (n + 1))
  have hM₀ : finrank ℝ M₀ = n + 1 := finrank_euclideanSpace_fin
  set f' : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x
  set ω₀ : _root_.Orientation ℝ M₀ (Fin (n + 1)) :=
    (modelOrientationAt o x).map (Fin (n + 1)) L_E.toLinearEquiv with hω₀
  set φ' := (chartAt E x).transHomeomorph L_E.toHomeomorph
  set χ' := (chartAt F (f x)).transHomeomorph L_F.toHomeomorph
  have hfd : HasFDerivAt (chartAt F (f x) ∘ f ∘ (chartAt E x).symm) f' (chartAt E x x) := by
    have h := (mdifferentiableAt_of_isInvertible_mfderiv hf).hasMFDerivAt.2
    simp only [writtenInExtChartAt, hasFDerivWithinAt_univ, ModelWithCorners.range_eq_univ] at h
    exact h
  have hgfd := hasFDerivAt_transHomeomorph_chartAt hfd L_E L_F
  -- An open neighbourhood `U` of `x`, in the domains of the preferred charts at `x` and `f x`,
  -- meets the fibre only in `x`.
  obtain ⟨t, htne, hto, hxt⟩ := eventually_nhds_iff.1
    (eventually_nhdsWithin_iff.1 (eventually_ne_of_mfderiv_injective hf.injective))
  set U : Set M := ((chartAt E x).source ∩ t) ∩ f ⁻¹' (chartAt F (f x)).source
  have hUo : IsOpen U := ((chartAt E x).open_source.inter hto).inter
    ((chartAt F (f x)).open_source.preimage f.continuous)
  have hxU : x ∈ U := ⟨⟨mem_chart_source E x, hxt⟩, mem_chart_source F (f x)⟩
  have hU (z : M) (hz : z ∈ U) (hfz : f z = f x) : z = x := by
    by_contra hzx
    exact htne z hz.1.2 hzx hfz
  obtain ⟨e, he⟩ := hf
  let e' : E ≃L[ℝ] F := e
  let g : M₀ ≃L[ℝ] M₀ := L_E.symm.trans (e'.trans L_F)
  have hg : (g : M₀ →L[ℝ] M₀) =
      L_F.toContinuousLinearMap ∘L f' ∘L L_E.symm.toContinuousLinearMap := by
    have he' : (e' : E →L[ℝ] F) = f' := he
    ext z : 1
    simp [g, ← he']
  have hdet : (L_F.toContinuousLinearMap ∘L f' ∘L L_E.symm.toContinuousLinearMap).det ≠ 0 := by
    rw [← hg]
    exact (LinearEquiv.isUnit_det' g.toLinearEquiv).ne_zero
  have hxφ' : x ∈ φ'.source :=
    (chartAt E x).mem_transHomeomorph_source L_E.toHomeomorph (mem_chart_source E x)
  have hfxχ' : f x ∈ χ'.source :=
    (chartAt F (f x)).mem_transHomeomorph_source L_F.toHomeomorph (mem_chart_source F (f x))
  have key := φ'.localHomologyMap_restrict_localOrientationOfOrientedChart ω₀ hM₀ χ' f
    hxφ' hfxχ' hUo hxU hU hgfd hdet
  dsimp only [φ', χ', ω₀] at key
  rw [← localOrientationOfManifoldOrientation_eq_transHomeomorph o hE x
      (ω := modelOrientationAt o x) rfl L_E hM₀ hxφ', ← hω₀, ← ho,
    ← localOrientationOfManifoldOrientation_eq_transHomeomorph o' hF (f x)
      (ω := modelOrientationAt o' (f x)) rfl L_F hM₀ hfxχ',
    ← toHomologicalOrientation_apply, ← toHomologicalOrientation_apply] at key
  rw [(HomologicalOrientation.localIndex_eq_iff _ _ hF f rfl hUo hxU hU).2 key, ← hg]
  exact coe_sign_det_conj_eq_orientationSign o o' f e he L_E L_F ho

/-- **The local index at a point of invertible derivative is the orientation sign.** For a
continuous map `f : M → N` whose manifold derivative at `x` is invertible, the local index of `f`
at `x` with respect to the homological orientations of `o` and `o'` is `1` if `f` preserves the
orientations at `x` and `-1` if it reverses them. -/
theorem localIndex_toHomologicalOrientation (f : C(M, N)) {x : M}
    (hf : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).IsInvertible) :
    (o.toHomologicalOrientation hE).localIndex (o'.toHomologicalOrientation hF) f x =
      orientationSign o o' f x := by
  have hM₀ : finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 := finrank_euclideanSpace_fin
  let L_E : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    ContinuousLinearEquiv.ofFinrankEq (hE.trans hM₀.symm)
  let L_F : F ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    ContinuousLinearEquiv.ofFinrankEq (hF.trans hM₀.symm)
  -- Reversing `o'` if necessary, the transported tangent orientations at `x` and `f x` agree.
  rcases _root_.Orientation.eq_or_eq_neg
      ((modelOrientationAt o' (f x)).map (Fin (n + 1)) L_F.toLinearEquiv)
      ((modelOrientationAt o x).map (Fin (n + 1)) L_E.toLinearEquiv) (by simp [hM₀]) with ho | ho
  · exact localIndex_toHomologicalOrientation_of_map_orientationAt_eq hE hF o o' f hf L_E L_F ho
  · have h := localIndex_toHomologicalOrientation_of_map_orientationAt_eq hE hF o (-o') f hf L_E L_F
      (by
        rw [modelOrientationAt_neg, _root_.Orientation.map_neg, ho]
        exact neg_neg (G := _root_.Orientation ℝ (EuclideanSpace ℝ (Fin (n + 1))) (Fin (n + 1))) _)
    rwa [toHomologicalOrientation_neg, HomologicalOrientation.localIndex_neg_right,
      orientationSign_neg_right, neg_inj] at h

/-- **The homological degree is the signed count of preimages.** For a proper map `f : M → N`
onto a preconnected manifold and a regular value `y` of `f`, the degree of `f` with respect to the
homological orientations of `o` and `o'` is `degreeAtRegularValue o o' f y`. -/
theorem degree_toHomologicalOrientation [PreconnectedSpace N] {f : C(M, N)} (hf : IsProperMap f)
    {y : N} (hy : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, F) f y) :
    (o.toHomologicalOrientation hE).degree (o'.toHomologicalOrientation hF) hE f =
      degreeAtRegularValue o o' f y := by
  have hdim : finrank ℝ E = finrank ℝ F := hE.trans hF.symm
  have hfin := hy.finite_preimage_of_isProperMap hdim hf
  rw [HomologicalOrientation.degree_eq_sum_localIndex _ _ hE hF hf hfin,
    degreeAtRegularValue_eq_sum_of_finite hfin]
  exact Finset.sum_congr rfl fun x hx ↦ localIndex_toHomologicalOrientation hE hF o o' f
    ((isRegularPoint_iff_isInvertible_mfderiv hdim).1
      (hy.isRegularPoint (hfin.mem_toFinset.1 hx)))

/-- **The signed count of preimages computes the image of the fundamental class.** For a continuous
map `f : M → N` between compact manifolds, with `N` preconnected, and a regular value `y` of `f`,
`f_*[M] = (degreeAtRegularValue o o' f y) • [N]` in `Hₙ₊₁(N; ℤ)`, for the fundamental classes of
the homological orientations of `o` and `o'`. -/
theorem mapFundamentalClass_eq_degreeAtRegularValue_smul [CompactSpace M] [CompactSpace N]
    [PreconnectedSpace N] {f : C(M, N)} {y : N} (hy : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, F) f y) :
    (o.toHomologicalOrientation hE).mapFundamentalClass hE f =
      degreeAtRegularValue o o' f y • (o'.toHomologicalOrientation hF).fundamentalClass hF := by
  rw [HomologicalOrientation.mapFundamentalClass_eq_degree_smul _ _ hE hF,
    degree_toHomologicalOrientation hE hF o o' f.continuous.isProperMap hy]

end General

section Prod

attribute [local instance low] chartedSpaceProd

variable {M₁ M₂ E₁ E₂ : Type}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [TopologicalSpace M₁] [T2Space M₁] [ChartedSpace E₁ M₁] [IsManifold 𝓘(ℝ, E₁) 1 M₁]
  [TopologicalSpace M₂] [T2Space M₂] [ChartedSpace E₂ M₂] [IsManifold 𝓘(ℝ, E₂) 1 M₂]

/-- The homological orientation of a product manifold `M₁ × M₂` (charted by
`TauCeti.chartedSpaceProd`) induced by a smooth orientation for the product model
`𝓘(ℝ, E₁).prod 𝓘(ℝ, E₂)`. -/
def toHomologicalOrientationProd {n : ℕ} (hE : finrank ℝ (E₁ × E₂) = n + 1)
    (o : Manifold.Orientation (𝓘(ℝ, E₁).prod 𝓘(ℝ, E₂)) (M₁ × M₂) (Fin (n + 1))) :
    @HomologicalOrientation (M₁ × M₂) (E₁ × E₂) _ _ _ _ _ (chartedSpaceProd E₁ E₂ M₁ M₂) (n + 1) :=
  haveI : IsManifold 𝓘(ℝ, E₁ × E₂) 1 (M₁ × M₂) := isManifold_chartedSpaceProd
  ((modelWithCornersSelf_prod (𝕜 := ℝ) (E := E₁) (F := E₂)).symm ▸ o).toHomologicalOrientation hE

omit [T2Space M₁] [T2Space M₂] in
private theorem degreeAtRegularValue_congr_prod_model {N F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) 1 N] {n : ℕ}
    {I : ModelWithCorners ℝ (E₁ × E₂) (E₁ × E₂)} (hI : I = 𝓘(ℝ, E₁ × E₂))
    (hm : IsManifold I 1 (M₁ × M₂))
    (o : haveI := hm; Manifold.Orientation I (M₁ × M₂) (Fin (n + 1)))
    (o' : Manifold.Orientation 𝓘(ℝ, F) N (Fin (n + 1))) (f : M₁ × M₂ → N) (y : N) :
    haveI : IsManifold 𝓘(ℝ, E₁ × E₂) 1 (M₁ × M₂) := isManifold_chartedSpaceProd
    degreeAtRegularValue (hI ▸ o) o' f y =
      (haveI := hm; degreeAtRegularValue o o' f y) := by
  subst hI
  rfl

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂]
  [T2Space M₁] [IsManifold 𝓘(ℝ, E₁) 1 M₁] [T2Space M₂] [IsManifold 𝓘(ℝ, E₂) 1 M₂] in
private theorem isRegularValue_congr_prod_model {N F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace N] [ChartedSpace F N]
    {I : ModelWithCorners ℝ (E₁ × E₂) (E₁ × E₂)}
    (hI : I = 𝓘(ℝ, E₁ × E₂)) {f : M₁ × M₂ → N} {y : N}
    (hy : IsRegularValue I 𝓘(ℝ, F) f y) :
    IsRegularValue 𝓘(ℝ, E₁ × E₂) 𝓘(ℝ, F) f y := by
  subst hI
  exact hy

/-- For a continuous map `f : M₁ × M₂ → N` from a compact oriented product manifold to a compact
preconnected oriented manifold `N`, the image of the fundamental class of `M₁ × M₂` is the signed
count of preimages of any regular value times `[N]`. -/
theorem mapFundamentalClass_prod_eq_degreeAtRegularValue_smul
    {N F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace N] [T2Space N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) 1 N]
    [CompactSpace M₁] [CompactSpace M₂] [CompactSpace N] [PreconnectedSpace N]
    {n : ℕ} (hE : finrank ℝ (E₁ × E₂) = n + 1) (hF : finrank ℝ F = n + 1)
    (o : Manifold.Orientation (𝓘(ℝ, E₁).prod 𝓘(ℝ, E₂)) (M₁ × M₂) (Fin (n + 1)))
    (o' : Manifold.Orientation 𝓘(ℝ, F) N (Fin (n + 1)))
    {f : C(M₁ × M₂, N)} {y : N} (hy : IsRegularValue (𝓘(ℝ, E₁).prod 𝓘(ℝ, E₂)) 𝓘(ℝ, F) f y) :
    (o.toHomologicalOrientationProd hE).mapFundamentalClass hE f =
      degreeAtRegularValue o o' f y • (o'.toHomologicalOrientation hF).fundamentalClass hF := by
  have : IsManifold 𝓘(ℝ, E₁ × E₂) 1 (M₁ × M₂) := isManifold_chartedSpaceProd
  have hI : 𝓘(ℝ, E₁).prod 𝓘(ℝ, E₂) = 𝓘(ℝ, E₁ × E₂) :=
    (modelWithCornersSelf_prod (𝕜 := ℝ) (E := E₁) (F := E₂)).symm
  rw [toHomologicalOrientationProd,
    mapFundamentalClass_eq_degreeAtRegularValue_smul hE hF (hI ▸ o) o'
      (isRegularValue_congr_prod_model hI hy)]
  congr 1
  exact degreeAtRegularValue_congr_prod_model hI
    (inferInstance : IsManifold (𝓘(ℝ, E₁).prod 𝓘(ℝ, E₂)) 1 (M₁ × M₂)) o o' f y

end Prod

end Manifold.Orientation

end TauCeti
