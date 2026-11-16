/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LocalIndex
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.Geometry.Manifold.Degree.Basic
public import TauCeti.Geometry.Manifold.Orientation.FundamentalClass
public import TauCeti.Geometry.Manifold.RegularValue.Fibre
import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Geometry.Manifold.Degree.Diffeomorph
import TauCeti.Geometry.Manifold.MFDeriv.LocalInjectivity
import TauCeti.Geometry.Manifold.RegularValue.Diffeomorph

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
(`Manifold.Orientation.mapFundamentalClass_toHomologicalOrientation_eq_degreeAtRegularValue_smul`),
so a degree computed by counting preimages with signs computes the image of the fundamental class.

Using the general smooth fundamental class `TauCeti.Manifold.Orientation.fundamentalClass` and its
naturality under orientation-preserving homeomorphisms, the same formula extends to any pair of
compact boundaryless `C¹` manifolds `(M, I)` and `(N, J)` (`[BoundarylessManifold I M]`,
`[BoundarylessManifold J N]`): whenever `N` is preconnected and `y` is a regular value of a
continuous map `f : C(M, N)`, we have `f_*[M] = (degreeAtRegularValue o o' f y) • [N]`
(`TauCeti.Manifold.Orientation.mapFundamentalClass_eq_degreeAtRegularValue_smul`).

## Main results

* `TauCeti.Manifold.Orientation.localIndex_toHomologicalOrientation`: at a point of invertible
  derivative the local index is the orientation sign.
* `TauCeti.Manifold.Orientation.degree_toHomologicalOrientation`: the degree of a proper map onto
  a preconnected manifold is the signed count of preimages of any regular value.
* `Manifold.Orientation.mapFundamentalClass_toHomologicalOrientation_eq_degreeAtRegularValue_smul`:
  for a map between compact manifolds on the same inner product model, with preconnected target,
  `f_*[M]` is the signed count of preimages of a regular value times `[N]`.
* `TauCeti.Manifold.Orientation.mapFundamentalClass_eq_degreeAtRegularValue_smul`: for a continuous
  map `f : C(M, N)` between compact boundaryless `C¹` manifolds `(M, I)` and `(N, J)` with `N`
  preconnected and `y` a regular value of `f`,
  `f_*[M] = (degreeAtRegularValue o o' f y) • [N]`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Proposition 2.30 and Section 3.3 (fundamental classes and the degree as a sum of
  local degrees).
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5 (the degree as a signed count of preimages).
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Filter Module Set Topology
open scoped EuclideanSpace Manifold

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
theorem mapFundamentalClass_toHomologicalOrientation_eq_degreeAtRegularValue_smul
    [CompactSpace M] [CompactSpace N] [PreconnectedSpace N]
    {f : C(M, N)} {y : N} (hy : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, E) f y) :
    (o.toHomologicalOrientation hE).mapFundamentalClass hE f =
      degreeAtRegularValue o o' f y • (o'.toHomologicalOrientation hE).fundamentalClass hE := by
  rw [HomologicalOrientation.mapFundamentalClass_eq_degree_smul _ _ hE hE,
    degree_toHomologicalOrientation hE o o' f.continuous.isProperMap hy]

open scoped ContDiff

section Boundaryless

/-- Transferring `f_*[M] = deg(f, y) • [N]` along `C¹` diffeomorphisms `Φ : M ≃ₘ^1 M₁` and
`Ψ : N ≃ₘ^1 N₁` when `Φ.symm` and `Ψ` preserve orientations. -/
private theorem mapFundamentalClass_eq_degreeAtRegularValue_smul_of_diffeomorph
    {E F E₁ F₁ H H' H₁ H₁' : Type*} {M N M₁ N₁ : Type} {n : ℕ}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
    [TopologicalSpace H₁'] {J₁ : ModelWithCorners ℝ F₁ H₁'}
    [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I 1 M]
    [BoundarylessManifold I M] [CompactSpace M]
    [TopologicalSpace N] [T2Space N] [ChartedSpace H' N] [IsManifold J 1 N]
    [BoundarylessManifold J N] [CompactSpace N]
    [TopologicalSpace M₁] [T2Space M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ 1 M₁]
    [BoundarylessManifold I₁ M₁] [CompactSpace M₁]
    [TopologicalSpace N₁] [T2Space N₁] [ChartedSpace H₁' N₁] [IsManifold J₁ 1 N₁]
    [BoundarylessManifold J₁ N₁] [CompactSpace N₁]
    (o : Manifold.Orientation I M (Fin (n + 1))) (o' : Manifold.Orientation J N (Fin (n + 1)))
    (o₁ : Manifold.Orientation I₁ M₁ (Fin (n + 1))) (o₁' : Manifold.Orientation J₁ N₁ (Fin (n + 1)))
    (Φ : M ≃ₘ^1⟮I, I₁⟯ M₁) (Ψ : N ≃ₘ^1⟮J, J₁⟯ N₁)
    (hΦs : ∀ z, IsOrientationPreservingAt o₁ o Φ.symm z)
    (hΨ : ∀ y, IsOrientationPreservingAt o' o₁' Ψ y)
    {f : C(M, N)} {y : N} (hy : IsRegularValue I J f y)
    (hbase :
      let g : C(M₁, N₁) :=
        (Ψ.toHomeomorph : C(N, N₁)).comp (f.comp (Φ.symm.toHomeomorph : C(M₁, M)))
      IsRegularValue I₁ J₁ g (Ψ y) →
        o₁.mapFundamentalClass g = degreeAtRegularValue o₁ o₁' g (Ψ y) • o₁'.fundamentalClass) :
    o.mapFundamentalClass f = degreeAtRegularValue o o' f y • o'.fundamentalClass := by
  let g : C(M₁, N₁) :=
    (Ψ.toHomeomorph : C(N, N₁)).comp (f.comp (Φ.symm.toHomeomorph : C(M₁, M)))
  have hg_coe : ⇑g = ⇑Ψ ∘ (⇑f ∘ ⇑Φ.symm) := by
    ext z
    simp only [g, ContinuousMap.comp_apply, ContinuousMap.coe_ofClass, Diffeomorph.coe_toHomeomorph,
      Function.comp_apply]
  have hyg : IsRegularValue I₁ J₁ g (Ψ y) := by
    rw [hg_coe, Ψ.isRegularValue_diffeomorph_comp_apply_iff one_ne_zero]
    exact (Φ.symm.isRegularValue_comp_diffeomorph_iff one_ne_zero f y).2 hy
  have hdeg : degreeAtRegularValue o₁ o₁' g (Ψ y) = degreeAtRegularValue o o' f y := by
    rw [hg_coe,
      Ψ.degreeAtRegularValue_diffeomorph_comp_apply_of_isOrientationPreservingAt one_ne_zero
        (f ∘ Φ.symm) (hΨ y),
      Φ.symm.degreeAtRegularValue_comp_diffeomorph_of_isOrientationPreservingAt one_ne_zero f
        fun z _ ↦ hΦs z]
  have hfg : f.comp (Φ.symm.toHomeomorph : C(M₁, M)) =
      (Ψ.symm.toHomeomorph : C(N₁, N)).comp g := by
    ext z
    simp only [g, ContinuousMap.comp_apply, ContinuousMap.coe_ofClass, Diffeomorph.coe_toHomeomorph,
      Ψ.symm_apply_apply]
  have hΦc : o₁.mapFundamentalClass (Φ.symm.toHomeomorph : C(M₁, M)) = o.fundamentalClass :=
    mapFundamentalClass_homeomorph o₁ o Φ.symm.toHomeomorph fun z ↦ by
      rw [Diffeomorph.coe_toHomeomorph]
      exact hΦs z
  have hΨs : ∀ w, IsOrientationPreservingAt o₁' o' Ψ.symm w :=
    fun w ↦ (hΨ (Ψ.symm w)).diffeomorph_symm one_ne_zero
  have hΨc : o₁'.mapFundamentalClass (Ψ.symm.toHomeomorph : C(N₁, N)) = o'.fundamentalClass :=
    mapFundamentalClass_homeomorph o₁' o' Ψ.symm.toHomeomorph fun w ↦ by
      rw [Diffeomorph.coe_toHomeomorph]
      exact hΨs w
  rw [o.mapFundamentalClass_def, ← hΦc, ← o₁.mapFundamentalClass_comp, hfg,
    o₁.mapFundamentalClass_comp, hbase hyg, hdeg, map_zsmul, ← o₁'.mapFundamentalClass_def, hΨc]

/-- Self-modelled case of `mapFundamentalClass_eq_degreeAtRegularValue_smul`, reduced to
`𝓡 (n + 1)` via `BoundarylessModel.diffeomorphTransContinuousLinearEquiv`. -/
private theorem mapFundamentalClass_eq_degreeAtRegularValue_smul_self
    {E F : Type*} {M N : Type} {n : ℕ}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [CompactSpace M]
    [TopologicalSpace N] [T2Space N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) 1 N] [CompactSpace N]
    [PreconnectedSpace N]
    (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1)))
    (o' : Manifold.Orientation 𝓘(ℝ, F) N (Fin (n + 1)))
    {f : C(M, N)} {y : N} (hy : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, F) f y) :
    o.mapFundamentalClass f = degreeAtRegularValue o o' f y • o'.fundamentalClass := by
  let Φ := BoundarylessModel.diffeomorphTransContinuousLinearEquiv 𝓘(ℝ, E) (M := M)
    o.modelEquivEuclidean 1
  let Ψ := BoundarylessModel.diffeomorphTransContinuousLinearEquiv 𝓘(ℝ, F) (M := N)
    o'.modelEquivEuclidean 1
  refine mapFundamentalClass_eq_degreeAtRegularValue_smul_of_diffeomorph o o'
    (o.boundarylessTransContinuousLinearEquiv o.modelEquivEuclidean)
    (o'.boundarylessTransContinuousLinearEquiv o'.modelEquivEuclidean) Φ Ψ
    (o.isOrientationPreservingAt_diffeomorphTransContinuousLinearEquiv_symm o.modelEquivEuclidean 1)
    (o'.isOrientationPreservingAt_diffeomorphTransContinuousLinearEquiv o'.modelEquivEuclidean 1)
    hy fun hyg ↦ ?_
  rw [mapFundamentalClass_euclideanSpace, fundamentalClass_euclideanSpace]
  exact mapFundamentalClass_toHomologicalOrientation_eq_degreeAtRegularValue_smul
    finrank_euclideanSpace_fin _ _ hyg

variable {E F H H' : Type*} {M N : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I 1 M] [BoundarylessManifold I M]
  [CompactSpace M]
  [TopologicalSpace N] [T2Space N] [ChartedSpace H' N] [IsManifold J 1 N] [BoundarylessManifold J N]
  [CompactSpace N]
  {n : ℕ}

/-- **The signed count of preimages computes the image of the fundamental class for arbitrary
boundaryless manifolds.** Let `(M, I)` and `(N, J)` be compact boundaryless `C¹` manifolds of
dimension `n + 1` (`[BoundarylessManifold I M]`, `[BoundarylessManifold J N]`) with `N`
preconnected, oriented by `o` and `o'`. For any continuous map `f : C(M, N)` and any regular value
`y` of `f`, `f_*[M] = (degreeAtRegularValue o o' f y) • [N]` in `Hₙ₊₁(N; ℤ)`. -/
theorem mapFundamentalClass_eq_degreeAtRegularValue_smul [PreconnectedSpace N]
    (o : Manifold.Orientation I M (Fin (n + 1)))
    (o' : Manifold.Orientation J N (Fin (n + 1)))
    {f : C(M, N)} {y : N} (hy : IsRegularValue I J f y) :
    o.mapFundamentalClass f = degreeAtRegularValue o o' f y • o'.fundamentalClass := by
  let : ChartedSpace E (BoundarylessModel I M) := BoundarylessModel.interiorChartedSpace I
  let : ChartedSpace F (BoundarylessModel J N) := BoundarylessModel.interiorChartedSpace J
  exact mapFundamentalClass_eq_degreeAtRegularValue_smul_of_diffeomorph o o'
    o.interiorOrientation o'.interiorOrientation
    (BoundarylessModel.interiorDiffeomorph I 1) (BoundarylessModel.interiorDiffeomorph J 1)
    (o.isOrientationPreservingAt_interiorDiffeomorph_symm 1)
    (o'.isOrientationPreservingAt_interiorDiffeomorph 1) hy fun hyg ↦
      mapFundamentalClass_eq_degreeAtRegularValue_smul_self _ _ hyg

end Boundaryless

end Manifold.Orientation

end TauCeti
