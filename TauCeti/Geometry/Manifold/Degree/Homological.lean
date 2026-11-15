/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LocalIndex
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.Geometry.Manifold.Degree.Diffeomorph
public import TauCeti.Geometry.Manifold.RegularValue.Fibre
import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Geometry.Manifold.MFDeriv.LocalInjectivity
import TauCeti.Geometry.Manifold.ModelTransport.Boundaryless
import TauCeti.Geometry.Manifold.Orientation.LinearEquiv
import TauCeti.Geometry.Manifold.Orientation.Pullback

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

An orientation-preserving `C^k` diffeomorphism (`k ≠ 0`) between manifolds modelled on `E` pulls
back `toHomologicalOrientation`
(`TauCeti.Manifold.Orientation.toHomologicalOrientation_comap_diffeomorph`) and carries the
fundamental class of the source to that of the target. Transporting any compact boundaryless `C¹`
manifold `(M, I)` (`[I.Boundaryless]`) to a self-modelled Euclidean copy via
`ModelWithCorners.transContinuousLinearEquiv` and `TauCeti.BoundarylessModel` therefore defines a
canonical integral fundamental class `TauCeti.Manifold.Orientation.fundamentalClass` in
`Hₙ₊₁(M; ℤ)` independent of the model linear equivalence, agreeing with the Euclidean homological
fundamental class on `𝓡 (n + 1)` (`TauCeti.Manifold.Orientation.fundamentalClass_euclideanSpace`),
and satisfying `f_*[M] = (degreeAtRegularValue o o' f y) • [N]` for maps between compact
boundaryless manifolds with distinct models `(I, J)`
(`TauCeti.Manifold.Orientation.mapFundamentalClass_eq_degreeAtRegularValue_smul_fundamentalClass`).

## Main definitions

* `TauCeti.Manifold.Orientation.fundamentalClass`: the integral fundamental class in `Hₙ₊₁(M; ℤ)`
  of a compact oriented boundaryless `C¹` manifold `(M, I)`.
* `TauCeti.Manifold.Orientation.mapFundamentalClass`: the pushforward `f_*[M] ∈ Hₙ₊₁(X; ℤ)` along
  a continuous map `f : C(M, X)`.

## Main results

* `TauCeti.Manifold.Orientation.localIndex_toHomologicalOrientation`: at a point of invertible
  derivative the local index is the orientation sign.
* `TauCeti.Manifold.Orientation.degree_toHomologicalOrientation`: the degree of a proper map onto
  a preconnected manifold is the signed count of preimages of any regular value.
* `TauCeti.Manifold.Orientation.mapFundamentalClass_eq_degreeAtRegularValue_smul`: for a map
  between compact manifolds on the same inner product model, with preconnected target, `f_*[M]` is
  the signed count of preimages of a regular value times `[N]`.
* `TauCeti.Manifold.Orientation.toHomologicalOrientation_comap_diffeomorph`: an
  orientation-preserving diffeomorphism pulls back `toHomologicalOrientation`.
* `TauCeti.Manifold.Orientation.mapFundamentalClass_eq_degreeAtRegularValue_smul_fundamentalClass`:
  `f_*[M] = (degreeAtRegularValue o o' f y) • [N]` for maps between compact boundaryless `C¹`
  manifolds with arbitrary boundaryless models `(I, J)`.

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
theorem mapFundamentalClass_eq_degreeAtRegularValue_smul [CompactSpace M] [CompactSpace N]
    [PreconnectedSpace N] {f : C(M, N)} {y : N} (hy : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, E) f y) :
    (o.toHomologicalOrientation hE).mapFundamentalClass hE f =
      degreeAtRegularValue o o' f y • (o'.toHomologicalOrientation hE).fundamentalClass hE := by
  rw [HomologicalOrientation.mapFundamentalClass_eq_degree_smul _ _ hE hE,
    degree_toHomologicalOrientation hE o o' f.continuous.isProperMap hy]

open scoped ContDiff

/-- An orientation-preserving `C^k` diffeomorphism (`k ≠ 0`) between boundaryless `C¹` manifolds
modelled on `E` pulls back the homological orientation of the target to that of the source. -/
theorem toHomologicalOrientation_comap_diffeomorph {k : ℕ∞ω} (hk : k ≠ 0)
    (Φ : M ≃ₘ^k⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ N) (hΦ : ∀ x, IsOrientationPreservingAt o o' Φ x) :
    (o'.toHomologicalOrientation hE).comap Φ.toHomeomorph.isOpenEmbedding =
      o.toHomologicalOrientation hE := by
  set μ := o.toHomologicalOrientation hE
  set μ' := o'.toHomologicalOrientation hE
  ext x : 1
  apply Subtype.ext
  let φC : C(M, N) := Φ.toHomeomorph
  have hφC : ⇑φC = ⇑Φ := rfl
  have hcomap := HomologicalOrientation.localIndex_comap hE μ μ' IsOpenEmbedding.id
    Φ.toHomeomorph.isOpenEmbedding (f := .id M) (g := φC) (x := x)
    (.of_forall fun _ ↦ rfl)
  rw [μ.comap_id, id_eq] at hcomap
  have hidx : μ.localIndex (μ'.comap Φ.toHomeomorph.isOpenEmbedding) (.id M) x = 1 := by
    refine hcomap.trans ((localIndex_toHomologicalOrientation hE o o' φC ?_).trans ?_)
    · rw [hφC]
      exact Φ.isInvertible_mfderiv hk
    · rw [hφC]
      exact orientationSign_of_isOrientationPreservingAt (hΦ x)
  have h₁ := μ.localHomologyMap_restrict_localOrientationEquiv_symm μ (.id M) rfl
    isOpen_univ (mem_univ x) fun _ _ hz ↦ hz
  have h₂ := μ.localHomologyMap_restrict_localOrientationEquiv_symm
    (μ'.comap Φ.toHomeomorph.isOpenEmbedding) (.id M) rfl
    isOpen_univ (mem_univ x) fun _ _ hz ↦ hz
  rw [μ.localIndex_id hE x, one_zsmul] at h₁
  rw [hidx, one_zsmul] at h₂
  exact h₂.symm.trans h₁

/-- An orientation-preserving `C^k` diffeomorphism (`k ≠ 0`) between compact boundaryless `C¹`
manifolds modelled on `E` carries the fundamental class of the source to that of the target. -/
theorem mapFundamentalClass_toHomologicalOrientation_diffeomorph [CompactSpace M] [CompactSpace N]
    {k : ℕ∞ω} (hk : k ≠ 0) (Φ : M ≃ₘ^k⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ N)
    (hΦ : ∀ x, IsOrientationPreservingAt o o' Φ x) :
    (o.toHomologicalOrientation hE).mapFundamentalClass hE (Φ.toHomeomorph : C(M, N)) =
      (o'.toHomologicalOrientation hE).fundamentalClass hE := by
  rw [← toHomologicalOrientation_comap_diffeomorph hE o o' hk Φ hΦ,
    HomologicalOrientation.mapFundamentalClass_comap]

section Boundaryless

section Model

variable {E H : Type*} {M : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n : ℕ}

/-- The identity map on `M` as a `C¹` diffeomorphism onto the self-modelled Euclidean copy
`BoundarylessModel (I.transContinuousLinearEquiv e) M`. -/
private def euclideanDiffeomorph (I : ModelWithCorners ℝ E H) [I.Boundaryless] (M : Type)
    [TopologicalSpace M] [ChartedSpace H M] (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    M ≃ₘ^1⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))⟯
      BoundarylessModel (I.transContinuousLinearEquiv e) M :=
  (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := 1) I M e).trans
    (BoundarylessModel.diffeomorph (I.transContinuousLinearEquiv e) 1)

/-- The orientation of the self-modelled Euclidean copy pulled back from `o` along the inverse
recharting diffeomorphism. -/
private def euclideanOrientation (o : Manifold.Orientation I M (Fin (n + 1)))
    (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    Manifold.Orientation 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (BoundarylessModel (I.transContinuousLinearEquiv e) M) (Fin (n + 1)) :=
  o.pullback (euclideanDiffeomorph I M e).symm.contMDiff
    (fun _ ↦ (euclideanDiffeomorph I M e).symm.isInvertible_mfderiv one_ne_zero)
    (by simp)

private theorem isOrientationPreservingAt_euclideanDiffeomorph_symm
    (o : Manifold.Orientation I M (Fin (n + 1)))
    (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (y : BoundarylessModel (I.transContinuousLinearEquiv e) M) :
    IsOrientationPreservingAt (o.euclideanOrientation e) o
      (euclideanDiffeomorph I M e).symm y :=
  isOrientationPreservingAt_pullback _ _ _ _ y

private theorem isOrientationPreservingAt_euclideanDiffeomorph
    (o : Manifold.Orientation I M (Fin (n + 1)))
    (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) (x : M) :
    IsOrientationPreservingAt o (o.euclideanOrientation e) (euclideanDiffeomorph I M e) x := by
  have h := (isOrientationPreservingAt_euclideanDiffeomorph_symm o e
    (euclideanDiffeomorph I M e x)).diffeomorph_symm one_ne_zero
  have hcoe : ⇑(euclideanDiffeomorph I M e).symm.symm = ⇑(euclideanDiffeomorph I M e) := rfl
  rwa [hcoe] at h

/-- A chosen continuous linear equivalence `E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1))` from the
dimension equality carried by `o`; `fundamentalClass_eq` shows the resulting fundamental class is
independent of this choice. -/
private def modelEquivEuclidean (o : Manifold.Orientation I M (Fin (n + 1))) :
    E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  (finBasisOfFinrankEq ℝ E (by simpa using o.card_eq.symm)).equivFun.toContinuousLinearEquiv.trans
    (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm

variable [T2Space M] [CompactSpace M]

/-- **The integral fundamental class of a compact oriented boundaryless `C¹` manifold** `(M, I)`:
the class in `Hₙ₊₁(M; ℤ)` obtained by transporting `(M, I)` to a self-modelled Euclidean copy and
pushing forward its homological fundamental class. It does not depend on the chosen linear
equivalence with `EuclideanSpace ℝ (Fin (n + 1))`, and on `𝓡 (n + 1)` it agrees with
`(o.toHomologicalOrientation _).fundamentalClass _` (`fundamentalClass_euclideanSpace`). -/
def fundamentalClass (o : Manifold.Orientation I M (Fin (n + 1))) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of M) :=
  ((o.euclideanOrientation o.modelEquivEuclidean).toHomologicalOrientation
    finrank_euclideanSpace_fin).mapFundamentalClass finrank_euclideanSpace_fin
    ((euclideanDiffeomorph I M o.modelEquivEuclidean).symm.toHomeomorph :
      C(BoundarylessModel (I.transContinuousLinearEquiv o.modelEquivEuclidean) M, M))

/-- Any continuous linear equivalence `e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1))` computes the
same fundamental class `o.fundamentalClass`. -/
private theorem fundamentalClass_eq (o : Manifold.Orientation I M (Fin (n + 1)))
    (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    o.fundamentalClass =
      ((o.euclideanOrientation e).toHomologicalOrientation
        finrank_euclideanSpace_fin).mapFundamentalClass finrank_euclideanSpace_fin
        ((euclideanDiffeomorph I M e).symm.toHomeomorph :
          C(BoundarylessModel (I.transContinuousLinearEquiv e) M, M)) := by
  rw [fundamentalClass]
  set e₀ := o.modelEquivEuclidean
  let Ψ := (euclideanDiffeomorph I M e₀).symm.trans (euclideanDiffeomorph I M e)
  have hΨ : ∀ z, IsOrientationPreservingAt (o.euclideanOrientation e₀)
      (o.euclideanOrientation e) Ψ z := fun z ↦
    (isOrientationPreservingAt_euclideanDiffeomorph o e _).comp
      (isOrientationPreservingAt_euclideanDiffeomorph_symm o e₀ z)
  let ψC : C(BoundarylessModel (I.transContinuousLinearEquiv e₀) M,
      BoundarylessModel (I.transContinuousLinearEquiv e) M) := Ψ.toHomeomorph
  have hcomp : ((euclideanDiffeomorph I M e₀).symm.toHomeomorph :
      C(BoundarylessModel (I.transContinuousLinearEquiv e₀) M, M)) =
      ((euclideanDiffeomorph I M e).symm.toHomeomorph :
        C(BoundarylessModel (I.transContinuousLinearEquiv e) M, M)).comp ψC :=
    ContinuousMap.ext fun z ↦ ((euclideanDiffeomorph I M e).symm_apply_apply
      ((euclideanDiffeomorph I M e₀).symm z)).symm
  rw [← toHomologicalOrientation_comap_diffeomorph finrank_euclideanSpace_fin
    (o.euclideanOrientation e₀) (o.euclideanOrientation e) one_ne_zero Ψ hΨ, hcomp,
    HomologicalOrientation.mapFundamentalClass_comap_comp]

/-- Reversing a manifold orientation negates its fundamental class. -/
@[simp]
theorem fundamentalClass_neg (o : Manifold.Orientation I M (Fin (n + 1))) :
    (-o).fundamentalClass = -o.fundamentalClass := by
  rw [(-o).fundamentalClass_eq o.modelEquivEuclidean, fundamentalClass]
  have hneg : (-o).euclideanOrientation o.modelEquivEuclidean =
      -o.euclideanOrientation o.modelEquivEuclidean :=
    pullback_neg o _ _ _
  rw [hneg, toHomologicalOrientation_neg, HomologicalOrientation.mapFundamentalClass_neg]

/-- The image `f_*[M] ∈ Hₙ₊₁(X; ℤ)` of the fundamental class of a compact oriented boundaryless
`C¹` manifold `(M, I)` under a continuous map `f : C(M, X)`. -/
def mapFundamentalClass (o : Manifold.Orientation I M (Fin (n + 1)))
    {X : Type} [TopologicalSpace X] (f : C(M, X)) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of X) :=
  (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj
    (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom f)).hom o.fundamentalClass

/-- Equation lemma unfolding `Manifold.Orientation.mapFundamentalClass`. -/
theorem mapFundamentalClass_def (o : Manifold.Orientation I M (Fin (n + 1)))
    {X : Type} [TopologicalSpace X] (f : C(M, X)) :
    o.mapFundamentalClass f =
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom f)).hom o.fundamentalClass :=
  (rfl)

/-- The image of the fundamental class under the identity is the fundamental class. -/
@[simp]
theorem mapFundamentalClass_id (o : Manifold.Orientation I M (Fin (n + 1))) :
    o.mapFundamentalClass (ContinuousMap.id M) = o.fundamentalClass := by
  rw [mapFundamentalClass_def, TopCat.ofHom_id, CategoryTheory.Functor.map_id, ModuleCat.id_apply]

/-- Functoriality of `mapFundamentalClass` under composition of continuous maps. -/
theorem mapFundamentalClass_comp (o : Manifold.Orientation I M (Fin (n + 1)))
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (g : C(X, Y)) (f : C(M, X)) :
    o.mapFundamentalClass (g.comp f) =
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom g)).hom (o.mapFundamentalClass f) := by
  rw [mapFundamentalClass_def, mapFundamentalClass_def, TopCat.ofHom_comp,
    CategoryTheory.Functor.map_comp, ModuleCat.comp_apply]

/-- Reversing the orientation negates `mapFundamentalClass`. -/
@[simp]
theorem mapFundamentalClass_neg (o : Manifold.Orientation I M (Fin (n + 1)))
    {X : Type} [TopologicalSpace X] (f : C(M, X)) :
    (-o).mapFundamentalClass f = -o.mapFundamentalClass f := by
  rw [mapFundamentalClass_def, mapFundamentalClass_def, fundamentalClass_neg, map_neg]

/-- Homotopic continuous maps carry `o.fundamentalClass` to the same homology class. -/
theorem mapFundamentalClass_eq_of_homotopic
    (o : Manifold.Orientation I M (Fin (n + 1))) {X : Type} [TopologicalSpace X]
    {f g : C(M, X)} (h : f.Homotopic g) :
    o.mapFundamentalClass f = o.mapFundamentalClass g := by
  rw [mapFundamentalClass_def, mapFundamentalClass_def]
  congr 2
  exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor (C := ModuleCat.{0} ℤ)
    (f := TopCat.ofHom f) (g := TopCat.ofHom g) h.some _ (n + 1)

end Model

/-- On a compact manifold modelled on `𝓡 (n + 1)`, `Manifold.Orientation.fundamentalClass` agrees
with `(o.toHomologicalOrientation _).fundamentalClass _`. -/
@[simp]
theorem fundamentalClass_euclideanSpace {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] [IsManifold (𝓡 (n + 1)) 1 M]
    [CompactSpace M] (o : Manifold.Orientation (𝓡 (n + 1)) M (Fin (n + 1))) :
    o.fundamentalClass =
      (o.toHomologicalOrientation finrank_euclideanSpace_fin).fundamentalClass
        finrank_euclideanSpace_fin := by
  rw [o.fundamentalClass_eq (.refl ℝ (EuclideanSpace ℝ (Fin (n + 1))))]
  exact mapFundamentalClass_toHomologicalOrientation_diffeomorph finrank_euclideanSpace_fin
    _ o one_ne_zero _ (isOrientationPreservingAt_euclideanDiffeomorph_symm o _)

/-- On a compact manifold modelled on `𝓡 (n + 1)`, `Manifold.Orientation.mapFundamentalClass`
agrees with `(o.toHomologicalOrientation _).mapFundamentalClass _`. -/
@[simp]
theorem mapFundamentalClass_euclideanSpace {M X : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] [IsManifold (𝓡 (n + 1)) 1 M]
    [CompactSpace M] [TopologicalSpace X]
    (o : Manifold.Orientation (𝓡 (n + 1)) M (Fin (n + 1))) (f : C(M, X)) :
    o.mapFundamentalClass f =
      (o.toHomologicalOrientation finrank_euclideanSpace_fin).mapFundamentalClass
        finrank_euclideanSpace_fin f := by
  rw [o.mapFundamentalClass_def, o.fundamentalClass_euclideanSpace,
    HomologicalOrientation.mapFundamentalClass_def]

section TwoModels

variable {E F H H' : Type*} {M N : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I 1 M] [CompactSpace M]
  [TopologicalSpace N] [T2Space N] [ChartedSpace H' N] [IsManifold J 1 N] [CompactSpace N]
  {n : ℕ}

/-- An orientation-preserving `C^k` diffeomorphism (`k ≠ 0`) between compact boundaryless `C¹`
manifolds carries the fundamental class of the source to that of the target. -/
theorem mapFundamentalClass_diffeomorph {k : ℕ∞ω} (hk : k ≠ 0)
    (o : Manifold.Orientation I M (Fin (n + 1)))
    (o' : Manifold.Orientation J N (Fin (n + 1)))
    (Ψ : M ≃ₘ^k⟮I, J⟯ N) (hΨ : ∀ x, IsOrientationPreservingAt o o' Ψ x) :
    o.mapFundamentalClass (Ψ.toHomeomorph : C(M, N)) = o'.fundamentalClass := by
  let Ψ₁ : M ≃ₘ^1⟮I, J⟯ N :=
    ⟨Ψ.toEquiv, Ψ.contMDiff.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk),
      Ψ.symm.contMDiff.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)⟩
  set Φ := euclideanDiffeomorph I M o.modelEquivEuclidean
  set Φ' := euclideanDiffeomorph J N o'.modelEquivEuclidean
  let Θ := (Φ.symm.trans Ψ₁).trans Φ'
  have hΘ : ∀ z, IsOrientationPreservingAt (o.euclideanOrientation o.modelEquivEuclidean)
      (o'.euclideanOrientation o'.modelEquivEuclidean) Θ z := fun z ↦
    (isOrientationPreservingAt_euclideanDiffeomorph o' _ _).comp
      ((hΨ (Φ.symm z)).comp (isOrientationPreservingAt_euclideanDiffeomorph_symm o _ z))
  let θC : C(BoundarylessModel (I.transContinuousLinearEquiv o.modelEquivEuclidean) M,
      BoundarylessModel (J.transContinuousLinearEquiv o'.modelEquivEuclidean) N) := Θ.toHomeomorph
  have hcomp : (Ψ.toHomeomorph : C(M, N)).comp
      (Φ.symm.toHomeomorph :
        C(BoundarylessModel (I.transContinuousLinearEquiv o.modelEquivEuclidean) M, M)) =
      (Φ'.symm.toHomeomorph :
        C(BoundarylessModel (J.transContinuousLinearEquiv o'.modelEquivEuclidean) N, N)).comp
        θC :=
    ContinuousMap.ext fun z ↦ (Φ'.symm_apply_apply (Ψ (Φ.symm z))).symm
  rw [o.mapFundamentalClass_def, fundamentalClass,
    ← HomologicalOrientation.mapFundamentalClass_comp, hcomp,
    ← toHomologicalOrientation_comap_diffeomorph finrank_euclideanSpace_fin _ _ one_ne_zero Θ hΘ,
    HomologicalOrientation.mapFundamentalClass_comap_comp, ← fundamentalClass]

/-- **The signed count of preimages computes the image of the fundamental class for arbitrary
boundaryless models.** Let `(M, I)` and `(N, J)` be compact boundaryless `C¹` manifolds of
dimension `n + 1` with `N` preconnected, oriented by `o` and `o'`. For any continuous map
`f : C(M, N)` and any regular value `y` of `f`,
`f_*[M] = (degreeAtRegularValue o o' f y) • [N]` in `Hₙ₊₁(N; ℤ)`. -/
theorem mapFundamentalClass_eq_degreeAtRegularValue_smul_fundamentalClass [PreconnectedSpace N]
    (o : Manifold.Orientation I M (Fin (n + 1)))
    (o' : Manifold.Orientation J N (Fin (n + 1)))
    {f : C(M, N)} {y : N} (hy : IsRegularValue I J f y) :
    o.mapFundamentalClass f = degreeAtRegularValue o o' f y • o'.fundamentalClass := by
  set Φ := euclideanDiffeomorph I M o.modelEquivEuclidean
  set Ψ := euclideanDiffeomorph J N o'.modelEquivEuclidean
  let φSymm : C(BoundarylessModel (I.transContinuousLinearEquiv o.modelEquivEuclidean) M, M) :=
    Φ.symm.toHomeomorph
  let ψC : C(N, BoundarylessModel (J.transContinuousLinearEquiv o'.modelEquivEuclidean) N) :=
    Ψ.toHomeomorph
  let ψSymm : C(BoundarylessModel (J.transContinuousLinearEquiv o'.modelEquivEuclidean) N, N) :=
    Ψ.symm.toHomeomorph
  let g := ψC.comp (f.comp φSymm)
  have hg_coe : ⇑g = Ψ ∘ (f ∘ Φ.symm) := rfl
  have hyg : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) g (Ψ y) := by
    rw [hg_coe, Ψ.isRegularValue_diffeomorph_comp_apply one_ne_zero]
    exact (Φ.symm.isRegularValue_comp_diffeomorph one_ne_zero f y).2 hy
  have hdeg : degreeAtRegularValue (o.euclideanOrientation o.modelEquivEuclidean)
      (o'.euclideanOrientation o'.modelEquivEuclidean) g (Ψ y) =
      degreeAtRegularValue o o' f y := by
    rw [hg_coe, degreeAtRegularValue_diffeomorph_comp_of_isOrientationPreservingAt Ψ one_ne_zero
      (f ∘ Φ.symm) (isOrientationPreservingAt_euclideanDiffeomorph o' _ y),
      degreeAtRegularValue_comp_diffeomorph_of_isOrientationPreservingAt Φ.symm one_ne_zero f
        fun z _ ↦ isOrientationPreservingAt_euclideanDiffeomorph_symm o _ z]
  have hfg : f.comp φSymm = ψSymm.comp g :=
    ContinuousMap.ext fun z ↦ (Ψ.symm_apply_apply (f (Φ.symm z))).symm
  rw [o.mapFundamentalClass_def, fundamentalClass,
    ← HomologicalOrientation.mapFundamentalClass_comp, hfg,
    HomologicalOrientation.mapFundamentalClass_comp,
    mapFundamentalClass_eq_degreeAtRegularValue_smul finrank_euclideanSpace_fin _ _ hyg, hdeg,
    fundamentalClass, HomologicalOrientation.mapFundamentalClass_def]
  exact map_zsmul (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj
    (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom ψSymm)).hom
    (degreeAtRegularValue o o' f y) _

end TwoModels

end Boundaryless

end Manifold.Orientation

end TauCeti
