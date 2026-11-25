/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Covering
public import TauCeti.Geometry.Manifold.Riemannian.Covering.Universal
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Symmetric.Basic
import Mathlib.Topology.Homotopy.Lifting
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.MFDeriv.Congr
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback

/-!
# Lifting symmetries along Riemannian coverings

Let `f : M → N` be a local Riemannian isometry and a topological covering map from a simply
connected, locally path-connected boundaryless manifold `M` modelled on a complete normed space.
Every global Riemannian isometry `Φ : Isom J N` lifts uniquely to a global Riemannian isometry
`Φ' : Isom I M` once the image of one basepoint is specified: the topological lift and its inverse
are obtained by the lifting theorem for covering spaces, are smooth because `f` is a local
diffeomorphism, and preserve the Riemannian metric because `f` is a local isometry.

In particular, every geodesic symmetry at `f x` lifts uniquely to a geodesic symmetry at `x`
covering it, so the property of being a Riemannian symmetric space lifts to every simply connected
Riemannian covering, and specifically to the universal cover equipped with the pullback metric.

## Main results

* `IsCoveringMap.leftInverse_of_comp_eq`: two continuous lifts along a covering map on a
  preconnected space that cover a left-inverse pair and satisfy `R (L x) = x` at one point satisfy
  `LeftInverse R L`.
* `TauCeti.IsLocalRiemannianIsometry.inner_mfderiv_of_comp_eq`: a differentiable map intertwined
  with a local Riemannian isometry by local Riemannian isometries preserves inner products.
* `TauCeti.IsLocalRiemannianIsometry.existsUnique_lift_isom_of_isCoveringMap`: every Riemannian
  isometry of the base lifts uniquely to a Riemannian isometry of a simply connected covering space
  with prescribed value at one point.
* `TauCeti.IsLocalRiemannianIsometry.existsUnique_isGeodesicSymmetryAt_of_isCoveringMap`: every
  geodesic symmetry at `f x` lifts uniquely to a geodesic symmetry at `x` covering it.
* `TauCeti.IsLocalRiemannianIsometry.isRiemannianSymmetricSpace_of_isCoveringMap`: a simply
  connected Riemannian covering of a Riemannian symmetric space is a Riemannian symmetric space.
* `TauCeti.IsLocalRiemannianIsometry.apply_geodesicSymmetry_of_isCoveringMap`: a simply connected
  Riemannian covering intertwines geodesic symmetries.
* `Bundle.ContMDiffRiemannianMetric.isRiemannianSymmetricSpace_pullback_of_isCoveringMap`: the
  pullback of a symmetric metric along a simply connected smooth covering is symmetric.
* `Bundle.ContMDiffRiemannianMetric.isRiemannianSymmetricSpace_universalCover`: the universal
  cover of a Riemannian symmetric space, endowed with the pullback metric, is a Riemannian
  symmetric space.

## References

* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, AMS (2001), Ch. IV, §3.
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. II, Wiley (1969),
  Ch. XI, §1.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Ch. 6.
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

section CoveringLeftInverse

/-- On a preconnected covering space, if continuous maps `L, R : M → M` lift maps `φ, ψ : N → N`
with `LeftInverse ψ φ` and `R (L x) = x` at one point `x`, then `R` is a left inverse of `L`. -/
theorem IsCoveringMap.leftInverse_of_comp_eq {M N : Type*} [TopologicalSpace M]
    [TopologicalSpace N] [PreconnectedSpace M] {f : M → N} (hcov : IsCoveringMap f)
    {L R : M → M} {φ ψ : N → N} (hL_cont : Continuous L) (hR_cont : Continuous R)
    (hL : f ∘ L = φ ∘ f) (hR : f ∘ R = ψ ∘ f) (hψφ : Function.LeftInverse ψ φ)
    {x : M} (hx : R (L x) = x) :
    Function.LeftInverse R L := by
  have hcomp : f ∘ (R ∘ L) = f ∘ id := by
    funext z
    calc
      f (R (L z)) = ψ (f (L z)) := congrFun hR (L z)
      _ = ψ (φ (f z)) := congrArg ψ (congrFun hL z)
      _ = f z := hψφ (f z)
  exact congrFun (hcov.eq_of_comp_eq (hR_cont.comp hL_cont) continuous_id hcomp x hx)

end CoveringLeftInverse

namespace TauCeti.IsLocalRiemannianIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

/-- If `f₁` and `f₂` are local Riemannian isometries, `Φ` is a local Riemannian isometry, and `L`
is differentiable at `z` with `f₂ ∘ L = Φ ∘ f₁`, then `dL_z` preserves inner products. -/
theorem inner_mfderiv_of_comp_eq
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [RiemannianBundle (fun x : M₁ ↦ TangentSpace I₁ x)]
    {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    [RiemannianBundle (fun x : M₂ ↦ TangentSpace I₂ x)]
    {f₁ : M₁ → M} {f₂ : M₂ → N} {Φ : M → N} {L : M₁ → M₂} {z : M₁}
    (hf₁ : IsLocalRiemannianIsometry I₁ I f₁)
    (hf₂ : IsLocalRiemannianIsometry I₂ J f₂)
    (hΦ : IsLocalRiemannianIsometry I J Φ)
    (hLz : MDifferentiableAt I₁ I₂ L z) (hcomp : f₂ ∘ L = Φ ∘ f₁)
    (u v : TangentSpace I₁ z) :
    inner ℝ (mfderiv I₁ I₂ L z u) (mfderiv I₁ I₂ L z v) = inner ℝ u v := by
  have hd : ∀ w : TangentSpace I₁ z,
      (mfderiv I₂ J f₂ (L z) (mfderiv I₁ I₂ L z w) : F) =
        mfderiv I J Φ (f₁ z) (mfderiv I₁ I f₁ z w) := fun w ↦ by
    have h1 := DFunLike.congr_fun (mfderiv_comp z (hf₂.mdifferentiableAt (L z)) hLz) w
    have h2 := DFunLike.congr_fun (mfderiv_comp z (hΦ.mdifferentiableAt (f₁ z))
      (hf₁.mdifferentiableAt z)) w
    have h12 : (mfderiv I₁ J (f₂ ∘ L) z w : F) = mfderiv I₁ J (Φ ∘ f₁) z w := by
      rw [hcomp]
    exact h1.symm.trans (h12.trans h2)
  calc
    inner ℝ (mfderiv I₁ I₂ L z u) (mfderiv I₁ I₂ L z v) =
        inner ℝ (mfderiv I₂ J f₂ (L z) (mfderiv I₁ I₂ L z u))
          (mfderiv I₂ J f₂ (L z) (mfderiv I₁ I₂ L z v)) :=
      (hf₂.inner_mfderiv (L z) _ _).symm
    _ = inner ℝ (mfderiv I J Φ (f₁ z) (mfderiv I₁ I f₁ z u))
          (mfderiv I J Φ (f₁ z) (mfderiv I₁ I f₁ z v)) :=
      inner_tangentSpace_congr (congrFun hcomp z) (hd u) (hd v)
    _ = inner ℝ (mfderiv I₁ I f₁ z u) (mfderiv I₁ I f₁ z v) :=
      hΦ.inner_mfderiv (f₁ z) _ _
    _ = inner ℝ u v := hf₁.inner_mfderiv z u v

section Lifting

variable [CompleteSpace E] [BoundarylessManifold I M] [IsManifold I ∞ M] [IsManifold J ∞ N]
  [SimplyConnectedSpace M] [LocallyPathConnectedSpace M] {f : M → N}

/-- **Lifting Riemannian isometries to a simply connected covering.** Let `f : M → N` be a
Riemannian covering from a simply connected, locally path-connected boundaryless manifold. Given
`Φ : Isom J N` and points `x, y : M` with `f y = Φ (f x)`, there is a unique global isometry
`Φ' : Isom I M` with `Φ' x = y` and `f ∘ Φ' = Φ ∘ f`. -/
theorem existsUnique_lift_isom_of_isCoveringMap (hf : IsLocalRiemannianIsometry I J f)
    (hcov : IsCoveringMap f) (Φ : Isom J N) {x y : M} (hxy : f y = Φ (f x)) :
    ∃! Φ' : Isom I M, Φ' x = y ∧ f ∘ Φ' = Φ ∘ f := by
  let fC : C(M, N) := ⟨f, hf.contMDiff.continuous⟩
  let ΦC : C(N, N) := ⟨Φ, Φ.toDiffeomorph.continuous⟩
  let ΦinvC : C(N, N) := ⟨⇑(Φ⁻¹), (Φ⁻¹).toDiffeomorph.continuous⟩
  obtain ⟨L, ⟨hLx, hL⟩, hLuniq⟩ :=
    hcov.existsUnique_continuousMap_lifts (ΦC.comp fC) x y hxy
  obtain ⟨R, ⟨hRy, hR⟩, -⟩ :=
    hcov.existsUnique_continuousMap_lifts (ΦinvC.comp fC) y x (by simp [ΦinvC, fC, hxy])
  have hloc : IsLocalDiffeomorph I J ∞ f := hf.isLocalDiffeomorph (n := ∞) (by simp) le_rfl
  have hL_smooth : ContMDiff I I ∞ L :=
    ContMDiff.of_comp_isLocalDiffeomorph hloc L.continuous
      (by rw [hL]; exact Φ.toDiffeomorph.contMDiff.comp hf.contMDiff)
  have hR_smooth : ContMDiff I I ∞ R :=
    ContMDiff.of_comp_isLocalDiffeomorph hloc R.continuous
      (by rw [hR]; exact (Φ⁻¹).toDiffeomorph.contMDiff.comp hf.contMDiff)
  let d : M ≃ₘ^∞⟮I, I⟯ M :=
    { toEquiv :=
        { toFun := L
          invFun := R
          left_inv := hcov.leftInverse_of_comp_eq L.continuous R.continuous hL hR
            Φ.symm_apply_apply (by rw [hLx, hRy])
          right_inv := hcov.leftInverse_of_comp_eq R.continuous L.continuous hR hL
            Φ.apply_symm_apply (by rw [hRy, hLx]) }
      contMDiff_toFun := hL_smooth
      contMDiff_invFun := hR_smooth }
  let Φ' : Isom I M :=
    { toDiffeomorph := d
      inner_mfderiv' := fun z u v ↦ by
        rw [← d.coe_toEquiv]
        exact hf.inner_mfderiv_of_comp_eq hf Φ.isLocalRiemannianIsometry
          (hL_smooth.mdifferentiableAt (by simp)) hL u v }
  refine ⟨Φ', ⟨hLx, hL⟩, fun Ψ ⟨hΨx, hΨ⟩ ↦ ?_⟩
  have hΨC : (⟨Ψ, Ψ.toDiffeomorph.continuous⟩ : C(M, M)) = L := hLuniq _ ⟨hΨx, hΨ⟩
  exact RiemannianIsometry.ext fun z ↦ DFunLike.congr_fun hΨC z

/-- **Lifting a geodesic symmetry to a simply connected covering.** Every geodesic symmetry at
`f x` lifts uniquely to a geodesic symmetry at `x` covering it. -/
theorem existsUnique_isGeodesicSymmetryAt_of_isCoveringMap (hf : IsLocalRiemannianIsometry I J f)
    (hcov : IsCoveringMap f) {Φ : Isom J N} {x : M} (hΦ : IsGeodesicSymmetryAt Φ (f x)) :
    ∃! Φ' : Isom I M, IsGeodesicSymmetryAt Φ' x ∧ f ∘ Φ' = Φ ∘ f := by
  obtain ⟨Φ', ⟨hΦ'x, hΦ'⟩, huniq⟩ :=
    hf.existsUnique_lift_isom_of_isCoveringMap hcov Φ hΦ.apply_eq.symm
  have hsym : IsGeodesicSymmetryAt Φ' x := by
    refine ⟨hΦ'x, ?_, ?_⟩
    · have hΦ'_cont : Continuous ⇑Φ' := Φ'.toDiffeomorph.continuous
      have hinv := hcov.leftInverse_of_comp_eq hΦ'_cont hΦ'_cont hΦ' hΦ' hΦ.involutive
        (by rw [hΦ'x, hΦ'x])
      ext z
      rw [RiemannianIsometry.mul_apply, RiemannianIsometry.one_apply]
      exact hinv z
    · refine eq_neg_id_of_apply hΦ'x fun v ↦ ?_
      have h1 : (mfderiv I J (f ∘ Φ') x v : F) = mfderiv I J f (Φ' x) (mfderiv I I Φ' x v) :=
        DFunLike.congr_fun
          (mfderiv_comp x (hf.mdifferentiableAt (Φ' x)) (Φ'.mdifferentiableAt x)) v
      have h2 : (mfderiv I J (Φ ∘ f) x v : F) = mfderiv J J Φ (f x) (mfderiv I J f x v) :=
        DFunLike.congr_fun
          (mfderiv_comp x (Φ.mdifferentiableAt (f x)) (hf.mdifferentiableAt x)) v
      have h12 : (mfderiv I J (f ∘ Φ') x v : F) = mfderiv I J (Φ ∘ f) x v := by
        rw [hΦ']
      let w : TangentSpace I x := tangentSpaceCast I (Φ' x) x (mfderiv I I Φ' x v)
      have hw : (mfderiv I I Φ' x v : E) = w :=
        (coe_tangentSpaceCast I (Φ' x) x (mfderiv I I Φ' x v)).symm
      have hlhs : (mfderiv I J f x w : F) = -(mfderiv I J f x v : F) :=
        (mfderiv_apply_congr_point hΦ'x hw).symm.trans
          (h1.symm.trans (h12.trans (h2.trans (hΦ.mfderiv_apply _))))
      have hwx : mfderiv I J f x w = mfderiv I J f x (-v) :=
        hlhs.trans (map_neg (mfderiv I J f x) v).symm
      exact hw.trans (hf.mfderiv_injective x hwx)
  exact ⟨Φ', ⟨hsym, hΦ'⟩,
    fun Ψ ⟨hΨsym, hΨ⟩ ↦ huniq Ψ ⟨hΨsym.apply_eq, hΨ⟩⟩

/-- **A simply connected Riemannian covering of a Riemannian symmetric space is symmetric.** -/
theorem isRiemannianSymmetricSpace_of_isCoveringMap (hf : IsLocalRiemannianIsometry I J f)
    (hcov : IsCoveringMap f) [IsRiemannianSymmetricSpace J N] :
    IsRiemannianSymmetricSpace I M where
  exists_isGeodesicSymmetryAt x := by
    obtain ⟨Φ', ⟨hΦ', -⟩, -⟩ := hf.existsUnique_isGeodesicSymmetryAt_of_isCoveringMap hcov
      (isGeodesicSymmetryAt_geodesicSymmetry (I := J) (f x))
    exact ⟨Φ', hΦ'⟩

omit [BoundarylessManifold I M] in
/-- A simply connected Riemannian covering between Riemannian symmetric spaces intertwines their
geodesic symmetries. -/
theorem apply_geodesicSymmetry_of_isCoveringMap [FiniteDimensional ℝ E] [T2Space M]
    [I.Boundaryless] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (hf : IsLocalRiemannianIsometry I J f) (hcov : IsCoveringMap f)
    [IsRiemannianSymmetricSpace I M] [IsRiemannianSymmetricSpace J N] (x y : M) :
    f (geodesicSymmetry I M x y) = geodesicSymmetry J N (f x) (f y) := by
  obtain ⟨Φ', ⟨hΦ', hcovΦ'⟩, -⟩ :=
    hf.existsUnique_isGeodesicSymmetryAt_of_isCoveringMap hcov
      (isGeodesicSymmetryAt_geodesicSymmetry (I := J) (f x))
  rw [← hΦ'.eq_geodesicSymmetry]
  exact congrFun hcovΦ' y

end Lifting

end TauCeti.IsLocalRiemannianIsometry

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- **Pullback of a symmetric metric along a simply connected covering.** If `f : M → N` is a
smooth covering map out of a simply connected, locally path-connected boundaryless manifold with
everywhere invertible differential, and `g` makes `N` a Riemannian symmetric space, then the
pullback metric `f^* g` makes `M` a Riemannian symmetric space. -/
theorem isRiemannianSymmetricSpace_pullback_of_isCoveringMap [BoundarylessManifold I M]
    [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]
    (g : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)) {f : M → N}
    (hf : ContMDiff I J (∞ + 1) f) (hinv : ∀ x, (mfderiv I J f x).IsInvertible)
    (hcov : IsCoveringMap f)
    (h : letI : RiemannianBundle (fun y : N ↦ TangentSpace J y) := ⟨g.toRiemannianMetric⟩
      IsRiemannianSymmetricSpace J N) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g.pullback f hf fun x ↦ (hinv x).injective).toRiemannianMetric⟩
    IsRiemannianSymmetricSpace I M :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.pullback f hf fun x ↦ (hinv x).injective).toRiemannianMetric⟩
  letI : RiemannianBundle (fun y : N ↦ TangentSpace J y) := ⟨g.toRiemannianMetric⟩
  letI : IsRiemannianSymmetricSpace J N := h
  (isLocalRiemannianIsometry_pullback_of_isInvertible g hf hinv
    ).isRiemannianSymmetricSpace_of_isCoveringMap hcov

/-- **The universal cover of a Riemannian symmetric space is a Riemannian symmetric space** when
endowed with `g.universalCover x₀` (the metric pulled back along the covering projection). -/
theorem isRiemannianSymmetricSpace_universalCover [I.Boundaryless]
    [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (x₀ : M)
    (h : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      IsRiemannianSymmetricSpace I M) :
    letI : RiemannianBundle (fun x : UniversalCover x₀ ↦ TangentSpace I x) :=
      ⟨(g.universalCover x₀).toRiemannianMetric⟩
    IsRiemannianSymmetricSpace I (UniversalCover x₀) :=
  letI : RiemannianBundle (fun x : UniversalCover x₀ ↦ TangentSpace I x) :=
    ⟨(g.universalCover x₀).toRiemannianMetric⟩
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  letI : IsRiemannianSymmetricSpace I M := h
  (g.isLocalRiemannianIsometry_universalCoverProj x₀
    ).isRiemannianSymmetricSpace_of_isCoveringMap (UniversalCover.isCoveringMap x₀)

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti.UniversalCover

open scoped TauCeti

/-- Under `open scoped TauCeti`, the universal cover of a Riemannian symmetric space inherits a
`IsRiemannianSymmetricSpace` structure from the pullback `RiemannianBundle` instance. -/
theorem instIsRiemannianSymmetricSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianSymmetricSpace I M]
    (x₀ : M) :
    IsRiemannianSymmetricSpace I (UniversalCover x₀) :=
  (isLocalRiemannianIsometry_proj (I := I) x₀).isRiemannianSymmetricSpace_of_isCoveringMap
    (isCoveringMap x₀)

scoped[TauCeti] attribute [instance] TauCeti.UniversalCover.instIsRiemannianSymmetricSpace

end TauCeti.UniversalCover
