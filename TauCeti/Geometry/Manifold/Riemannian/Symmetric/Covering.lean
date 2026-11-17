/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Covering
public import TauCeti.Geometry.Manifold.Instances.UniversalCover
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Symmetric.Basic
import Mathlib.Topology.Homotopy.Lifting
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
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

namespace TauCeti.IsLocalRiemannianIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

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
  have hxy_inv : f x = (ΦinvC.comp fC) y := by
    simp [ΦinvC, fC, hxy]
  obtain ⟨R, ⟨hRy, hR⟩, -⟩ :=
    hcov.existsUnique_continuousMap_lifts (ΦinvC.comp fC) y x hxy_inv
  have hRL_eq : R.comp L = ContinuousMap.id M := by
    obtain ⟨_, -, huniq⟩ := hcov.existsUnique_continuousMap_lifts fC x x rfl
    have h1 : R.comp L = _ := huniq (R.comp L) ⟨by simp [hLx, hRy], by
      funext z
      have hLz : f (L z) = Φ (f z) := congrFun hL z
      have hRz : f (R (L z)) = (Φ⁻¹) (f (L z)) := congrFun hR (L z)
      simpa [fC, Function.comp_apply, RiemannianIsometry.inv_apply, hLz] using hRz⟩
    have h2 : ContinuousMap.id M = _ := huniq (ContinuousMap.id M) ⟨rfl, rfl⟩
    exact h1.trans h2.symm
  have hLR_eq : L.comp R = ContinuousMap.id M := by
    obtain ⟨_, -, huniq⟩ := hcov.existsUnique_continuousMap_lifts fC y y rfl
    have h1 : L.comp R = _ := huniq (L.comp R) ⟨by simp [hRy, hLx], by
      funext z
      have hRz : f (R z) = (Φ⁻¹) (f z) := congrFun hR z
      have hLz : f (L (R z)) = Φ (f (R z)) := congrFun hL (R z)
      simpa [fC, Function.comp_apply, RiemannianIsometry.inv_apply, hRz] using hLz⟩
    have h2 : ContinuousMap.id M = _ := huniq (ContinuousMap.id M) ⟨rfl, rfl⟩
    exact h1.trans h2.symm
  have hloc : IsLocalDiffeomorph I J ∞ f := hf.isLocalDiffeomorph (n := ∞) (by simp) le_rfl
  have hL_smooth : ContMDiff I I ∞ L :=
    ContMDiff.of_comp_isLocalDiffeomorph hloc L.continuous
      (by rw [hL]; exact Φ.toDiffeomorph.contMDiff.comp hf.contMDiff)
  have hR_smooth : ContMDiff I I ∞ R :=
    ContMDiff.of_comp_isLocalDiffeomorph hloc R.continuous
      (by rw [hR]; exact (Φ⁻¹).toDiffeomorph.contMDiff.comp hf.contMDiff)
  let Φ' : Isom I M :=
    { toEquiv :=
        { toFun := L
          invFun := R
          left_inv := fun z ↦ DFunLike.congr_fun hRL_eq z
          right_inv := fun z ↦ DFunLike.congr_fun hLR_eq z }
      contMDiff_toFun := hL_smooth
      contMDiff_invFun := hR_smooth
      inner_mfderiv' := fun z u v ↦ by
        change inner ℝ (mfderiv I I L z u) (mfderiv I I L z v) = inner ℝ u v
        have hcomp : ∀ w : TangentSpace I z,
            (mfderiv I J f (L z) (mfderiv I I L z w) : F) =
              mfderiv J J Φ (f z) (mfderiv I J f z w) := fun w ↦ by
          have h1 := DFunLike.congr_fun
            (mfderiv_comp z (hf.mdifferentiableAt (L z)) (hL_smooth.mdifferentiableAt (by simp))) w
          have h2 := DFunLike.congr_fun
            (mfderiv_comp z (Φ.mdifferentiableAt (f z)) (hf.mdifferentiableAt z)) w
          have h12 : (mfderiv I J (f ∘ L) z w : F) = mfderiv I J (Φ ∘ f) z w := by
            rw [show (f ∘ L : M → N) = Φ ∘ f from hL]
          exact h1.symm.trans (h12.trans h2)
        have hinner : ∀ {q₁ q₂ : N} (_ : q₁ = q₂) (a₁ b₁ : TangentSpace J q₁)
            (a₂ b₂ : TangentSpace J q₂), (a₁ : F) = a₂ → (b₁ : F) = b₂ →
            inner ℝ a₁ b₁ = inner ℝ a₂ b₂ := by
          rintro q _ rfl a b _ _ rfl rfl
          rfl
        calc
          inner ℝ (mfderiv I I L z u) (mfderiv I I L z v) =
              inner ℝ (mfderiv I J f (L z) (mfderiv I I L z u))
                (mfderiv I J f (L z) (mfderiv I I L z v)) :=
            (hf.inner_mfderiv (L z) _ _).symm
          _ = inner ℝ (mfderiv J J Φ (f z) (mfderiv I J f z u))
                (mfderiv J J Φ (f z) (mfderiv I J f z v)) :=
            hinner (congrFun hL z) _ _ _ _ (hcomp u) (hcomp v)
          _ = inner ℝ (mfderiv I J f z u) (mfderiv I J f z v) :=
            Φ.inner_mfderiv (f z) _ _
          _ = inner ℝ u v := hf.inner_mfderiv z u v }
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
    · obtain ⟨_, -, huniq1⟩ :=
        hf.existsUnique_lift_isom_of_isCoveringMap hcov (1 : Isom J N) (x := x) (y := x) (by simp)
      have hsq : Φ' * Φ' = _ := huniq1 (Φ' * Φ') ⟨by simp [hΦ'x], by
        funext z
        have h1 : f (Φ' z) = Φ (f z) := congrFun hΦ' z
        have h2 : f (Φ' (Φ' z)) = Φ (f (Φ' z)) := congrFun hΦ' (Φ' z)
        simpa [RiemannianIsometry.mul_apply, h1, hΦ.apply_apply] using h2⟩
      have hone : (1 : Isom I M) = _ := huniq1 1 ⟨by simp, by funext z; simp⟩
      exact hsq.trans hone.symm
    · ext v
      apply hf.mfderiv_injective x
      have h1 : (mfderiv I J (f ∘ Φ') x v : F) = mfderiv I J f (Φ' x) (mfderiv I I Φ' x v) :=
        DFunLike.congr_fun
          (mfderiv_comp x (hf.mdifferentiableAt (Φ' x)) (Φ'.mdifferentiableAt x)) v
      have h2 : (mfderiv I J (Φ ∘ f) x v : F) = mfderiv J J Φ (f x) (mfderiv I J f x v) :=
        DFunLike.congr_fun
          (mfderiv_comp x (Φ.mdifferentiableAt (f x)) (hf.mdifferentiableAt x)) v
      have h12 : (mfderiv I J (f ∘ Φ') x v : F) = mfderiv I J (Φ ∘ f) x v := by
        rw [hΦ']
      have hstep : ∀ {q : M} (_ : q = x) (w : TangentSpace I q) (w' : TangentSpace I x),
          (w : E) = w' → (mfderiv I J f q w : F) = mfderiv I J f x w' := by
        rintro q rfl w _ rfl
        rfl
      have hlhs : (mfderiv I J f x (mfderiv I I Φ' x v) : F) =
          -(mfderiv I J f x v : F) :=
        (hstep hΦ'x _ _ rfl).symm.trans
          (h1.symm.trans (h12.trans (h2.trans (hΦ.mfderiv_apply _))))
      have hrhs : (mfderiv I J f x ((-ContinuousLinearMap.id ℝ (TangentSpace I x)) v) : F) =
          -(mfderiv I J f x v : F) := by
        change (mfderiv I J f x (-v) : F) = -(mfderiv I J f x v : F)
        rw [map_neg]
      exact hlhs.trans hrhs.symm
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
endowed with the metric pulled back along the covering projection. -/
theorem isRiemannianSymmetricSpace_universalCover [I.Boundaryless]
    [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (x₀ : M)
    (h : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      IsRiemannianSymmetricSpace I M) :
    letI : RiemannianBundle (fun x : UniversalCover x₀ ↦ TangentSpace I x) :=
      ⟨(g.pullback (UniversalCover.proj (x₀ := x₀)) (UniversalCover.contMDiff_proj x₀)
        fun x ↦ (((UniversalCover.isLocalDiffeomorph_proj x₀ (I := I) (n := ∞)) x
          ).isInvertible_mfderiv (by simp)).injective).toRiemannianMetric⟩
    IsRiemannianSymmetricSpace I (UniversalCover x₀) :=
  g.isRiemannianSymmetricSpace_pullback_of_isCoveringMap
    (UniversalCover.contMDiff_proj x₀)
    (fun x ↦ ((UniversalCover.isLocalDiffeomorph_proj x₀ (I := I) (n := ∞)) x
      ).isInvertible_mfderiv (by simp))
    (UniversalCover.isCoveringMap x₀) h

end Bundle.ContMDiffRiemannianMetric
