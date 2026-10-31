/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Quotient
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback

/-!
# Descending Riemannian metrics along local diffeomorphisms

Let `f : M → N` be a surjective local diffeomorphism and `g` a Riemannian metric on `M`. If the
inner product of `g` is compatible with `f`, in the sense that tangent vectors at points of one
fibre with the same images under the differential of `f` have the same inner products, then `g`
descends to a Riemannian metric `g.descend` on `N`: at `f x` it is `g` at `x` read through the
inverse of the differential of `f` at `x`. It is the unique metric on `N` whose pullback along
`f` is `g` (`Bundle.ContMDiffRiemannianMetric.pullback_eq_iff_eq_descend`), so `f` is a local
Riemannian isometry from `g` to `g.descend`. Near each point the descended metric is the pullback
of `g` along a local inverse of `f`, which makes it as regular as `g` when `f` is one degree more
regular. Since curvature is natural under local isometries, the descended metric has the scalar
curvature of `g`: `Scal(g.descend) (f x) = Scal(g) x`.

The main example is the orbit projection of a free, properly discontinuous smooth action of a
group `G` on `M` by isometries of `g`: then `g` descends to the orbit space `M / G`
(`Bundle.ContMDiffRiemannianMetric.quotient`). Examples are the round metric on real projective
spaces and lens spaces, product metrics on Dold manifolds `(Sᵃ × ℂPᵇ) / C₂`, and the metric
`dt² + g` on the mapping torus of an isometry of `g`.

## Main definitions and results

* `Bundle.ContMDiffRiemannianMetric.descend`: the metric descended along a surjective local
  diffeomorphism.
* `Bundle.ContMDiffRiemannianMetric.descend_inner_mfderiv`: the descended metric at `f x`, applied
  to the images of two tangent vectors at `x`, is their inner product for `g`.
* `Bundle.ContMDiffRiemannianMetric.pullback_eq_iff_eq_descend`: the descended metric is the
  unique metric on `N` whose pullback along `f` is `g`.
* `Bundle.ContMDiffRiemannianMetric.isLocalRiemannianIsometry_descend`: `f` is a local Riemannian
  isometry from `g` to the descended metric.
* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_descend`: the descended metric has the scalar
  curvature of `g`.
* `Bundle.ContMDiffRiemannianMetric.inner_eq_of_quotientMk_eq`: a metric invariant under a free,
  properly discontinuous group action is compatible with the orbit projection.
* `Bundle.ContMDiffRiemannianMetric.quotient`: a metric invariant under a free, properly
  discontinuous smooth group action descends to the orbit space.
* `Bundle.ContMDiffRiemannianMetric.pullback_eq_iff_eq_quotient`: the metric on the orbit space is
  the unique metric whose pullback along the orbit projection is the invariant metric.
* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_quotient`: the metric on the orbit space has the
  scalar curvature of the invariant metric.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 2 (Riemannian coverings and quotients by isometric group actions) and Proposition 7.6
  (naturality of curvature).
-/

public section

open Bundle Manifold Function
open scoped ContDiff Manifold Topology

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {n : ℕ∞ω}

section Descend

variable [IsManifold I 1 M] [IsManifold J 1 N]
  (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) {f : M → N}
  (hf : IsLocalDiffeomorph I J (n + 1) f) (hsurj : Surjective f)
  (hg : ∀ (x x' : M) (v w : TangentSpace I x) (v' w' : TangentSpace I x'), f x = f x' →
    mfderiv I J f x v = mfderiv I J f x' v' → mfderiv I J f x w = mfderiv I J f x' w' →
    g.inner x v w = g.inner x' v' w')

omit [IsManifold I 1 M] [IsManifold J 1 N] in
include hf in
/-- The differential of a local diffeomorphism is invertible at every point. -/
private theorem isInvertible_mfderiv (x : M) : (mfderiv I J f x).IsInvertible :=
  hf.isInvertible_mfderiv (by simp) x

/-- The Riemannian metric on `N` obtained by descending a metric `g` on `M` along a surjective
local diffeomorphism `f : M → N`, when tangent vectors at points of one fibre with the same images
under the differential of `f` have the same inner products. At `y = f x` it is `g` at `x`,
evaluated on the preimages of tangent vectors under the differential of `f` at `x`; the
hypothesis makes this independent of the choice of `x`. -/
def descend : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y) where
  inner y :=
    (ContinuousLinearMap.precomp ℝ (mfderiv I J f (surjInv hsurj y)).inverse).comp
      ((g.inner (surjInv hsurj y)).comp (mfderiv I J f (surjInv hsurj y)).inverse)
  symm y v w := g.symm (surjInv hsurj y) _ _
  pos y v hv := g.pos _ _ fun h0 ↦ hv <| by
    have h := (isInvertible_mfderiv hf (surjInv hsurj y)).self_apply_inverse v
    -- `h0` states the vanishing of the same vector through the coercion to a linear map.
    have h0' : (mfderiv I J f (surjInv hsurj y)).inverse v = 0 := h0
    rw [h0', map_zero] at h
    exact h.symm
  isVonNBounded y := by
    set x := surjInv hsurj y
    have hinv := isInvertible_mfderiv hf x
    refine ((g.isVonNBounded x).image (mfderiv I J f x)).subset ?_
    intro v hv
    exact ⟨(mfderiv I J f x).inverse v, hv, hinv.self_apply_inverse v⟩
  contMDiff y := by
    obtain ⟨x, rfl⟩ := hsurj y
    -- Near `f x`, the descended metric is the pullback of `g` along a local inverse of `f`.
    have hloc := hf x
    set s := hloc.localInverse
    refine (g.contMDiffAt_pullback hloc.contMDiffAt_localInverse).congr_of_eventuallyEq ?_
    filter_upwards [s.open_source.mem_nhds hloc.localInverse_mem_source] with z hz
    have hzs : f (s z) = z := hloc.localInverse_right_inv hz
    -- The differential of the local inverse at `z` is a right inverse of that of `f` at `s z`.
    have hds (u : TangentSpace J z) : mfderiv I J f (s z) (mfderiv J I s z u) = u := by
      have hsd : MDifferentiableAt J I s z :=
        (hloc.contMDiffOn_localInverse.contMDiffAt (s.open_source.mem_nhds hz)).mdifferentiableAt
          (by simp)
      have hcomp : f ∘ s =ᶠ[𝓝 z] id := Filter.eventuallyEq_of_mem
        (s.open_source.mem_nhds hz) hloc.localInverse_eqOn_right
      have h := mfderiv_comp z ((hf (s z)).mdifferentiableAt (by simp)) hsd
      rw [hcomp.mfderiv_eq, mfderiv_id] at h
      exact (DFunLike.congr_fun h u).symm
    have hinv := isInvertible_mfderiv hf (surjInv hsurj z)
    congr 1
    ext v w
    exact hg _ _ _ _ _ _ ((surjInv_eq hsurj z).trans hzs.symm)
      ((hinv.self_apply_inverse v).trans (hds v).symm)
      ((hinv.self_apply_inverse w).trans (hds w).symm)

/-- The descended metric at `y = f x`, applied to the images under the differential of `f` at `x`
of two tangent vectors at `x`, is their inner product for `g`. -/
theorem descend_inner_mfderiv_of_eq {x : M} {y : N} (h : f x = y) (v w : TangentSpace I x) :
    (g.descend hf hsurj hg).inner y (mfderiv I J f x v) (mfderiv I J f x w) = g.inner x v w := by
  have hinv := isInvertible_mfderiv hf (surjInv hsurj y)
  exact hg _ _ _ _ _ _ ((surjInv_eq hsurj y).trans h.symm) (hinv.self_apply_inverse _)
    (hinv.self_apply_inverse _)

/-- The descended metric at `f x`, applied to the images under the differential of `f` at `x`
of two tangent vectors at `x`, is their inner product for `g`. -/
@[simp]
theorem descend_inner_mfderiv (x : M) (v w : TangentSpace I x) :
    (g.descend hf hsurj hg).inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) =
      g.inner x v w :=
  g.descend_inner_mfderiv_of_eq hf hsurj hg rfl v w

variable [FiniteDimensional ℝ E]

/-- Pulling the descended metric back along `f` recovers `g`. -/
@[simp]
theorem pullback_descend (hf' : ContMDiff I J (n + 1) f)
    (hinj : ∀ x, Injective (mfderiv I J f x)) :
    (g.descend hf hsurj hg).pullback f hf' hinj = g := by
  ext x v w
  rw [pullback_inner, descend_inner_mfderiv]

/-- The descended metric is the unique metric on `N` whose pullback along `f` is `g`. -/
theorem pullback_eq_iff_eq_descend
    (h : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y))
    (hf' : ContMDiff I J (n + 1) f) (hinj : ∀ x, Injective (mfderiv I J f x)) :
    h.pullback f hf' hinj = g ↔ h = g.descend hf hsurj hg := by
  refine ⟨fun hpull ↦ ?_, fun hdesc ↦ hdesc ▸ g.pullback_descend hf hsurj hg hf' hinj⟩
  ext y v w
  obtain ⟨x, rfl⟩ := hsurj y
  have hinv := isInvertible_mfderiv hf x
  obtain ⟨v, rfl⟩ : ∃ u, mfderiv I J f x u = v := ⟨_, hinv.self_apply_inverse v⟩
  obtain ⟨w, rfl⟩ : ∃ u, mfderiv I J f x u = w := ⟨_, hinv.self_apply_inverse w⟩
  rw [descend_inner_mfderiv, ← hpull, pullback_inner]

end Descend

section Smooth

variable [IsManifold I ∞ M] [IsManifold J ∞ N]
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {f : M → N}
  (hf : IsLocalDiffeomorph I J (∞ + 1) f) (hsurj : Surjective f)
  (hg : ∀ (x x' : M) (v w : TangentSpace I x) (v' w' : TangentSpace I x'), f x = f x' →
    mfderiv I J f x v = mfderiv I J f x' v' → mfderiv I J f x w = mfderiv I J f x' w' →
    g.inner x v w = g.inner x' v' w')

/-- With `g` installed on `M` and the descended metric on `N`, the map `f` is a local Riemannian
isometry. -/
theorem isLocalRiemannianIsometry_descend :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    letI : RiemannianBundle (fun y : N ↦ TangentSpace J y) :=
      ⟨(g.descend hf hsurj hg).toRiemannianMetric⟩
    TauCeti.IsLocalRiemannianIsometry I J f :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  letI : RiemannianBundle (fun y : N ↦ TangentSpace J y) :=
    ⟨(g.descend hf hsurj hg).toRiemannianMetric⟩
  { contMDiff := hf.contMDiff
    isInvertible_mfderiv := isInvertible_mfderiv hf
    inner_mfderiv := g.descend_inner_mfderiv hf hsurj hg }

/-- **Scalar curvature of a descended metric.** The descended metric has the scalar curvature of
`g`: its scalar curvature at `f x` is the scalar curvature of `g` at `x`. -/
@[simp]
theorem scalarCurvature_descend [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M]
    [T2Space N] (x : M) :
    (g.descend hf hsurj hg).scalarCurvature (f x) = g.scalarCurvature x := by
  have hinv := isInvertible_mfderiv hf
  conv_rhs => rw [← g.pullback_descend hf hsurj hg hf.contMDiff fun x ↦ (hinv x).injective]
  exact (scalarCurvature_pullback_of_isInvertible _ hf.contMDiff hinv x).symm

end Smooth

/-! ### Quotients by isometric group actions -/

section Quotient

variable {G : Type*} [Group G] [MulAction G M]
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M]
  [IsCancelSMul G M] [T2Space M] [LocallyCompactSpace M]

/-- A metric preserved by every element of `G` is compatible with the orbit projection of a free,
properly discontinuous `C^1` action: tangent vectors at points of one orbit with the same
images in the orbit space have the same inner products. This is the compatibility hypothesis of
`Bundle.ContMDiffRiemannianMetric.descend` for the orbit projection, for a metric of any
regularity. -/
theorem inner_eq_of_quotientMk_eq [ContMDiffConstSMul I 1 G M] [IsManifold I 1 M]
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (hg : ∀ (a : G) (x : M) (v w : TangentSpace I x),
      g.inner (a • x) (mfderiv I I (a • ·) x v) (mfderiv I I (a • ·) x w) = g.inner x v w)
    (x x' : M) (v w : TangentSpace I x) (v' w' : TangentSpace I x')
    (hx : Quotient.mk (MulAction.orbitRel G M) x = Quotient.mk (MulAction.orbitRel G M) x')
    (hv : mfderiv I I (Quotient.mk (MulAction.orbitRel G M)) x v =
      mfderiv I I (Quotient.mk (MulAction.orbitRel G M)) x' v')
    (hw : mfderiv I I (Quotient.mk (MulAction.orbitRel G M)) x w =
      mfderiv I I (Quotient.mk (MulAction.orbitRel G M)) x' w') :
    g.inner x v w = g.inner x' v' w' := by
  obtain ⟨a, ha⟩ := Quotient.exact hx.symm
  dsimp only at ha
  subst ha
  have hq := TauCeti.isLocalDiffeomorph_quotientMk (I := I) (n := 1) (G := G) (M := M)
  have hn : (1 : ℕ∞ω) ≠ 0 := by simp
  -- The differential of `a • ·` at `x` carries `v` to the unique preimage of its image at `a • x`.
  have hmap (u : TangentSpace I x) (u' : TangentSpace I (a • x))
      (hu : mfderiv I I (Quotient.mk (MulAction.orbitRel G M)) x u =
        mfderiv I I (Quotient.mk (MulAction.orbitRel G M)) (a • x) u') :
      mfderiv I I (a • ·) x u = u' := by
    refine (hq.isInvertible_mfderiv hn (a • x)).injective ?_
    rw [TauCeti.mfderiv_quotientMk_smul_apply hn ((hq (a • x)).mdifferentiableAt hn), hu]
  rw [← hmap v v' hv, ← hmap w w' hw, hg]

variable [ContMDiffConstSMul I ∞ G M] [IsManifold I ∞ M]
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
  (hg : ∀ (a : G) (x : M) (v w : TangentSpace I x),
    g.inner (a • x) (mfderiv I I (a • ·) x v) (mfderiv I I (a • ·) x w) = g.inner x v w)

/-- The metric on the orbit space of a free, properly discontinuous smooth action of `G` by
isometries of `g`, descended from `g` along the orbit projection. -/
def quotient :
    ContMDiffRiemannianMetric I ∞ E (fun x : MulAction.orbitRel.Quotient G M ↦ TangentSpace I x) :=
  g.descend (TauCeti.isLocalDiffeomorph_quotientMk (n := ∞)) Quotient.mk_surjective
    (g.inner_eq_of_quotientMk_eq hg)

/-- The metric on the orbit space at the orbit of `x`, applied to the images of two tangent
vectors at `x`, is their inner product for `g`. -/
@[simp]
theorem quotient_inner_mfderiv (x : M) (v w : TangentSpace I x) :
    (g.quotient hg).inner (Quotient.mk _ x)
        (mfderiv I I (Quotient.mk (MulAction.orbitRel G M)) x v)
        (mfderiv I I (Quotient.mk (MulAction.orbitRel G M)) x w) =
      g.inner x v w :=
  g.descend_inner_mfderiv _ _ _ x v w

variable [FiniteDimensional ℝ E]

/-- Pulling the metric on the orbit space back along the orbit projection recovers `g`. -/
@[simp]
theorem pullback_quotient (hq : ContMDiff I I (∞ + 1) (Quotient.mk (MulAction.orbitRel G M)))
    (hinj : ∀ x, Injective (mfderiv I I (Quotient.mk (MulAction.orbitRel G M)) x)) :
    (g.quotient hg).pullback (Quotient.mk _) hq hinj = g :=
  g.pullback_descend _ _ _ hq hinj

/-- The metric on the orbit space is the unique metric on the orbit space whose pullback along
the orbit projection is `g`. -/
theorem pullback_eq_iff_eq_quotient
    (h : ContMDiffRiemannianMetric I ∞ E
      (fun x : MulAction.orbitRel.Quotient G M ↦ TangentSpace I x))
    (hq : ContMDiff I I (∞ + 1) (Quotient.mk (MulAction.orbitRel G M)))
    (hinj : ∀ x, Injective (mfderiv I I (Quotient.mk (MulAction.orbitRel G M)) x)) :
    h.pullback (Quotient.mk _) hq hinj = g ↔ h = g.quotient hg :=
  g.pullback_eq_iff_eq_descend _ _ _ h hq hinj

/-- The metric on the orbit space has the scalar curvature of `g`: at the orbit of `x` it is the
scalar curvature of `g` at `x`. -/
@[simp]
theorem scalarCurvature_quotient (x : M) :
    (g.quotient hg).scalarCurvature (Quotient.mk _ x) = g.scalarCurvature x :=
  g.scalarCurvature_descend _ _ _ x

end Quotient

end Bundle.ContMDiffRiemannianMetric
