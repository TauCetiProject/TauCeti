/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Geometry.Manifold.Riemannian.WarpedProd

/-!
# Products of Riemannian manifolds

The product `M × N` of two Riemannian manifolds carries the product Riemannian metric, in which
the inner product of tangent vectors `(v₁, v₂)` and `(w₁, w₂)` at `(x, y)` is
`⟪v₁, w₁⟫ + ⟪v₂, w₂⟫`: the two factors are orthogonal and each carries its own metric. This is
the warped product (`TauCeti.Geometry.Manifold.Riemannian.WarpedProd`) with constant warping
function `1`. This file constructs that metric as that case and shows that it is `C^n`,
respectively continuous, when the metrics of both factors are. Products such as `S² × ℝ` and
`ℍ² × ℝ` are among Thurston's model geometries, and isometries of products are in
`TauCeti.Geometry.Manifold.Riemannian.Isometry.Prod.Basic`.

## Main definitions

* `Bundle.RiemannianMetric.prodTangentSpace`: the product of two Riemannian metrics.
* `Bundle.ContMDiffRiemannianMetric.prodTangentSpace`: the product of two `C^n` Riemannian
  metrics, as a `C^n` Riemannian metric.
* `TauCeti.Manifold.instRiemannianBundleProd`,
  `TauCeti.Manifold.instIsContinuousRiemannianBundleProd`, and
  `TauCeti.Manifold.instIsContMDiffRiemannianBundleProd`: the corresponding instances, in the
  `TauCeti` scope; use `open scoped TauCeti` to install them.

## Main results

* `TauCeti.Manifold.inner_tangentSpace_prod`: the inner product of the product metric is the sum
  of the inner products of the components.
* `TauCeti.Manifold.isWarpedProduct_one`: the product metric is the warped product with warping
  function `1`.
* `TauCeti.Manifold.inner_tangentSpace_prod_mk_zero` and
  `TauCeti.Manifold.inner_tangentSpace_prod_zero_mk`: tangent vectors supported in one factor
  have that factor's inner product.
* `TauCeti.Manifold.tangentSpaceProdLinearIsometryEquiv`: in the product metric, the tangent space
  of `M × N` is isometric to the `L²` product of the tangent spaces of the factors.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, Chapter 2
  (product metrics).
-/

public section

open Bundle Bornology Manifold Set
open scoped Bundle ContDiff Manifold

noncomputable section

namespace Bundle.RiemannianMetric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

/-- The orthogonal sum of the inner products `g₁` on `T_{p.1} M` and `g₂` on `T_{p.2} N`, read on
the tangent space of `M × N` at `p`. -/
private def prodTangentInner (g₁ : RiemannianMetric (fun x : M ↦ TangentSpace I x))
    (g₂ : RiemannianMetric (fun y : N ↦ TangentSpace J y)) (p : M × N) :
    TangentSpace (I.prod J) p →L[ℝ] TangentSpace (I.prod J) p →L[ℝ] ℝ :=
  let e := TauCeti.Manifold.tangentSpaceProdEquiv (I := I) (J := J) p
  e.symm.arrowCongr (e.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))
    ((ContinuousLinearMap.coprodEquivL (S := ℝ)).toContinuousLinearMap.comp
      ((g₁.inner p.1).prodMap (g₂.inner p.2)))

private theorem prodTangentInner_apply (g₁ : RiemannianMetric (fun x : M ↦ TangentSpace I x))
    (g₂ : RiemannianMetric (fun y : N ↦ TangentSpace J y)) (p : M × N)
    (v w : TangentSpace (I.prod J) p) :
    prodTangentInner g₁ g₂ p v w =
      g₁.inner p.1 (TauCeti.Manifold.tangentSpaceProdEquiv p v).1
          (TauCeti.Manifold.tangentSpaceProdEquiv p w).1 +
        g₂.inner p.2 (TauCeti.Manifold.tangentSpaceProdEquiv p v).2
          (TauCeti.Manifold.tangentSpaceProdEquiv p w).2 :=
  (rfl)

/-- The warped product with warping function `1` has the inner product of the product metric. -/
private theorem warpedProdTangentSpace_one_inner
    (g₁ : RiemannianMetric (fun x : M ↦ TangentSpace I x))
    (g₂ : RiemannianMetric (fun y : N ↦ TangentSpace J y)) :
    (g₁.warpedProdTangentSpace (fun _ ↦ 1) (fun _ ↦ one_ne_zero) g₂).inner =
      prodTangentInner g₁ g₂ := by
  ext p v w
  rw [warpedProdTangentSpace_inner, prodTangentInner_apply, one_pow, one_mul]

/-- The product of Riemannian metrics `g₁` on `M` and `g₂` on `N`: the Riemannian metric on
`M × N` whose inner product of tangent vectors `(v₁, v₂)` and `(w₁, w₂)` at `(x, y)` is
`g₁ x v₁ w₁ + g₂ y v₂ w₂`. This is the warped product `warpedProdTangentSpace` with warping
function `1`, whose properties it inherits; its inner product drops the factor `1 ^ 2`, so that it
pairs the factors definitionally. -/
def prodTangentSpace (g₁ : RiemannianMetric (fun x : M ↦ TangentSpace I x))
    (g₂ : RiemannianMetric (fun y : N ↦ TangentSpace J y)) :
    RiemannianMetric (fun p : M × N ↦ TangentSpace (I.prod J) p) where
  inner := prodTangentInner g₁ g₂
  symm := warpedProdTangentSpace_one_inner g₁ g₂ ▸
    (g₁.warpedProdTangentSpace (fun _ ↦ 1) (fun _ ↦ one_ne_zero) g₂).symm
  pos := warpedProdTangentSpace_one_inner g₁ g₂ ▸
    (g₁.warpedProdTangentSpace (fun _ ↦ 1) (fun _ ↦ one_ne_zero) g₂).pos
  continuousAt := warpedProdTangentSpace_one_inner g₁ g₂ ▸
    (g₁.warpedProdTangentSpace (fun _ ↦ 1) (fun _ ↦ one_ne_zero) g₂).continuousAt
  isVonNBounded := warpedProdTangentSpace_one_inner g₁ g₂ ▸
    (g₁.warpedProdTangentSpace (fun _ ↦ 1) (fun _ ↦ one_ne_zero) g₂).isVonNBounded

/-- The product metric pairs tangent vectors factor by factor. -/
@[simp]
theorem prodTangentSpace_inner (g₁ : RiemannianMetric (fun x : M ↦ TangentSpace I x))
    (g₂ : RiemannianMetric (fun y : N ↦ TangentSpace J y)) (p : M × N)
    (v w : TangentSpace (I.prod J) p) :
    (g₁.prodTangentSpace g₂).inner p v w =
      g₁.inner p.1 (TauCeti.Manifold.tangentSpaceProdEquiv p v).1
          (TauCeti.Manifold.tangentSpaceProdEquiv p w).1 +
        g₂.inner p.2 (TauCeti.Manifold.tangentSpaceProdEquiv p v).2
          (TauCeti.Manifold.tangentSpaceProdEquiv p w).2 :=
  (rfl)

end Bundle.RiemannianMetric

namespace Bundle.ContMDiffRiemannianMetric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N] {n : ℕ∞ω}

/-- The product of `C^n` Riemannian metrics on `M` and `N` is a `C^n` Riemannian metric on
`M × N`. -/
def prodTangentSpace (g₁ : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (g₂ : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y)) :
    ContMDiffRiemannianMetric (I.prod J) n (E × F) (fun p : M × N ↦ TangentSpace (I.prod J) p) :=
  { g₁.toRiemannianMetric.prodTangentSpace g₂.toRiemannianMetric with
  contMDiff := by
    have h := (g₁.warpedProdTangentSpace (fun _ ↦ 1) contMDiff_const (fun _ ↦ one_ne_zero)
      g₂).contMDiff
    have e : (g₁.warpedProdTangentSpace (fun _ ↦ 1) contMDiff_const (fun _ ↦ one_ne_zero)
        g₂).inner = (g₁.toRiemannianMetric.prodTangentSpace g₂.toRiemannianMetric).inner := by
      ext p v w
      rw [warpedProdTangentSpace_inner, RiemannianMetric.prodTangentSpace_inner, one_pow, one_mul]
      -- The two sides now differ only by `gᵢ.toRiemannianMetric.inner = gᵢ.inner`, which holds
      -- by definition of `ContMDiffRiemannianMetric.toRiemannianMetric`.
      rfl
    rwa [e] at h
  }

/-- The product of `C^n` Riemannian metrics pairs tangent vectors factor by factor. -/
@[simp]
theorem prodTangentSpace_inner
    (g₁ : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (g₂ : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y)) (p : M × N)
    (v w : TangentSpace (I.prod J) p) :
    (g₁.prodTangentSpace g₂).inner p v w =
      g₁.inner p.1 (TauCeti.Manifold.tangentSpaceProdEquiv p v).1
          (TauCeti.Manifold.tangentSpaceProdEquiv p w).1 +
        g₂.inner p.2 (TauCeti.Manifold.tangentSpaceProdEquiv p v).2
          (TauCeti.Manifold.tangentSpaceProdEquiv p w).2 :=
  (rfl)

/-- Forgetting smoothness after taking the product of two `C^n` Riemannian metrics gives the
product of the underlying Riemannian metrics. -/
@[simp]
theorem prodTangentSpace_toRiemannianMetric
    (g₁ : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (g₂ : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y)) :
    (g₁.prodTangentSpace g₂).toRiemannianMetric =
      g₁.toRiemannianMetric.prodTangentSpace g₂.toRiemannianMetric :=
  (rfl)

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

/-- A product of Riemannian manifolds carries the product Riemannian metric. -/
@[instance_reducible]
noncomputable def instRiemannianBundleProd :
    RiemannianBundle (fun p : M × N ↦ TangentSpace (I.prod J) p) :=
  ⟨RiemannianBundle.g.prodTangentSpace RiemannianBundle.g⟩

scoped[TauCeti] attribute [instance] Manifold.instRiemannianBundleProd

/-- The metric installed on a product is the product of the metrics of the factors. -/
@[simp]
theorem riemannianBundleProd_g :
    RiemannianBundle.g (E := fun p : M × N ↦ TangentSpace (I.prod J) p) =
      (RiemannianBundle.g (E := fun x : M ↦ TangentSpace I x)).prodTangentSpace
        (RiemannianBundle.g (E := fun y : N ↦ TangentSpace J y)) :=
  (rfl)

/-- In the product metric, the inner product of two tangent vectors is the sum of the inner
products of their components. -/
@[simp]
theorem inner_tangentSpace_prod (p : M × N) (v w : TangentSpace (I.prod J) p) :
    inner ℝ v w =
      inner ℝ (tangentSpaceProdEquiv p v).1 (tangentSpaceProdEquiv p w).1 +
        inner ℝ (tangentSpaceProdEquiv p v).2 (tangentSpaceProdEquiv p w).2 :=
  (rfl)

/-- The product metric is the warped product with the constant warping function `1`. -/
theorem isWarpedProduct_one : IsWarpedProduct I J N (fun _ : M ↦ (1 : ℝ)) :=
  ⟨fun p v w ↦ by rw [inner_tangentSpace_prod, one_pow, one_mul]⟩

/-- The product metric is continuous when the metrics of both factors are. -/
theorem instIsContinuousRiemannianBundleProd [IsManifold I 1 M] [IsManifold J 1 N]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle F (fun y : N ↦ TangentSpace J y)] :
    IsContinuousRiemannianBundle (E × F) (fun p : M × N ↦ TangentSpace (I.prod J) p) := by
  let _ : IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  let _ : IsContMDiffRiemannianBundle J 0 F (fun y : N ↦ TangentSpace J y) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  have := (isWarpedProduct_one (I := I) (J := J) (M := M) (N := N)).isContMDiffRiemannianBundle
    (n := 0) contMDiff_const
  exact IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I.prod J) (n := 0)

scoped[TauCeti] attribute [instance] Manifold.instIsContinuousRiemannianBundleProd

/-- The product metric is `C^n` when the metrics of both factors are. -/
theorem instIsContMDiffRiemannianBundleProd {n : ℕ∞ω} [IsManifold I 1 M] [IsManifold J 1 N]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle J n F (fun y : N ↦ TangentSpace J y)] :
    IsContMDiffRiemannianBundle (I.prod J) n (E × F)
      (fun p : M × N ↦ TangentSpace (I.prod J) p) :=
  isWarpedProduct_one.isContMDiffRiemannianBundle contMDiff_const

scoped[TauCeti] attribute [instance] Manifold.instIsContMDiffRiemannianBundleProd

/-- Tangent vectors supported in the first factor have that factor's inner product. -/
@[simp]
theorem inner_tangentSpace_prod_mk_zero (p : M × N) (v w : TangentSpace I p.1) :
    inner ℝ (E := TangentSpace (I.prod J) p)
      ((v, 0) : TangentSpace I p.1 × TangentSpace J p.2)
      ((w, 0) : TangentSpace I p.1 × TangentSpace J p.2) = inner ℝ v w := by
  have h := inner_tangentSpace_prod p
    ((tangentSpaceProdEquiv (I := I) (J := J) p).symm (v, 0))
    ((tangentSpaceProdEquiv (I := I) (J := J) p).symm (w, 0))
  simp only [ContinuousLinearEquiv.apply_symm_apply, inner_zero_left, add_zero] at h
  simpa only [tangentSpaceProdEquiv_symm_apply] using h

/-- Tangent vectors supported in the second factor have that factor's inner product. -/
@[simp]
theorem inner_tangentSpace_prod_zero_mk (p : M × N) (v w : TangentSpace J p.2) :
    inner ℝ (E := TangentSpace (I.prod J) p)
      ((0, v) : TangentSpace I p.1 × TangentSpace J p.2)
      ((0, w) : TangentSpace I p.1 × TangentSpace J p.2) = inner ℝ v w := by
  have h := inner_tangentSpace_prod p
    ((tangentSpaceProdEquiv (I := I) (J := J) p).symm (0, v))
    ((tangentSpaceProdEquiv (I := I) (J := J) p).symm (0, w))
  simp only [ContinuousLinearEquiv.apply_symm_apply, inner_zero_left, zero_add] at h
  simpa only [tangentSpaceProdEquiv_symm_apply] using h

/-- In the product metric, the tangent space of `M × N` at `p` is isometric to the `L²` product of
the tangent spaces of the factors, via the canonical identification `tangentSpaceProdEquiv`.
Orthonormal bases of the two factors therefore combine into an orthonormal basis of the product
(`OrthonormalBasis.prod`). -/
def tangentSpaceProdLinearIsometryEquiv (p : M × N) :
    TangentSpace (I.prod J) p ≃ₗᵢ[ℝ] WithLp 2 (TangentSpace I p.1 × TangentSpace J p.2) :=
  ((tangentSpaceProdEquiv p).toLinearEquiv.trans
    (WithLp.linearEquiv 2 ℝ (TangentSpace I p.1 × TangentSpace J p.2)).symm).isometryOfInner
    fun v w ↦ by simp [WithLp.coe_symm_linearEquiv]

@[simp]
theorem tangentSpaceProdLinearIsometryEquiv_apply (p : M × N) (v : TangentSpace (I.prod J) p) :
    tangentSpaceProdLinearIsometryEquiv p v = WithLp.toLp 2 (tangentSpaceProdEquiv p v) :=
  (rfl)

@[simp]
theorem tangentSpaceProdLinearIsometryEquiv_symm_apply (p : M × N)
    (v : WithLp 2 (TangentSpace I p.1 × TangentSpace J p.2)) :
    (tangentSpaceProdLinearIsometryEquiv p).symm v = (tangentSpaceProdEquiv p).symm v.ofLp :=
  (rfl)

end TauCeti.Manifold
