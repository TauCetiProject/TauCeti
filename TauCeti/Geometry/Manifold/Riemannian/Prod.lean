/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LocallyConvex.Bounded
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent

/-!
# Products of Riemannian manifolds

The product `M × N` of two Riemannian manifolds carries the product Riemannian metric, in which
the inner product of tangent vectors `(v₁, v₂)` and `(w₁, w₂)` at `(x, y)` is
`⟪v₁, w₁⟫ + ⟪v₂, w₂⟫`: the two factors are orthogonal and each carries its own metric. This file
constructs that metric and shows that it is `C^n`, respectively continuous, when the metrics of
both factors are. Products such as `S² × ℝ` and `ℍ² × ℝ` are among Thurston's model geometries,
and isometries of products are in `TauCeti.Geometry.Manifold.Riemannian.Isometry.Prod`.

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

/-- The product of Riemannian metrics `g₁` on `M` and `g₂` on `N`: the Riemannian metric on
`M × N` whose inner product of tangent vectors `(v₁, v₂)` and `(w₁, w₂)` at `(x, y)` is
`g₁ x v₁ w₁ + g₂ y v₂ w₂`. -/
def prodTangentSpace (g₁ : RiemannianMetric (fun x : M ↦ TangentSpace I x))
    (g₂ : RiemannianMetric (fun y : N ↦ TangentSpace J y)) :
    RiemannianMetric (fun p : M × N ↦ TangentSpace (I.prod J) p) where
  inner := prodTangentInner g₁ g₂
  symm p v w := by
    rw [prodTangentInner_apply, prodTangentInner_apply, g₁.symm, g₂.symm]
  pos p v hv := by
    set e := TauCeti.Manifold.tangentSpaceProdEquiv (I := I) (J := J) p
    rw [prodTangentInner_apply]
    have hev : e v ≠ 0 := e.toLinearEquiv.map_ne_zero_iff.mpr hv
    rcases eq_or_ne (e v).1 0 with h₁ | h₁
    · have h₂ : (e v).2 ≠ 0 := fun h₂ ↦ hev (Prod.ext h₁ h₂)
      rw [h₁, map_zero, zero_add]
      exact g₂.pos p.2 _ h₂
    · exact add_pos_of_pos_of_nonneg (g₁.pos p.1 _ h₁) ((g₂.toCore p.2).re_inner_nonneg _)
  continuousAt p := by
    set e := TauCeti.Manifold.tangentSpaceProdEquiv (I := I) (J := J) p
    have h₁ : ContinuousAt (fun v ↦ g₁.inner p.1 (e v).1 (e v).1) 0 :=
      (g₁.continuousAt p.1).comp_of_eq (continuous_fst.comp e.continuous).continuousAt
        (by simp)
    have h₂ : ContinuousAt (fun v ↦ g₂.inner p.2 (e v).2 (e v).2) 0 :=
      (g₂.continuousAt p.2).comp_of_eq (continuous_snd.comp e.continuous).continuousAt
        (by simp)
    simp only [prodTangentInner_apply]
    exact h₁.add h₂
  isVonNBounded p := by
    set e := TauCeti.Manifold.tangentSpaceProdEquiv (I := I) (J := J) p
    refine (((g₁.isVonNBounded p.1).prod (g₂.isVonNBounded p.2)).image
      e.symm.toContinuousLinearMap).subset ?_
    intro v hv
    rw [mem_ofPred_eq, prodTangentInner_apply] at hv
    refine ⟨e v, ⟨?_, ?_⟩, e.symm_apply_apply v⟩
    · exact lt_of_le_of_lt (le_add_of_nonneg_right ((g₂.toCore p.2).re_inner_nonneg _)) hv
    · exact lt_of_le_of_lt (le_add_of_nonneg_left ((g₁.toCore p.1).re_inner_nonneg _)) hv

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
  contMDiff p₀ := by
    rw [contMDiffAt_section]
    have h₁ := g₁.contMDiff p₀.1
    have h₂ := g₂.contMDiff p₀.2
    rw [contMDiffAt_section] at h₁ h₂
    have h := contMDiffAt_const (c := (ContinuousLinearMap.coprodEquivL ℝ :
        ((E →L[ℝ] ℝ) × (F →L[ℝ] ℝ)) ≃L[ℝ] (E × F →L[ℝ] ℝ)).toContinuousLinearMap)
      |>.clm_comp ((h₁.comp p₀ contMDiffAt_fst).clm_prodMap (h₂.comp p₀ contMDiffAt_snd))
    apply h.congr_of_eventuallyEq
    filter_upwards [(trivializationAt (E × F) (TangentSpace (I.prod J) : M × N → Type _)
      p₀).open_baseSet.mem_nhds (mem_baseSet_trivializationAt (E × F)
        (TangentSpace (I.prod J) : M × N → Type _) p₀)] with q hq
    have hq₁ : q.1 ∈ (trivializationAt E (TangentSpace I : M → Type _) p₀.1).baseSet := by
      simp only [TangentBundle.trivializationAt_baseSet] at hq ⊢
      exact hq.1
    have hq₂ : q.2 ∈ (trivializationAt F (TangentSpace J : N → Type _) p₀.2).baseSet := by
      simp only [TangentBundle.trivializationAt_baseSet] at hq ⊢
      exact hq.2
    refine ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext fun w ↦ ?_
    simp only [hom_trivializationAt_apply]
    rw [inCoordinates_apply_eq₂ hq hq (by simp)]
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_prodMap', ContinuousLinearEquiv.coe_coe, Prod.map_fst, Prod.map_snd,
      ContinuousLinearMap.coprodEquivL_apply_apply]
    rw [inCoordinates_apply_eq₂ hq₁ hq₁ (by simp), inCoordinates_apply_eq₂ hq₂ hq₂ (by simp)]
    simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
      LinearMap.id_apply, RiemannianMetric.prodTangentSpace_inner]
    rw [← Trivialization.symmL_apply (R := ℝ) _ hq, ← Trivialization.symmL_apply (R := ℝ) _ hq,
      ← Trivialization.symmL_apply (R := ℝ) _ hq₁, ← Trivialization.symmL_apply (R := ℝ) _ hq₁,
      ← Trivialization.symmL_apply (R := ℝ) _ hq₂, ← Trivialization.symmL_apply (R := ℝ) _ hq₂]
    have hq' : q ∈ (chartAt (ModelProd H G) p₀).source := by simpa using hq
    rw [TauCeti.Manifold.tangentSpaceProdEquiv_symmL_trivializationAt hq',
      TauCeti.Manifold.tangentSpaceProdEquiv_symmL_trivializationAt hq']
    -- The two sides now differ only by `gᵢ.toRiemannianMetric.inner = gᵢ.inner`, which holds by
    -- definition of `ContMDiffRiemannianMetric.toRiemannianMetric`.
    rfl
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

/-- The product metric is continuous when the metrics of both factors are. -/
theorem instIsContinuousRiemannianBundleProd [IsManifold I 1 M] [IsManifold J 1 N]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle F (fun y : N ↦ TangentSpace J y)] :
    IsContinuousRiemannianBundle (E × F) (fun p : M × N ↦ TangentSpace (I.prod J) p) := by
  let _ : IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  let _ : IsContMDiffRiemannianBundle J 0 F (fun y : N ↦ TangentSpace J y) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  let g := (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := I) (n := 0) (F := E)
    (V := fun x : M ↦ TangentSpace I x)).prodTangentSpace
      (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := J) (n := 0) (F := F)
        (V := fun y : N ↦ TangentSpace J y))
  refine ⟨g.inner, g.contMDiff.continuous, fun p v w ↦ ?_⟩
  rw [ContMDiffRiemannianMetric.prodTangentSpace_inner,
    ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner,
    ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]
  -- The fiber inner product of a `RiemannianBundle` is by definition its metric, here the product
  -- of the two factor metrics.
  rfl

scoped[TauCeti] attribute [instance] Manifold.instIsContinuousRiemannianBundleProd

/-- The product metric is `C^n` when the metrics of both factors are. -/
theorem instIsContMDiffRiemannianBundleProd {n : ℕ∞ω} [IsManifold I 1 M] [IsManifold J 1 N]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle J n F (fun y : N ↦ TangentSpace J y)] :
    IsContMDiffRiemannianBundle (I.prod J) n (E × F)
      (fun p : M × N ↦ TangentSpace (I.prod J) p) := by
  let g := (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := I) (n := n) (F := E)
    (V := fun x : M ↦ TangentSpace I x)).prodTangentSpace
      (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := J) (n := n) (F := F)
        (V := fun y : N ↦ TangentSpace J y))
  refine ⟨g.inner, g.contMDiff, fun p v w ↦ ?_⟩
  rw [ContMDiffRiemannianMetric.prodTangentSpace_inner,
    ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner,
    ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]
  -- The fiber inner product of a `RiemannianBundle` is by definition its metric, here the product
  -- of the two factor metrics.
  rfl

scoped[TauCeti] attribute [instance] Manifold.instIsContMDiffRiemannianBundleProd

/-- In the product metric, the inner product of two tangent vectors is the sum of the inner
products of their components. -/
@[simp]
theorem inner_tangentSpace_prod (p : M × N) (v w : TangentSpace (I.prod J) p) :
    inner ℝ v w =
      inner ℝ (tangentSpaceProdEquiv p v).1 (tangentSpaceProdEquiv p w).1 +
        inner ℝ (tangentSpaceProdEquiv p v).2 (tangentSpaceProdEquiv p w).2 :=
  (rfl)

end TauCeti.Manifold
