/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import TauCeti.Analysis.LocallyConvex.Bounded
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Warped products of Riemannian manifolds

Given Riemannian manifolds `M` and `N` and a nowhere vanishing function `f : M → ℝ`, the
*warped product* `M ×_f N` is `M × N` with the Riemannian metric

`⟪(u₁, u₂), (v₁, v₂)⟫ = ⟪u₁, v₁⟫ + f(x)² ⟪u₂, v₂⟫`

at `(x, y)`. The fibres `{x} × N` are copies of `N` rescaled by the constant `f(x)²`, the
horizontal slices `M × {y}` are isometric copies of `M`, and the two are orthogonal. A constant
warping function `f = 1` gives the product metric, which
`TauCeti.Geometry.Manifold.Riemannian.Prod` constructs as that case. Warped products are the
standard models of rotationally symmetric metrics: the Euclidean metric away from the origin is
`(0, ∞) ×_r S^(n-1)`, the round sphere minus two antipodal points is `(0, π) ×_(sin r) S^(n-1)`,
and hyperbolic space minus a point is `(0, ∞) ×_(sinh r) S^(n-1)`.

The predicate `TauCeti.Manifold.IsWarpedProduct I J N f` says that the Riemannian metric installed
on `M × N` is the warped product of the metrics installed on the factors. Geometric quantities of a
warped product, such as its Levi-Civita connection, are computed for any metric satisfying it, so
that they apply both to the construction below and to any metric shown to have the warped form.

## Main definitions

* `Bundle.RiemannianMetric.warpedProdTangentSpace`: the warped product of two Riemannian metrics
  with a nowhere vanishing warping function.
* `Bundle.ContMDiffRiemannianMetric.warpedProdTangentSpace`: the warped product of two `C^n`
  Riemannian metrics with a nowhere vanishing `C^n` warping function, as a `C^n` Riemannian
  metric.
* `TauCeti.Manifold.IsWarpedProduct`: the metric of `M × N` is the warped product of the metrics
  of `M` and `N` with warping function `f`.

## Main results

* `TauCeti.Manifold.isWarpedProduct_of_eq`: the warped product metric is a warped product.
* `TauCeti.Manifold.IsWarpedProduct.isContMDiffRiemannianBundle`: a warped product of `C^n`
  metrics with a `C^n` warping function is `C^n`.

## References

* R. L. Bishop and B. O'Neill, *Manifolds of negative curvature*, Trans. Amer. Math. Soc. 145
  (1969), 1–49, Section 7.
* B. O'Neill, *Semi-Riemannian Geometry*, Academic Press (1983), Chapter 7.
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

/-- The orthogonal sum of the inner product `g₁` on `T_{p.1} M` and the inner product `g₂` on
`T_{p.2} N` rescaled by `f(p.1)²`, read on the tangent space of `M × N` at `p`. -/
private def warpedProdTangentInner (g₁ : RiemannianMetric (fun x : M ↦ TangentSpace I x))
    (f : M → ℝ) (g₂ : RiemannianMetric (fun y : N ↦ TangentSpace J y)) (p : M × N) :
    TangentSpace (I.prod J) p →L[ℝ] TangentSpace (I.prod J) p →L[ℝ] ℝ :=
  let e := TauCeti.Manifold.tangentSpaceProdEquiv (I := I) (J := J) p
  e.symm.arrowCongr (e.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))
    ((ContinuousLinearMap.coprodEquivL (S := ℝ)).toContinuousLinearMap.comp
      ((g₁.inner p.1).prodMap (f p.1 ^ 2 • g₂.inner p.2)))

private theorem warpedProdTangentInner_apply
    (g₁ : RiemannianMetric (fun x : M ↦ TangentSpace I x)) (f : M → ℝ)
    (g₂ : RiemannianMetric (fun y : N ↦ TangentSpace J y)) (p : M × N)
    (v w : TangentSpace (I.prod J) p) :
    warpedProdTangentInner g₁ f g₂ p v w =
      g₁.inner p.1 (TauCeti.Manifold.tangentSpaceProdEquiv p v).1
          (TauCeti.Manifold.tangentSpaceProdEquiv p w).1 +
        f p.1 ^ 2 * g₂.inner p.2 (TauCeti.Manifold.tangentSpaceProdEquiv p v).2
          (TauCeti.Manifold.tangentSpaceProdEquiv p w).2 :=
  (rfl)

/-- The warped product of Riemannian metrics `g₁` on `M` and `g₂` on `N` with a nowhere vanishing
warping function `f : M → ℝ`: the Riemannian metric on `M × N` whose inner product of tangent
vectors `(v₁, v₂)` and `(w₁, w₂)` at `(x, y)` is `g₁ x v₁ w₁ + f(x)² g₂ y v₂ w₂`. -/
def warpedProdTangentSpace (g₁ : RiemannianMetric (fun x : M ↦ TangentSpace I x))
    (f : M → ℝ) (hf : ∀ x, f x ≠ 0) (g₂ : RiemannianMetric (fun y : N ↦ TangentSpace J y)) :
    RiemannianMetric (fun p : M × N ↦ TangentSpace (I.prod J) p) where
  inner := warpedProdTangentInner g₁ f g₂
  symm p v w := by
    rw [warpedProdTangentInner_apply, warpedProdTangentInner_apply, g₁.symm, g₂.symm]
  pos p v hv := by
    set e := TauCeti.Manifold.tangentSpaceProdEquiv (I := I) (J := J) p
    rw [warpedProdTangentInner_apply]
    have hev : e v ≠ 0 := e.toLinearEquiv.map_ne_zero_iff.mpr hv
    have hf₂ : 0 < f p.1 ^ 2 := pow_pos (abs_pos.mpr (hf p.1)) 2 |>.trans_eq (sq_abs _)
    rcases eq_or_ne (e v).1 0 with h₁ | h₁
    · have h₂ : (e v).2 ≠ 0 := fun h₂ ↦ hev (Prod.ext h₁ h₂)
      rw [h₁, map_zero, zero_add]
      exact mul_pos hf₂ (g₂.pos p.2 _ h₂)
    · exact add_pos_of_pos_of_nonneg (g₁.pos p.1 _ h₁)
        (mul_nonneg hf₂.le ((g₂.toCore p.2).re_inner_nonneg _))
  continuousAt p := by
    set e := TauCeti.Manifold.tangentSpaceProdEquiv (I := I) (J := J) p
    have h₁ : ContinuousAt (fun v ↦ g₁.inner p.1 (e v).1 (e v).1) 0 :=
      (g₁.continuousAt p.1).comp_of_eq (continuous_fst.comp e.continuous).continuousAt
        (by simp)
    have h₂ : ContinuousAt (fun v ↦ g₂.inner p.2 (e v).2 (e v).2) 0 :=
      (g₂.continuousAt p.2).comp_of_eq (continuous_snd.comp e.continuous).continuousAt
        (by simp)
    simp only [warpedProdTangentInner_apply]
    exact h₁.add (continuousAt_const.mul h₂)
  isVonNBounded p := by
    -- The unit ball is contained in the image of the product of the unit balls of `g₁` and `g₂`
    -- under `(v₁, v₂) ↦ (v₁, |f(p.1)|⁻¹ v₂)`.
    set e := TauCeti.Manifold.tangentSpaceProdEquiv (I := I) (J := J) p
    set c := |f p.1|
    have hc : 0 < c := abs_pos.mpr (hf p.1)
    refine (((g₁.isVonNBounded p.1).prod (g₂.isVonNBounded p.2)).image
      (e.symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.id ℝ _).prodMap (c⁻¹ • ContinuousLinearMap.id ℝ _)))).subset ?_
    intro v hv
    rw [mem_ofPred_eq, warpedProdTangentInner_apply] at hv
    have hc2 : c * c = f p.1 ^ 2 := by rw [← sq, sq_abs]
    refine ⟨((e v).1, c • (e v).2), ⟨?_, ?_⟩, ?_⟩
    · exact lt_of_le_of_lt (le_add_of_nonneg_right
        (mul_nonneg (sq_nonneg _) ((g₂.toCore p.2).re_inner_nonneg _))) hv
    · have hle : f p.1 ^ 2 * g₂.inner p.2 (e v).2 (e v).2 < 1 :=
        lt_of_le_of_lt (le_add_of_nonneg_left ((g₁.toCore p.1).re_inner_nonneg _)) hv
      simp only [mem_ofPred_eq, map_smul, smul_apply, smul_eq_mul]
      rwa [← mul_assoc, hc2]
    · simp [smul_smul, inv_mul_cancel₀ hc.ne']

/-- The warped product metric pairs tangent vectors factor by factor, with the second factor
rescaled by the square of the warping function. -/
@[simp]
theorem warpedProdTangentSpace_inner (g₁ : RiemannianMetric (fun x : M ↦ TangentSpace I x))
    (f : M → ℝ) (hf : ∀ x, f x ≠ 0) (g₂ : RiemannianMetric (fun y : N ↦ TangentSpace J y))
    (p : M × N) (v w : TangentSpace (I.prod J) p) :
    (g₁.warpedProdTangentSpace f hf g₂).inner p v w =
      g₁.inner p.1 (TauCeti.Manifold.tangentSpaceProdEquiv p v).1
          (TauCeti.Manifold.tangentSpaceProdEquiv p w).1 +
        f p.1 ^ 2 * g₂.inner p.2 (TauCeti.Manifold.tangentSpaceProdEquiv p v).2
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

/-- The warped inner product of `C^n` Riemannian metrics with a `C^n` warping function is a `C^n`
section. No nonvanishing hypothesis on the warping function is needed. -/
private theorem contMDiff_warpedProdTangentInner
    (g₁ : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) n f)
    (g₂ : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y)) :
    ContMDiff (I.prod J) ((I.prod J).prod 𝓘(ℝ, E × F →L[ℝ] E × F →L[ℝ] ℝ)) n
      (fun p ↦ TotalSpace.mk' (E × F →L[ℝ] E × F →L[ℝ] ℝ) p
        (RiemannianMetric.warpedProdTangentInner g₁.toRiemannianMetric f g₂.toRiemannianMetric
          p)) :=
  fun p₀ ↦ by
    rw [contMDiffAt_section_iff]
    have h₁ := g₁.contMDiff p₀.1
    have h₂ := g₂.contMDiff p₀.2
    rw [contMDiffAt_section_iff] at h₁ h₂
    have hf₂ : ContMDiffAt (I.prod J) 𝓘(ℝ) n (fun q : M × N ↦ f q.1 ^ 2) p₀ :=
      ((hf p₀.1).comp p₀ contMDiffAt_fst).pow 2
    have h := contMDiffAt_const (c := (ContinuousLinearMap.coprodEquivL ℝ :
        ((E →L[ℝ] ℝ) × (F →L[ℝ] ℝ)) ≃L[ℝ] (E × F →L[ℝ] ℝ)).toContinuousLinearMap)
      |>.clm_comp ((h₁.comp p₀ contMDiffAt_fst).clm_prodMap
        (hf₂.smul (h₂.comp p₀ contMDiffAt_snd)))
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
      ContinuousLinearMap.coprodEquivL_apply_apply, Pi.smul_apply', smul_apply, smul_eq_mul]
    rw [inCoordinates_apply_eq₂ hq₁ hq₁ (by simp), inCoordinates_apply_eq₂ hq₂ hq₂ (by simp)]
    simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
      LinearMap.id_apply, RiemannianMetric.warpedProdTangentInner_apply]
    rw [← Trivialization.symmL_apply (R := ℝ) _ hq, ← Trivialization.symmL_apply (R := ℝ) _ hq,
      ← Trivialization.symmL_apply (R := ℝ) _ hq₁, ← Trivialization.symmL_apply (R := ℝ) _ hq₁,
      ← Trivialization.symmL_apply (R := ℝ) _ hq₂, ← Trivialization.symmL_apply (R := ℝ) _ hq₂]
    have hq' : q ∈ (chartAt (ModelProd H G) p₀).source := by simpa using hq
    rw [TauCeti.Manifold.tangentSpaceProdEquiv_symmL_trivializationAt hq',
      TauCeti.Manifold.tangentSpaceProdEquiv_symmL_trivializationAt hq']
    -- The two sides now differ only by `gᵢ.toRiemannianMetric.inner = gᵢ.inner`, which holds by
    -- definition of `ContMDiffRiemannianMetric.toRiemannianMetric`.
    rfl

/-- The warped product of `C^n` Riemannian metrics on `M` and `N` with a nowhere vanishing `C^n`
warping function `f : M → ℝ` is a `C^n` Riemannian metric on `M × N`. -/
def warpedProdTangentSpace (g₁ : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) n f) (hf₀ : ∀ x, f x ≠ 0)
    (g₂ : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y)) :
    ContMDiffRiemannianMetric (I.prod J) n (E × F) (fun p : M × N ↦ TangentSpace (I.prod J) p) :=
  { g₁.toRiemannianMetric.warpedProdTangentSpace f hf₀ g₂.toRiemannianMetric with
    contMDiff := contMDiff_warpedProdTangentInner g₁ hf g₂ }

/-- The warped product of `C^n` Riemannian metrics pairs tangent vectors factor by factor, with
the second factor rescaled by the square of the warping function. -/
@[simp]
theorem warpedProdTangentSpace_inner
    (g₁ : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) n f) (hf₀ : ∀ x, f x ≠ 0)
    (g₂ : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y)) (p : M × N)
    (v w : TangentSpace (I.prod J) p) :
    (g₁.warpedProdTangentSpace f hf hf₀ g₂).inner p v w =
      g₁.inner p.1 (TauCeti.Manifold.tangentSpaceProdEquiv p v).1
          (TauCeti.Manifold.tangentSpaceProdEquiv p w).1 +
        f p.1 ^ 2 * g₂.inner p.2 (TauCeti.Manifold.tangentSpaceProdEquiv p v).2
          (TauCeti.Manifold.tangentSpaceProdEquiv p w).2 :=
  (rfl)

/-- Forgetting smoothness after taking the warped product of two `C^n` Riemannian metrics gives
the warped product of the underlying Riemannian metrics. -/
@[simp]
theorem warpedProdTangentSpace_toRiemannianMetric
    (g₁ : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) n f) (hf₀ : ∀ x, f x ≠ 0)
    (g₂ : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y)) :
    (g₁.warpedProdTangentSpace f hf hf₀ g₂).toRiemannianMetric =
      g₁.toRiemannianMetric.warpedProdTangentSpace f hf₀ g₂.toRiemannianMetric :=
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

variable (I J N) in
/-- The Riemannian metric installed on `M × N` is the **warped product** of the metrics of `M`
and `N` with warping function `f : M → ℝ`: at `(x, y)` the inner product of `(u₁, u₂)` and
`(v₁, v₂)` is `⟪u₁, v₁⟫ + f(x)² ⟪u₂, v₂⟫`. -/
structure IsWarpedProduct [RiemannianBundle (fun p : M × N ↦ TangentSpace (I.prod J) p)]
    (f : M → ℝ) : Prop where
  /-- The inner product of the warped product. -/
  inner_eq (p : M × N) (v w : TangentSpace (I.prod J) p) :
    inner ℝ v w = inner ℝ (tangentSpaceProdEquiv p v).1 (tangentSpaceProdEquiv p w).1 +
      f p.1 ^ 2 * inner ℝ (tangentSpaceProdEquiv p v).2 (tangentSpaceProdEquiv p w).2

/-- A metric on `M × N` equal to the warped product metric
`Bundle.RiemannianMetric.warpedProdTangentSpace` of the metrics of `M` and `N` is a warped
product. -/
theorem isWarpedProduct_of_eq [RiemannianBundle (fun p : M × N ↦ TangentSpace (I.prod J) p)]
    {f : M → ℝ} (hf : ∀ x, f x ≠ 0)
    (hg : (RiemannianBundle.g : RiemannianMetric (fun p : M × N ↦ TangentSpace (I.prod J) p)) =
      RiemannianBundle.g.warpedProdTangentSpace f hf RiemannianBundle.g) :
    IsWarpedProduct I J N f :=
  -- The inner product of a fibre is by definition the installed metric `RiemannianBundle.g`.
  ⟨fun p v w ↦ congrArg (fun g : RiemannianMetric _ ↦ g.inner p v w) hg⟩

variable [IsManifold I 1 M] [IsManifold J 1 N]
  [RiemannianBundle (fun p : M × N ↦ TangentSpace (I.prod J) p)]

/-- A warped product of `C^n` metrics with a `C^n` warping function is a `C^n` metric. -/
theorem IsWarpedProduct.isContMDiffRiemannianBundle {n : ℕ∞ω} {f : M → ℝ}
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle J n F (fun y : N ↦ TangentSpace J y)]
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) n f) :
    IsContMDiffRiemannianBundle (I.prod J) n (E × F)
      (fun p : M × N ↦ TangentSpace (I.prod J) p) := by
  refine ⟨_, ContMDiffRiemannianMetric.contMDiff_warpedProdTangentInner
    (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := I) (n := n) (F := E)
      (V := fun x : M ↦ TangentSpace I x)) hf
    (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := J) (n := n) (F := F)
      (V := fun y : N ↦ TangentSpace J y)), fun p v w ↦ ?_⟩
  rw [h.inner_eq, RiemannianMetric.warpedProdTangentInner_apply]
  simp only [ContMDiffRiemannianMetric.toRiemannianMetric,
    ContinuousRiemannianMetric.toRiemannianMetric,
    ContMDiffRiemannianMetric.toContinuousRiemannianMetric,
    ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]
  -- The fiber inner products of the factors are by definition their installed metrics.
  rfl

end TauCeti.Manifold
