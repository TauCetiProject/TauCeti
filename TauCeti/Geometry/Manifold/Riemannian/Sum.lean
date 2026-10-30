/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import TauCeti.Geometry.Manifold.VectorBundle.Tangent

/-!
# Disjoint unions of Riemannian manifolds

The disjoint union `M ⊕ M'` of two manifolds modelled on the same space carries the Riemannian
metric which is a given metric `g₁` on `M` and a given metric `g₂` on `M'`. This file constructs
that metric and shows that it is `C^n` when `g₁` and `g₂` are. Each summand is open in `M ⊕ M'`
and its charts are those of the summand, so near a point of `M` the tangent-bundle trivializations
of `M ⊕ M'` are those of `M`, and the metric there is read in the same coordinates as `g₁`.

Disjoint unions are how manifolds with several components, such as the boundary of a bordism,
are assembled from connected pieces; the curvature of the disjoint union metric is computed in
`TauCeti.Geometry.Manifold.Riemannian.Isometry.Sum`.

## Main definitions and results

* `Bundle.ContMDiffRiemannianMetric.sumTangentSpace`: the disjoint union of two `C^n` Riemannian
  metrics, as a `C^n` Riemannian metric.
* `Bundle.ContMDiffRiemannianMetric.sumTangentSpace_inner_inl` and
  `Bundle.ContMDiffRiemannianMetric.sumTangentSpace_inner_inr`: it restricts to the given metrics
  on the two summands.
-/

public section

open Bundle Filter Manifold
open scoped Bundle ContDiff Manifold Topology

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I 1 M']

/-- The disjoint union of `C^n` Riemannian metrics `g₁` on `M` and `g₂` on `M'`: the `C^n`
Riemannian metric on `M ⊕ M'` which is `g₁` on `M` and `g₂` on `M'`. -/
def sumTangentSpace (g₁ : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (g₂ : ContMDiffRiemannianMetric I n E (fun x : M' ↦ TangentSpace I x)) :
    ContMDiffRiemannianMetric I n E (fun p : M ⊕ M' ↦ TangentSpace I p) where
  inner
    | .inl x => g₁.inner x
    | .inr y => g₂.inner y
  symm
    | .inl x => g₁.symm x
    | .inr y => g₂.symm y
  pos
    | .inl x => g₁.pos x
    | .inr y => g₂.pos y
  isVonNBounded
    | .inl x => g₁.isVonNBounded x
    | .inr y => g₂.isVonNBounded y
  contMDiff
    | .inl x => by
      have h := g₁.contMDiff x
      rw [contMDiffAt_section] at h ⊢
      -- Near `inl x`, the section is read through the retraction of `M ⊕ M'` onto `M` which
      -- collapses `M'` to `x`.
      have hr : ContMDiff I I n (Sum.elim id fun _ : M' ↦ x) :=
        contMDiff_id.sumElim contMDiff_const
      refine (h.comp (Sum.inl x) (hr (Sum.inl x))).congr_of_eventuallyEq ?_
      rw [nhds_inl, EventuallyEq, eventually_map]
      filter_upwards [(chartAt H x).open_source.mem_nhds (mem_chart_source H x)] with z hz
      have hzM : z ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet := by
        rwa [TangentBundle.trivializationAt_baseSet]
      have hz' : (Sum.inl z : M ⊕ M') ∈
          (trivializationAt E (TangentSpace I : M ⊕ M' → Type _) (Sum.inl x)).baseSet := by
        have : Nonempty H := nonempty_of_chartedSpace x
        simpa [ChartedSpace.sum_chartAt_inl] using hz
      -- The tangent-bundle trivializations of `M ⊕ M'` at `inl x` restrict to those of `M`.
      have hsymm (u : E) :
          (trivializationAt E (TangentSpace I : M ⊕ M' → Type _) (Sum.inl x)).symm (Sum.inl z) u =
            (trivializationAt E (TangentSpace I : M → Type _) x).symm z u := by
        rw [← Trivialization.symmL_apply (R := ℝ) _ hz',
          ← Trivialization.symmL_apply (R := ℝ) _ hzM]
        exact DFunLike.congr_fun (TauCeti.Manifold.symmL_trivializationAt_sumInl hz) u
      ext v w
      refine (inCoordinates_apply_eq₂ hz' hz' (by simp)).trans
        (Eq.trans ?_ (inCoordinates_apply_eq₂ hzM hzM (by simp)).symm)
      simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
        LinearMap.id_apply]
      rw [hsymm v, hsymm w, Sum.elim_inl, id_eq]
      -- The two sides now differ only in the fibre types `TangentSpace I (Sum.inl z)` and
      -- `TangentSpace I z` of the evaluated vectors, which are both `E` by definition.
      rfl
    | .inr y => by
      have h := g₂.contMDiff y
      rw [contMDiffAt_section] at h ⊢
      have hr : ContMDiff I I n (Sum.elim (fun _ : M ↦ y) id) :=
        contMDiff_const.sumElim contMDiff_id
      refine (h.comp (Sum.inr y) (hr (Sum.inr y))).congr_of_eventuallyEq ?_
      rw [nhds_inr, EventuallyEq, eventually_map]
      filter_upwards [(chartAt H y).open_source.mem_nhds (mem_chart_source H y)] with z hz
      have hzM : z ∈ (trivializationAt E (TangentSpace I : M' → Type _) y).baseSet := by
        rwa [TangentBundle.trivializationAt_baseSet]
      have hz' : (Sum.inr z : M ⊕ M') ∈
          (trivializationAt E (TangentSpace I : M ⊕ M' → Type _) (Sum.inr y)).baseSet := by
        have : Nonempty H := nonempty_of_chartedSpace y
        simpa [ChartedSpace.sum_chartAt_inr] using hz
      -- The tangent-bundle trivializations of `M ⊕ M'` at `inr y` restrict to those of `M'`.
      have hsymm (u : E) :
          (trivializationAt E (TangentSpace I : M ⊕ M' → Type _) (Sum.inr y)).symm (Sum.inr z) u =
            (trivializationAt E (TangentSpace I : M' → Type _) y).symm z u := by
        rw [← Trivialization.symmL_apply (R := ℝ) _ hz',
          ← Trivialization.symmL_apply (R := ℝ) _ hzM]
        exact DFunLike.congr_fun (TauCeti.Manifold.symmL_trivializationAt_sumInr hz) u
      ext v w
      refine (inCoordinates_apply_eq₂ hz' hz' (by simp)).trans
        (Eq.trans ?_ (inCoordinates_apply_eq₂ hzM hzM (by simp)).symm)
      simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
        LinearMap.id_apply]
      rw [hsymm v, hsymm w, Sum.elim_inr, id_eq]
      -- The two sides now differ only in the fibre types `TangentSpace I (Sum.inr z)` and
      -- `TangentSpace I z` of the evaluated vectors, which are both `E` by definition.
      rfl

variable
  (g₁ : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
  (g₂ : ContMDiffRiemannianMetric I n E (fun x : M' ↦ TangentSpace I x))

/-- On `M`, the disjoint union of the metrics `g₁` and `g₂` is `g₁`. -/
@[simp]
theorem sumTangentSpace_inner_inl (x : M) (v w : TangentSpace I x) :
    (g₁.sumTangentSpace g₂).inner (Sum.inl x) v w = g₁.inner x v w :=
  (rfl)

/-- On `M'`, the disjoint union of the metrics `g₁` and `g₂` is `g₂`. -/
@[simp]
theorem sumTangentSpace_inner_inr (y : M') (v w : TangentSpace I y) :
    (g₁.sumTangentSpace g₂).inner (Sum.inr y) v w = g₂.inner y v w :=
  (rfl)

end Bundle.ContMDiffRiemannianMetric
