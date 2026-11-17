/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative
public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic

/-!
# Relative volume density under pullback and restriction

Transporting two metrics through a tangent-space linear equivalence preserves their relative
volume density. In particular, pulling back by a map whose differential is bijective preserves
the density, as does restricting both metrics to an open submanifold or a closed time interval.
-/

public section

open Bundle
open scoped ContDiff Manifold

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {n n' : ℕ∞ω}

section Transport

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]

/-- Pulling back both metrics preserves their relative volume density wherever the differential
is surjective as well as injective. -/
theorem relativeVolumeDensity_pullback
    (g : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y))
    (g' : ContMDiffRiemannianMetric J n' F (fun y : N ↦ TangentSpace J y))
    (f : M → N) (hf : ContMDiff I J (n + 1) f) (hf' : ContMDiff I J (n' + 1) f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (x : M) (hsurj : Function.Surjective (mfderiv I J f x)) :
    relativeVolumeDensity (g.pullback f hf hinj) (g'.pullback f hf' hinj) x =
      relativeVolumeDensity g g' (f x) := by
  let e := LinearEquiv.ofBijective (mfderiv I J f x).toLinearMap ⟨hinj x, hsurj⟩
  exact relativeVolumeDensity_eq_of_linearEquiv _ _ g g' e
    (g.pullback_inner f hf hinj x) (g'.pullback_inner f hf' hinj x)

/-- In equal dimensions, pulling back both metrics along an immersion preserves their relative
volume density. -/
theorem relativeVolumeDensity_pullback_of_finrank_eq
    (g : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y))
    (g' : ContMDiffRiemannianMetric J n' F (fun y : N ↦ TangentSpace J y))
    (f : M → N) (hf : ContMDiff I J (n + 1) f) (hf' : ContMDiff I J (n' + 1) f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (x : M) :
    relativeVolumeDensity (g.pullback f hf hinj) (g'.pullback f hf' hinj) x =
      relativeVolumeDensity g g' (f x) := by
  -- Tangent spaces have the model's linear structure; stating the dimension argument on the
  -- models avoids asking instance synthesis to unfold the tangent-space type synonym.
  have hsurj : Function.Surjective (mfderiv I J f x) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (K := ℝ) (V := E) (V₂ := F) (f := (mfderiv I J f x).toLinearMap) hdim).1 (hinj x)
  exact relativeVolumeDensity_pullback g g' f hf hf' hinj x hsurj

end Transport

/-- Restricting both metrics to an open submanifold preserves their relative volume density. -/
@[simp]
theorem relativeVolumeDensity_restrictOpenTangentSpace
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (g' : ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x))
    (U : TopologicalSpace.Opens M) (x : U) :
    relativeVolumeDensity (g.restrictOpenTangentSpace U) (g'.restrictOpenTangentSpace U) x =
      relativeVolumeDensity g g' x.val := by
  rw [restrictOpenTangentSpace_eq_pullback, restrictOpenTangentSpace_eq_pullback]
  apply relativeVolumeDensity_pullback
  rw [TauCeti.Manifold.mfderiv_subtype_val]
  exact (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x).surjective

/-- Restricting both metrics to a closed time interval preserves their relative volume density,
including at the endpoints. -/
@[simp]
theorem relativeVolumeDensity_restrictIcc {a b : ℝ} [Fact (a < b)]
    (g : ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) n (E × ℝ)
      (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p))
    (g' : ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) n' (E × ℝ)
      (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p)) (p : M × Set.Icc a b) :
    relativeVolumeDensity (g.restrictIcc a b) (g'.restrictIcc a b) p =
      relativeVolumeDensity g g' (p.1, p.2) := by
  rw [restrictIcc_eq_pullback, restrictIcc_eq_pullback]
  exact relativeVolumeDensity_pullback g g' _ _ _ _ p
    (TauCeti.Manifold.isInvertible_mfderiv_prodMap_id_subtypeVal_Icc p).surjective

end Bundle.ContMDiffRiemannianMetric
