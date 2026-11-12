/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Distance

/-!
# Distance and completeness for a dominating metric

If a Riemannian metric `g` dominates the given tangent norms on `M`, the identification
`ofWithMetric : WithMetric g → M` does not increase Riemannian extended distance.
When `M` is complete for that distance, the copy carrying `g` is complete as well.
Extended distances allow points in distinct connected components to be infinitely far apart.

The carrier and tangent-norm comparison are provided by `TauCeti.WithMetric`.
See M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §3, Lemma 3.3.
-/

public section

open Bundle Manifold MeasureTheory Set TauCeti.Manifold
open scoped ContDiff ENNReal Manifold Topology

noncomputable section

namespace TauCeti.WithMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}

section Intrinsic

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}

/-- If `g` dominates the given metric, forgetting the copy carrying `g` does not increase
Riemannian extended distance. -/
theorem riemannianEDist_ofWithMetric_le
    (hg : ∀ x (v : TangentSpace I x), ‖v‖ ^ 2 ≤ g.inner x v v) (x y : WithMetric g) :
    riemannianEDist I x.ofWithMetric y.ofWithMetric ≤ riemannianEDist I x y := by
  refine le_riemannianEDist_of_forall_le_pathELength fun γ h0 h1 hγ ↦ ?_
  have hcomp : CMDiff[Icc 0 1] 1 (ofWithMetric ∘ γ) :=
    contMDiff_ofWithMetric.comp_contMDiffOn hγ
  refine (Manifold.riemannianEDist_le_pathELength hcomp
    (congrArg ofWithMetric h0) (congrArg ofWithMetric h1) zero_le_one).trans ?_
  rw [pathELength_eq_lintegral_mfderiv_Ioo, pathELength_eq_lintegral_mfderiv_Ioo]
  refine setLIntegral_mono' measurableSet_Ioo fun t ht ↦ ?_
  have hdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
    (hγ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt one_ne_zero
  rw [mfderiv_comp t (hasMFDerivAt_ofWithMetric _).mdifferentiableAt hdiff,
    ContinuousLinearMap.comp_apply, ← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (norm_mfderiv_ofWithMetric_le hg _ _)

end Intrinsic

section Ambient

variable {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  {g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}

/-- If `g` dominates the given metric and the copy is equipped with its Riemannian distance,
`ofWithMetric` is `1`-Lipschitz. -/
theorem lipschitzWith_ofWithMetric [PseudoEMetricSpace (WithMetric g)]
    [IsRiemannianManifold I (WithMetric g)]
    (hg : ∀ x (v : TangentSpace I x), ‖v‖ ^ 2 ≤ g.inner x v v) :
    LipschitzWith 1 (ofWithMetric : WithMetric g → M) := by
  apply LipschitzWith.of_edist_le
  intro x y
  rw [IsRiemannianManifold.out (I := I), IsRiemannianManifold.out (I := I)]
  exact riemannianEDist_ofWithMetric_le hg x y

end Ambient

variable {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  {g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}

/-- A metric dominating a complete Riemannian metric is complete for its own Riemannian
extended distance. -/
theorem completeSpace_of_sq_norm_le [CompleteSpace M]
    (hg : ∀ x (v : TangentSpace I x), ‖v‖ ^ 2 ≤ g.inner x v v) :
    let : EMetricSpace (WithMetric g) := .ofRiemannianMetric I (WithMetric g)
    CompleteSpace (WithMetric g) := by
  let : EMetricSpace (WithMetric g) := .ofRiemannianMetric I (WithMetric g)
  exact CompleteSpace.of_comp_eq_id (toWithMetric g) ofWithMetric rfl
    continuous_toWithMetric (lipschitzWith_ofWithMetric hg).uniformContinuous

end TauCeti.WithMetric

end
