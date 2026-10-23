/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Restriction
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Sum
public import TauCeti.Geometry.Manifold.Riemannian.Scaling
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Prod

/-!
# Positive scalar curvature

A smooth Riemannian metric `g` on the tangent bundle has positive scalar curvature when its
scalar curvature `Bundle.ContMDiffRiemannianMetric.scalarCurvature`, that of the Levi-Civita
connection of `g`, is positive at every point. Since scalar curvature is a smooth function of
the point, on a compact manifold such a metric has scalar curvature bounded below by a positive
constant. Scalar curvature is invariant under diffeomorphisms, so pulling a metric back along a
diffeomorphism preserves and reflects positive scalar curvature. Scalar curvature is also local,
so the restriction of a metric of positive scalar curvature to an open submanifold has positive
scalar curvature. No assumption on the boundary is made. The disjoint union of two metrics has
the scalar curvature of each metric on its summand, so it has positive scalar curvature exactly
when both metrics do.

Since `Scal(c g) = c⁻¹ Scal(g)` for a constant `c > 0`, rescaling by a positive constant preserves
and reflects positive scalar curvature. The scalar curvature of a product metric `g₁ × g₂` is the
sum of the scalar curvatures of the factors, so `g₁ × g₂` has positive scalar curvature when `g₁`
does and `g₂` has nonnegative scalar curvature, as for a flat factor. More importantly,
shrinking a compact factor of positive scalar curvature makes its contribution `c⁻¹ Scal(g₂)`
dominate any scalar curvature of the other factor that is bounded below: if `N` is compact, `g₂`
has positive scalar curvature and the scalar curvature of `g₁` is bounded below, then `g₁ × c g₂`
has positive scalar curvature for every sufficiently small `c > 0`.
On a compact manifold the scalar curvature of every smooth metric is bounded below.

## Main definitions and results

* `Bundle.ContMDiffRiemannianMetric.HasPositiveScalarCurvature`: positivity at every point.
* `Bundle.ContMDiffRiemannianMetric.HasPositiveScalarCurvature.exists_pos_le`: on a compact
  manifold, positive scalar curvature has a uniform positive lower bound.
* `Bundle.ContMDiffRiemannianMetric.hasPositiveScalarCurvature_iff_exists_pos_le`: on a compact
  manifold, positive scalar curvature is equivalent to a uniform positive lower bound.
* `Bundle.ContMDiffRiemannianMetric.hasPositiveScalarCurvature_pullback_iff`: the pullback of a
  metric along a diffeomorphism has positive scalar curvature exactly when the metric does.
* `Bundle.ContMDiffRiemannianMetric.HasPositiveScalarCurvature.restrictOpenTangentSpace`: the
  restriction of a metric of positive scalar curvature to an open submanifold has positive scalar
  curvature.
* `Bundle.ContMDiffRiemannianMetric.hasPositiveScalarCurvature_sumTangentSpace_iff`: the disjoint
  union of two metrics has positive scalar curvature exactly when both metrics do.
* `Bundle.ContMDiffRiemannianMetric.hasPositiveScalarCurvature_rescale_const_iff`: rescaling a
  metric by a positive constant preserves and reflects positive scalar curvature.
* `Bundle.ContMDiffRiemannianMetric.HasPositiveScalarCurvature.prodTangentSpace_of_nonneg`: the
  product of a metric of positive scalar curvature with one of nonnegative scalar curvature has
  positive scalar curvature.
* `Bundle.ContMDiffRiemannianMetric.exists_pos_hasPositiveScalarCurvature_prodTangentSpace_rescale`:
  a compact factor of positive scalar curvature, scaled down, dominates a factor whose scalar
  curvature is bounded below; more generally
  `exists_pos_hasPositiveScalarCurvature_prodTangentSpace_rescale_of_forall_le` does so for a
  factor whose scalar curvature has a positive lower bound.

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive
  scalar curvature*, Ann. of Math. 111 (1980), 423–434.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 7, for the scalar-curvature convention.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))

/-- A smooth Riemannian metric has positive scalar curvature if its scalar curvature is positive
at every point. -/
def HasPositiveScalarCurvature : Prop :=
  ∀ x, 0 < g.scalarCurvature x

/-- A metric has positive scalar curvature exactly when its scalar curvature is positive at
every point. -/
theorem hasPositiveScalarCurvature_iff :
    g.HasPositiveScalarCurvature ↔ ∀ x, 0 < g.scalarCurvature x :=
  Iff.rfl

variable {g} in
/-- On a compact manifold, a metric of positive scalar curvature has scalar curvature bounded
below by a positive constant. -/
theorem HasPositiveScalarCurvature.exists_pos_le [CompactSpace M]
    (h : g.HasPositiveScalarCurvature) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, ε ≤ g.scalarCurvature x := by
  simpa only [Set.mem_univ, forall_const] using
    isCompact_univ.exists_forall_le' g.continuous_scalarCurvature.continuousOn
      fun x _ ↦ h x

/-- On a compact manifold, a metric has positive scalar curvature exactly when its scalar
curvature has a uniform positive lower bound. -/
theorem hasPositiveScalarCurvature_iff_exists_pos_le [CompactSpace M] :
    g.HasPositiveScalarCurvature ↔ ∃ ε : ℝ, 0 < ε ∧ ∀ x, ε ≤ g.scalarCurvature x :=
  ⟨HasPositiveScalarCurvature.exists_pos_le, fun ⟨_, hε, h⟩ x ↦ hε.trans_le (h x)⟩

section Pullback

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- The pullback of a metric along a diffeomorphism has positive scalar curvature exactly when the
metric does. -/
@[simp]
theorem hasPositiveScalarCurvature_pullback_iff
    (g : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y))
    (Φ : M ≃ₘ^∞⟮I, J⟯ N) (hf : ContMDiff I J (∞ + 1) Φ)
    (hinj : ∀ x, Function.Injective (mfderiv I J Φ x)) :
    (g.pullback Φ hf hinj).HasPositiveScalarCurvature ↔ g.HasPositiveScalarCurvature := by
  simp only [hasPositiveScalarCurvature_iff, scalarCurvature_pullback]
  exact ⟨fun h y ↦ by simpa using h (Φ.symm y), fun h x ↦ h (Φ x)⟩

variable {g : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)} in
/-- Pulling a metric of positive scalar curvature back along a diffeomorphism gives a metric of
positive scalar curvature. -/
theorem HasPositiveScalarCurvature.pullback (h : g.HasPositiveScalarCurvature)
    (Φ : M ≃ₘ^∞⟮I, J⟯ N) (hf : ContMDiff I J (∞ + 1) Φ)
    (hinj : ∀ x, Function.Injective (mfderiv I J Φ x)) :
    (g.pullback Φ hf hinj).HasPositiveScalarCurvature :=
  (hasPositiveScalarCurvature_pullback_iff g Φ hf hinj).2 h

end Pullback

variable {g} in
/-- The restriction of a metric of positive scalar curvature to an open submanifold has positive
scalar curvature. -/
theorem HasPositiveScalarCurvature.restrictOpenTangentSpace (h : g.HasPositiveScalarCurvature)
    (U : TopologicalSpace.Opens M) : (g.restrictOpenTangentSpace U).HasPositiveScalarCurvature :=
  fun x ↦ by
    rw [scalarCurvature_restrictOpenTangentSpace]
    exact h x

section Sum

variable {M' : Type*} [TopologicalSpace M'] [T2Space M'] [ChartedSpace H M'] [IsManifold I ∞ M']

/-- The disjoint union of two metrics has positive scalar curvature exactly when both metrics
do. -/
@[simp]
theorem hasPositiveScalarCurvature_sumTangentSpace_iff
    (g₂ : ContMDiffRiemannianMetric I ∞ E (fun y : M' ↦ TangentSpace I y)) :
    (g.sumTangentSpace g₂).HasPositiveScalarCurvature ↔
      g.HasPositiveScalarCurvature ∧ g₂.HasPositiveScalarCurvature := by
  simp only [hasPositiveScalarCurvature_iff, Sum.forall, scalarCurvature_sumTangentSpace_inl,
    scalarCurvature_sumTangentSpace_inr]

variable {g} in
/-- The disjoint union of two metrics of positive scalar curvature has positive scalar
curvature. -/
theorem HasPositiveScalarCurvature.sumTangentSpace
    {g₂ : ContMDiffRiemannianMetric I ∞ E (fun y : M' ↦ TangentSpace I y)}
    (h : g.HasPositiveScalarCurvature) (h₂ : g₂.HasPositiveScalarCurvature) :
    (g.sumTangentSpace g₂).HasPositiveScalarCurvature :=
  (hasPositiveScalarCurvature_sumTangentSpace_iff g g₂).2 ⟨h, h₂⟩

end Sum

section Rescale

/-- Rescaling a metric by a positive constant preserves and reflects positive scalar
curvature. -/
@[simp]
theorem hasPositiveScalarCurvature_rescale_const_iff {c : ℝ} (hc : 0 < c) :
    (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).HasPositiveScalarCurvature ↔
      g.HasPositiveScalarCurvature := by
  simp only [hasPositiveScalarCurvature_iff, scalarCurvature_rescale_const, inv_pos, hc,
    mul_pos_iff_of_pos_left]

variable {g} in
/-- Rescaling a metric of positive scalar curvature by a positive constant gives a metric of
positive scalar curvature. -/
theorem HasPositiveScalarCurvature.rescale_const (h : g.HasPositiveScalarCurvature) {c : ℝ}
    (hc : 0 < c) : (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).HasPositiveScalarCurvature :=
  (hasPositiveScalarCurvature_rescale_const_iff g hc).2 h

end Rescale

section Prod

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {g₂ : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)}

variable {g} in
/-- The product of a metric of positive scalar curvature with a metric of nonnegative scalar
curvature has positive scalar curvature. -/
theorem HasPositiveScalarCurvature.prodTangentSpace_of_nonneg (h : g.HasPositiveScalarCurvature)
    (h₂ : ∀ y, 0 ≤ g₂.scalarCurvature y) : (g.prodTangentSpace g₂).HasPositiveScalarCurvature :=
  fun p ↦ by
    rw [scalarCurvature_prodTangentSpace]
    exact add_pos_of_pos_of_nonneg (h p.1) (h₂ p.2)

/-- **Shrinking a factor of uniformly positive scalar curvature.** Let `g₂` be a metric whose
scalar curvature is at least `δ > 0`, and let `g` be a metric whose scalar curvature is bounded
below. Then there is `ε > 0` such that `g × c g₂` has positive scalar curvature for every
`0 < c < ε`. -/
theorem exists_pos_hasPositiveScalarCurvature_prodTangentSpace_rescale_of_forall_le
    (h : BddBelow (Set.range g.scalarCurvature)) {δ : ℝ} (hδ : 0 < δ)
    (h₂ : ∀ y, δ ≤ g₂.scalarCurvature y) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (c : ℝ) (hc : 0 < c), c < ε →
      (g.prodTangentSpace
        (g₂.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc)).HasPositiveScalarCurvature := by
  obtain ⟨m, hm⟩ := h
  have hm₀ : 0 < |m| + 1 := by positivity
  refine ⟨δ / (|m| + 1), div_pos hδ hm₀, fun c hc hcε p ↦ ?_⟩
  -- `Scal(p) = Scal_g(p.1) + c⁻¹ Scal_{g₂}(p.2) ≥ m + c⁻¹ δ`, and `c⁻¹ δ > |m| + 1`.
  rw [scalarCurvature_prodTangentSpace, scalarCurvature_rescale_const]
  have h₁ : m ≤ g.scalarCurvature p.1 := hm ⟨p.1, rfl⟩
  have hδc : |m| + 1 < c⁻¹ * δ := by
    rw [inv_mul_eq_div, lt_div_iff₀ hc]
    rwa [lt_div_iff₀ hm₀, mul_comm] at hcε
  have hδ₂ : c⁻¹ * δ ≤ c⁻¹ * g₂.scalarCurvature p.2 :=
    mul_le_mul_of_nonneg_left (h₂ p.2) (inv_pos.2 hc).le
  linarith [neg_abs_le m]

/-- **Shrinking a compact factor of positive scalar curvature.** Let `g₂` be a metric of positive
scalar curvature on a compact manifold `N`, and let `g` be a metric whose scalar curvature is
bounded below. Then there is `ε > 0` such that `g × c g₂` has positive scalar curvature for every
`0 < c < ε`. -/
theorem exists_pos_hasPositiveScalarCurvature_prodTangentSpace_rescale [CompactSpace N]
    (h : BddBelow (Set.range g.scalarCurvature)) (h₂ : g₂.HasPositiveScalarCurvature) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (c : ℝ) (hc : 0 < c), c < ε →
      (g.prodTangentSpace
        (g₂.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc)).HasPositiveScalarCurvature :=
  let ⟨_, hδ, hδg⟩ := h₂.exists_pos_le
  exists_pos_hasPositiveScalarCurvature_prodTangentSpace_rescale_of_forall_le g h hδ hδg

end Prod

end Bundle.ContMDiffRiemannianMetric
