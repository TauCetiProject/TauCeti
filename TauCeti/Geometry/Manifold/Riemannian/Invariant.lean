/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.Riemannian.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Mean

/-!
# Invariant Riemannian metrics for finite smooth actions

Average the pullbacks of a Riemannian metric over a finite group acting by diffeomorphisms.
The result is a metric preserved by every element, including elements acting trivially. Its
regularity is `C^n` when the metric is `C^n` and the action maps are `C^(n+1)`. In particular a
smooth finite action admits a smooth invariant metric whenever the manifold admits a smooth
metric. Such metrics give invariant orthonormal frame bundles on finite quotient charts.

The construction combines `TauCeti.meanRiemannianMetric` with
`Bundle.ContMDiffRiemannianMetric.pullback`.

## References

* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Cambridge University Press
  (2007), Chapter 1, for invariant metrics on finite quotient charts.
-/

public noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n : ℕ∞ω} (G : Type*) [Group G] [Fintype G] [MulAction G M]
  [ContMDiffConstSMul I (n + 1) G M]

/-- The invariant metric obtained by averaging all translates of a metric over a finite group.
The full group is used, without dividing out the ineffective kernel of the action. -/
def averageRiemannianMetric (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) :
    ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _) :=
  meanRiemannianMetric fun a : G ↦
    g.pullback (Diffeomorph.constSmul I (n + 1) a)
      (Diffeomorph.constSmul I (n + 1) a).contMDiff
      (fun _ ↦ ((Diffeomorph.constSmul I (n + 1) a).isInvertible_mfderiv (by simp)).injective)

/-- The averaged inner product is the normalized sum of the pulled-back inner products. -/
@[simp]
theorem averageRiemannianMetric_inner
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (x : M) (v w : TangentSpace I x) :
    (averageRiemannianMetric G g).inner x v w = (Fintype.card G : ℝ)⁻¹ *
      ∑ a : G, g.inner (a • x) (mfderiv I I (a • ·) x v) (mfderiv I I (a • ·) x w) := by
  have hcoe (a : G) : ⇑(Diffeomorph.constSmul I (n + 1) a : M ≃ₘ^ (n + 1)⟮I, I⟯ M) =
      (a • ·) := funext (Diffeomorph.constSmul_apply a)
  simp only [averageRiemannianMetric, meanRiemannianMetric_inner,
    ContMDiffRiemannianMetric.pullback_inner, hcoe]

/-- Every action map preserves the averaged metric. -/
theorem averageRiemannianMetric_inner_mfderiv
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (a : G) (x : M) (v w : TangentSpace I x) :
    (averageRiemannianMetric G g).inner (a • x)
        (mfderiv I I (a • ·) x v) (mfderiv I I (a • ·) x w) =
      (averageRiemannianMetric G g).inner x v w := by
  simp only [averageRiemannianMetric_inner]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulRight a) _ _ fun b ↦ ?_
  have hcomp : (fun y : M ↦ b • y) ∘ (a • ·) = ((b * a) • ·) :=
    funext fun y ↦ (mul_smul b a y).symm
  have hd := mfderiv_comp x
    ((contMDiff_const_smul b : ContMDiff I I (n + 1) _).mdifferentiableAt (by simp))
    ((contMDiff_const_smul a : ContMDiff I I (n + 1) _).mdifferentiableAt (by simp))
  -- Change the map, its value and both tangent vectors together, so that all fibre indices agree.
  have h := congrArg (fun f : M → M ↦
    g.inner (f x) (mfderiv I I f x v) (mfderiv I I f x w)) hcomp
  simp only [hd, ContinuousLinearMap.comp_apply, Function.comp_apply] at h
  convert! h using 1

/-- A metric is fixed by averaging exactly when all action maps preserve it. -/
theorem averageRiemannianMetric_eq_self_iff
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) :
    averageRiemannianMetric G g = g ↔
      ∀ (a : G) (x : M) (v w : TangentSpace I x),
        g.inner (a • x) (mfderiv I I (a • ·) x v) (mfderiv I I (a • ·) x w) = g.inner x v w := by
  constructor
  · intro h
    rw [← h]
    exact averageRiemannianMetric_inner_mfderiv G g
  · intro hg
    ext x v w
    simp [hg, Fintype.card_ne_zero]

/-- Averaging a metric twice gives the same invariant metric. -/
@[simp]
theorem averageRiemannianMetric_idempotent
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) :
    averageRiemannianMetric G (averageRiemannianMetric G g) = averageRiemannianMetric G g :=
  (averageRiemannianMetric_eq_self_iff G _).mpr (averageRiemannianMetric_inner_mfderiv G g)

end TauCeti
