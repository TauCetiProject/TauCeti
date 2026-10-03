/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic
public import TauCeti.Geometry.Manifold.Diffeomorph.Basic

/-!
# Mostow rigidity for hyperbolic metrics

This file records the metric-level statement of Mostow rigidity for closed hyperbolic manifolds.
`HyperbolicMetric.Isometry` compares two bundled metrics by an explicit metric-tensor equation,
and `MostowRigidity` states that every pair of such metrics is related by one once the manifold
is known to be hyperbolic and to have dimension at least three.  The explicit comparison is
needed because `RiemannianIsometry` stores its metric in a typeclass, whereas a Mostow statement
compares the two metric fields carried by `HyperbolicMetric`.

The formulation follows Ratcliffe, *Foundations of Hyperbolic Manifolds*, 3rd ed., Theorem
11.8.5.  The rigidity proposition is stated here; its geometric proof will supply the
metric-independent hyperbolic volume used by the later Weeks-manifold target.
-/

public section

open Manifold
open scoped ContDiff Manifold

noncomputable section

universe uE uH uM

namespace TauCeti

variable {E : Type uE} {H : Type uH} {M : Type uM} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [T3Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [CompactSpace M] [ConnectedSpace M]

namespace HyperbolicMetric

/-- A smooth diffeomorphism preserving the metric tensors of two bundled hyperbolic metrics. -/
structure Isometry (g g' : HyperbolicMetric (I := I) (M := M)) where
  /-- The underlying smooth equivalence. -/
  toDiffeomorph : Diffeomorph I I M M ∞
  /-- Pulling back `g'` along the diffeomorphism gives `g`. -/
  inner_mfderiv' : ∀ (x : M) (v w : TangentSpace I x),
    g'.metric.inner (toDiffeomorph x) (mfderiv I I toDiffeomorph x v)
        (mfderiv I I toDiffeomorph x w) =
      g.metric.inner x v w

namespace Isometry

/-- The identity diffeomorphism is an isometry from a hyperbolic metric to itself. -/
protected def refl (g : HyperbolicMetric (I := I) (M := M)) : Isometry g g where
  toDiffeomorph := Diffeomorph.refl I M ∞
  inner_mfderiv' := by
    intro x v w
    rw [Diffeomorph.coe_refl, mfderiv_id]
    rfl

/-- The inverse of a hyperbolic-metric isometry. -/
protected def symm {g g' : HyperbolicMetric (I := I) (M := M)}
    (Φ : Isometry g g') : Isometry g' g where
  toDiffeomorph := Φ.toDiffeomorph.symm
  inner_mfderiv' := by
    intro y v w
    obtain ⟨x, rfl⟩ : ∃ x : M, Φ.toDiffeomorph x = y :=
      ⟨Φ.toDiffeomorph.symm y, Φ.toDiffeomorph.apply_symm_apply y⟩
    have hx : Φ.toDiffeomorph.symm (Φ.toDiffeomorph x) = x :=
      Φ.toDiffeomorph.symm_apply_apply x
    have h := Φ.inner_mfderiv' x
      (mfderiv I I Φ.toDiffeomorph.symm (Φ.toDiffeomorph x) v)
      (mfderiv I I Φ.toDiffeomorph.symm (Φ.toDiffeomorph x) w)
    rw [Diffeomorph.mfderiv_apply_mfderiv_symm_apply Φ.toDiffeomorph
        (by simp) x v,
      Diffeomorph.mfderiv_apply_mfderiv_symm_apply Φ.toDiffeomorph
        (by simp) x w] at h
    rw [hx]
    exact h.symm

/-- Isometries compose in the order of their underlying diffeomorphisms. -/
protected def trans {g₁ g₂ g₃ : HyperbolicMetric (I := I) (M := M)}
    (Φ : Isometry g₁ g₂) (Ψ : Isometry g₂ g₃) : Isometry g₁ g₃ where
  toDiffeomorph := Φ.toDiffeomorph.trans Ψ.toDiffeomorph
  inner_mfderiv' := by
    intro x v w
    have hΨ := Ψ.toDiffeomorph.mdifferentiable (by simp)
    have hΦ := Φ.toDiffeomorph.mdifferentiable (by simp)
    rw [Diffeomorph.coe_trans, mfderiv_comp_apply x (hΨ (Φ.toDiffeomorph x)) (hΦ x) v,
      mfderiv_comp_apply x (hΨ (Φ.toDiffeomorph x)) (hΦ x) w]
    calc
      g₃.metric.inner (Ψ.toDiffeomorph (Φ.toDiffeomorph x))
          (mfderiv I I Ψ.toDiffeomorph (Φ.toDiffeomorph x)
            (mfderiv I I Φ.toDiffeomorph x v))
          (mfderiv I I Ψ.toDiffeomorph (Φ.toDiffeomorph x)
            (mfderiv I I Φ.toDiffeomorph x w)) =
        g₂.metric.inner (Φ.toDiffeomorph x) (mfderiv I I Φ.toDiffeomorph x v)
          (mfderiv I I Φ.toDiffeomorph x w) :=
            Ψ.inner_mfderiv' (Φ.toDiffeomorph x) _ _
      _ = g₁.metric.inner x v w := Φ.inner_mfderiv' x v w

end Isometry

end HyperbolicMetric

/-- The Mostow rigidity theorem, universally over closed connected manifolds.

From the hyperbolicity and dimension hypotheses it gives a smooth metric-preserving
diffeomorphism between every pair of bundled complete constant-curvature `-1` metrics. -/
def MostowRigidity : Prop :=
  ∀ {E : Type uE} {H : Type uH} {M : Type uM} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [T3Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] [CompactSpace M] [ConnectedSpace M],
    IsHyperbolic (I := I) (M := M) →
      3 ≤ Module.finrank ℝ E →
        ∀ (g g' : HyperbolicMetric (I := I) (M := M)),
          Nonempty (HyperbolicMetric.Isometry g g')

/-- The Mostow rigidity theorem supplies an isometry from its geometric hypotheses. -/
theorem MostowRigidity.isometry (h : MostowRigidity.{uE, uH, uM})
    (hM : IsHyperbolic (I := I) (M := M)) (hdim : 3 ≤ Module.finrank ℝ E)
    (g g' : HyperbolicMetric (I := I) (M := M)) :
    Nonempty (HyperbolicMetric.Isometry g g') :=
  h (E := E) (H := H) (M := M) (I := I) hM hdim g g'

end TauCeti
