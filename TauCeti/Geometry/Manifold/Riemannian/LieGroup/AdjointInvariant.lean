/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.InvariantForm
public import TauCeti.Geometry.Manifold.Riemannian.LieGroup.LeftInvariant
public import TauCeti.Geometry.Manifold.Riemannian.LieGroup.BiInvariant
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity

/-!
# Connection and curvature of the metric from an Ad-invariant inner product

The smooth left-invariant metric constructed from an Ad-invariant positive inner product on
`T₁G` is bi-invariant. This file identifies its inner product with an infinitesimally invariant
form, so the existing Koszul and curvature calculations apply without a separate infinitesimal
invariance assumption. In particular its Levi-Civita connection satisfies
`∇_{X_a} X_b = ½ X_[a,b]` and its curvature at the identity is
`R(a,b)c = −¼ [[a,b],c]`.

The construction is `TauCeti.leftInvariantMetric`, and the connection and curvature calculations
are `CovariantDerivative.IsLeviCivitaConnection.apply_mulInvariantVectorField` and
`CovariantDerivative.IsLeviCivitaConnection.curvatureTensor_one`. The implication from group to
Lie-algebra invariance uses `TauCeti.Lie.lieInvariant_of_adjoint_invariant`.

## References

* J. Milnor, *Curvatures of left invariant metrics on Lie groups*, Advances in Math. 21
  (1976), 293–329.
* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapters 3 and 7.
-/

public noncomputable section

open Bundle CovariantDerivative Manifold
open scoped ContDiff Manifold

namespace ContinuousLinearMap

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable (b : TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G) →L[ℝ] ℝ)
  (hsymm : ∀ v w, b v w = b w v) (hpos : ∀ v, v ≠ 0 → 0 < b v v)
  (had : ∀ (g : G) (a c : TangentSpace I (1 : G)),
    b (Lie.adjointContinuousLinearMap g a) (Lie.adjointContinuousLinearMap g c) = b a c)

include had

/-- The inner product at the identity of the metric constructed from an Ad-invariant form
is infinitesimally invariant. No connectedness assumption is needed. -/
theorem lieInvariant_inner_leftInvariantMetric :
    letI : RiemannianBundle (fun x : G ↦ TangentSpace I x) :=
      ⟨(leftInvariantMetric (m := ∞) (n := ∞) (by simp) b hsymm hpos).toRiemannianMetric⟩
    LinearMap.BilinForm.lieInvariant (TangentSpace I (1 : G))
      (innerₗ (TangentSpace I (1 : G))) := by
  let : RiemannianBundle (fun x : G ↦ TangentSpace I x) :=
    ⟨(leftInvariantMetric (m := ∞) (n := ∞) (by simp) b hsymm hpos).toRiemannianMetric⟩
  have h := Lie.lieInvariant_of_adjoint_invariant (I := I) (G := G) had
  intro a c d
  simpa only [innerₗ_apply_apply, ContMDiffRiemannianMetric.inner_riemannianBundle,
    leftInvariantMetric_inner_one, ContinuousLinearMap.toBilinForm_apply] using h a c d

/-- For the metric from an Ad-invariant inner product, the Levi-Civita derivative of
left-invariant fields is half their bracket. -/
theorem leviCivitaConnection_leftInvariantMetric_mulInvariantVectorField
    (a c : TangentSpace I (1 : G)) (x : G) :
    letI : RiemannianBundle (fun x : G ↦ TangentSpace I x) :=
      ⟨(leftInvariantMetric (m := ∞) (n := ∞) (by simp) b hsymm hpos).toRiemannianMetric⟩
    leviCivitaConnection I G (mulInvariantVectorField c) x (mulInvariantVectorField a x) =
      mulInvariantVectorField ((2 : ℝ)⁻¹ • ⁅a, c⁆) x := by
  let : RiemannianBundle (fun x : G ↦ TangentSpace I x) :=
    ⟨(leftInvariantMetric (m := ∞) (n := ∞) (by simp) b hsymm hpos).toRiemannianMetric⟩
  exact (isLeviCivitaConnection_leviCivitaConnection (M := G) I).apply_mulInvariantVectorField
    (inner_mulInvariantVectorField_leftInvariantMetric (by simp) b hsymm hpos)
    (lieInvariant_inner_leftInvariantMetric b hsymm hpos had) a c x

/-- For the metric from an Ad-invariant inner product, the curvature at the identity is
`R(a,c)d = −¼ [[a,c],d]`, in the convention where the round sphere has positive curvature. -/
theorem curvatureTensor_leftInvariantMetric_one (a c d : TangentSpace I (1 : G)) :
    letI : T2Space G := I.t2Space_of_lieGroup ∞
    letI : RiemannianBundle (fun x : G ↦ TangentSpace I x) :=
      ⟨(leftInvariantMetric (m := ∞) (n := ∞) (by simp) b hsymm hpos).toRiemannianMetric⟩
    (leviCivitaConnection I G).curvatureTensor 1 a c d = -(4 : ℝ)⁻¹ • ⁅⁅a, c⁆, d⁆ := by
  let : RiemannianBundle (fun x : G ↦ TangentSpace I x) :=
    ⟨(leftInvariantMetric (m := ∞) (n := ∞) (by simp) b hsymm hpos).toRiemannianMetric⟩
  let : T2Space G := I.t2Space_of_lieGroup ∞
  exact (isLeviCivitaConnection_leviCivitaConnection (M := G) I).curvatureTensor_one
    (inner_mulInvariantVectorField_leftInvariantMetric (by simp) b hsymm hpos)
    (lieInvariant_inner_leftInvariantMetric b hsymm hpos had) a c d

end ContinuousLinearMap
