/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Commutative
public import TauCeti.Algebra.Group.NormalizerQuotient.Basic
public import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Subrepresentation
import TauCeti.Geometry.Lie.Adjoint.Representation.Basic

/-!
# The Weyl group of a subgroup and its actions

For a subgroup `K` of a group `G`, the **Weyl group** of `K` is the quotient `N(K) / K` of the
normalizer of `K` by `K`, `Subgroup.normalizerQuotient K`. The normalizer acts on `K` by
conjugation (`Subgroup.normalizerMonoidHom`) and, when `G` is a finite-dimensional real Lie
group, on the Lie algebra `Lie(K)` by the adjoint action. When `K` is commutative both actions
are trivial on `K`, so they descend to the Weyl group: `Subgroup.normalizerQuotientMulAut` is the
action on `K` by automorphisms and `Subgroup.weylAdjointRepresentation` the adjoint
representation on `Lie(K)`. The exponential map of `G` intertwines the two.

## Main definitions

* `Subgroup.normalizerAdjointRepresentation`: the adjoint representation of `G` restricted to
  the normalizer of `K` and to `Lie(K)`.
* `Subgroup.weylAdjointRepresentation`: the adjoint representation of the Weyl group of a
  commutative subgroup on its Lie algebra.

## Main results

* `TauCeti.Lie.lieExp_weylAdjointRepresentation_apply`: the exponential of a closed commutative
  subgroup intertwines the two actions of its Weyl group.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter IV, § 1 (Maximal Tori), Definition (1.3) and (1.4).
* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 15 (Tori), Proposition 15.8.
-/

public section

noncomputable section

namespace TauCeti.Lie

open scoped ContDiff Manifold


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- **The adjoint representation of the normalizer of `K` on `Lie(K)`**: the adjoint
representation of `G`, restricted to the normalizer and to the invariant subspace `Lie(K)`. -/
def _root_.Subgroup.normalizerAdjointRepresentation (K : Subgroup G) :
    Representation ℝ (Subgroup.normalizer (K : Set G))
      (lieSubalgebraOfSubgroup (I := I) K).toSubmodule :=
  (⟨(lieSubalgebraOfSubgroup (I := I) K).toSubmodule, fun g _ hX => by
      simpa [ContRepresentation.toMonoidHom_apply] using Ad_mem_lieSubalgebraOfSubgroup g.2 hX⟩ :
    Subrepresentation ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.comp
      (Subgroup.normalizer (K : Set G)).subtype)).toRepresentation

@[simp]
theorem _root_.Subgroup.coe_normalizerAdjointRepresentation_apply (K : Subgroup G)
    (g : Subgroup.normalizer (K : Set G)) (X : (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) :
    (K.normalizerAdjointRepresentation (I := I) g X : LeftInvariantDerivation I G) =
      Ad (I := I) (g : G) X := by
  rw [Subgroup.normalizerAdjointRepresentation]
  refine (Subrepresentation.toRepresentation_apply_coe.mp rfl).symm.trans ?_
  simp [ContRepresentation.toMonoidHom_apply]

/-- **The adjoint representation of the Weyl group of a commutative subgroup on its Lie
algebra.** -/
def _root_.Subgroup.weylAdjointRepresentation (K : Subgroup G) [IsMulCommutative K] :
    Representation ℝ K.normalizerQuotient
      (lieSubalgebraOfSubgroup (I := I) K).toSubmodule :=
  K.normalizerQuotientLift (K.normalizerAdjointRepresentation (I := I)) fun g hg =>
    LinearMap.ext fun X => Subtype.ext <| by
      rw [Module.End.one_apply, Subgroup.coe_normalizerAdjointRepresentation_apply]
      exact Ad_apply_eq_self_of_mem_lieSubalgebraOfSubgroup hg X.2

@[simp]
theorem _root_.Subgroup.coe_weylAdjointRepresentation_mk_apply (K : Subgroup G) [IsMulCommutative K]
    (g : Subgroup.normalizer (K : Set G)) (X : (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) :
    (K.weylAdjointRepresentation (I := I) (g : K.normalizerQuotient) X :
        LeftInvariantDerivation I G) = Ad (I := I) (g : G) X := by
  simp only [Subgroup.weylAdjointRepresentation, Subgroup.normalizerQuotientLift,
    QuotientGroup.lift_mk, Subgroup.coe_normalizerAdjointRepresentation_apply]

/-- **The exponential intertwines the two actions of the Weyl group** of a closed commutative
subgroup. -/
theorem lieExp_weylAdjointRepresentation_apply {K : Subgroup G} [IsMulCommutative K]
    (hK : IsClosed (K : Set G)) (w : K.normalizerQuotient)
    (X : (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) :
    lieExp (I := I) (K.weylAdjointRepresentation (I := I) w X : LeftInvariantDerivation I G) =
      K.normalizerQuotientMulAut w
        ⟨lieExp (I := I) X, lieExp_mem_of_mem_lieSubalgebraOfSubgroup hK X.2⟩ := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective w
  rw [Subgroup.coe_weylAdjointRepresentation_mk_apply,
    Subgroup.coe_normalizerQuotientMulAut_mk_apply, conj_lieExp]

end TauCeti.Lie
