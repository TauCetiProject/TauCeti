/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Basic
public import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Quotient
import TauCeti.Topology.Homotopy.Covering

/-!
# Simply connected commutative Lie groups are vector groups

Let `G` be a connected commutative finite-dimensional real Lie group with Lie algebra `𝔤`. Its
exponential `exp : 𝔤 → G` is an open surjective homomorphism whose kernel `Λ` is discrete, so it
identifies `G` with `𝔤 ⧸ Λ` (`TauCeti.lieExpQuotientKerContinuousAddEquiv`). The quotient map of a
topological group by a discrete subgroup is a covering map, so the exponential is a covering map
(`TauCeti.isCoveringMap_lieExp`).

A covering map from the path-connected vector space `𝔤` onto a simply connected space is
injective. So when `G` is simply connected the kernel of the exponential is trivial, and the
exponential is an isomorphism of topological groups `𝔤 ≃ₜ+ G`
(`TauCeti.lieExpContinuousAddEquiv`): a simply connected commutative Lie group is its Lie algebra,
a real vector space `ℝʳ`. This is how the centre factor of the universal cover of a compact Lie
group is identified with `ℝʳ`.

The circle shows that simple connectivity is needed: its exponential `ℝ → S¹` is a covering map
with kernel `2πℤ`.

## Main results

* `TauCeti.isCoveringMap_lieExp`: the exponential of a connected commutative Lie group is a
  covering map.
* `TauCeti.lieExp_bijective_of_simplyConnectedSpace`: the exponential of a simply connected
  commutative Lie group is bijective.
* `TauCeti.lieExpContinuousAddEquiv`: a simply connected commutative Lie group is isomorphic to
  its Lie algebra as a topological group, through the exponential.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter I, § 3 (The Exponential Map).
* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer (2012),
  Proposition 9.5.6 (simply connected abelian Lie groups are vector groups).
-/

public section

noncomputable section

namespace TauCeti

open Function
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
  [IsMulCommutative G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- The Lie algebra is finite-dimensional; a local instance for the rest of this file. -/
noncomputable local instance : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
  finiteDimensional_leftInvariantDerivation
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))

/-- **The exponential of a connected commutative Lie group is a covering map.** It is an open
continuous surjective homomorphism, hence a quotient map, and its kernel is discrete. -/
theorem isCoveringMap_lieExp [PreconnectedSpace G] : IsCoveringMap (lieExp (I := I) (G := G)) := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have h := ((isOpenMap_lieExpAddMonoidHom (I := I) (G := G)).isQuotientMap
    (continuous_lieExpAddMonoidHom (I := I) (G := G))
    lieExpAddMonoidHom_surjective_of_preconnectedSpace
    ).isAddQuotientCoveringMap_of_isDiscrete_ker_addMonoidHom
    (SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance) |>.isCoveringMap
  rw [coe_lieExpAddMonoidHom] at h
  exact h

variable [SimplyConnectedSpace G]

/-- **The exponential of a simply connected commutative Lie group is bijective.** It is a covering
map from the path-connected Lie algebra onto a simply connected space. -/
theorem lieExp_bijective_of_simplyConnectedSpace : Bijective (lieExp (I := I) (G := G)) :=
  ⟨isCoveringMap_lieExp.injective, lieExp_surjective_of_preconnectedSpace⟩

/-- **A simply connected commutative Lie group is its Lie algebra.** The exponential is an
isomorphism of topological groups from the additive group of the Lie algebra, a finite-dimensional
real vector space, onto the group. -/
def lieExpContinuousAddEquiv : LeftInvariantDerivation I G ≃ₜ+ Additive G :=
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  ContinuousAddEquiv.mk'
    ((Equiv.ofBijective (lieExpAddMonoidHom (I := I) (G := G)) (by
      rw [coe_lieExpAddMonoidHom]
      exact Additive.ofMul.bijective.comp lieExp_bijective_of_simplyConnectedSpace)
      ).toHomeomorphOfContinuousOpen
      (continuous_lieExpAddMonoidHom (I := I) (G := G))
      (isOpenMap_lieExpAddMonoidHom (I := I) (G := G)))
    (map_add (lieExpAddMonoidHom (I := I) (G := G)))

@[simp]
theorem lieExpContinuousAddEquiv_apply (X : LeftInvariantDerivation I G) :
    lieExpContinuousAddEquiv (I := I) (G := G) X = Additive.ofMul (lieExp X) :=
  lieExpAddMonoidHom_apply X

@[simp]
theorem lieExpContinuousAddEquiv_symm_apply (X : LeftInvariantDerivation I G) :
    (lieExpContinuousAddEquiv (I := I) (G := G)).symm (Additive.ofMul (lieExp X)) = X := by
  rw [← lieExpContinuousAddEquiv_apply, ContinuousAddEquiv.symm_apply_apply]

@[simp]
theorem lieExp_lieExpContinuousAddEquiv_symm_apply (g : Additive G) :
    lieExp ((lieExpContinuousAddEquiv (I := I) (G := G)).symm g) = Additive.toMul g :=
  congrArg Additive.toMul
    ((lieExpContinuousAddEquiv_apply _).symm.trans (ContinuousAddEquiv.apply_symm_apply _ g))

end TauCeti
