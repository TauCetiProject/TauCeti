/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Basic
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Covering
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Pointed
public import TauCeti.AlgebraicTopology.UniversalCover.Covering

/-!
# Milnor's classifying space is a `K(G, 1)`

The orbit map `classifyingSpaceProj G` from Milnor's countable join to `classifyingSpace G` is a
quotient covering map for `G` whose total space is simply connected with vanishing higher homotopy
groups. So `classifyingSpace G` is an Eilenberg--Mac Lane space of type `K(G, 1)`, for every group
`G`, with no finiteness, countability or presentation hypothesis.

## The direction of the identification of `π₁`

Mathlib's `IsQuotientCoveringMap.fundamentalGroupEquiv` identifies the fundamental group of the
base of a simply connected quotient covering map with the *opposite* of the acting group: a loop
`γ` goes to `op g` when its lift starting at the chosen point `e` ends at `g • e`. Here this is
composed with the inverse of `MulEquiv.inv' G : G ≃* Gᵐᵒᵖ`, so
`classifyingSpaceFundamentalGroupMulEquiv G` sends a loop at the base point to `g` exactly when
its lift starting at the vertex `⟨0, 1⟩` ends at the vertex `⟨0, g⁻¹⟩`.

## Main definitions

* `TauCeti.classifyingSpaceFundamentalGroupMulEquiv`: the isomorphism `π₁(BG) ≃* G`.
* `TauCeti.universalGSpaceHomeomorphUniversalCover`: the pointed homeomorphism over the
  classifying space between the countable join and the based-path universal cover.

## Main results

* `TauCeti.classifyingSpaceFundamentalGroupMulEquiv_apply_eq_iff`: the direction of the
  identification, through the monodromy of the orbit map.
* `TauCeti.isEilenbergMacLaneSpaceOne_classifyingSpace`: **the classifying space is a
  `K(G, 1)`**.
* `TauCeti.exists_isEilenbergMacLaneSpaceOne`: **every group has a `K(G, 1)`**, which moreover
  satisfies the standing hypotheses of covering-space theory.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B.
-/

public section

noncomputable section

open Topology unitInterval
open scoped Topology.Homotopy

namespace TauCeti

universe u

variable (G : Type u) [Group G]

/-- **The fundamental group of the classifying space is `G`.** A loop at the base point goes to
`g` exactly when its lift starting at the vertex `⟨0, 1⟩` of the countable join ends at the vertex
`⟨0, g⁻¹⟩`; see `classifyingSpaceFundamentalGroupMulEquiv_apply_eq_iff`. -/
def classifyingSpaceFundamentalGroupMulEquiv :
    FundamentalGroup (classifyingSpace G) (classifyingSpaceBasepoint G) ≃* G :=
  ((isQuotientCoveringMap_classifyingSpaceProj G).fundamentalGroupEquiv
    ⟨universalGSpaceBasepoint G, classifyingSpaceProj_universalGSpaceBasepoint G⟩).trans
      (MulEquiv.inv' G).symm

variable {G}

/-- A loop at the base point of the classifying space corresponds to `g` exactly when its
monodromy carries the vertex `⟨0, 1⟩` of the countable join to the vertex `⟨0, g⁻¹⟩`. -/
theorem classifyingSpaceFundamentalGroupMulEquiv_apply_eq_iff
    {γ : FundamentalGroup (classifyingSpace G) (classifyingSpaceBasepoint G)} {g : G} :
    classifyingSpaceFundamentalGroupMulEquiv G γ = g ↔
      ((isQuotientCoveringMap_classifyingSpaceProj G).isCoveringMap.monodromy γ.asHom
          ⟨universalGSpaceBasepoint G, classifyingSpaceProj_universalGSpaceBasepoint G⟩ :
          universalGSpace G) =
        (indexedJoin fun _ : ℕ => G).vertex ⟨0, g⁻¹⟩ := by
  rw [classifyingSpaceFundamentalGroupMulEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_eq,
    MulEquiv.inv'_apply, ← smul_universalGSpaceBasepoint]
  -- `fundamentalGroupEquiv` is `MulEquiv.ofBijective` of `fundamentalGroupToMulOpposite`.
  exact (IsQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_iff _).trans eq_comm

/-- A loop at the base point of the classifying space whose lift starting at the vertex `⟨0, 1⟩`
of the countable join ends at the vertex `⟨0, g⁻¹⟩` corresponds to `g`. -/
theorem classifyingSpaceFundamentalGroupMulEquiv_apply_mk_eq
    {γ : Path (classifyingSpaceBasepoint G) (classifyingSpaceBasepoint G)}
    {Γ : C(I, universalGSpace G)} {g : G} (hΓ : classifyingSpaceProj G ∘ Γ = γ)
    (hΓ₀ : Γ 0 = universalGSpaceBasepoint G)
    (hΓ₁ : Γ 1 = (indexedJoin fun _ : ℕ => G).vertex ⟨0, g⁻¹⟩) :
    classifyingSpaceFundamentalGroupMulEquiv G (.of (.mk γ)) = g :=
  classifyingSpaceFundamentalGroupMulEquiv_apply_eq_iff.mpr <| by
    rw [IsCoveringMap.monodromy_eq_apply_one _ hΓ hΓ₀, hΓ₁]

variable (G)

/-- **Milnor's classifying space is a `K(G, 1)`**: it is path-connected, its higher homotopy
groups vanish, and its fundamental group is `G`. -/
theorem isEilenbergMacLaneSpaceOne_classifyingSpace :
    IsEilenbergMacLaneSpaceOne G (classifyingSpace G) (classifyingSpaceBasepoint G) :=
  (isQuotientCoveringMap_classifyingSpaceProj G).isEilenbergMacLaneSpaceOne
    (classifyingSpaceProj_universalGSpaceBasepoint G)
    fun n => subsingleton_homotopyGroup_universalGSpace G (n + 1) _

/-- Every homotopy group of the classifying space in dimension at least two is trivial, at every
base point. -/
theorem subsingleton_homotopyGroup_classifyingSpace (n : ℕ) (x : classifyingSpace G) :
    Subsingleton (π_ (n + 2) (classifyingSpace G) x) :=
  ((isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical.of_basepoint x)
    |>.subsingleton_homotopyGroup n

/-- **Every group has a `K(G, 1)`**, in its own universe, satisfying the standing hypotheses of
covering-space theory: local path-connectedness and semilocal simple connectivity. No hypothesis
on the group is needed. -/
theorem exists_isEilenbergMacLaneSpaceOne :
    ∃ (X : Type u) (_ : TopologicalSpace X) (x : X), LocallyPathConnectedSpace X ∧
      SemilocallySimplyConnectedSpace X ∧ IsEilenbergMacLaneSpaceOne G X x :=
  ⟨classifyingSpace G, inferInstance, classifyingSpaceBasepoint G, inferInstance, inferInstance,
    isEilenbergMacLaneSpaceOne_classifyingSpace G⟩

/-- **The countable join is the universal cover of the classifying space.** The pointed
homeomorphism over `classifyingSpace G` from the countable join, based at the vertex `⟨0, 1⟩`, to
the based-path universal cover, based at the class of the constant path. -/
def universalGSpaceHomeomorphUniversalCover :
    universalGSpace G ≃ₜ UniversalCover (classifyingSpaceBasepoint G) :=
  IsCoveringMap.totalSpaceHomeomorphOfRangeEq
    (isQuotientCoveringMap_classifyingSpaceProj G).isCoveringMap
    (UniversalCover.isCoveringMap _) (classifyingSpaceProj_universalGSpaceBasepoint G)
    (UniversalCover.proj_basepointLift _) <| by
      rw [FundamentalGroup.mapOfEq_range_eq_bot_of_subsingleton,
        FundamentalGroup.mapOfEq_range_eq_bot_of_subsingleton]

/-- The comparison homeomorphism carries the base point of the countable join to the class of
the constant path. -/
@[simp]
theorem universalGSpaceHomeomorphUniversalCover_basepoint :
    universalGSpaceHomeomorphUniversalCover G (universalGSpaceBasepoint G) =
      UniversalCover.basepointLift (classifyingSpaceBasepoint G) :=
  IsCoveringMap.totalSpaceHomeomorphOfRangeEq_apply_basepoint ..

/-- The comparison homeomorphism lies over the classifying space. -/
@[simp]
theorem proj_universalGSpaceHomeomorphUniversalCover (x : universalGSpace G) :
    (universalGSpaceHomeomorphUniversalCover G x).proj = classifyingSpaceProj G x :=
  IsCoveringMap.comp_totalSpaceHomeomorphOfRangeEq_apply ..

variable {G}

/-- The comparison homeomorphism is the only continuous map from the countable join to the
universal cover that lies over the classifying space and preserves the base points. -/
theorem eq_universalGSpaceHomeomorphUniversalCover
    {f : C(universalGSpace G, UniversalCover (classifyingSpaceBasepoint G))}
    (hf₀ : f (universalGSpaceBasepoint G) =
      UniversalCover.basepointLift (classifyingSpaceBasepoint G))
    (hf : UniversalCover.proj ∘ f = classifyingSpaceProj G) :
    f = (universalGSpaceHomeomorphUniversalCover G : C(_, _)) :=
  IsCoveringMap.eq_totalSpaceHomeomorphOfRangeEq _ _ _ _ _ hf₀ hf

end TauCeti
