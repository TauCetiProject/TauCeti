/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Action
public import TauCeti.AlgebraicTopology.ClassifyingSpace.WeakContractibility
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Covering
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.LocallyPathConnected
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Quotient.ActingGroup

/-!
# Milnor's classifying space as an orbit space

For a group `G`, `classifyingSpace G` is the quotient of Milnor's countable join
`universalGSpace G` by the free action of `G` that relabels vertices, with the quotient topology.
The orbit map `classifyingSpaceProj G` is a quotient covering map for `G` in the sense of
Mathlib's `IsQuotientCoveringMap`: the open star of a vertex is a neighbourhood whose translates
by distinct group elements are disjoint.

This file gives the orbit space the interface a user needs without unfolding the quotient. Two
points of the countable join have the same image exactly when a unique group element carries one
to the other, the fibre through a point is its orbit, a continuous `G`-invariant map descends to
the orbit space, and, since the countable join is connected, the acting group is the deck
transformation group of the orbit map.

The classifying space satisfies the standing hypotheses of covering-space theory: it is
path-connected and locally path-connected, being a quotient of the countable join, which is both,
and it is semilocally simply connected, being covered by the simply connected countable join.

## Main definitions

* `TauCeti.classifyingSpace`: the orbit space of the countable join.
* `TauCeti.classifyingSpaceProj`: the orbit map.
* `TauCeti.classifyingSpaceBasepoint`: the image of the base point of the countable join.
* `TauCeti.classifyingSpaceLift`: descent of a continuous `G`-invariant map.
* `TauCeti.classifyingSpaceDeckMulEquiv`: `G ≃* deck (classifyingSpaceProj G)`.

## Main results

* `TauCeti.isQuotientCoveringMap_classifyingSpaceProj`: the orbit map is a quotient covering
  map for `G`.
* `TauCeti.classifyingSpaceProj_eq_iff_existsUnique`: two points have the same image exactly when
  a unique group element carries one to the other.
* `TauCeti.preimage_classifyingSpaceProj_singleton`: the fibre through a point is its orbit.
* `TauCeti.instPathConnectedSpaceClassifyingSpace`,
  `TauCeti.instLocallyPathConnectedSpaceClassifyingSpace` and
  `TauCeti.instSemilocallySimplyConnectedSpaceClassifyingSpace`: the standing hypotheses of
  covering-space theory.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B.
-/

public section

noncomputable section

open Topology

namespace TauCeti

universe u

variable (G : Type u) [Group G]

/-- Milnor's classifying space of a group `G`: the orbit space of the countable join of copies
of `G` under the free action relabelling its vertices. -/
def classifyingSpace : Type u :=
  MulAction.orbitRel.Quotient G (universalGSpace G)

/-- The classifying space carries the quotient topology of the countable join. -/
instance instTopologicalSpaceClassifyingSpace : TopologicalSpace (classifyingSpace G) :=
  inferInstanceAs (TopologicalSpace (MulAction.orbitRel.Quotient G (universalGSpace G)))

/-- The orbit map from the countable join to the classifying space. -/
def classifyingSpaceProj : universalGSpace G → classifyingSpace G :=
  Quotient.mk (MulAction.orbitRel G (universalGSpace G))

/-- The base point of the classifying space: the orbit of the vertex over index zero labelled by
the unit. -/
def classifyingSpaceBasepoint : classifyingSpace G :=
  classifyingSpaceProj G (universalGSpaceBasepoint G)

/-- The base point of the classifying space is the image of the base point of the countable
join. -/
@[simp]
theorem classifyingSpaceProj_universalGSpaceBasepoint :
    classifyingSpaceProj G (universalGSpaceBasepoint G) = classifyingSpaceBasepoint G :=
  (rfl)

/-- The orbit map is a quotient map. -/
theorem isQuotientMap_classifyingSpaceProj : IsQuotientMap (classifyingSpaceProj G) :=
  isQuotientMap_quotient_mk'

/-- The orbit map is continuous. -/
@[fun_prop, continuity]
theorem continuous_classifyingSpaceProj : Continuous (classifyingSpaceProj G) :=
  (isQuotientMap_classifyingSpaceProj G).continuous

/-- Every point of the classifying space is the orbit of a point of the countable join. -/
theorem classifyingSpaceProj_surjective : Function.Surjective (classifyingSpaceProj G) :=
  (isQuotientMap_classifyingSpaceProj G).surjective

variable {G}

/-- Two points of the countable join have the same image in the classifying space exactly when
they lie in the same orbit. -/
theorem classifyingSpaceProj_eq_iff {x y : universalGSpace G} :
    classifyingSpaceProj G x = classifyingSpaceProj G y ↔ x ∈ MulAction.orbit G y :=
  Quotient.eq''.trans MulAction.orbitRel_apply

/-- Translation does not change the image in the classifying space. -/
@[simp]
theorem classifyingSpaceProj_smul (g : G) (x : universalGSpace G) :
    classifyingSpaceProj G (g • x) = classifyingSpaceProj G x :=
  classifyingSpaceProj_eq_iff.mpr (MulAction.mem_orbit x g)

/-- Two points of the countable join have the same image in the classifying space exactly when a
unique group element carries the second to the first; uniqueness is freeness of the action. -/
theorem classifyingSpaceProj_eq_iff_existsUnique {x y : universalGSpace G} :
    classifyingSpaceProj G x = classifyingSpaceProj G y ↔ ∃! g : G, g • y = x := by
  rw [classifyingSpaceProj_eq_iff, MulAction.mem_orbit_iff]
  refine ⟨fun ⟨g, hg⟩ => ⟨g, hg, fun g' hg' => ?_⟩, ExistsUnique.exists⟩
  exact IsCancelSMul.right_cancel g' g y (hg'.trans hg.symm)

/-- The fibre of the orbit map through a point of the countable join is the orbit of that
point. -/
theorem preimage_classifyingSpaceProj_singleton (x : universalGSpace G) :
    classifyingSpaceProj G ⁻¹' {classifyingSpaceProj G x} = MulAction.orbit G x :=
  Set.ext fun _ => classifyingSpaceProj_eq_iff

variable (G) in
/-- **The orbit map of Milnor's countable join is a quotient covering map.** The open star of a
vertex is a neighbourhood of each of its points whose translates by distinct group elements are
disjoint. -/
theorem isQuotientCoveringMap_classifyingSpaceProj :
    IsQuotientCoveringMap (classifyingSpaceProj G) G where
  toIsQuotientMap := isQuotientMap_classifyingSpaceProj G
  apply_eq_iff_mem_orbit := classifyingSpaceProj_eq_iff
  disjoint x := by
    obtain ⟨v, hv⟩ := (indexedJoin fun _ : ℕ => G).exists_mem_openStarRealization x
    exact ⟨_, ((indexedJoin fun _ : ℕ => G).isOpen_openStarRealization v).mem_nhds hv,
      fun g => eq_one_of_image_smul_openStarRealization_inter_nonempty g v⟩

/-- The classifying space is path-connected, as the image of the path-connected countable join. -/
instance instPathConnectedSpaceClassifyingSpace : PathConnectedSpace (classifyingSpace G) :=
  (classifyingSpaceProj_surjective G).pathConnectedSpace (continuous_classifyingSpaceProj G)

/-- The classifying space is locally path-connected, as a quotient of the locally path-connected
countable join. -/
instance instLocallyPathConnectedSpaceClassifyingSpace :
    LocallyPathConnectedSpace (classifyingSpace G) :=
  (isQuotientMap_classifyingSpaceProj G).locallyPathConnectedSpace

/-- The classifying space is semilocally simply connected, being covered by the simply connected
countable join. -/
instance instSemilocallySimplyConnectedSpaceClassifyingSpace :
    SemilocallySimplyConnectedSpace (classifyingSpace G) :=
  .of_isCoveringMap (isQuotientCoveringMap_classifyingSpaceProj G).isCoveringMap
    (classifyingSpaceProj_surjective G)

/-- A continuous map out of the countable join that is invariant under the group action descends
to a continuous map out of the classifying space. -/
def classifyingSpaceLift {X : Type*} [TopologicalSpace X] (f : C(universalGSpace G, X))
    (hf : ∀ (g : G) (x : universalGSpace G), f (g • x) = f x) : C(classifyingSpace G, X) where
  toFun := Quotient.lift f fun _ _ h => by
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    exact hf g _
  continuous_toFun := continuous_quot_lift _ f.continuous

/-- The descended map agrees with the original map on the image of each point. -/
@[simp]
theorem classifyingSpaceLift_apply {X : Type*} [TopologicalSpace X] (f : C(universalGSpace G, X))
    (hf : ∀ (g : G) (x : universalGSpace G), f (g • x) = f x) (x : universalGSpace G) :
    classifyingSpaceLift f hf (classifyingSpaceProj G x) = f x :=
  (rfl)

/-- Two continuous maps out of the classifying space agree once they agree on the image of the
orbit map. -/
theorem classifyingSpace_continuousMap_ext {X : Type*} [TopologicalSpace X]
    {φ ψ : C(classifyingSpace G, X)}
    (h : ∀ x : universalGSpace G, φ (classifyingSpaceProj G x) = ψ (classifyingSpaceProj G x)) :
    φ = ψ :=
  ContinuousMap.ext ((classifyingSpaceProj_surjective G).forall.mpr h)

variable (G)

/-- **The acting group is the deck transformation group of the orbit map.** Translation by a
group element is a deck transformation, and every deck transformation arises this way because
the countable join is connected. -/
def classifyingSpaceDeckMulEquiv : G ≃* deck (classifyingSpaceProj G) :=
  Deck.IsQuotientCoveringMap.deckMulEquiv (isQuotientCoveringMap_classifyingSpaceProj G)

/-- The deck transformation attached to a group element is translation by that element. -/
@[simp]
theorem classifyingSpaceDeckMulEquiv_apply (g : G) (x : universalGSpace G) :
    (classifyingSpaceDeckMulEquiv G g).1 x = g • x :=
  Deck.IsQuotientCoveringMap.deckMulEquiv_apply _ g x

/-- A deck transformation of the orbit map is translation by the group element it corresponds
to. -/
@[simp]
theorem classifyingSpaceDeckMulEquiv_symm_apply (φ : deck (classifyingSpaceProj G))
    (x : universalGSpace G) : (classifyingSpaceDeckMulEquiv G).symm φ • x = φ.1 x :=
  Deck.IsQuotientCoveringMap.deckMulEquiv_symm_apply _ φ x

end TauCeti
