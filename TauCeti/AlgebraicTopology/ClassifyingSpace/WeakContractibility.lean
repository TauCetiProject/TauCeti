/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.CountableJoin
public import TauCeti.AlgebraicTopology.SimplicialComplex.Join.WeakContractibility
public import TauCeti.AlgebraicTopology.Singular.Cubical.Based.Retraction

/-!
# Weak contractibility of the countable join

An indexed join is weakly contractible when nonempty family members occur at infinitely many
indices (`AlgebraicTopology/SimplicialComplex/Join/WeakContractibility.lean`).  This file
specializes those facts to Milnor's countable join `universalGSpace`, whose family members are
all nonempty as soon as `G` is.

## Main results

* `TauCeti.instSimplyConnectedSpaceUniversalGSpace`: simple connectedness of the countable join.
* `TauCeti.subsingleton_homotopyGroup_universalGSpace`: all its positive-dimensional homotopy
  groups vanish.
* `TauCeti.isZero_singularHomology_universalGSpace`: its singular homology vanishes in positive
  degrees.
* `ContinuousMap.nullhomotopic_to_universalGSpace`: every map from a compact space to it is
  nullhomotopic.
-/

public section

noncomputable section

open Set Topology
open scoped Topology.Homotopy

universe u

namespace TauCeti

/-- Milnor's countable join of a nonempty type is simply connected. -/
instance instSimplyConnectedSpaceUniversalGSpace (G : Type u) [Nonempty G] :
    SimplyConnectedSpace (universalGSpace G) :=
  simplyConnectedSpace_realization_indexedJoin (Set.infinite_univ.mono fun _ _ => ‹Nonempty G›)

/-- Every positive-dimensional homotopy group of Milnor's countable join is trivial. -/
theorem subsingleton_homotopyGroup_universalGSpace (G : Type u) [Nonempty G]
    (n : ℕ) (x : universalGSpace G) :
    Subsingleton (π_ (n + 1) (universalGSpace G) x) :=
  subsingleton_homotopyGroup_realization_indexedJoin
    (Set.infinite_univ.mono fun _ _ => ‹Nonempty G›) (Fin (n + 1)) x

/-- **The singular homology of Milnor's countable join vanishes in positive degrees**, since all
its homotopy groups vanish. -/
theorem isZero_singularHomology_universalGSpace (k : Type u) [Ring k] (G : Type u) [Nonempty G]
    (n : ℕ) :
    CategoryTheory.Limits.IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k)
      (n + 1)).obj (ModuleCat.of k k)).obj (TopCat.of (universalGSpace G))) := by
  obtain ⟨x⟩ : Nonempty (universalGSpace G) := inferInstance
  refine isZero_singularHomologyFunctor_of_subsingleton_homotopyGroup (n := n + 2)
    (X := TopCat.of (universalGSpace G)) (x := x) (fun m _ ↦ ?_) k (by lia) (by lia)
  rcases m with _ | m
  · exact HomotopyGroup.pi0EquivZerothHomotopy.subsingleton
  · exact subsingleton_homotopyGroup_universalGSpace G m x

end TauCeti

namespace ContinuousMap

open TauCeti

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Every map from a compact space to Milnor's countable join is nullhomotopic. -/
theorem nullhomotopic_to_universalGSpace {G : Type u} [Nonempty G]
    (f : C(X, universalGSpace G)) : f.Nullhomotopic :=
  nullhomotopic_to_indexedJoin f (isCompact_range f.continuous)
    (Set.infinite_univ.mono fun _ _ => ‹Nonempty G›)

end ContinuousMap
