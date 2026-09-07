/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Closure
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Index

/-!
# Type-B spin-carrier data for validated indices

This file attaches Tau Ceti's explicit full-weight type-`B` spin carrier to a validated index of
the untwisted family `Bₙ(q)`. The carrier at parameter `n` has type `B (n + 1)`, so an index of
rank `r` uses parameter `r - 1`. The bound `TauCeti.TypeBLieIndex.two_le_rank` ensures this
subtraction does not truncate, and `TauCeti.TypeBLieIndex.carrierRank_add_one` identifies the
resulting node type with the Bourbaki numbering of the index.

The simple-root subgroup at a numbered node is the corresponding raising subgroup of
`TauCeti.TypeBSpinCarrier`. Its torus character agrees with the simple root of the simply
connected type-`Bₙ` root datum, as recorded by
`TauCeti.TypeBLieIndex.rootWeight_carrierNode_eq_root_simpleIndex`.

Nothing here identifies the spin carrier with the pinned simply connected Chevalley--Demazure
group scheme of type `Bₙ`, or defines a Steinberg endomorphism or fixed-point quotient for the
family. No reductivity, finiteness, perfectness, or simplicity assertion is made.

## Main declarations

* `TauCeti.TypeBLieIndex.AmbientGroup`: the algebraic-closure-valued points of the full-weight
  type-`B` spin carrier at the index's rank.
* `TauCeti.TypeBLieIndex.simpleRootSubgroup`: its positive simple-root subgroup at a
  Bourbaki-numbered node.
* `TauCeti.TypeBLieIndex.rootWeight_carrierNode_eq_root_simpleIndex`: the carrier root character
  agrees with the corresponding simple root of the index's root datum.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 11.3.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II.
-/
public section

namespace TauCeti

namespace TypeBLieIndex

variable (d : TypeBLieIndex)

noncomputable section

/-! ## The carrier rank and the node correspondence -/

/-- **The rank parameter of the type-`B` spin carrier serving a validated type-`B` index.**
`TauCeti.TypeBSpinCarrier.groupScheme n` is the carrier of type `B (n + 1)`, so the carrier serving
an index of rank `r` is the one at `r - 1`. The subtraction never truncates, `r` being at least two
by `TauCeti.TypeBLieIndex.two_le_rank`; `TauCeti.TypeBLieIndex.carrierRank_add_one` is the
identification that recovers `r`. -/
def carrierRank : ℕ := d.1.rank - 1

/-- The carrier rank of a validated type-`B` index is one less than its rank. It is oriented
towards `TauCeti.ValidLieTypeIndex.rank`, so that `simp` normalizes the successor of the carrier
rank to the rank the index's own Bourbaki index type is built on. -/
@[simp]
theorem carrierRank_add_one : d.carrierRank + 1 = d.1.rank := by
  have := d.two_le_rank
  -- The body is unexposed, so the subtraction has to be unfolded before `omega` sees it.
  rw [carrierRank]
  omega

/-- **The carrier node numbered by a Bourbaki node of the index's diagram.** The type-`B` spin
carrier at `TauCeti.TypeBLieIndex.carrierRank` numbers its generators by the Bourbaki numbering of
the type-`B` diagram that the index names, node for node, so this is the rank identification and
nothing else. -/
abbrev carrierNode (i : Fin d.1.rank) : Fin (d.carrierRank + 1) :=
  Fin.cast d.carrierRank_add_one.symm i

/-- **The node correspondence transports the type-`B` Cartan matrix.** The entry at a pair of
carrier nodes is the entry at the pair of Bourbaki nodes they number: `carrierNode` moves no node
value, only the rank its index type is built on, and `TauCeti.TypeBLieIndex.carrierRank_add_one`
identifies the two ranks. -/
theorem cartanMatrix_B_carrierNode (i j : Fin d.1.rank) :
    CartanMatrix.B (d.carrierRank + 1) (d.carrierNode i) (d.carrierNode j) =
      CartanMatrix.B d.1.rank i j := by
  have hrank : d.1.rank - 1 = d.carrierRank := by
    have := d.carrierRank_add_one
    omega
  -- Both sides are the same table of conditions on the two node values, which `carrierNode` leaves
  -- unchanged, and on the last node, where the two spellings of the rank agree by `hrank`.
  simp only [CartanMatrix.B, Matrix.of_apply, carrierNode, Fin.ext_iff, Fin.val_cast,
    Nat.add_sub_cancel, hrank]

/-- The Dynkin type of the carrier serving a validated type-`B` index is valid, its rank being at
least two. This is the hypothesis under which the upstream carrier reads its root characters in the
simply connected root datum. -/
theorem valid_B_carrierRank_add_one : (DynkinType.B (d.carrierRank + 1)).Valid := by
  rw [DynkinType.valid_B, d.carrierRank_add_one]
  exact d.two_le_rank

/-! ## The ambient group and its simple root subgroups -/

/-- **The ambient group of a validated type-`B` index**: the points of the explicit full-weight
type-`Bₙ` spin Chevalley carrier, at the rank the index names, over the algebraic closure of its
prime field.

It is infinite, and no finiteness, reductivity, pinning or maximality statement is attached to it;
in particular it is not claimed to be the points of the pinned simply connected
Chevalley--Demazure group scheme of type `Bₙ`, no identification of the spin carrier with that
group being proved here. -/
abbrev AmbientGroup : Type := TypeBSpinCarrier.points d.carrierRank d.1.Closure

/-- The classification recipe is run inside this group, so it carries a group structure; the
carrier being a subgroup of a general linear group supplies it. -/
example : Group d.AmbientGroup := inferInstance

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i` of the `Bₙ` diagram. It is
the carrier's numbered raising subgroup at the node that `carrierNode` names, the index type
`Fin d.1.rank` being the Bourbaki index type of the index's own Dynkin type. -/
def simpleRootSubgroup (i : Fin d.1.rank) : Multiplicative d.1.Closure →* d.AmbientGroup :=
  TypeBSpinCarrier.rootSubgroupPoints d.carrierRank (.inl (d.carrierNode i)) d.1.Closure

/-- The simple-root subgroup is the carrier's numbered raising subgroup at the corresponding
carrier node. This is the equation through which the upstream root-subgroup API reaches
`simpleRootSubgroup`, whose definition itself stays sealed. -/
theorem simpleRootSubgroup_def (i : Fin d.1.rank) :
    d.simpleRootSubgroup i =
      TypeBSpinCarrier.rootSubgroupPoints d.carrierRank (.inl (d.carrierNode i)) d.1.Closure :=
  (rfl)

/-- **The simple-root subgroups sit at the simple roots of the type-`Bₙ` root datum.** The
character by which the carrier's split torus rescales the parameter of `simpleRootSubgroup i`, read
in the same node correspondence, is the `i`-th simple root of
`TauCeti.DynkinType.simplyConnectedRootDatum` at the Dynkin type the index names. This is the sense
in which the spin carrier serves that diagram; it is not a claim that the carrier is the pinned
group of the diagram, no pinning being constructed for it.

The character itself is `TauCeti.TypeBSpinCarrier.rootWeight`, which
`TauCeti.TypeBSpinCarrier.weightTorusPoints_conj_rootSubgroupPoints` exhibits as the one
conjugation by the carrier's split torus rescales the parameter by. -/
theorem rootWeight_carrierNode_eq_root_simpleIndex (i j : Fin d.1.rank) :
    TypeBSpinCarrier.rootWeight d.carrierRank (.inl (d.carrierNode i)) (d.carrierNode j) =
      (d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).root
        (d.1.dynkinType.simpleIndex d.1.dynkinType_valid i) j := by
  -- Both sides are read as entries of the type-`B` Cartan matrix: the carrier's by the upstream
  -- identification of its root weights with the simple roots of the carrier's own datum, and the
  -- index's by the uniform `DynkinType.root_simpleIndex`. The two index transports that remain
  -- are then the stated equations `cartanMatrix_B_carrierNode` and `dynkinType_cartanMatrix_apply`.
  rw [TypeBSpinCarrier.rootWeight_inl_eq_root_simpleIndex d.carrierRank
      d.valid_B_carrierRank_add_one,
    congrFun (DynkinType.root_simpleIndex (DynkinType.B (d.carrierRank + 1))
      d.valid_B_carrierRank_add_one (d.carrierNode i)) (d.carrierNode j),
    DynkinType.cartanMatrix_B, d.cartanMatrix_B_carrierNode]
  simp only [DynkinType.root_simpleIndex]
  exact (d.dynkinType_cartanMatrix_apply i j).symm

end

end TypeBLieIndex

end TauCeti
