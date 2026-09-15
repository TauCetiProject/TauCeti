/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Frobenius
public import TauCeti.GroupTheory.FixedPointCandidate
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Index
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly

/-!
# The spin carrier and the candidate group of the untwisted family `Bₙ(q)`

The untwisted odd orthogonal family `Bₙ(q)` is built on the diagram `Bₙ`, and Tau Ceti's explicit
full-weight Chevalley carrier for that diagram is `TauCeti.TypeBSpinCarrier.groupScheme`, the
Kostant toral closure of the split spin representation inside `GL_(2^n)` over `ℤ`, whose weights
span the whole character lattice of the simply connected form. This file attaches that carrier to
a validated type-`B` index: the group of algebraic-closure-valued points of the carrier at the
index's rank, its Bourbaki-numbered simple root subgroups, the reading of their root characters in
the type-`B` root datum the index names, and the carrier's `q`-power Frobenius, where `q` is the
field order the index records. The family is untwisted, so that Frobenius is its Steinberg
endomorphism outright, and the candidate group of the family is the derived subgroup of the
Steinberg fixed points modulo the centre of that derived subgroup,

```text
H_d = fixedSubgroup d.steinberg,        d.Group = [H_d, H_d] / Z([H_d, H_d]).
```

The carrier is indexed by `n` in the spelling `B (n + 1)`, so a validated index of rank `r` uses
the carrier at `TauCeti.TypeBLieIndex.carrierRank`, which is `r - 1`. That subtraction is harmless
because `TauCeti.TypeBLieIndex.two_le_rank` bounds the rank below by two:
`TauCeti.TypeBLieIndex.carrierRank_add_one` recovers `r`, and every numbered object below is indexed
by `Fin d.1.rank`, the upstream Bourbaki index type of the index's own Dynkin type, rather than by a
node of the carrier. The two numberings agree node for node, so
`TauCeti.TypeBLieIndex.carrierNode` is the rank identification and nothing more; that is what
`TauCeti.TypeBLieIndex.rootWeight_carrierNode_eq_root_simpleIndex` records, reading the character
of the `i`-th raising subgroup as the `i`-th simple root of the type-`B` root datum the index names.

The spin carrier takes no rank hypothesis beyond the one the subtype supplies, so everything below
is stated for every validated type-`B` index, the rank-two members `B₂(q)` included. Those members
are also served, beside the Suzuki family that shares their diagram, by the rank-two type-`C`
carrier of `TauCeti/GroupTheory/SpecificGroups/CFSG/TypeB/Two.lean`, reached through
`TauCeti.TypeB2LieIndex`; the two carriers of the `B₂` diagram are not identified with each other
here.

The spin carrier rather than the Geck carrier is used because the Geck carrier is built from the
adjoint representation, so its weights span the whole character lattice exactly in the types `E₈`,
`F₄` and `G₂`, by `TauCeti.DynkinType.span_range_geckWeight_eq_top_iff`; the spin representation is
what sees the spinor coset of the type-`B` root lattice, and its weights span the whole weight
lattice, the root lattice together with that coset, by
`TauCeti.TypeBSpinCarrier.span_range_basisWeight_eq_top`.

Nothing here asserts that the carrier is reductive, that its weight torus is maximal, that it is
the spin group scheme or the pinned simply connected Chevalley--Demazure group scheme of type `Bₙ`,
or that any group below is finite, perfect, or simple. The Steinberg endomorphism and the candidate
group transfer to that pinned group scheme only along an identification of the carrier with it,
once one is proved.

## Main declarations

* `TauCeti.TypeBLieIndex.AmbientGroup`: the algebraic-closure-valued points of the full-weight
  type-`B` spin carrier at the index's rank.
* `TauCeti.TypeBLieIndex.simpleRootSubgroup`: its positive simple-root subgroup at a
  Bourbaki-numbered node, with
  `TauCeti.TypeBLieIndex.rootWeight_carrierNode_eq_root_simpleIndex` identifying the character of
  that subgroup with the corresponding simple root of the type-`B` root datum.
* `TauCeti.TypeBLieIndex.frobenius`, `TauCeti.TypeBLieIndex.coe_frobenius_apply` and
  `TauCeti.TypeBLieIndex.frobenius_simpleRootSubgroup`: the carrier's `q`-power Frobenius, its
  entrywise description, and its simple-root-subgroup action formula `Frob_q (x_i(u)) = x_i(u ^ q)`.
* `TauCeti.TypeBLieIndex.frobenius_weightTorusPoints`: its action on the split spin weight torus,
  raising every coordinate to the `q`-th power.
* `TauCeti.TypeBLieIndex.mem_fixedSubgroup_frobenius_iff`: its fixed points are the carrier points
  whose matrix entries all lie in the field of `q` elements inside the closure.
* `TauCeti.TypeBLieIndex.steinberg`, `TauCeti.TypeBLieIndex.steinberg_simpleRootSubgroup` and
  `TauCeti.TypeBLieIndex.mem_fixedSubgroup_steinberg_iff`: the Steinberg endomorphism of the
  untwisted family, its simple-root-subgroup action formula, and the description of the group it
  fixes.
* `TauCeti.TypeBLieIndex.FixedPoints` and `TauCeti.TypeBLieIndex.Group`: that fixed group and the
  candidate group of `Bₙ(q)`, its derived central quotient.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II, for the spin representation the
  carrier is built from.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 14.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17, for
  the entrywise Frobenius action.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II, for the numbering of the
  `Bₙ` diagram that the root subgroups below are indexed by.
-/

-- Adapted from `TauCeti.GroupTheory.SpecificGroups.CFSG.TypeD`, which attaches the type-`D` spin
-- carrier the same way, and from `TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC` for the rank
-- offset of the carrier.

public section

namespace TauCeti

namespace TypeBLieIndex

variable (d : TypeBLieIndex)

noncomputable section

/-! ## The carrier rank and the node correspondence -/

/-- **The rank parameter of the spin carrier serving a validated type-`B` index.**
`TauCeti.TypeBSpinCarrier.groupScheme n` is the carrier of type `B (n + 1)`, so the carrier
serving an index of rank `r` is the one at `r - 1`. The subtraction never truncates, `r` being at
least two by `TauCeti.TypeBLieIndex.two_le_rank`; `TauCeti.TypeBLieIndex.carrierRank_add_one` is
the identification that recovers `r`. -/
def carrierRank : ℕ := d.1.rank - 1

/-- The carrier rank of a validated type-`B` index is one less than its rank. -/
-- Oriented towards `TauCeti.ValidLieTypeIndex.rank`, so that the successor of the carrier rank
-- normalizes to the rank the index's own Bourbaki index type is built on.
@[simp]
theorem carrierRank_add_one : d.carrierRank + 1 = d.1.rank := by
  have := d.two_le_rank
  -- The body is unexposed, so the subtraction has to be unfolded before `omega` sees it.
  rw [carrierRank]
  omega

/-- **The carrier node numbered by a Bourbaki node of the index's diagram.** This is the rank
identification and nothing else: the spin carrier at `TauCeti.TypeBLieIndex.carrierRank` numbers
its generators by the Bourbaki numbering of the type-`B` diagram that the index names, node for
node. -/
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

/-! ## The ambient group and its simple root subgroups -/

/-- **The ambient group this file attaches to a validated type-`B` index**: the points of the
explicit full-weight type-`B` spin Chevalley carrier at the index's rank, over the algebraic
closure of its prime field. It is infinite. No finiteness, reductivity, pinning or maximality
statement is attached to it, and it is not claimed to be the points of the pinned simply connected
group scheme of type `Bₙ`, no identification of the two carriers being proved. -/
abbrev AmbientGroup : Type := TypeBSpinCarrier.points d.carrierRank d.1.Closure

/-- The ambient group carries a group structure; the carrier being a subgroup of a general linear
group supplies it. -/
example : Group d.AmbientGroup := inferInstance

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i` of the type-`B` diagram. It
is the carrier's numbered raising subgroup at the node that `carrierNode` names. -/
def simpleRootSubgroup (i : Fin d.1.rank) : Multiplicative d.1.Closure →* d.AmbientGroup :=
  TypeBSpinCarrier.rootSubgroupPoints d.carrierRank (.inl (d.carrierNode i)) d.1.Closure

/-- The simple-root subgroup is the carrier's numbered raising subgroup at the corresponding
carrier node. -/
-- Not a `simp` lemma: `frobenius_simpleRootSubgroup` is the form the simple-root-subgroup action
-- equations below are stated against, and unfolding to
-- `TauCeti.TypeBSpinCarrier.rootSubgroupPoints` would keep it from firing.
theorem simpleRootSubgroup_def (i : Fin d.1.rank) :
    d.simpleRootSubgroup i =
      TypeBSpinCarrier.rootSubgroupPoints d.carrierRank (.inl (d.carrierNode i)) d.1.Closure :=
  (rfl)

/-- **The simple-root subgroups sit at the simple roots of the type-`B` root datum.** The character
by which the carrier's split torus rescales the parameter of `simpleRootSubgroup i`, read in the
same node correspondence, is the `i`-th simple root of
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
  -- The carrier reads its raising-generator weight as a simple root of the pinned datum at
  -- `B (carrierRank + 1)`, which is a valid type since the rank is at least two. Both sides are
  -- then entries of the type-`B` Cartan matrix, by the uniform `DynkinType.root_simpleIndex`, and
  -- the two index transports that remain are the stated equations `cartanMatrix_B_carrierNode`
  -- and `dynkinType_cartanMatrix_apply`.
  have ht : (DynkinType.B (d.carrierRank + 1)).Valid := by
    rw [DynkinType.valid_B, d.carrierRank_add_one]
    exact d.two_le_rank
  -- The carrier-side instance of `root_simpleIndex` is given explicitly: its node is typed by the
  -- carrier's `Fin (carrierRank + 1)`, which is the datum's `Fin (B (carrierRank + 1)).rank` only
  -- after unfolding `DynkinType.rank`, further than `simp` unifies.
  rw [TypeBSpinCarrier.rootWeight_inl_eq_root_simpleIndex d.carrierRank ht,
    DynkinType.root_simpleIndex (DynkinType.B (d.carrierRank + 1)) ht (d.carrierNode i)]
  simp only [DynkinType.root_simpleIndex, DynkinType.cartanMatrix_B]
  rw [d.dynkinType_cartanMatrix_apply, d.cartanMatrix_B_carrierNode]

/-! ## The Frobenius endomorphism -/

/-- **The `q`-power Frobenius of the spin carrier attached to a validated type-`B` index**, where
`q` is the field order recorded by the index. It is the endomorphism of the point group raising
every matrix entry to the `q`-th power, and it is the Steinberg endomorphism of the family, by
`TauCeti.TypeBLieIndex.steinberg_def`. -/
def frobenius : d.AmbientGroup →* d.AmbientGroup :=
  TypeBSpinCarrier.frobenius d.carrierRank d.1.characteristic d.1.fieldExponent d.1.Closure

/-- The Frobenius is the spin carrier's Frobenius at the characteristic and field exponent
recorded by the index. -/
-- Not a `simp` lemma: `frobenius_simpleRootSubgroup` and `coe_frobenius_apply` are the forms the
-- equations below are stated against, and unfolding to `TauCeti.TypeBSpinCarrier.frobenius` would
-- keep them from firing.
theorem frobenius_def :
    d.frobenius =
      TypeBSpinCarrier.frobenius d.carrierRank d.1.characteristic d.1.fieldExponent
        d.1.Closure :=
  (rfl)

/-- The Frobenius acts on the ambient group by raising every matrix entry to the `q`-th power. -/
@[simp]
theorem coe_frobenius_apply (g : d.AmbientGroup)
    (r c : Fin (TypeBSpinCarrier.dimension d.carrierRank)) :
    ((d.frobenius g : Matrix.GeneralLinearGroup
          (Fin (TypeBSpinCarrier.dimension d.carrierRank)) d.1.Closure) :
        Matrix (Fin (TypeBSpinCarrier.dimension d.carrierRank))
          (Fin (TypeBSpinCarrier.dimension d.carrierRank)) d.1.Closure) r c =
      ((g : Matrix.GeneralLinearGroup
          (Fin (TypeBSpinCarrier.dimension d.carrierRank)) d.1.Closure) :
        Matrix (Fin (TypeBSpinCarrier.dimension d.carrierRank))
          (Fin (TypeBSpinCarrier.dimension d.carrierRank)) d.1.Closure) r c ^ d.1.fieldOrder := by
  rw [frobenius_def, d.1.fieldOrder_eq_characteristic_pow]
  exact TypeBSpinCarrier.coe_frobenius_apply _ _ _ _ g r c

/-- **The Frobenius fixes the Bourbaki numbering of a simple-root subgroup and raises its parameter
to the `q`-th power**, that is, `Frob_q (x_i(u)) = x_i(u ^ q)`. -/
@[simp]
theorem frobenius_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.frobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [frobenius_def, simpleRootSubgroup_def, TypeBSpinCarrier.frobenius_rootSubgroupPoints,
    ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]

/-- **The Frobenius raises every coordinate of the split spin weight torus to the `q`-th
power.** -/
@[simp]
theorem frobenius_weightTorusPoints (s : Fin (d.carrierRank + 1) → d.1.Closureˣ) :
    d.frobenius (TypeBSpinCarrier.weightTorusPoints d.carrierRank d.1.Closure s) =
      TypeBSpinCarrier.weightTorusPoints d.carrierRank d.1.Closure (s ^ d.1.fieldOrder) := by
  rw [frobenius_def, TypeBSpinCarrier.frobenius_weightTorusPoints,
    ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]

/-- **A point of the ambient group is fixed by the Frobenius exactly when all of its matrix entries
lie in the field of definition.** Writing `𝔽_q` for `TauCeti.ValidLieTypeIndex.fixedField`, the copy
of the field of `q` elements inside the algebraic closure, the Frobenius fixed points are the points
of the spin carrier whose entries lie in `𝔽_q`. -/
-- As for `TauCeti.ValidLieTypeIndex.mem_fixedSubgroup_geckFrobenius_iff`, not a `simp` lemma:
-- `TauCeti.fixedSubgroup` is `MonoidHom.eqLocus` against the identity, so its left-hand side
-- rewrites to `d.frobenius g = g` through `MonoidHom.mem_eqLocus`, and `simpNF` rejects the
-- annotation.
theorem mem_fixedSubgroup_frobenius_iff (g : d.AmbientGroup) :
    g ∈ fixedSubgroup d.frobenius ↔
      ∀ r c, ((g : Matrix.GeneralLinearGroup
          (Fin (TypeBSpinCarrier.dimension d.carrierRank)) d.1.Closure) :
        Matrix (Fin (TypeBSpinCarrier.dimension d.carrierRank))
          (Fin (TypeBSpinCarrier.dimension d.carrierRank)) d.1.Closure) r c ∈ d.1.fixedField := by
  rw [mem_fixedSubgroup, frobenius_def, TypeBSpinCarrier.frobenius_eq_self_iff]
  simp only [mem_frobeniusFixedSubring, ValidLieTypeIndex.mem_fixedField,
    d.1.fieldOrder_eq_characteristic_pow]

/-! ## The Steinberg endomorphism -/

/-- **The Steinberg endomorphism of a validated type-`B` index**: the `q`-power Frobenius of the
ambient group, `q` being the field order the index records. The family is untwisted, so no diagram
automorphism and no half-Frobenius enters; `TauCeti.TypeBLieIndex.diagramPerm_eq_one` records that
the diagram permutation attached to the index is trivial.

It is formed on the spin carrier, which is not identified with the pinned simply connected group
scheme of type `Bₙ`; it transfers to that pinned group only along such an identification, and not
before. -/
def steinberg : d.AmbientGroup →* d.AmbientGroup := d.frobenius

/-- The Steinberg map of a type-`B` index is the carrier's Frobenius. -/
-- This is the equation through which the Frobenius API above reaches the Steinberg map.
theorem steinberg_def : d.steinberg = d.frobenius := (rfl)

/-- **The Steinberg map fixes the Bourbaki numbering of a simple-root subgroup and raises its
parameter to the `q`-th power**, that is, `Frob_q (x_i(u)) = x_i(u ^ q)`, the simple-root-subgroup
action formula of an untwisted Steinberg endomorphism. -/
@[simp]
theorem steinberg_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.steinberg (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [steinberg_def]
  exact d.frobenius_simpleRootSubgroup i u

/-- **A point of the ambient group is fixed by the Steinberg map exactly when all of its matrix
entries lie in the field of definition**, so the fixed group `H_d` of the family is the group of
points of the spin carrier whose entries lie in `𝔽_q`. -/
-- Not a `simp` lemma, for the reason given at `mem_fixedSubgroup_frobenius_iff`.
theorem mem_fixedSubgroup_steinberg_iff (g : d.AmbientGroup) :
    g ∈ fixedSubgroup d.steinberg ↔
      ∀ r c, ((g : Matrix.GeneralLinearGroup
          (Fin (TypeBSpinCarrier.dimension d.carrierRank)) d.1.Closure) :
        Matrix (Fin (TypeBSpinCarrier.dimension d.carrierRank))
          (Fin (TypeBSpinCarrier.dimension d.carrierRank)) d.1.Closure) r c ∈ d.1.fixedField := by
  rw [steinberg_def]
  exact d.mem_fixedSubgroup_frobenius_iff g

/-! ## The finite-group candidate -/

/-- The fixed subgroup of the Steinberg endomorphism attached to a type-`B` index. -/
abbrev FixedPoints : Type := ↥(fixedSubgroup d.steinberg)

/-- **The finite-simple-group candidate attached to a type-`B` index**: the derived subgroup of
the Steinberg fixed points, modulo the centre of that derived subgroup. No finiteness or
simplicity assertion is part of this definition, nor any identification of the spin carrier with
the pinned simply connected group scheme of type `Bₙ`. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

/-- The candidate carries a group structure; the quotient construction supplies it. -/
example : _root_.Group d.Group := inferInstance

end

end TypeBLieIndex

end TauCeti
