/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Frobenius
public import TauCeti.GroupTheory.FixedPointCandidate
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.GraphTwisted
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Index
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly

/-!
# The untwisted family `Bₙ(q)` on the type-`B` spin carrier

The classification list carries one family on the diagram `Bₙ`, the untwisted `Bₙ(q)` for `n ≥ 2`,
whose matrix name in Gorenstein--Lyons--Solomon is `Ω_{2n+1}(q)`; `TauCeti.TypeBLieIndex` is the
subtype of validated indices that names it. This file attaches to such an index the group of
algebraic-closure-valued points of Tau Ceti's explicit full-weight type-`B` spin Chevalley carrier
at the index's own rank, `TauCeti.TypeBSpinCarrier.points`, together with that group's
Bourbaki-numbered simple root subgroups and its `q`-power Frobenius; and it then forms the
Steinberg endomorphism of the family and the quotient of the derived subgroup of its fixed points
by the centre of that derived subgroup.

The diagram `Bₙ` is a chain with two root lengths, so it has no nontrivial symmetry and the family
composes its Frobenius with no graph automorphism: `TauCeti.TypeBLieIndex.diagramPerm_eq_one` is
that check, and `TauCeti.TypeBLieIndex.steinberg` is accordingly the `q`-power Frobenius outright.
The single family on this diagram is the reason the Steinberg map and the shared Frobenius are
declared on one and the same subtype here, unlike the three families sharing a type-`D` diagram in
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeD.lean`.

The spin carrier rather than the Geck carrier is used because the Geck carrier is built from the
adjoint representation, so its weights span the whole character lattice exactly in the types `E₈`,
`F₄` and `G₂`, by `TauCeti.DynkinType.span_range_geckWeight_eq_top_iff`; a type-`B` diagram is not
one of those. The full spin representation is what sees the half-integral coset of the type-`B`
root lattice, and its weights span the character lattice, by
`TauCeti.TypeBSpinCarrier.span_range_basisWeight_eq_top`.

## The carrier rank

`TauCeti.TypeBSpinCarrier.points n` is the carrier of the diagram `B (n + 1)`, so an index of rank
`r` uses the carrier at `r - 1`. That subtraction never truncates, the rank being at least two by
`TauCeti.TypeBLieIndex.two_le_rank`, and `TauCeti.TypeBLieIndex.carrierRank_add_one` recovers `r`.
The two numberings agree node for node, so `TauCeti.TypeBLieIndex.carrierNode` is the rank
identification and nothing more, and every numbered object below is indexed by `Fin d.1.rank`, the
upstream Bourbaki index type of the index's own Dynkin type.

At rank two the same family is also reached, beside the Suzuki family, by
`TauCeti.RankTwoBLieIndex` in `TauCeti/GroupTheory/SpecificGroups/CFSG/TypeB/Two.lean`, on the
rank-two standard symplectic carrier the Suzuki family needs for its special isogeny. That carrier
is a different object from the one below and the two are not identified here; what is offered
below is the carrier of the family at every valid rank, in the rank-uniform shape the untwisted
recipe is stated in.

Nothing here asserts that the spin carrier is reductive, that its weight torus is maximal, or that
any group below is finite, perfect, or simple.

## Main declarations

* `TauCeti.TypeBLieIndex.AmbientGroup`: the algebraic-closure-valued points of the full-weight
  type-`B` spin carrier at the rank the index names, the group inside which the classification
  recipe is run below.
* `TauCeti.TypeBLieIndex.simpleRootSubgroup`: the positive simple-root subgroup at a Bourbaki node.
* `TauCeti.TypeBLieIndex.frobenius` and `TauCeti.TypeBLieIndex.steinberg`: the `q`-power Frobenius
  of the ambient group and the Steinberg endomorphism of the family, which is that Frobenius.
* `TauCeti.TypeBLieIndex.Group`: the derived subgroup of the fixed points of the Steinberg map,
  modulo the centre of that derived subgroup.

## Main results

* `TauCeti.TypeBLieIndex.rootWeight_carrierNode_eq_root_simpleIndex`: the character of the
  simple-root subgroup at node `i` is the `i`-th simple root of the root datum of the Dynkin type
  the index names.
* `TauCeti.TypeBLieIndex.coe_frobenius_apply` and
  `TauCeti.TypeBLieIndex.steinberg_simpleRootSubgroup`: the Steinberg map raises every matrix
  entry to the `q`-th power, and on a simple-root subgroup it reads `Frob_q (x_i(u)) = x_i(u ^ q)`.
* `TauCeti.TypeBLieIndex.mem_fixedSubgroup_steinberg_iff`: its fixed points are the points of the
  spin carrier whose matrix entries lie in the field of definition `𝔽_q`.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II, for the spin representation the
  carrier is built from.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 11.3, for the fixed-point construction of
  the classical families and the orthogonal name `Ω_{2n+1}(q)` of this one.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II, for the numbering of the
  `Bₙ` diagram that the root subgroups below are indexed by.

## Roadmap

Milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md` asks for the points of the *pinned* simply
connected Chevalley--Demazure group scheme of `TauCeti.DynkinType.simplyConnectedRootDatum` at the
diagram the index names, with its root subgroups. **This file does not close L0 on the type-`B`
branch, and the spin carrier is not offered as a substitute for that pinned group.** The pinned
group scheme, its pinning, and any identification of a carrier with it are Layer 9 targets of
`TauCetiRoadmap/ReductiveGroups/README.md` that the CFSG roadmap consumes rather than builds; none
of them is proved of `TauCeti.TypeBSpinCarrier.groupScheme` here or in the files this one imports.
What this file supplies is the family's explicit carrier, its numbered root characters read in the
type-`Bₙ` root datum, the equation `Frob_q (x_i(u)) = x_i(u ^ q)` that milestone L1 asks of an
ordinary Frobenius factor, and the milestone L3 recipe run on that Frobenius, each in the shape
those milestones state it; they transfer to the L0 carrier along that Layer 9 identification, and
not before. The counterparts on the branches already assembled are
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeA.lean`,
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeD.lean`,
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeE6.lean` and
`TauCeti/GroupTheory/SpecificGroups/CFSG/Unimodular.lean`.
-/

-- The signatures realized here follow the human-authored formal skeleton
-- `TauCetiRoadmap/CFSGStatement/Suggested.lean`.

public section

namespace TauCeti

namespace TypeBLieIndex

variable (d : TypeBLieIndex)

noncomputable section

/-! ## The carrier rank and the node correspondence -/

/-- **The rank parameter of the type-`B` spin carrier serving a validated type-`B` index.**
`TauCeti.TypeBSpinCarrier.points n` is the carrier of type `B (n + 1)`, so the carrier serving an
index of rank `r` is the one at `r - 1`. The subtraction never truncates, `r` being at least two by
`TauCeti.TypeBLieIndex.two_le_rank`; `TauCeti.TypeBLieIndex.carrierRank_add_one` is the
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

/-- The diagram of the carrier serving a validated type-`B` index is a valid Dynkin type: it is the
type-`B` diagram at the index's own rank, which is at least two. -/
theorem valid_B_carrierRank_add_one : (DynkinType.B (d.carrierRank + 1)).Valid := by
  have := d.two_le_rank
  have := d.carrierRank_add_one
  rw [DynkinType.valid_B]
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

/-! ## The ambient group and its simple root subgroups -/

/-- **The ambient group this file attaches to a validated type-`B` index**: the points of the
explicit full-weight type-`Bₙ` spin Chevalley carrier, at the rank the index names, over the
algebraic closure of its prime field.

It is infinite, and no finiteness, reductivity, pinning or maximality statement is attached to it;
it is not claimed to be the pinned `Bₙ` group scheme's points that milestone L0 asks for, that
identification being the Layer 9 target described in the module docstring. -/
abbrev AmbientGroup : Type := TypeBSpinCarrier.points d.carrierRank d.1.Closure

/-- Milestone L3 runs its recipe inside this group, so it carries a group structure; the carrier
being a subgroup of a general linear group supplies it. -/
example : Group d.AmbientGroup := inferInstance

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i` of the `Bₙ` diagram. It is
the carrier's numbered raising subgroup at the node that `carrierNode` names, the index type
`Fin d.1.rank` being the upstream Bourbaki index type of the index's own Dynkin type. -/
def simpleRootSubgroup (i : Fin d.1.rank) : Multiplicative d.1.Closure →* d.AmbientGroup :=
  TypeBSpinCarrier.rootSubgroupPoints d.carrierRank (.inl (d.carrierNode i)) d.1.Closure

/-- The simple-root subgroup is the carrier's numbered raising subgroup at the corresponding
carrier node. This is the equation through which the upstream root-subgroup API reaches
`simpleRootSubgroup`, whose definition itself stays sealed.

It is deliberately not a `simp` lemma: `frobenius_simpleRootSubgroup` is the normal form the pinned
equations of this file are stated against, and unfolding to
`TauCeti.TypeBSpinCarrier.rootSubgroupPoints` would keep it from firing. -/
theorem simpleRootSubgroup_def (i : Fin d.1.rank) :
    d.simpleRootSubgroup i =
      TypeBSpinCarrier.rootSubgroupPoints d.carrierRank (.inl (d.carrierNode i)) d.1.Closure :=
  (rfl)

/-- **The simple-root subgroups sit at the simple roots of the type-`Bₙ` root datum.** The
character by which the carrier's split torus rescales the parameter of `simpleRootSubgroup i`,
read in the same node correspondence, is the `i`-th simple root of
`TauCeti.DynkinType.simplyConnectedRootDatum` at the Dynkin type the index names, in the same
Bourbaki numbering. This is the sense in which the spin carrier serves that diagram; it is not a
claim that the carrier is the pinned group of the diagram, no pinning being constructed for it.

The character itself is `TauCeti.TypeBSpinCarrier.rootWeight`, which
`TauCeti.TypeBSpinCarrier.weightTorusPoints_conj_rootSubgroupPoints` exhibits as the one
conjugation by the carrier's split torus rescales the parameter by. -/
theorem rootWeight_carrierNode_eq_root_simpleIndex (i j : Fin d.1.rank) :
    TypeBSpinCarrier.rootWeight d.carrierRank (.inl (d.carrierNode i)) (d.carrierNode j) =
      (d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).root
        (d.1.dynkinType.simpleIndex d.1.dynkinType_valid i) j := by
  -- Both sides are read as entries of the type-`B` Cartan matrix, the carrier's by the upstream
  -- `TypeBSpinCarrier.rootWeight_inl_eq_root_simpleIndex` and the datum's by the uniform
  -- `DynkinType.root_simpleIndex`, which is the same route the upstream identification takes past
  -- the dependent root index; both are applied as terms, the two node index types agreeing only
  -- up to the unfolding of `DynkinType.rank`. The single index transport that remains is then the
  -- stated equation `cartanMatrix_B_carrierNode`.
  have hB := d.valid_B_carrierRank_add_one
  have hcarrier :
      TypeBSpinCarrier.rootWeight d.carrierRank (.inl (d.carrierNode i)) (d.carrierNode j) =
        CartanMatrix.B (d.carrierRank + 1) (d.carrierNode i) (d.carrierNode j) := by
    rw [TypeBSpinCarrier.rootWeight_inl_eq_root_simpleIndex d.carrierRank hB]
    exact (congrFun (DynkinType.root_simpleIndex _ hB (d.carrierNode i)) (d.carrierNode j)).trans
      (congrFun₂ (DynkinType.cartanMatrix_B (d.carrierRank + 1)) _ _)
  have hdatum :
      (d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).root
          (d.1.dynkinType.simpleIndex d.1.dynkinType_valid i) j =
        CartanMatrix.B d.1.rank i j :=
    (congrFun (DynkinType.root_simpleIndex _ d.1.dynkinType_valid i) j).trans
      (d.dynkinType_cartanMatrix_apply i j)
  rw [hcarrier, hdatum, d.cartanMatrix_B_carrierNode]

/-! ## The Frobenius endomorphism -/

/-- **The `q`-power Frobenius endomorphism of the ambient group of a validated type-`B` index**,
for `q` the field order the index records. The family being untwisted, it is the Steinberg map
itself, by `TauCeti.TypeBLieIndex.steinberg_def`. -/
def frobenius : d.AmbientGroup →* d.AmbientGroup :=
  TypeBSpinCarrier.frobenius d.carrierRank d.1.characteristic d.1.fieldExponent d.1.Closure

/-- The Frobenius of a validated type-`B` index is the carrier's Frobenius at the exponent the
index records. This is its unfolding lemma; the definition itself stays sealed.

It is deliberately not a `simp` lemma: `frobenius_simpleRootSubgroup` and `coe_frobenius_apply` are
the normal forms the pinned equations of this file are stated against, and unfolding to
`TauCeti.TypeBSpinCarrier.frobenius` would keep them from firing. -/
theorem frobenius_def :
    d.frobenius =
      TypeBSpinCarrier.frobenius d.carrierRank d.1.characteristic d.1.fieldExponent d.1.Closure :=
  (rfl)

/-- The Frobenius acts on the ambient group by raising every matrix entry to the `q`-th power. -/
@[simp]
theorem coe_frobenius_apply (g : d.AmbientGroup)
    (r c : Fin (TypeBSpinCarrier.dimension d.carrierRank)) :
    ((d.frobenius g :
        Matrix.GeneralLinearGroup (Fin (TypeBSpinCarrier.dimension d.carrierRank))
          d.1.Closure) :
        Matrix (Fin (TypeBSpinCarrier.dimension d.carrierRank))
          (Fin (TypeBSpinCarrier.dimension d.carrierRank)) d.1.Closure) r c =
      ((g : Matrix.GeneralLinearGroup (Fin (TypeBSpinCarrier.dimension d.carrierRank))
          d.1.Closure) :
        Matrix (Fin (TypeBSpinCarrier.dimension d.carrierRank))
          (Fin (TypeBSpinCarrier.dimension d.carrierRank)) d.1.Closure) r c ^ d.1.fieldOrder := by
  rw [frobenius_def, d.1.fieldOrder_eq_characteristic_pow]
  exact TypeBSpinCarrier.coe_frobenius_apply _ _ _ _ g r c

/-- **The Frobenius fixes the Bourbaki numbering of a simple-root subgroup and raises its parameter
to the `q`-th power**, that is, `Frob_q (x_i(u)) = x_i(u ^ q)`. This is the equation milestone L1
asks of an ordinary Frobenius factor. -/
@[simp]
theorem frobenius_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.frobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [frobenius_def, simpleRootSubgroup_def, TypeBSpinCarrier.frobenius_rootSubgroupPoints,
    ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]

/-- **A point of the ambient group is fixed by the Frobenius exactly when all of its matrix entries
lie in the field of definition.** Writing `𝔽_q` for `TauCeti.ValidLieTypeIndex.fixedField`, the copy
of the field of `q` elements inside the algebraic closure, the Frobenius fixed points are the
points of the spin carrier whose entries lie in `𝔽_q`.

As for `TauCeti.ValidLieTypeIndex.mem_fixedSubgroup_geckFrobenius_iff`, this is not a `simp` lemma:
`TauCeti.fixedSubgroup` is `MonoidHom.eqLocus` against the identity, so `simp` rewrites its
left-hand side to `d.frobenius g = g` through `MonoidHom.mem_eqLocus`, and the `simpNF` linter
rejects the annotation. -/
theorem mem_fixedSubgroup_frobenius_iff (g : d.AmbientGroup) :
    g ∈ fixedSubgroup d.frobenius ↔
      ∀ r c, ((g :
          Matrix.GeneralLinearGroup (Fin (TypeBSpinCarrier.dimension d.carrierRank))
            d.1.Closure) :
        Matrix (Fin (TypeBSpinCarrier.dimension d.carrierRank))
          (Fin (TypeBSpinCarrier.dimension d.carrierRank)) d.1.Closure) r c ∈ d.1.fixedField := by
  rw [mem_fixedSubgroup, frobenius_def, TypeBSpinCarrier.frobenius_eq_self_iff]
  simp only [mem_frobeniusFixedSubring, ValidLieTypeIndex.mem_fixedField,
    d.1.fieldOrder_eq_characteristic_pow]

/-! ## The Steinberg endomorphism -/

/-- **The milestone L1 Steinberg endomorphism of a validated type-`B` index, formed on the spin
carrier**: the `q`-power Frobenius of the ambient group, `q` being the field order the index
records. The family is untwisted, so no diagram automorphism and no half-Frobenius enters;
`diagramPerm_eq_one` is the check that its diagram permutation is trivial.

It is the Steinberg map of `Bₙ(q)` on the pinned carrier milestone L0 asks for only along the
Layer 9 identification of the two carriers described in the module docstring, and not before. -/
def steinberg : d.AmbientGroup →* d.AmbientGroup := d.frobenius

/-- The Steinberg map of a validated type-`B` index is the `q`-power Frobenius of its ambient
group. This is its unfolding lemma; the definition itself stays sealed, and it is through this
equation that the ambient-group API above reaches the Steinberg map. -/
theorem steinberg_def : d.steinberg = d.frobenius := (rfl)

/-- **The Steinberg map fixes the Bourbaki numbering of a simple-root subgroup and raises its
parameter to the `q`-th power**, that is, `Frob_q (x_i(u)) = x_i(u ^ q)`. This is the equation
milestone L1 asks of the untwisted families, on this branch. -/
@[simp]
theorem steinberg_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.steinberg (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [steinberg_def]
  exact d.frobenius_simpleRootSubgroup i u

/-- **A point of the ambient group is fixed by the Steinberg map exactly when all of its matrix
entries lie in the field of definition**, so the group `H_d` that the milestone L3 recipe is run on
below is the group of points of the spin carrier whose entries lie in `𝔽_q`. -/
theorem mem_fixedSubgroup_steinberg_iff (g : d.AmbientGroup) :
    g ∈ fixedSubgroup d.steinberg ↔
      ∀ r c, ((g :
          Matrix.GeneralLinearGroup (Fin (TypeBSpinCarrier.dimension d.carrierRank))
            d.1.Closure) :
        Matrix (Fin (TypeBSpinCarrier.dimension d.carrierRank))
          (Fin (TypeBSpinCarrier.dimension d.carrierRank)) d.1.Closure) r c ∈ d.1.fixedField := by
  rw [steinberg_def]
  exact d.mem_fixedSubgroup_frobenius_iff g

/-! ## The milestone L3 quotient -/

/-- **The milestone L3 quotient on the type-`Bₙ` spin carrier**: the derived subgroup of the fixed
points of the Steinberg map above, modulo the centre of that derived subgroup.

This is the shape milestone L3 asks of the untwisted family `Bₙ(q)`, formed on the spin carrier
rather than on the pinned simply connected Chevalley--Demazure group scheme that milestone L0 asks
for. It becomes the candidate simple group of that family along the Layer 9 identification of the
two carriers described in the module docstring, and not before; it is not offered as that candidate
here. Nothing below asserts that it is finite, perfect, or simple. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

/-- Milestone L3 asks every valid branch to carry a group instance; the quotient construction
supplies it. -/
example : _root_.Group d.Group := inferInstance

end

end TypeBLieIndex

end TauCeti
