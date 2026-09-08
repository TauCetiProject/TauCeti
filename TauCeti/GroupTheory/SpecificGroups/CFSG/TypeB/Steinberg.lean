/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.IntegralMatrix
public import TauCeti.GroupTheory.FixedPointCandidate
public import TauCeti.GroupTheory.SpecificGroups.CFSG.GraphTwisted
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Two

/-!
# The Steinberg map and the candidate group of the untwisted family `B₂(q)`

Of the two classification-list families on the rank-two diagram `B₂`, this file serves the
untwisted one, `B₂(q)`, whose validated indices are `TauCeti.TypeB2LieIndex`. Its ambient group,
its Bourbaki-numbered simple root subgroups and its `q`-power Frobenius are supplied on the shared
rank-two type-`C` Chevalley carrier by
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeB/Two.lean`, which stops there because the two
families on that diagram differ exactly in the endomorphism whose fixed points are taken. What is
added here is that endomorphism for the untwisted family, and the quotient the classification
recipe forms from it.

The family is untwisted, so its Steinberg map is the `q`-power Frobenius outright, with no diagram
automorphism composed in: the `B₂` diagram has no symmetry to twist by, its two nodes carrying
different root lengths, and `TauCeti.TypeB2LieIndex.diagramPerm_toGraphTwistedIndex` is the check
that the diagram permutation the index itself carries is the identity. The other family on the
same diagram, the Suzuki family `²B₂(2^(2m+1))`, is excluded from `TauCeti.TypeB2LieIndex` and gets
an odd power of the carrier's special isogeny instead; nothing below applies to it.

The three equations that identify the map are the pinned action on the numbered simple root
subgroups, `Frob_q (x_i(u)) = x_i(u ^ q)`, the coordinatewise `q`-th power on the pinned split
weight torus, and the description of the fixed points as the carrier points whose matrix entries
lie in the field of definition `𝔽_q`. Together with
`simpleRootSubgroup_mem_fixedSubgroup_steinberg_iff` and
`weightTorusPoints_mem_fixedSubgroup_steinberg`, which say that the fixed group meets each simple
root subgroup in exactly its `𝔽_q`-points and contains the `𝔽_q`-points of the split weight torus,
they show that the group the recipe is run on is the group of `𝔽_q`-points of the carrier and not a
degenerate subgroup of it.

## What is and is not claimed

As in the files for the branches already assembled, the carrier here is Tau Ceti's explicit
full-weight rank-two type-`C` Chevalley carrier, not the pinned simply connected
Chevalley--Demazure group scheme of type `B₂` that milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md` asks for: no pinning datum is constructed for it, here or
in the files this one imports. So `TauCeti.TypeB2LieIndex.steinberg` becomes the Steinberg map of
`B₂(q)` in the sense of that milestone, and `TauCeti.TypeB2LieIndex.Group` the candidate simple
group of that family, only along the identification of the two carriers that Layer 9 of the
reductive-groups roadmap owns, and not before. What is recorded of the carrier is the
identification of numbered root characters with the simple roots of the `B₂` root datum proved in
`TauCeti.RankTwoBLieIndex.rootGeneratorWeight_carrierNode_eq_root_simpleIndex`.

The carrier is not left unidentified as a group of points, though. Over a field its points are
exactly the symplectic matrices, by `TauCeti.SpStd.points_eq_GLSymplecticFin`, so the ambient
group below is `Sp₄` over the algebraic closure of the prime field, and its numbered raising
points are the transvections and difference short-root elements of that group named by
`TauCeti.SpStd.rootSubgroupPoints_inl_last_eq_positiveLongRootTransvectionUnit` and its siblings.
What is absent is the scheme-level datum: no pinning is constructed for the carrier and the two
group schemes are not shown to agree.

Nothing below asserts that any group in sight is finite, perfect, simple, or isomorphic to the
projective symplectic group `PSp₄(q)` that Gorenstein--Lyons--Solomon write for this family. The
list's small-parameter exclusions are already carried by the index:
`TauCeti.TypeB2LieIndex.four_le_fieldOrder` records that `B₂(2)`, whose recipe returns `A₆` under
another name, and `B₂(3)`, which the list carries as `²A₃(2)`, are not indices of this subtype.

The same milestone L1 and L3 material on the branches already assembled is in
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeA.lean`,
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeD.lean` and
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeE6.lean`.

## Main declarations

* `TauCeti.TypeB2LieIndex.steinberg`: the Steinberg endomorphism of the untwisted family `B₂(q)`,
  the `q`-power Frobenius of its ambient group.
* `TauCeti.TypeB2LieIndex.steinberg_simpleRootSubgroup` and
  `TauCeti.TypeB2LieIndex.steinberg_weightTorusPoints`: its pinned equations on the numbered simple
  root subgroups and on the split weight torus.
* `TauCeti.TypeB2LieIndex.mem_fixedSubgroup_steinberg_iff`: its fixed points are the carrier points
  whose matrix entries lie in the field of definition.
* `TauCeti.TypeB2LieIndex.simpleRootSubgroup_mem_fixedSubgroup_steinberg_iff`: the fixed group meets
  the simple root subgroup at a node in exactly the points whose parameter lies in that field.
* `TauCeti.TypeB2LieIndex.weightTorusPoints_mem_fixedSubgroup_steinberg`: it contains the points of
  the split weight torus whose coordinates lie in that field.
* `TauCeti.TypeB2LieIndex.Group`: the milestone L3 quotient, the derived subgroup of those fixed
  points modulo the centre of that derived subgroup.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 11.3, for the fixed-point construction and
  the untwisted Steinberg map.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* D. Gorenstein, R. Lyons and R. Solomon, *The Classification of the Finite Simple Groups*,
  Number 1, §2.2, for the small-parameter exclusions the validated index carries.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II, for the numbering of the
  `B₂` diagram.
-/

public section

namespace TauCeti

namespace TypeB2LieIndex

noncomputable section

variable (d : TypeB2LieIndex)

/-! ## The Steinberg endomorphism -/

/-- **The milestone L1 Steinberg endomorphism of a validated untwisted index `B₂(q)`, formed on the
rank-two type-`C` carrier**: the `q`-power Frobenius of its ambient group, `q` being the field order
the index records. The family is untwisted, so no diagram automorphism and no half-Frobenius enters;
`diagramPerm_toGraphTwistedIndex` is the check that its diagram permutation is trivial.

It is the Steinberg map of `B₂(q)` on the pinned carrier that milestone L0 asks for only along the
Layer 9 identification of the two carriers described in the module docstring, and not before. -/
def steinberg : d.1.AmbientGroup →* d.1.AmbientGroup := d.1.frobenius

/-- The Steinberg map of an untwisted index on the `B₂` diagram is the Frobenius that both families
on that diagram share. This is its unfolding lemma; the definition itself stays sealed, and it is
through this equation that the ambient-group API of `TauCeti.RankTwoBLieIndex` reaches the Steinberg
map. -/
theorem steinberg_def : d.steinberg = d.1.frobenius := (rfl)

/-- **The Steinberg map fixes the Bourbaki numbering of a simple-root subgroup and raises its
parameter to the `q`-th power**, that is, `Frob_q (x_i(u)) = x_i(u ^ q)`. This is the equation
milestone L1 asks of the untwisted families, on this branch: the numbering is fixed because the
diagram permutation of the index is the identity, which is
`diagramPerm_toGraphTwistedIndex`. -/
@[simp]
theorem steinberg_simpleRootSubgroup (i : Fin d.1.1.rank) (u : Multiplicative d.1.1.Closure) :
    d.steinberg (d.1.simpleRootSubgroup i u) =
      d.1.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.1.fieldOrder)) := by
  rw [steinberg_def]
  exact d.1.frobenius_simpleRootSubgroup i u

/-- **The Steinberg map raises every coordinate of the pinned split weight torus to the `q`-th
power.** Together with `steinberg_simpleRootSubgroup` this is the action on the pinning data of the
carrier: the torus is the split maximal torus the numbered root subgroups are normalized
against. -/
@[simp]
theorem steinberg_weightTorusPoints (s : Fin 2 → d.1.1.Closureˣ) :
    d.steinberg (SpStd.weightTorusPoints 1 d.1.1.Closure s) =
      SpStd.weightTorusPoints 1 d.1.1.Closure (s ^ d.1.1.fieldOrder) := by
  rw [steinberg_def, RankTwoBLieIndex.frobenius_def, SpStd.frobenius_weightTorusPoints,
    ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]

/-! ## The fixed points of the Steinberg map -/

/-- **A point of the ambient group is fixed by the Steinberg map exactly when all of its matrix
entries lie in the field of definition**, so the group `H_d` that the milestone L3 recipe is run on
below is the group of points of the rank-two type-`C` carrier whose entries lie in `𝔽_q`. As in
`TauCeti.RankTwoBLieIndex.mem_fixedSubgroup_frobenius_iff`, the index type is written `Fin 4` for
the carrier's own `Fin ((1 + 1) + (1 + 1))`.

It is not a `simp` lemma, for the reason recorded there: `TauCeti.fixedSubgroup` is
`MonoidHom.eqLocus` against the identity, so `simp` rewrites its left-hand side through
`MonoidHom.mem_eqLocus` and the `simpNF` linter rejects the annotation. -/
theorem mem_fixedSubgroup_steinberg_iff (g : d.1.AmbientGroup) :
    g ∈ fixedSubgroup d.steinberg ↔
      ∀ r c, ((g : Matrix.GeneralLinearGroup (Fin 4) d.1.1.Closure) :
        Matrix (Fin 4) (Fin 4) d.1.1.Closure) r c ∈ d.1.1.fixedField := by
  rw [steinberg_def]
  exact d.1.mem_fixedSubgroup_frobenius_iff g

-- The parameter of a raising point is one of its own matrix entries, which is what turns the
-- entrywise description of the fixed group into a statement about the parameter. Both numbered
-- raising generators of the rank-two carrier have an integral matrix with a `1` off the diagonal:
-- the long one is a single matrix unit, and the short one a difference of two units whose
-- rows differ. Which of the two a Bourbaki node names is immaterial, so the node is generalized
-- away before the case split.
private theorem exists_coe_simpleRootSubgroup_eq (i : Fin d.1.1.rank)
    (u : Multiplicative d.1.1.Closure) :
    ∃ r c, ((d.1.simpleRootSubgroup i u :
        Matrix.GeneralLinearGroup (Fin 4) d.1.1.Closure) :
      Matrix (Fin 4) (Fin 4) d.1.1.Closure) r c = Multiplicative.toAdd u := by
  rw [d.1.simpleRootSubgroup_def]
  generalize d.1.carrierNode i = k
  by_cases hk : k = Fin.last 1
  · refine ⟨finSumFinEquiv (Sum.inl (Fin.last 1)), finSumFinEquiv (Sum.inr (Fin.last 1)), ?_⟩
    rw [hk, SpStd.coe_rootSubgroupPoints_eq_one_add_smul, SpStd.rootIntMatrix_inl_last]
    simp
  · have h1 : (1 : Matrix (Fin (1 + 1 + (1 + 1))) (Fin (1 + 1 + (1 + 1))) d.1.1.Closure)
        (finSumFinEquiv (Sum.inl k)) (finSumFinEquiv (Sum.inl (SpStd.next 1 k hk))) = 0 :=
      Matrix.one_apply_ne fun h => (SpStd.lt_next 1 k hk).ne (by simpa using h)
    refine ⟨finSumFinEquiv (Sum.inl k), finSumFinEquiv (Sum.inl (SpStd.next 1 k hk)), ?_⟩
    rw [SpStd.coe_rootSubgroupPoints_eq_one_add_smul, SpStd.rootIntMatrix_inl_of_ne_last _ _ hk]
    simp [h1]

/-- **The fixed group meets a simple root subgroup in exactly its `𝔽_q`-points.** The point
`x_i(u)` of the ambient group is fixed by the Steinberg map precisely when its parameter lies in
the field of definition.

So the group the milestone L3 recipe is run on below contains a faithful copy of the additive group
of `𝔽_q` at each of the two Bourbaki nodes and is not a degenerate subgroup of the ambient group,
which is what makes the fixed-point construction of this branch non-vacuous. Nothing stronger is
claimed: the fixed group is not shown to be generated by these subgroups. -/
theorem simpleRootSubgroup_mem_fixedSubgroup_steinberg_iff (i : Fin d.1.1.rank)
    (u : Multiplicative d.1.1.Closure) :
    d.1.simpleRootSubgroup i u ∈ fixedSubgroup d.steinberg ↔
      Multiplicative.toAdd u ∈ d.1.1.fixedField := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨r, c, hrc⟩ := d.exists_coe_simpleRootSubgroup_eq i u
    exact hrc ▸ (d.mem_fixedSubgroup_steinberg_iff _).mp h r c
  · rw [ValidLieTypeIndex.mem_fixedField] at h
    rw [mem_fixedSubgroup, steinberg_simpleRootSubgroup, h]
    rfl

/-- **The fixed group contains the `𝔽_q`-points of the pinned split weight torus.** A torus point
whose two coordinates lie in the field of definition is fixed by the Steinberg map, so the group the
milestone L3 recipe is run on contains a copy of `(𝔽_q^×) ^ 2` beside the root subgroups above.

Only this direction is stated. The converse is not the corresponding entrywise statement, because
the matrix entries of a torus point are the values of the standard-module weights on it and not its
two coordinates, so recovering the coordinates from them needs the weight table of the carrier's
standard representation, which is not read off here. -/
theorem weightTorusPoints_mem_fixedSubgroup_steinberg {s : Fin 2 → d.1.1.Closureˣ}
    (hs : ∀ j, ((s j : d.1.1.Closure)) ∈ d.1.1.fixedField) :
    SpStd.weightTorusPoints 1 d.1.1.Closure s ∈ fixedSubgroup d.steinberg := by
  rw [mem_fixedSubgroup, steinberg_weightTorusPoints]
  congr 1
  funext j
  refine Units.ext ?_
  simpa using ValidLieTypeIndex.mem_fixedField.mp (hs j)

/-! ## The milestone L3 quotient -/

/-- **The milestone L3 quotient on the rank-two type-`C` carrier**: the derived subgroup of the
fixed points of the Steinberg map above, modulo the centre of that derived subgroup.

This is the shape milestone L3 asks of the untwisted family `B₂(q)`. It becomes the candidate simple
group of that family along the Layer 9 identification of the two carriers described in the module
docstring, and not before; it is not offered as that candidate here. Nothing below asserts that it
is finite, perfect, or simple. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

/-- Milestone L3 asks every valid branch to carry a group instance; the quotient construction
supplies it. -/
example : _root_.Group d.Group := inferInstance

end

end TypeB2LieIndex

end TauCeti
