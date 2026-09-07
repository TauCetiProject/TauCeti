/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Frobenius
public import TauCeti.GroupTheory.FixedPointCandidate
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeE7.Basic

/-!
# The Steinberg endomorphism of `E₇(q)` and its finite candidate

`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeE7/Basic.lean` attaches to a validated `E₇` index the
group `TauCeti.TypeE7LieIndex.AmbientGroup` of points of the explicit full-weight minuscule
Chevalley carrier `TauCeti.E7Minuscule.groupScheme` over the algebraic closure of the index's prime
field, with its Bourbaki-numbered simple root subgroups. This file forms the endomorphism whose
fixed points cut a finite group out of that infinite ambient group, and the group the construction
of finite groups of Lie type builds from those fixed points.

The uniform ordinary Steinberg map `TauCeti.GraphTwistedIndex.geckSteinberg` is defined at an `E₇`
index too, but on a different carrier and not as a substitute for the map below: the Geck carrier
is built from the adjoint representation, whose weights span the whole character lattice exactly in
the types `E₈`, `F₄` and `G₂`, by `TauCeti.DynkinType.span_range_geckWeight_eq_top_iff`. The `E₇`
root lattice sits in the `E₇` weight lattice with index two, so the adjoint carrier is not the
simply connected form there, whereas the minuscule carrier is full-weight. That is why `E₈(q)`,
`F₄(q)` and `G₂(q)` run the recipe on the Geck carrier in
`TauCeti/GroupTheory/SpecificGroups/CFSG/Unimodular.lean` and `E₇(q)` runs it here.

The `E₇` diagram is a tree with no nontrivial symmetry, so the family carries no graph
automorphism and no half-Frobenius, and its Steinberg endomorphism is the `q`-power field
Frobenius outright, `q = d.fieldOrder` being the field order the index records. On the pinning
data of the carrier it acts by

```text
Frob_q (x_i(u)) = x_i(u ^ q),        Frob_q (t(s)) = t(s ^ q),
```

so it preserves both the numbered simple root subgroups and the split weight torus, raising their
parameters to the `q`-th power. Its fixed points are the carrier points all of whose matrix
entries lie in the copy `TauCeti.ValidLieTypeIndex.fixedField` of `𝔽_q` inside the closure.

Writing `H` for that fixed subgroup, the finite group the family names is

```text
[H, H] / Z([H, H]),
```

the derived subgroup of `H` modulo the centre of that derived subgroup, which is
`TauCeti.FixedPointCandidate` of the Steinberg map.

Nothing here asserts that the carrier is reductive, that its weight torus is maximal, or that the
carrier is the simply connected Chevalley--Demazure group scheme of type `E₇`; no such
identification is proved of `TauCeti.E7Minuscule.groupScheme` here or in the files this one
imports. Nor is any group below asserted to be finite, perfect, or simple. What relates the
carrier to the `E₇` diagram is the pinning equation
`TauCeti.TypeE7LieIndex.weightTorusPoints_conj_simpleRootSubgroup` proved in the file above.

## Main declarations

* `TauCeti.TypeE7LieIndex.steinberg`: the Steinberg endomorphism of the family, the `q`-power
  Frobenius of the ambient group.
* `TauCeti.TypeE7LieIndex.Group`: the finite group candidate `[H, H] / Z([H, H])` cut out by it.

## Main results

* `TauCeti.TypeE7LieIndex.steinberg_simpleRootSubgroup` and
  `TauCeti.TypeE7LieIndex.steinberg_weightTorusPoints`: the action of the Steinberg map on the
  carrier's pinning data, `Frob_q (x_i(u)) = x_i(u ^ q)` and `Frob_q (t(s)) = t(s ^ q)`.
* `TauCeti.TypeE7LieIndex.coe_steinberg_apply`: entrywise, it raises each matrix coefficient to
  its `q`-th power.
* `TauCeti.TypeE7LieIndex.mem_fixedSubgroup_steinberg_iff`: the group `H` it fixes is the group of
  carrier points with entries in the field of definition `𝔽_q`, and
  `TauCeti.TypeE7LieIndex.simpleRootSubgroup_mem_fixedSubgroup_steinberg` exhibits the
  `𝔽_q`-points of the numbered simple root subgroups inside it.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 14, for the fixed-point construction of the
  exceptional families.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17, for
  Steinberg endomorphisms.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VI, for the numbering of the
  `E₇` diagram that the root subgroups below are indexed by.
-/

public section

namespace TauCeti

namespace TypeE7LieIndex

noncomputable section

variable (d : TypeE7LieIndex)

/-! ## The Steinberg endomorphism -/

/-- **The Steinberg endomorphism of a validated `E₇` index**: the `q`-power Frobenius of the
ambient group, `q` being the field order the index records. The `E₇` diagram has no nontrivial
symmetry, so no diagram automorphism and no half-Frobenius enters;
`TauCeti.TypeE7LieIndex.diagramPerm_toGraphTwistedIndex` is the check that the diagram permutation
this index carries is trivial. -/
def steinberg : d.AmbientGroup →* d.AmbientGroup :=
  E7Minuscule.frobenius d.1.characteristic d.1.fieldExponent d.1.Closure

/-- The Steinberg map of an `E₇` index is the carrier's Frobenius at the exponent the index
records. This is its unfolding lemma; the definition itself stays sealed.

It is deliberately not a `simp` lemma: `steinberg_simpleRootSubgroup`,
`steinberg_weightTorusPoints` and `coe_steinberg_apply` are the normal forms the equations of this
file are stated against, and unfolding to `TauCeti.E7Minuscule.frobenius` would keep them from
firing. -/
theorem steinberg_def :
    d.steinberg = E7Minuscule.frobenius d.1.characteristic d.1.fieldExponent d.1.Closure :=
  (rfl)

/-- The Steinberg map acts on the ambient group by raising every matrix entry to the `q`-th
power. -/
@[simp]
theorem coe_steinberg_apply (g : d.AmbientGroup) (r c : Fin 56) :
    ((d.steinberg g : Matrix.GeneralLinearGroup (Fin 56) d.1.Closure) :
        Matrix (Fin 56) (Fin 56) d.1.Closure) r c =
      ((g : Matrix.GeneralLinearGroup (Fin 56) d.1.Closure) :
        Matrix (Fin 56) (Fin 56) d.1.Closure) r c ^ d.1.fieldOrder := by
  rw [steinberg_def, d.1.fieldOrder_eq_characteristic_pow]
  exact E7Minuscule.coe_frobenius_apply _ _ _ g r c

/-- **The Steinberg map fixes the Bourbaki numbering of a simple-root subgroup and raises its
parameter to the `q`-th power**, that is, `Frob_q (x_i(u)) = x_i(u ^ q)`. This is the defining
equation of an ordinary Steinberg endomorphism on the pinned simple root subgroups. -/
@[simp]
theorem steinberg_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.steinberg (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [steinberg_def, simpleRootSubgroup_def, E7Minuscule.frobenius_rootSubgroupPoints,
    d.1.fieldOrder_eq_characteristic_pow]

/-- **The Steinberg map preserves the pinned split weight torus, raising each of its coordinates
to the `q`-th power**, that is, `Frob_q (t(s)) = t(s ^ q)`. Together with
`steinberg_simpleRootSubgroup` this describes the map on the whole of the carrier's pinning
data. -/
@[simp]
theorem steinberg_weightTorusPoints (s : Fin 7 → d.1.Closureˣ) :
    d.steinberg (E7Minuscule.weightTorusPoints d.1.Closure s) =
      E7Minuscule.weightTorusPoints d.1.Closure (s ^ d.1.fieldOrder) := by
  rw [steinberg_def, E7Minuscule.frobenius_weightTorusPoints,
    d.1.fieldOrder_eq_characteristic_pow]

/-- **The fixed subgroup contains the `𝔽_q`-points of every numbered simple root subgroup.** A
simple-root point `x_i(u)` is fixed by the Steinberg map as soon as its parameter lies in the
field of definition, so the group `H` below is at least as large as the subgroup those points
generate. -/
theorem simpleRootSubgroup_mem_fixedSubgroup_steinberg (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) (hu : Multiplicative.toAdd u ∈ d.1.fixedField) :
    d.simpleRootSubgroup i u ∈ fixedSubgroup d.steinberg := by
  rw [mem_fixedSubgroup, steinberg_simpleRootSubgroup,
    ValidLieTypeIndex.mem_fixedField.mp hu, ofAdd_toAdd]

/-- **A point of the ambient group is fixed by the Steinberg map exactly when all of its matrix
entries lie in the field of definition.** Writing `𝔽_q` for
`TauCeti.ValidLieTypeIndex.fixedField`, the copy of the field of `q` elements inside the algebraic
closure, the group `H` cut out below is therefore the group of points of the minuscule carrier
whose entries lie in `𝔽_q`.

As for `TauCeti.TypeE6LieIndex.mem_fixedSubgroup_steinberg_iff`, this is not a `simp` lemma:
`TauCeti.fixedSubgroup` is `MonoidHom.eqLocus` against the identity, so `simp` rewrites its
left-hand side to `d.steinberg g = g` through `MonoidHom.mem_eqLocus`, and the `simpNF` linter
rejects the annotation. -/
theorem mem_fixedSubgroup_steinberg_iff (g : d.AmbientGroup) :
    g ∈ fixedSubgroup d.steinberg ↔
      ∀ r c, ((g : Matrix.GeneralLinearGroup (Fin 56) d.1.Closure) :
        Matrix (Fin 56) (Fin 56) d.1.Closure) r c ∈ d.1.fixedField := by
  rw [mem_fixedSubgroup, steinberg_def, E7Minuscule.frobenius_eq_self_iff]
  simp only [mem_frobeniusFixedSubring, ValidLieTypeIndex.mem_fixedField,
    d.1.fieldOrder_eq_characteristic_pow]

/-! ## The finite candidate -/

/-- **The candidate simple group of the exceptional family `E₇(q)`**: the derived subgroup of the
fixed points of its Steinberg map, modulo the centre of that derived subgroup.

Nothing here asserts that it is finite, perfect, or simple, nor that the minuscule carrier it is
formed on is the simply connected Chevalley--Demazure group scheme of type `E₇`. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

/-- The quotient construction supplies the group structure the candidate carries. -/
example : _root_.Group d.Group := inferInstance

end

end TypeE7LieIndex

end TauCeti
