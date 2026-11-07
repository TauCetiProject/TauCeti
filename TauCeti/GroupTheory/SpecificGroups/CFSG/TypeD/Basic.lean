/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Frobenius
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.GraphAutomorphism
public import TauCeti.GroupTheory.FixedPointCandidate
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.GraphTwisted
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly

/-!
# The three families on a type-`D` diagram, and the candidate groups of `Dₙ(q)` and `²Dₙ(q)`

Three classification-list families are built on the diagram `Dₙ`: the untwisted `Dₙ(q)`, the
graph-twisted `²Dₙ(q)`, and, at rank four, the triality-twisted `³D₄(q)`. They share a diagram, and
`TauCeti.TypeDDiagramLieIndex` is the subtype that collects exactly them.
This file attaches to such an index the group of algebraic-closure-valued points of Tau Ceti's
explicit full-weight type-`D` spin Chevalley carrier at the index's own rank,
`TauCeti.TypeDSpinCarrier.points`, together with that group's Bourbaki-numbered simple root
subgroups and its `q`-power Frobenius; and it then forms the Steinberg endomorphism and the
candidate group on the untwisted branch, where the Frobenius *is* the Steinberg map, and on the
graph-twisted branch, where the Steinberg map is the Frobenius composed with the fork-exchange
graph automorphism of the carrier.

The rank is available because it is at least four on this subtype, by
`TauCeti.TypeDDiagramLieIndex.four_le_rank`, which is exactly the hypothesis the carrier takes: the
carrier is built from the type-`Dₙ` Serre presentation, whose diagram is `A₁ × A₁` at rank two and
`A₃` at rank three, so it is offered only in the range where `Dₙ` is a valid Dynkin type.

The spin carrier rather than the Geck carrier is used because the Geck carrier is built from the
adjoint representation, so its weights span the whole character lattice exactly in the types `E₈`,
`F₄` and `G₂`, by `TauCeti.DynkinType.span_range_geckWeight_eq_top_iff`. A type-`D` diagram is not
one of those, by `TauCeti.LieTypeIndex.not_hasUnimodularDiagram_of_hasTypeDDiagram`, and the full
spin representation is what sees both spinor cosets of the type-`D` root lattice; its weights span
that lattice, by `TauCeti.TypeDSpinCarrier.span_range_basisWeight_eq_top`.

## The three Steinberg maps

The three families differ exactly in the endomorphism whose fixed points the classification recipe
takes. On the untwisted branch that endomorphism is the `q`-power Frobenius outright, and
`TauCeti.TypeDLieIndex.diagramPerm_toGraphTwistedIndex` checks that the diagram permutation the
index carries is trivial. So `TauCeti.TypeDLieIndex.steinberg` is the shared Frobenius, and the
recipe

```text
H_d = fixedSubgroup d.steinberg,        d.Group = [H_d, H_d] / Z([H_d, H_d])
```

runs on this branch, on the spin carrier.

On the graph-twisted branch the Steinberg map is `γ₂ ∘ Frob_q`, where `γ₂` is the graph
automorphism `TauCeti.TypeDSpinCarrier.graphAutPoints` of the carrier, conjugation by a signed
permutation matrix of the spin coordinates. It realizes the diagram permutation the index carries,
the fork exchange `TauCeti.graphPermD`, by the pinned equation `γ₂ (x_i(u)) = x_{σ i}(u)` on the
simple-root subgroups, it is an involution, and it commutes with the Frobenius, so that

```text
F = γ₂ ∘ Frob_q = Frob_q ∘ γ₂,        F (x_i(u)) = x_{σ i}(u ^ q).
```

`TauCeti.TypeTwistedDLieIndex.steinberg` is this composite and the same recipe runs on it. The
Frobenius fixed points are the points with entries in `𝔽_q`; the fixed points of the composite are
not characterized here.

The triality-twisted branch takes `γ₃ ∘ Frob_q` for an order-three symmetry that has no linear
realization on the spin module: triality permutes the three eight-dimensional representations of
`D₄`, so the spin module `8ₛ ⊕ 8_c` is not stable under it and no fixed linear automorphism of that
module realizes it. (The spin representation is faithful, so triality does act on the spin carrier
as an abstract automorphism; it is an explicit linear realization that is missing.) The `³D₄(q)`
branch is therefore built on the tripled carrier `TauCeti.D4Tripled.groupScheme`, on which triality
is a permutation of the weight basis, in `TauCeti/GroupTheory/SpecificGroups/CFSG/TrialityD4.lean`;
the spin-carrier points and Frobenius attached below to a triality-twisted index are not the
ambient group and Frobenius of that branch.

The spin carrier is not identified with the pinned simply connected Chevalley--Demazure group
scheme of type `Dₙ`, and nothing here identifies the two: the constructions below transfer to that
pinned group only along such an identification, once one is proved. Nor is it asserted that the
carrier is reductive, that its weight torus is maximal, or that any group below is finite, perfect,
or simple.

## Main declarations

* `TauCeti.TypeDDiagramLieIndex.AmbientGroup`: the algebraic-closure-valued points of the
  full-weight type-`D` spin carrier at the rank the index names, the group inside which the
  classification recipe is run on the two branches below.
* `TauCeti.TypeDDiagramLieIndex.simpleRootSubgroup`: the positive simple-root subgroup at a
  Bourbaki node.
* `TauCeti.TypeDDiagramLieIndex.rootGeneratorWeight_eq_root_simpleIndex`: the character of that
  subgroup is the corresponding simple root of the root datum of the Dynkin type the index names.
* `TauCeti.TypeDDiagramLieIndex.frobenius`, `TauCeti.TypeDDiagramLieIndex.coe_frobenius_apply` and
  `TauCeti.TypeDDiagramLieIndex.frobenius_simpleRootSubgroup`: the `q`-power Frobenius, its
  entrywise description, and its pinned equation `Frob_q (x_i(u)) = x_i(u ^ q)`.
* `TauCeti.TypeDDiagramLieIndex.mem_fixedSubgroup_frobenius_iff`: its fixed points are the points
  whose matrix entries lie in the field of definition `𝔽_q`.
* `TauCeti.TypeDLieIndex.steinberg` and `TauCeti.TypeDLieIndex.Group`: the Steinberg endomorphism
  of the untwisted family `Dₙ(q)`, which is the Frobenius, and its candidate group.
* `TauCeti.TypeTwistedDLieIndex.graphAut`, with
  `TauCeti.TypeTwistedDLieIndex.graphAut_simpleRootSubgroup`,
  `TauCeti.TypeTwistedDLieIndex.graphAut_sq`,
  `TauCeti.TypeTwistedDLieIndex.graphAut_pow_twistOrder` and
  `TauCeti.TypeTwistedDLieIndex.graphAut_comp_frobenius`: the fork-exchange graph automorphism of
  the ambient group of a `²Dₙ` index, its pinned equation `γ₂ (x_i(u)) = x_{σ i}(u)`, the relation
  `γ₂ ^ 2 = 1`, also in the form the twist order of the index states it, and its commutation with
  the Frobenius.
* `TauCeti.TypeTwistedDLieIndex.steinberg`, with `TauCeti.TypeTwistedDLieIndex.steinberg_def`,
  `TauCeti.TypeTwistedDLieIndex.steinberg_eq_frobenius_comp_graphAut` and
  `TauCeti.TypeTwistedDLieIndex.steinberg_simpleRootSubgroup`: the Steinberg endomorphism
  `γ₂ ∘ Frob_q` of `²Dₙ(q)`, its two factorizations, and its pinned equation
  `F (x_i(u)) = x_{σ i}(u ^ q)`.
* `TauCeti.TypeTwistedDLieIndex.FixedPoints` and `TauCeti.TypeTwistedDLieIndex.Group`: the fixed
  subgroup of that Steinberg map, and the candidate group of `²Dₙ(q)`.

* `TauCeti.TypeDDiagramLieIndex.primeFrobenius`, with
  `TauCeti.TypeDDiagramLieIndex.primeFrobenius_simpleRootSubgroup` and
  `TauCeti.TypeDDiagramLieIndex.frobenius_eq_primeFrobenius_pow`: the prime-field Frobenius, its
  pinned equation `Frob_p (x_i(u)) = x_i(u ^ p)`, and the `q`-power Frobenius as its `e`-th
  power.
## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II, for the spin representation the
  carrier is built from.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4, 12.2 and 14.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §§1.15 and
  1.17.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV, for the numbering of the
  `Dₙ` diagram that the index's rank and diagram permutation are read in.
-/

public section

namespace TauCeti

namespace TypeDDiagramLieIndex

noncomputable section

variable (d : TypeDDiagramLieIndex)

/-! ## The ambient group and its simple root subgroups -/

/-- **The ambient group this file attaches to a validated index on a type-`D` diagram**: the points
of the explicit full-weight type-`Dₙ` spin Chevalley carrier, at the rank the index names, over the
algebraic closure of its prime field.

It is infinite, and it is the same group for every index on the diagram of a given rank and field
order. The untwisted and graph-twisted families run their recipes inside it; the triality-twisted
family's own branch is instead built on the tripled carrier, in
`TauCeti/GroupTheory/SpecificGroups/CFSG/TrialityD4.lean`. No finiteness, reductivity, pinning or
maximality statement is attached to it, and it is not identified with the points of the pinned
simply connected `Dₙ` group scheme, as the module docstring describes. -/
abbrev AmbientGroup : Type :=
  TypeDSpinCarrier.points d.1.rank d.four_le_rank d.1.Closure

/-- The classification recipe runs its fixed-point and quotient construction inside this group, so
it carries a group structure; the carrier being a subgroup of a general linear group supplies
it. -/
example : Group d.AmbientGroup := inferInstance

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i` of the `Dₙ` diagram. It is
the carrier's numbered raising subgroup at the same node, the index type `Fin d.1.rank` being the
upstream Bourbaki index type of the index's own Dynkin type and the carrier's own rank. -/
def simpleRootSubgroup (i : Fin d.1.rank) : Multiplicative d.1.Closure →* d.AmbientGroup :=
  TypeDSpinCarrier.rootSubgroupPoints d.1.rank d.four_le_rank (.inl i) d.1.Closure

/-- The simple-root subgroup is the carrier's numbered raising subgroup at the corresponding node.
This is the equation through which the upstream root-subgroup API reaches `simpleRootSubgroup`,
whose definition itself stays sealed.

It is deliberately not a `simp` lemma: `frobenius_simpleRootSubgroup` is the normal form the pinned
equations of this file are stated against, and unfolding to
`TauCeti.TypeDSpinCarrier.rootSubgroupPoints` would keep it from firing. -/
theorem simpleRootSubgroup_def (i : Fin d.1.rank) :
    d.simpleRootSubgroup i =
      TypeDSpinCarrier.rootSubgroupPoints d.1.rank d.four_le_rank (.inl i) d.1.Closure :=
  (rfl)

/-- **The simple-root subgroups sit at the simple roots of the type-`Dₙ` root datum.** The
character by which the carrier's split torus rescales the parameter of `simpleRootSubgroup i` is
the `i`-th simple root of `TauCeti.DynkinType.simplyConnectedRootDatum` at the Dynkin type the
index names, in the same Bourbaki numbering. This is the sense in which the spin carrier serves
that diagram; it is not a claim that the carrier is the pinned group of the diagram, no pinning
being constructed for it.

The character itself is `TauCeti.TypeDStd.rootGeneratorWeight`, which
`TauCeti.TypeDSpinCarrier.weightTorusPoints_conj_rootSubgroupPoints` exhibits as the one conjugation
by the carrier's split torus rescales the parameter by. -/
theorem rootGeneratorWeight_eq_root_simpleIndex (i j : Fin d.1.rank) :
    TypeDStd.rootGeneratorWeight d.1.rank (.inl i) j =
      (d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).root
        (d.1.dynkinType.simpleIndex d.1.dynkinType_valid i) j := by
  -- Both sides are read as entries of the type-`D` Cartan matrix, the carrier's by the upstream
  -- `TypeDStd.rootGeneratorWeight_inl` and the datum's by the uniform
  -- `DynkinType.root_simpleIndex`, leaving the stated index transport
  -- `dynkinType_cartanMatrix_apply` between them.
  rw [TypeDStd.rootGeneratorWeight_inl]
  simp only [DynkinType.root_simpleIndex]
  rw [d.dynkinType_cartanMatrix_apply]

/-! ## The Frobenius endomorphism -/

/-- **The `q`-power Frobenius endomorphism of the ambient group of an index on a type-`D`
diagram**, for `q` the field order the index records. On the untwisted family `Dₙ(q)` it is the
Steinberg map itself, by `TauCeti.TypeDLieIndex.steinberg_def`. On the two twisted families it is
not: there the Steinberg map is `γ ∘ Frob_q` for a nontrivial diagram permutation, and this is the
factor that composite composes with, as `TauCeti.TypeTwistedDLieIndex.steinberg_def` records on the
graph-twisted family. -/
def frobenius : d.AmbientGroup →* d.AmbientGroup :=
  TypeDSpinCarrier.frobenius d.1.rank d.four_le_rank d.1.characteristic d.1.fieldExponent
    d.1.Closure

/-- The Frobenius of an index on a type-`D` diagram is the carrier's Frobenius at the exponent the
index records. This is its unfolding lemma; the definition itself stays sealed.

It is deliberately not a `simp` lemma: `frobenius_simpleRootSubgroup` and `coe_frobenius_apply` are
the normal forms the pinned equations of this file are stated against, and unfolding to
`TauCeti.TypeDSpinCarrier.frobenius` would keep them from firing. -/
theorem frobenius_def :
    d.frobenius =
      TypeDSpinCarrier.frobenius d.1.rank d.four_le_rank d.1.characteristic d.1.fieldExponent
        d.1.Closure :=
  (rfl)

/-- The Frobenius acts on the ambient group by raising every matrix entry to the `q`-th power. -/
@[simp]
theorem coe_frobenius_apply (g : d.AmbientGroup)
    (r c : Fin (TypeDSpinCarrier.dimension d.1.rank)) :
    ((d.frobenius g :
        Matrix.GeneralLinearGroup (Fin (TypeDSpinCarrier.dimension d.1.rank)) d.1.Closure) :
        Matrix (Fin (TypeDSpinCarrier.dimension d.1.rank))
          (Fin (TypeDSpinCarrier.dimension d.1.rank)) d.1.Closure) r c =
      ((g : Matrix.GeneralLinearGroup (Fin (TypeDSpinCarrier.dimension d.1.rank)) d.1.Closure) :
        Matrix (Fin (TypeDSpinCarrier.dimension d.1.rank))
          (Fin (TypeDSpinCarrier.dimension d.1.rank)) d.1.Closure) r c ^ d.1.fieldOrder := by
  rw [frobenius_def, d.1.fieldOrder_eq_characteristic_pow]
  exact TypeDSpinCarrier.coe_frobenius_apply _ _ _ _ _ g r c

/-- **The Frobenius fixes the Bourbaki numbering of a simple-root subgroup and raises its parameter
to the `q`-th power**, that is, `Frob_q (x_i(u)) = x_i(u ^ q)`. The diagram permutation of a
twisted family enters through the graph factor of its Steinberg map, and not through this one. -/
@[simp]
theorem frobenius_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.frobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [frobenius_def, simpleRootSubgroup_def, TypeDSpinCarrier.frobenius_rootSubgroupPoints,
    ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]

/-- **The prime-field Frobenius of the spin carrier of an index on a type-`D` diagram**, the
`p`-power map for `p` the defining characteristic. The `q`-power Frobenius is its `e`-th power, for
`e` the field exponent the index records, by `frobenius_eq_primeFrobenius_pow`. -/
def primeFrobenius : d.AmbientGroup →* d.AmbientGroup :=
  TypeDSpinCarrier.frobenius d.1.rank d.four_le_rank d.1.characteristic 1 d.1.Closure

/-- The prime-field Frobenius is the spin carrier's Frobenius at exponent one. -/
-- Not a `simp` lemma, for the reason `frobenius_def` is not.
theorem primeFrobenius_def :
    d.primeFrobenius =
      TypeDSpinCarrier.frobenius d.1.rank d.four_le_rank d.1.characteristic 1 d.1.Closure :=
  (rfl)

/-- The prime-field Frobenius acts on the ambient group by raising every matrix entry to the
`p`-th power, for `p` the defining characteristic. -/
@[simp]
theorem coe_primeFrobenius_apply (g : d.AmbientGroup)
    (r c : Fin (TypeDSpinCarrier.dimension d.1.rank)) :
    ((d.primeFrobenius g :
        Matrix.GeneralLinearGroup (Fin (TypeDSpinCarrier.dimension d.1.rank)) d.1.Closure) :
        Matrix (Fin (TypeDSpinCarrier.dimension d.1.rank))
          (Fin (TypeDSpinCarrier.dimension d.1.rank)) d.1.Closure) r c =
      ((g : Matrix.GeneralLinearGroup
          (Fin (TypeDSpinCarrier.dimension d.1.rank)) d.1.Closure) :
        Matrix (Fin (TypeDSpinCarrier.dimension d.1.rank))
          (Fin (TypeDSpinCarrier.dimension d.1.rank)) d.1.Closure) r c ^
            d.1.characteristic := by
  rw [primeFrobenius_def]
  simpa only [pow_one] using TypeDSpinCarrier.coe_frobenius_apply d.1.rank d.four_le_rank
    d.1.characteristic 1 d.1.Closure g r c

/-- **The prime-field Frobenius fixes the Bourbaki numbering of a simple-root subgroup and raises
its parameter to the `p`-th power**, that is, `Frob_p (x_i(u)) = x_i(u ^ p)`. -/
@[simp]
theorem primeFrobenius_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.primeFrobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.characteristic)) := by
  rw [primeFrobenius_def, simpleRootSubgroup_def, TypeDSpinCarrier.frobenius_rootSubgroupPoints,
    pow_one]

-- The `show` reads the prime-field Frobenius in the endomorphism monoid of the ambient group,
-- there being no power operation on `MonoidHom` itself; this is the form
-- `TauCeti.TypeDSpinCarrier.frobenius_pow` states the carrier's iteration law in.
/-- **The `q`-power Frobenius is the `e`-th power of the prime-field Frobenius**, for `e` the field
exponent the index records. -/
theorem frobenius_eq_primeFrobenius_pow :
    d.frobenius = (show Monoid.End _ from d.primeFrobenius) ^ d.1.fieldExponent := by
  rw [primeFrobenius_def, frobenius_def, TypeDSpinCarrier.frobenius_pow, Nat.one_mul]

/-- **A point of the ambient group is fixed by the Frobenius exactly when all of its matrix entries
lie in the field of definition.** Writing `𝔽_q` for `TauCeti.ValidLieTypeIndex.fixedField`, the copy
of the field of `q` elements inside the algebraic closure, the Frobenius fixed points are the points
of the spin carrier whose entries lie in `𝔽_q`.

As for `TauCeti.ValidLieTypeIndex.mem_fixedSubgroup_geckFrobenius_iff`, this is not a `simp` lemma:
`TauCeti.fixedSubgroup` is `MonoidHom.eqLocus` against the identity, so `simp` rewrites its
left-hand side to `d.frobenius g = g` through `MonoidHom.mem_eqLocus`, and the `simpNF` linter
rejects the annotation. -/
theorem mem_fixedSubgroup_frobenius_iff (g : d.AmbientGroup) :
    g ∈ fixedSubgroup d.frobenius ↔
      ∀ r c, ((g :
          Matrix.GeneralLinearGroup (Fin (TypeDSpinCarrier.dimension d.1.rank)) d.1.Closure) :
        Matrix (Fin (TypeDSpinCarrier.dimension d.1.rank))
          (Fin (TypeDSpinCarrier.dimension d.1.rank)) d.1.Closure) r c ∈ d.1.fixedField := by
  rw [mem_fixedSubgroup, frobenius_def, TypeDSpinCarrier.frobenius_eq_self_iff]
  simp only [mem_frobeniusFixedSubring, ValidLieTypeIndex.mem_fixedField,
    d.1.fieldOrder_eq_characteristic_pow]

end

end TypeDDiagramLieIndex

namespace TypeDLieIndex

noncomputable section

variable (d : TypeDLieIndex)

/-! ## The Steinberg endomorphism of the untwisted family -/

/-- **The Steinberg endomorphism of a validated untwisted type-`D` index, formed on the spin
carrier**: the `q`-power Frobenius of the ambient group, `q` being the field order the index
records. The family is untwisted, so no diagram automorphism and no half-Frobenius enters;
`diagramPerm_toGraphTwistedIndex` is the check that its diagram permutation is trivial.

It is the Steinberg map of `Dₙ(q)` on the pinned simply connected group only along an
identification of the spin carrier with that group, as the module docstring describes. -/
def steinberg :
    d.toTypeDDiagramLieIndex.AmbientGroup →* d.toTypeDDiagramLieIndex.AmbientGroup :=
  d.toTypeDDiagramLieIndex.frobenius

/-- The Steinberg map of an untwisted type-`D` index is the Frobenius that all three families on a
type-`D` diagram share. This is its unfolding lemma; the definition itself stays sealed, and it is
through this equation that the ambient-group API of `TauCeti.TypeDDiagramLieIndex` reaches the
Steinberg map. -/
theorem steinberg_def : d.steinberg = d.toTypeDDiagramLieIndex.frobenius := (rfl)

/-- **The Steinberg map fixes the Bourbaki numbering of a simple-root subgroup and raises its
parameter to the `q`-th power**, that is, `Frob_q (x_i(u)) = x_i(u ^ q)`, the pinned equation of
an untwisted family. -/
@[simp]
theorem steinberg_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.steinberg (d.toTypeDDiagramLieIndex.simpleRootSubgroup i u) =
      d.toTypeDDiagramLieIndex.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [steinberg_def]
  exact d.toTypeDDiagramLieIndex.frobenius_simpleRootSubgroup i u

/-- **A point of the ambient group is fixed by the Steinberg map exactly when all of its matrix
entries lie in the field of definition**, so the group `H_d` that the classification recipe is run
on below is the group of points of the spin carrier whose entries lie in `𝔽_q`. -/
theorem mem_fixedSubgroup_steinberg_iff (g : d.toTypeDDiagramLieIndex.AmbientGroup) :
    g ∈ fixedSubgroup d.steinberg ↔
      ∀ r c, ((g :
          Matrix.GeneralLinearGroup (Fin (TypeDSpinCarrier.dimension d.1.rank)) d.1.Closure) :
        Matrix (Fin (TypeDSpinCarrier.dimension d.1.rank))
          (Fin (TypeDSpinCarrier.dimension d.1.rank)) d.1.Closure) r c ∈ d.1.fixedField := by
  rw [steinberg_def]
  exact d.toTypeDDiagramLieIndex.mem_fixedSubgroup_frobenius_iff g

/-! ## The candidate group of the untwisted family -/

/-- **The finite-simple-group candidate attached to `Dₙ(q)`, formed on the spin carrier**: the
derived subgroup of the fixed points of the Steinberg map above, modulo the centre of that derived
subgroup. It becomes the candidate on the pinned simply connected group along an identification of
the spin carrier with that group, as the module docstring describes. No finiteness or simplicity
assertion is part of this definition. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

/-- The candidate group carries a group structure; the quotient construction supplies it. -/
example : _root_.Group d.Group := inferInstance

end

end TypeDLieIndex

namespace TypeTwistedDLieIndex

noncomputable section

variable (d : TypeTwistedDLieIndex)

/-! ## The graph automorphism factor of the Steinberg map of `²Dₙ(q)` -/

/-- **The graph automorphism of the ambient group of a validated `²Dₙ` index**: conjugation by the
signed permutation matrix of the spin coordinates that realizes the fork exchange of the `Dₙ`
diagram on the spin carrier. It sends the Bourbaki-numbered simple-root subgroup at `i` to the one
at `σ i`, for `σ` the diagram permutation the index carries, without changing its parameter, and
it is the left-hand factor `γ₂` of the Steinberg map `γ₂ ∘ Frob_q` of the family. -/
def graphAut : MulAut d.toTypeDDiagramLieIndex.AmbientGroup :=
  TypeDSpinCarrier.graphAutPoints d.1.rank d.toTypeDDiagramLieIndex.four_le_rank d.1.Closure

/-- The graph automorphism of a `²Dₙ` index is the spin carrier's graph automorphism on points at
the index's rank, over its closure. This is its unfolding lemma; the definition itself stays
sealed. -/
-- Not `@[simp]`: `graphAut_simpleRootSubgroup` and `graphAut_graphAut` are the normal forms the
-- pinned equations of this file are stated against, and unfolding to
-- `TauCeti.TypeDSpinCarrier.graphAutPoints` would keep them from firing.
theorem graphAut_def :
    d.graphAut =
      TypeDSpinCarrier.graphAutPoints d.1.rank d.toTypeDDiagramLieIndex.four_le_rank
        d.1.Closure :=
  (rfl)

/-- **The graph automorphism has the pinned action on every simple-root subgroup**: it sends
`x_i(u)` to `x_{σ i}(u)`, where `σ` is the diagram permutation the index carries, the fork
exchange. The parameter is carried across unchanged, with neither a field power nor a sign; on a
general root the equation would acquire a sign forced by the Chevalley structure constants. -/
@[simp]
theorem graphAut_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.graphAut (d.toTypeDDiagramLieIndex.simpleRootSubgroup i u) =
      d.toTypeDDiagramLieIndex.simpleRootSubgroup
        (d.toTypeDDiagramLieIndex.toGraphTwistedIndex.diagramPerm i) u := by
  rw [graphAut_def, TypeDDiagramLieIndex.simpleRootSubgroup_def,
    TypeDDiagramLieIndex.simpleRootSubgroup_def, TypeDSpinCarrier.graphAutPoints_rootSubgroupPoints,
    TypeDSpinCarrier.graphRootPerm_inl, diagramPerm_toGraphTwistedIndex]

/-- **The graph automorphism is an involution.** -/
@[simp]
theorem graphAut_graphAut (g : d.toTypeDDiagramLieIndex.AmbientGroup) :
    d.graphAut (d.graphAut g) = g := by
  rw [graphAut_def, TypeDSpinCarrier.graphAutPoints_apply_apply]

/-- **The graph automorphism squares to the identity**: `γ₂ ^ 2 = 1`. -/
@[simp]
theorem graphAut_sq : d.graphAut ^ 2 = 1 := by
  rw [pow_two]
  exact MulEquiv.ext fun g => by rw [MulAut.mul_apply, graphAut_graphAut, MulAut.one_apply]

/-- **The twist order of the index annihilates its graph automorphism.** This is the order relation
on the graph factor of the Steinberg map of a graph-twisted family, and it matches
`TauCeti.GraphTwistedIndex.diagramPerm_pow_twistOrder` on the diagram permutation that `γ₂`
realizes. -/
-- Not `@[simp]`: `twistOrder_toGraphTwistedIndex` already rewrites the exponent to `2`, after which
-- `graphAut_sq` applies.
theorem graphAut_pow_twistOrder :
    d.graphAut ^ d.toTypeDDiagramLieIndex.toGraphTwistedIndex.twistOrder = 1 := by
  rw [twistOrder_toGraphTwistedIndex, graphAut_sq]

/-- **The graph automorphism commutes with the Frobenius, as an identity of endomorphisms**:
`γ₂ ∘ Frob_q = Frob_q ∘ γ₂`. The graph automorphism is natural in the value ring, and the Frobenius
is the map on points induced by a ring endomorphism of the closure. -/
theorem graphAut_comp_frobenius :
    d.graphAut.toMonoidHom.comp d.toTypeDDiagramLieIndex.frobenius =
      d.toTypeDDiagramLieIndex.frobenius.comp d.graphAut.toMonoidHom := by
  rw [graphAut_def, TypeDDiagramLieIndex.frobenius_def, TypeDSpinCarrier.frobenius_eq_map]
  exact (TypeDSpinCarrier.map_comp_graphAutPoints _ _ _).symm

/-! ## The Steinberg endomorphism of the graph-twisted family -/

/-- **The Steinberg endomorphism of `²Dₙ(q)` on the spin carrier**: the fork-exchange graph
automorphism composed with the `q`-power Frobenius, `γ₂ ∘ Frob_q`, for `q` the field order the
index records. The two factors commute, so the order of composition is immaterial, by
`steinberg_eq_frobenius_comp_graphAut`.

It is the Steinberg map of `²Dₙ(q)` on the pinned simply connected group only along an
identification of the spin carrier with that group, as the module docstring describes. -/
def steinberg :
    d.toTypeDDiagramLieIndex.AmbientGroup →* d.toTypeDDiagramLieIndex.AmbientGroup :=
  d.graphAut.toMonoidHom.comp d.toTypeDDiagramLieIndex.frobenius

/-- **The Steinberg map of `²Dₙ(q)` is its graph automorphism composed with the shared Frobenius
of the type-`D` diagram.** This is its unfolding lemma; the definition itself stays sealed, and it
is through this equation that the two factors reach the Steinberg map. -/
-- Not `@[simp]`: `steinberg_simpleRootSubgroup` is the normal form the pinned equation of the
-- Steinberg map is stated against, and unfolding to the composite would keep it from firing.
theorem steinberg_def :
    d.steinberg = d.graphAut.toMonoidHom.comp d.toTypeDDiagramLieIndex.frobenius :=
  (rfl)

/-- The Steinberg map may equally be read with its Frobenius factor last, the two factors
commuting. -/
theorem steinberg_eq_frobenius_comp_graphAut :
    d.steinberg = d.toTypeDDiagramLieIndex.frobenius.comp d.graphAut.toMonoidHom := by
  rw [steinberg_def, graphAut_comp_frobenius]

/-- **The Steinberg map has the pinned action on every simple-root subgroup.** It sends `x_i(u)`
to `x_{σ i}(u ^ q)`, where `σ` is the diagram permutation the index carries, the fork exchange, and
`q` is its recorded field order. -/
@[simp]
theorem steinberg_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.steinberg (d.toTypeDDiagramLieIndex.simpleRootSubgroup i u) =
      d.toTypeDDiagramLieIndex.simpleRootSubgroup
        (d.toTypeDDiagramLieIndex.toGraphTwistedIndex.diagramPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [steinberg_def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    TypeDDiagramLieIndex.frobenius_simpleRootSubgroup, graphAut_simpleRootSubgroup]

/-! ## The candidate group of the graph-twisted family -/

/-- The fixed subgroup of the Steinberg endomorphism of `²Dₙ(q)`. Its points are not the points
with entries in `𝔽_q`, which are the fixed points of the Frobenius factor alone. -/
abbrev FixedPoints : Type := ↥(fixedSubgroup d.steinberg)

/-- **The finite-simple-group candidate attached to `²Dₙ(q)`, formed on the spin carrier**: the
derived subgroup of the fixed points of its Steinberg map, modulo the centre of that derived
subgroup. It becomes the candidate on the pinned simply connected group along an identification of
the spin carrier with that group, as the module docstring describes. No finiteness or simplicity
assertion is part of this definition. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

/-- The candidate group carries a group structure; the quotient construction supplies it. -/
example : _root_.Group d.Group := inferInstance

end

end TypeTwistedDLieIndex

end TauCeti
