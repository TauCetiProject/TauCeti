/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.TwistedFrobenius
public import TauCeti.GroupTheory.FixedPointCandidate
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.GraphTwisted
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly

/-!
# The graph-twisted family `²E₆(q)` on the doubled minuscule carrier

The classification list carries two families on the `E₆` diagram: the untwisted `E₆(q)`, whose
Steinberg map is the `q`-power Frobenius, and the graph-twisted `²E₆(q)`, whose Steinberg map is
that Frobenius composed with the order-two symmetry `γ₂` of the diagram. They are built on
different carriers, and that is forced rather than chosen: the `E₆` diagram symmetry exchanges the
minuscule representation `V(ϖ₁)` with its contragredient `V(ϖ₆)` rather than preserving either, so
it does not act on the `27`-dimensional carrier `TauCeti.E6Minuscule.groupScheme` that
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeE6.lean` runs the recipe on. The graph-stable carrier
is `TauCeti.E6DoubledMinuscule.groupScheme`, built on `V(ϖ₁) ⊕ V(ϖ₆)` inside `GL₅₄` over `ℤ`.

This file attaches that carrier to a validated `²E₆` index and runs the classification recipe on
it. It supplies the group of algebraic-closure-valued points and the Bourbaki-numbered simple root
subgroups, identifies the character of those subgroups with the corresponding simple root of the
`E₆` root datum, records that the involution of the fifty-four doubled coordinates realizes on the
doubled weight family the diagram permutation the index itself carries, and builds the two factors
of the branch's Steinberg map: the `q`-power Frobenius `Frob_q`, with the pinned equation
`Frob_q (x_i(u)) = x_i(u ^ q)` on the numbered simple-root subgroups, and the graph automorphism
`γ₂` that the coordinate involution induces, with the pinned equation
`γ₂ (x_i(u)) = x_{σ i}(u)` for `σ` the diagram permutation the index carries. Their composite is the
Steinberg map, and the candidate group is the derived subgroup of its fixed points modulo the
centre of that derived subgroup,

```text
H_d = fixedSubgroup d.steinberg,        d.Group = [H_d, H_d] / Z([H_d, H_d]).
```

The two factors genuinely differ on this branch: `TauCeti.TypeTwistedE6LieIndex.frobenius` is the
Steinberg map of no family on the `E₆` diagram, the untwisted family `E₆(q)` being built on the
`27`-dimensional carrier instead. Its fixed points are the points with entries in the field of
definition `𝔽_q`, whereas the entries of a point fixed by the Steinberg map lie in the quadratic
extension `𝔽_{q²}`.

Nothing here asserts that the carrier is reductive, that its weight torus is maximal, that it is
the pinned simply connected Chevalley--Demazure group scheme of type `E₆`, or that any group
mentioned is finite, perfect, or simple.

## Main declarations

* `TauCeti.TypeTwistedE6LieIndex.AmbientGroup`: the algebraic-closure-valued points of the doubled
  minuscule carrier, the group the classification recipe for `²E₆(q)` will be run inside.
* `TauCeti.TypeTwistedE6LieIndex.simpleRootSubgroup`: its positive simple-root subgroup at a
  Bourbaki-numbered node.
* `TauCeti.TypeTwistedE6LieIndex.frobenius`: the `q`-power Frobenius factor of the branch's
  Steinberg map, at the field order the index records.
* `TauCeti.TypeTwistedE6LieIndex.graphAut`: its graph automorphism factor `γ₂`.
* `TauCeti.TypeTwistedE6LieIndex.steinberg`: the Steinberg map `γ₂ ∘ Frob_q` of the branch.
* `TauCeti.TypeTwistedE6LieIndex.Group`: the classification candidate attached to the index.

## Main results

* `TauCeti.TypeTwistedE6LieIndex.rootGeneratorWeight_eq_root_simpleIndex`: the character of that
  subgroup is the corresponding simple root of
  `TauCeti.DynkinType.simplyConnectedRootDatum` at `E₆`.
* `TauCeti.TypeTwistedE6LieIndex.frobenius_simpleRootSubgroup`: the pinned equation
  `Frob_q (x_i(u)) = x_i(u ^ q)` on the numbered simple-root subgroups.
* `TauCeti.TypeTwistedE6LieIndex.mem_fixedSubgroup_frobenius_iff`: a point is fixed by `Frob_q`
  exactly when all entries of its `54 × 54` matrix lie in the field of definition.
* `TauCeti.TypeTwistedE6LieIndex.e6DoubledMinusculeWeight_e6DoubledMinusculeGraphPerm_diagramPerm`:
  the coordinate involution of the doubled index set is equivariant for the diagram permutation
  that the index itself carries, read in the index's copy `Fin d.1.rank` of the Bourbaki index
  type.
* `TauCeti.TypeTwistedE6LieIndex.e6DoubledMinusculeGraphPerm_pow_twistOrder`: the twist order the
  index records annihilates that involution.
* `TauCeti.TypeTwistedE6LieIndex.graphAut_simpleRootSubgroup`: the pinned equation
  `γ₂ (x_i(u)) = x_{σ i}(u)`, with `σ` the diagram permutation the index carries.
* `TauCeti.TypeTwistedE6LieIndex.graphAut_pow_twistOrder` and
  `TauCeti.TypeTwistedE6LieIndex.graphAut_comp_frobenius`: the two relations required of the graph
  factor, that the twist order annihilates it and that it commutes with the Frobenius factor.
* `TauCeti.TypeTwistedE6LieIndex.steinberg_simpleRootSubgroup`: the pinned equation
  `γ₂ ∘ Frob_q (x_i(u)) = x_{σ i}(u ^ q)` of the Steinberg map.
* `TauCeti.TypeTwistedE6LieIndex.mem_frobeniusFixedSubfield_of_mem_fixedSubgroup_steinberg`: the
  entries of a point fixed by the Steinberg map lie in the quadratic extension of the field of
  definition.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§12.2 and 13, for the graph automorphism of `E₆` and
  the twisted family it defines.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §§1.15 and
  1.17, for the Steinberg endomorphisms of the graph-twisted families.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V, for the numbering of the
  `E₆` diagram that the root subgroups below are indexed by.
* The target signatures realized here follow the human-authored formal skeleton
  `TauCetiRoadmap/CFSGStatement/Suggested.lean`: the ambient group and the numbered simple root
  subgroup, taken on a validated-index subtype.

## Roadmap

Milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md` asks for the points of the *pinned* simply
connected Chevalley--Demazure group scheme of `TauCeti.DynkinType.simplyConnectedRootDatum` at the
diagram the index names, with its root subgroups. **This file does not close L0, and the doubled
minuscule carrier is not offered as a substitute for that pinned group.** The pinned group scheme,
its pinning, and any identification of a carrier with it are Layer 9 targets of
`TauCetiRoadmap/ReductiveGroups/README.md` that the CFSG roadmap consumes rather than builds; none
of them is proved of `TauCeti.E6DoubledMinuscule.groupScheme` here or in the files this one
imports. What this file supplies is the `²E₆` branch's explicit carrier, its numbered root
characters read in the `E₆` root datum, the two factors of its Steinberg map with their pinned
equations `γ (x_α(t)) = x_{γ α}(t)` and `Frob_q (x_α(t)) = x_α(t ^ q)` on the simple root
subgroups, and the milestone L3 candidate group built from their composite; they transfer to the
points of the pinned group along an identification of it with this carrier, and not before. The
counterparts on the branches already assembled
are `TauCeti/GroupTheory/SpecificGroups/CFSG/TypeA.lean`,
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeE6.lean` and
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeD.lean`.
-/

public section

namespace TauCeti

namespace TypeTwistedE6LieIndex

open DynkinType

noncomputable section

variable (d : TypeTwistedE6LieIndex)

/-! ## The ambient group and its simple root subgroups -/

/-- **The ambient group this file attaches to a validated `²E₆` index**: the points of the explicit
full-weight graph-stable type-`E₆` doubled minuscule Chevalley carrier over the algebraic closure
of its prime field. No finiteness, reductivity, pinning or maximality statement is attached to it,
and it is not claimed to be the pinned `E₆` group scheme's points that milestone L0 asks for, that
identification being the Layer 9 target described in the module docstring. -/
abbrev AmbientGroup : Type := E6DoubledMinuscule.points d.1.Closure

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i` of the `E₆` diagram. It is
the carrier's numbered raising subgroup at the same node, the index type `Fin d.1.rank` being the
upstream Bourbaki index type of the index's own Dynkin type. -/
def simpleRootSubgroup (i : Fin d.1.rank) : Multiplicative d.1.Closure →* d.AmbientGroup :=
  E6DoubledMinuscule.rootSubgroupPoints (.inl (finCongr d.rank_eq_six i)) d.1.Closure

/-- The simple-root subgroup is the carrier's numbered raising subgroup at the corresponding node.
This is the equation through which the upstream root-subgroup API reaches `simpleRootSubgroup`. It
is deliberately not a `simp` lemma: the pinned equations `γ₂ (x_i(u)) = x_{σ i}(u)` and
`Frob_q (x_i(u)) = x_i(u ^ q)` of this branch's Steinberg map will be stated against
`simpleRootSubgroup` itself, and unfolding to `TauCeti.E6DoubledMinuscule.rootSubgroupPoints` would
keep them from firing, as it does on the branches already assembled. -/
theorem simpleRootSubgroup_def (i : Fin d.1.rank) :
    d.simpleRootSubgroup i =
      E6DoubledMinuscule.rootSubgroupPoints (.inl (finCongr d.rank_eq_six i)) d.1.Closure :=
  (rfl)

/-- **The simple-root subgroups sit at the simple roots of the `E₆` root datum.** The character by
which the carrier's split torus rescales the parameter of `simpleRootSubgroup i`, pinned by
`TauCeti.E6DoubledMinuscule.weightTorus_conj_rootSubgroup`, is the `i`-th simple root of
`TauCeti.DynkinType.simplyConnectedRootDatum` at `E₆`, in the same Bourbaki numbering.

The characters themselves are shared with the `27`-dimensional carrier, `TauCeti.E6Minuscule`
having defined them from the `E₆` Cartan matrix alone, so this is the same identification the
untwisted branch records in `TauCeti.TypeE6LieIndex.rootGeneratorWeight_eq_root_simpleIndex`, on
the index subtype of this branch. It is not a claim that the doubled carrier is the pinned group of
that diagram, no pinning being constructed for it. -/
theorem rootGeneratorWeight_eq_root_simpleIndex (i : Fin d.1.rank) :
    E6Minuscule.rootGeneratorWeight (.inl (finCongr d.rank_eq_six i)) =
      (E6.simplyConnectedRootDatum valid_E6).root
        (E6.simpleIndex valid_E6 (finCongr d.rank_eq_six i)) := by
  -- The uniform `root_simpleIndex` is instantiated by hand rather than rewritten with: its index
  -- argument lives in `Fin E6.rank`, which is only definitionally the `Fin 6` the carrier uses.
  have h := root_simpleIndex E6 valid_E6 (finCongr d.rank_eq_six i)
  rw [E6Minuscule.rootGeneratorWeight_inl_eq_e6Root_e6SimpleIndex, root_e6SimpleIndex, h,
    cartanMatrix_E6]

/-! ## The diagram symmetry on the carrier's coordinates -/

/-- **The coordinate involution of the doubled index set realizes the diagram permutation that the
index carries.** `TauCeti.DynkinType.e6DoubledMinusculeGraphPerm` exchanges the two minuscule
summands, and this is the equivariance `wt (π x) (σ i) = wt x i` of the doubled weight family for
it, with `σ` read as `TauCeti.GraphTwistedIndex.diagramPerm` of this index rather than as
`TauCeti.graphPermE6` directly. That equivariance is the hypothesis under which a numbered
permutation of the coordinates extends to an automorphism of a Kostant toral-closure carrier, so
stating it against the index's own permutation is what will make the resulting automorphism the
`γ₂` of milestone L1's table rather than an unrelated symmetry.

The minuscule weight family alone admits no such equivariance, by
`TauCeti.DynkinType.e6MinusculeWeight_comp_graphPermE6_notMem_range`; that is why this branch is
built on the doubled carrier. -/
theorem e6DoubledMinusculeWeight_e6DoubledMinusculeGraphPerm_diagramPerm
    (x : Fin 27 ⊕ Fin 27) (i : Fin d.1.rank) :
    e6DoubledMinusculeWeight (e6DoubledMinusculeGraphPerm x)
        (finCongr d.rank_eq_six (d.toGraphTwistedIndex.diagramPerm i)) =
      e6DoubledMinusculeWeight x (finCongr d.rank_eq_six i) := by
  -- A `finCongr` round trip preserves the underlying natural number on the nose, so the two
  -- casts cancel by `Fin.ext` rather than by an `Equiv.apply_symm_apply` rewrite, which would
  -- have to be aimed at the inner occurrence.
  have hcast (j : Fin 6) : finCongr d.rank_eq_six (finCongr d.rank_eq_six.symm j) = j :=
    Fin.ext rfl
  have hinv (j : Fin 6) : graphPermE6 (graphPermE6 j) = j := by
    rw [← Equiv.Perm.mul_apply, ← pow_two, graphPermE6_sq, Equiv.Perm.one_apply]
  rw [diagramPerm_toGraphTwistedIndex, hcast,
    e6DoubledMinusculeWeight_e6DoubledMinusculeGraphPerm, hinv]

/-- **The twist order of the index annihilates the coordinate involution.** Together with
`TauCeti.GraphTwistedIndex.diagramPerm_pow_twistOrder` on the diagram side, this is the pair of
order relations from which the graph automorphism of the carrier inherits `γ₂ ^ 2 = 1`, the
relation milestone L1 requires of the `²E₆` branch. -/
theorem e6DoubledMinusculeGraphPerm_pow_twistOrder :
    e6DoubledMinusculeGraphPerm ^ d.toGraphTwistedIndex.twistOrder = 1 := by
  rw [d.twistOrder_toGraphTwistedIndex, pow_two]
  exact Equiv.ext e6DoubledMinusculeGraphPerm_apply_apply

/-! ## The Frobenius factor of the Steinberg map -/

/-- **The `q`-power Frobenius endomorphism of the ambient group of a validated `²E₆` index**, `q`
being the field order the index records.

It is *not* the Steinberg map of the family, which for a graph-twisted family is `γ₂ ∘ Frob_q`.
On this branch the two genuinely differ: the composite acts on the simple-root subgroups through
the diagram permutation the index carries, which is `TauCeti.graphPermE6` by
`TauCeti.TypeTwistedE6LieIndex.diagramPerm_toGraphTwistedIndex` and has order two by
`TauCeti.orderOf_graphPermE6`. This is the right-hand factor of that composite, and the subgroup of
points it fixes, characterized below, is correspondingly the untwisted one and not the fixed
subgroup of the composite. -/
def frobenius : d.AmbientGroup →* d.AmbientGroup :=
  E6DoubledMinuscule.frobenius d.1.characteristic d.1.fieldExponent d.1.Closure

/-- The Frobenius of a `²E₆` index is the doubled minuscule carrier's Frobenius at the
characteristic and the exponent the index records. -/
-- Not `@[simp]`: `frobenius_simpleRootSubgroup` and `coe_frobenius_apply` are the normal forms the
-- pinned equations of this file are stated against, and unfolding to
-- `TauCeti.E6DoubledMinuscule.frobenius` would keep them from firing, as it does on the branches
-- already assembled.
theorem frobenius_def :
    d.frobenius = E6DoubledMinuscule.frobenius d.1.characteristic d.1.fieldExponent d.1.Closure :=
  (rfl)

/-- The Frobenius acts on the ambient group by raising each entry of the `54 × 54` matrix of a
point to the `q`-th power. This is the coefficient-level form from which the commutation of
`Frob_q` with a coordinate symmetry of the carrier is read. -/
@[simp]
theorem coe_frobenius_apply (g : d.AmbientGroup) (r c : Fin 54) :
    ((d.frobenius g : Matrix.GeneralLinearGroup (Fin 54) d.1.Closure) :
        Matrix (Fin 54) (Fin 54) d.1.Closure) r c =
      ((g : Matrix.GeneralLinearGroup (Fin 54) d.1.Closure) :
        Matrix (Fin 54) (Fin 54) d.1.Closure) r c ^ d.1.fieldOrder := by
  rw [frobenius_def, d.1.fieldOrder_eq_characteristic_pow]
  exact E6DoubledMinuscule.coe_frobenius_apply _ _ _ g r c

/-- **The Frobenius fixes the Bourbaki numbering of a simple-root subgroup and raises its parameter
to the `q`-th power**, that is, `Frob_q (x_i(u)) = x_i(u ^ q)`. The diagram permutation of the
twisted family enters through the other factor `γ₂` of the Steinberg map, and not through this
one. -/
@[simp]
theorem frobenius_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.frobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [frobenius_def, simpleRootSubgroup_def, E6DoubledMinuscule.frobenius_rootSubgroupPoints,
    ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]

/-- **A point of the ambient group is fixed by the Frobenius exactly when every entry of its
`54 × 54` matrix lies in the field of definition.** Writing `𝔽_q` for
`TauCeti.ValidLieTypeIndex.fixedField`, the copy of the field of `q` elements inside the algebraic
closure, the Frobenius-fixed subgroup is therefore the group of points of the doubled minuscule
carrier with coordinates in `𝔽_q`. It is not the group of points fixed by the twisted composite
`γ₂ ∘ Frob_q`, which is the one the classification recipe for this branch is run inside. -/
-- Not `@[simp]`, as for `TauCeti.ValidLieTypeIndex.mem_fixedSubgroup_geckFrobenius_iff`:
-- `TauCeti.fixedSubgroup` is `MonoidHom.eqLocus` against the identity, so `simp` rewrites the
-- left-hand side to `d.frobenius g = g` through `MonoidHom.mem_eqLocus`, and the `simpNF` linter
-- rejects the annotation.
theorem mem_fixedSubgroup_frobenius_iff (g : d.AmbientGroup) :
    g ∈ fixedSubgroup d.frobenius ↔
      ∀ r c, ((g : Matrix.GeneralLinearGroup (Fin 54) d.1.Closure) :
        Matrix (Fin 54) (Fin 54) d.1.Closure) r c ∈ d.1.fixedField := by
  rw [mem_fixedSubgroup, frobenius_def, E6DoubledMinuscule.frobenius_eq_self_iff]
  simp only [mem_frobeniusFixedSubring, ValidLieTypeIndex.mem_fixedField,
    d.1.fieldOrder_eq_characteristic_pow]

/-! ## The graph automorphism factor of the Steinberg map -/

/-- **The graph automorphism `γ₂` of the ambient group of a validated `²E₆` index**: the carrier's
pinned automorphism `TauCeti.E6DoubledMinuscule.graphAutomorphismPoints`, conjugation by the signed
monomial matrix realizing the involution of the fifty-four doubled coordinates whose equivariance
for the index's diagram permutation is
`e6DoubledMinusculeWeight_e6DoubledMinusculeGraphPerm_diagramPerm` above.

It is the left-hand factor of this branch's Steinberg map, the right-hand one being
`TauCeti.TypeTwistedE6LieIndex.frobenius`. -/
def graphAut : MulAut d.AmbientGroup :=
  E6DoubledMinuscule.graphAutomorphismPoints d.1.Closure

/-- The graph automorphism of a `²E₆` index is the doubled minuscule carrier's graph automorphism
on points. This is its unfolding lemma; the definition itself stays sealed.

It is deliberately not a `simp` lemma, for the reason `frobenius_def` is not: the pinned equations
of this file are stated against `graphAut` itself. -/
theorem graphAut_def : d.graphAut = E6DoubledMinuscule.graphAutomorphismPoints d.1.Closure := (rfl)

/-- **The graph automorphism has the pinned action on every simple-root subgroup**: it sends
`x_i(u)` to `x_{σ i}(u)`, where `σ` is the diagram permutation `TauCeti.graphPermE6` that the index
carries. The parameter is carried across unchanged, with neither a field power nor a sign; on a
general root the equation would acquire a sign forced by the Chevalley structure constants. -/
@[simp]
theorem graphAut_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.graphAut (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup (d.toGraphTwistedIndex.diagramPerm i) u := by
  -- As in `e6DoubledMinusculeWeight_e6DoubledMinusculeGraphPerm_diagramPerm`, the `finCongr` round
  -- trip left by `diagramPerm_toGraphTwistedIndex` preserves the underlying natural number on the
  -- nose, so the two casts cancel by `Fin.ext`.
  have hcast (j : Fin 6) : finCongr d.rank_eq_six (finCongr d.rank_eq_six.symm j) = j :=
    Fin.ext rfl
  rw [graphAut_def, simpleRootSubgroup_def, simpleRootSubgroup_def,
    E6DoubledMinuscule.graphAutomorphismPoints_rootSubgroupPoints,
    E6DoubledMinuscule.graphRootPerm_inl, diagramPerm_toGraphTwistedIndex, hcast]

/-- **The graph automorphism of a `²E₆` index is an involution.** -/
@[simp]
theorem graphAut_graphAut (g : d.AmbientGroup) : d.graphAut (d.graphAut g) = g := by
  rw [graphAut_def, E6DoubledMinuscule.graphAutomorphismPoints_graphAutomorphismPoints]

/-- **The twist order of a `²E₆` index annihilates its graph automorphism**, so `γ₂ ^ 2 = 1`. This
is the order relation milestone L1 asks of the graph factor of a Steinberg map, and it matches
`TauCeti.GraphTwistedIndex.diagramPerm_pow_twistOrder` on the diagram permutation that `γ₂`
realizes.

As for `e6DoubledMinusculeGraphPerm_pow_twistOrder` above, this is not a `simp` lemma: the twist
order on the left is itself rewritten to `2` by `twistOrder_toGraphTwistedIndex`, so the statement
is not in `simp` normal form. The pointwise involution `graphAut_graphAut` is the `simp` form. -/
theorem graphAut_pow_twistOrder : d.graphAut ^ d.toGraphTwistedIndex.twistOrder = 1 := by
  rw [twistOrder_toGraphTwistedIndex, graphAut_def]
  exact E6DoubledMinuscule.graphAutomorphismPoints_sq _

/-- **The graph automorphism commutes with the Frobenius.** -/
theorem graphAut_frobenius (g : d.AmbientGroup) :
    d.graphAut (d.frobenius g) = d.frobenius (d.graphAut g) := by
  rw [graphAut_def, frobenius_def]
  exact E6DoubledMinuscule.graphAutomorphismPoints_frobenius _ _ _ g

/-- The graph automorphism commutes with the Frobenius, as an identity of endomorphisms. This is
the relation `γ₂ ∘ Frob_q = Frob_q ∘ γ₂` required of the graph-twisted families by milestone L1. -/
theorem graphAut_comp_frobenius :
    d.graphAut.toMonoidHom.comp d.frobenius = d.frobenius.comp d.graphAut.toMonoidHom :=
  MonoidHom.ext fun g => by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact d.graphAut_frobenius g

/-! ## The Steinberg endomorphism -/

/-- **The Steinberg endomorphism of a validated `²E₆` index**: the composite `γ₂ ∘ Frob_q` of the
graph automorphism with the `q`-power Frobenius, `q` being the field order the index records. This
is what milestone L1's table asks of a graph-twisted family; the untwisted family `E₆(q)` takes the
Frobenius alone, on a different carrier. -/
def steinberg : d.AmbientGroup →* d.AmbientGroup :=
  E6DoubledMinuscule.twistedFrobenius d.1.characteristic d.1.fieldExponent d.1.Closure

/-- The Steinberg map of a `²E₆` index is the carrier's graph-twisted Frobenius at the exponent the
index records. This is its unfolding lemma; the definition itself stays sealed.

It is deliberately not a `simp` lemma: `steinberg_simpleRootSubgroup` is the normal form the pinned
equation of this file is stated against, and unfolding to
`TauCeti.E6DoubledMinuscule.twistedFrobenius` would keep it from firing. -/
theorem steinberg_def :
    d.steinberg =
      E6DoubledMinuscule.twistedFrobenius d.1.characteristic d.1.fieldExponent d.1.Closure :=
  (rfl)

/-- **The Steinberg map of a `²E₆` index is its graph automorphism composed with its Frobenius.**
This is the factorization by which the two order relations proved above become relations about the
Steinberg map. -/
theorem steinberg_eq_graphAut_comp_frobenius :
    d.steinberg = d.graphAut.toMonoidHom.comp d.frobenius :=
  MonoidHom.ext fun g => by
    rw [steinberg_def, E6DoubledMinuscule.twistedFrobenius_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, graphAut_def, frobenius_def]

/-- The Steinberg map may equally be read with its Frobenius factor last, the two factors
commuting. -/
theorem steinberg_eq_frobenius_comp_graphAut :
    d.steinberg = d.frobenius.comp d.graphAut.toMonoidHom := by
  rw [steinberg_eq_graphAut_comp_frobenius, graphAut_comp_frobenius]

/-- **The Steinberg map renumbers a simple-root subgroup by the diagram permutation and raises its
parameter to the `q`-th power**, that is, `γ₂ ∘ Frob_q (x_i(u)) = x_{σ i}(u ^ q)`. This is the
equation milestone L1 asks of the graph-twisted families. -/
@[simp]
theorem steinberg_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.steinberg (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup (d.toGraphTwistedIndex.diagramPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [steinberg_eq_graphAut_comp_frobenius, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    frobenius_simpleRootSubgroup, graphAut_simpleRootSubgroup]

/-- **Every matrix entry of a point fixed by the Steinberg map lies in the quadratic extension of
the field of definition**, the subfield of the closure fixed by the `q ^ 2`-power Frobenius. The
exponent `2` is the twist order the index records, `twistOrder_toGraphTwistedIndex`, and
`TauCeti.ValidLieTypeIndex.mem_frobeniusFixedSubfield_iff_iterate_frobeniusEquiv_eq` reads
membership in the subfield displayed as being fixed by the second iterate of the index's own
Frobenius. This is the sense in which `²E₆(q)` is realized by `54 × 54` matrices over `𝔽_{q²}`
while its Frobenius parameter is `q`.

Only this containment holds, and not the converse: the untwisted group over `𝔽_{q²}` is strictly
larger than the twisted one, which is why the corresponding statement for the Frobenius factor,
`mem_fixedSubgroup_frobenius_iff`, is an equivalence and this one is not. -/
theorem mem_frobeniusFixedSubfield_of_mem_fixedSubgroup_steinberg {g : d.AmbientGroup}
    (hg : g ∈ fixedSubgroup d.steinberg) (r c : Fin 54) :
    ((g : Matrix.GeneralLinearGroup (Fin 54) d.1.Closure) :
        Matrix (Fin 54) (Fin 54) d.1.Closure) r c ∈
      frobeniusFixedSubfield d.1.Closure d.1.characteristic (d.1.fieldExponent * 2) := by
  have hfix : E6DoubledMinuscule.twistedFrobenius d.1.characteristic d.1.fieldExponent
      d.1.Closure g = g := by
    rw [← steinberg_def]
    exact mem_fixedSubgroup.mp hg
  rw [← Subfield.mem_toSubring, toSubring_frobeniusFixedSubfield,
    Nat.mul_comm d.1.fieldExponent 2]
  exact E6DoubledMinuscule.mem_frobeniusFixedSubring_of_twistedFrobenius_eq_self _ _ _ hfix r c

/-! ## The classification candidate -/

/-- **The candidate simple group of the graph-twisted family `²E₆(q)`**: the derived subgroup of
the fixed points of its Steinberg map, modulo the centre of that derived subgroup.

This is the milestone L3 recipe on the `²E₆` branch, run on the doubled minuscule carrier. Nothing
below asserts that it is finite, perfect, or simple, nor that the carrier is the one milestone L0
asks for. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

/-- Milestone L3 asks every valid branch to carry a group instance; the quotient construction
supplies it. -/
example : _root_.Group d.Group := inferInstance

end

end TypeTwistedE6LieIndex

end TauCeti
