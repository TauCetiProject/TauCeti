/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.Frobenius
public import TauCeti.Algebra.Lie.D4.Tripled.Triality
public import TauCeti.GroupTheory.FixedPointCandidate
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.GraphTwisted
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly

/-!
# The triality-twisted family `³D₄(q)` on the tripled carrier

The classification list carries three families on the `D₄` diagram: the untwisted `D₄(q)`, the
graph-twisted `²D₄(q)`, and the triality-twisted `³D₄(q)`, whose Steinberg map is the `q`-power
Frobenius composed with the order-three symmetry `γ₃` of the diagram. The first two are built on
the full-weight spin carrier in `TauCeti/GroupTheory/SpecificGroups/CFSG/TypeD.lean`. The third
needs a carrier on which triality is a linear symmetry of the representation space. Triality
permutes the three eight-dimensional representations of `D₄`, so neither the natural
representation nor the full spin module `V(ϖ₃) ⊕ V(ϖ₄)` is stable under it, and no fixed linear
automorphism of either realizes it (triality does act on the spin carrier as an abstract
automorphism, the spin representation being faithful, but not by such a matrix). The tripled
module `V(ϖ₁) ⊕ V(ϖ₃) ⊕ V(ϖ₄)` is a full-weight module that is stable. Its carrier is
`TauCeti.D4Tripled.groupScheme`, inside `GL₂₄` over `ℤ`, and triality acts on it by the
permutation of the twenty-four weight-basis vectors realized in
`TauCeti.Algebra.Lie.D4.Tripled.Triality`.

For a triality-twisted index the ambient group of the branch is the `AmbientGroup` below, on the
tripled carrier. The same index also lies in `TauCeti.TypeDDiagramLieIndex`, through
`TauCeti.TypeTrialityD4LieIndex.toTypeDDiagramLieIndex`, and so also reaches the spin-carrier
points `TauCeti.TypeDDiagramLieIndex.AmbientGroup` and their Frobenius; those are diagram-level
data shared with the untwisted and graph-twisted families, and they are not the ambient group or
the Frobenius of the `³D₄(q)` branch, which are the ones defined here.

This file attaches that carrier to a validated `³D₄` index. It supplies the group of
algebraic-closure-valued points and the Bourbaki-numbered simple root subgroups, identifies the
character of those subgroups with the corresponding simple root of the `D₄` root datum, and builds
the two factors of the Steinberg map and their composite:

```text
Frob_q (x_i(u)) = x_i(u ^ q),      γ₃ (x_i(u)) = x_{σ i}(u),      F = γ₃ ∘ Frob_q = Frob_q ∘ γ₃,
```

where `σ` is the diagram permutation the index itself carries, `TauCeti.trialityPermD4`, with
`γ₃ ^ 3 = 1`. These are the pinning equations on the numbered simple-root subgroups; no pinning of
the carrier is constructed, and `γ₃` is characterized by them only along an identification with a
pinned group. The fixed-point recipe is then run on `F`: `FixedPoints` is the fixed subgroup and
`Group` its derived subgroup modulo the centre of that derived subgroup.

Nothing here asserts that the carrier is reductive, that its weight torus is maximal, that it is
the pinned simply connected Chevalley--Demazure group scheme of type `D₄`, or that any group
mentioned is finite, perfect, or simple. No identification of this carrier with that pinned group
scheme is constructed in this module; constructions on the carrier transfer to that group only
along such an identification, once one is proved.

## Main declarations

* `TauCeti.TypeTrialityD4LieIndex.AmbientGroup`: the algebraic-closure-valued points of the
  tripled carrier, the group the classification recipe for `³D₄(q)` is run inside.
* `TauCeti.TypeTrialityD4LieIndex.simpleRootSubgroup`: its positive simple-root subgroup at a
  Bourbaki-numbered node.
* `TauCeti.TypeTrialityD4LieIndex.rootGeneratorWeight_eq_root_simpleIndex`: the character of that
  subgroup is the corresponding simple root of `TauCeti.DynkinType.simplyConnectedRootDatum`.
* `TauCeti.TypeTrialityD4LieIndex.frobenius`, `frobenius_simpleRootSubgroup` and
  `mem_fixedSubgroup_frobenius_iff`: the `q`-power Frobenius factor, its pinning equation, and its
  fixed points, the points with entries in `𝔽_q`.
* `TauCeti.TypeTrialityD4LieIndex.graphAut`, `graphAut_simpleRootSubgroup`, `graphAut_pow_three`,
  `graphAut_pow_twistOrder` and `graphAut_comp_frobenius`: the triality factor, its pinning
  equation, its order relation, and its commutation with Frobenius.
* `TauCeti.TypeTrialityD4LieIndex.steinberg`, `steinberg_def`,
  `steinberg_eq_frobenius_comp_graphAut` and `steinberg_simpleRootSubgroup`: the Steinberg map, its
  two factorizations, and its pinning equation `F (x_i(u)) = x_{σ i}(u ^ q)`.
* `TauCeti.TypeTrialityD4LieIndex.FixedPoints` and `TauCeti.TypeTrialityD4LieIndex.Group`: the
  fixed group and its derived central quotient.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§12.2 and 14, for triality and the family it
  defines.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §§1.15 and
  1.17, for the Steinberg endomorphisms of the graph-twisted families.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV, for the numbering of the
  `D₄` diagram.
* The layout follows `TauCeti.GroupTheory.SpecificGroups.CFSG.TwistedE6`, the graph-twisted
  branch on the doubled `E₆` carrier, with the involution there replaced by triality.
* K. Morrison and Claude Code,
  [Tau Ceti PR #6676](https://github.com/TauCetiProject/TauCeti/pull/6676), whose construction of
  this branch against an earlier triality API is adapted here to
  `TauCeti.D4Tripled.trialityPoints`.
-/

public section

namespace TauCeti

namespace TypeTrialityD4LieIndex

open DynkinType

noncomputable section

variable (d : TypeTrialityD4LieIndex)

/-! ## The ambient group and its simple root subgroups -/

/-- **The ambient group this file attaches to a validated `³D₄` index**: the points of the explicit
tripled type-`D₄` Chevalley carrier over the algebraic closure of its prime field. No finiteness,
reductivity, pinning or maximality statement is attached to it, and it is not claimed to be the
points of the pinned simply connected `D₄` group scheme, no identification with that group being
constructed in this module. -/
abbrev AmbientGroup : Type := D4Tripled.points d.1.Closure

/-- The fixed-point recipe runs inside this group, so it carries a group structure; the carrier
being a subgroup of a general linear group supplies it. -/
example : Group d.AmbientGroup := inferInstance

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i` of the `D₄` diagram. It is
the carrier's numbered raising subgroup at the same node, the index type `Fin d.1.rank` being the
upstream Bourbaki index type of the index's own Dynkin type. -/
def simpleRootSubgroup (i : Fin d.1.rank) : Multiplicative d.1.Closure →* d.AmbientGroup :=
  D4Tripled.rootSubgroupPoints (.inl (finCongr d.rank_eq_four i)) d.1.Closure

/-- The simple-root subgroup is the carrier's numbered raising subgroup at the corresponding node.
This is the equation through which the upstream root-subgroup API reaches `simpleRootSubgroup`,
whose definition itself stays sealed.

It is deliberately not a `simp` lemma: the pinning equations `γ₃ (x_i(u)) = x_{σ i}(u)` and
`Frob_q (x_i(u)) = x_i(u ^ q)` below are stated against `simpleRootSubgroup` itself, and unfolding
to `TauCeti.D4Tripled.rootSubgroupPoints` would keep them from firing. -/
theorem simpleRootSubgroup_def (i : Fin d.1.rank) :
    d.simpleRootSubgroup i =
      D4Tripled.rootSubgroupPoints (.inl (finCongr d.rank_eq_four i)) d.1.Closure :=
  (rfl)

/-- **The simple-root subgroups sit at the simple roots of the `D₄` root datum.** The character by
which the carrier's split torus rescales the parameter of `simpleRootSubgroup i`, given by
`TauCeti.D4Tripled.weightTorusPoints_conj_rootSubgroupPoints`, is the `i`-th simple root of
`TauCeti.DynkinType.simplyConnectedRootDatum` at the Dynkin type the index names, in the same
Bourbaki numbering. It is not a claim that the carrier is the pinned group of that diagram, no
pinning being constructed for it. -/
theorem rootGeneratorWeight_eq_root_simpleIndex (i j : Fin d.1.rank) :
    TypeDStd.rootGeneratorWeight 4 (.inl (finCongr d.rank_eq_four i)) (finCongr d.rank_eq_four j) =
      (d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).root
        (d.1.dynkinType.simpleIndex d.1.dynkinType_valid i) j := by
  -- Both sides are entries of the type-`D₄` Cartan matrix, the carrier's by
  -- `TypeDStd.rootGeneratorWeight_inl` and the datum's by the uniform
  -- `DynkinType.root_simpleIndex` followed by the rank-uniform bridge
  -- `TypeDDiagramLieIndex.dynkinType_cartanMatrix_apply`. On the introduction form of the index
  -- the rank is `4` by computation, so the two casts are the identity.
  rw [TypeDStd.rootGeneratorWeight_inl]
  simp only [DynkinType.root_simpleIndex]
  rw [d.toTypeDDiagramLieIndex.dynkinType_cartanMatrix_apply]
  obtain ⟨q, rfl⟩ := d.exists_eq_of
  rfl

/-! ## The Frobenius factor of the Steinberg map -/

/-- **The `q`-power Frobenius endomorphism of the ambient group of a validated `³D₄` index**, `q`
being the field order the index records. It is the right-hand factor of the Steinberg map
`γ₃ ∘ Frob_q`, and not that map itself. -/
def frobenius : d.AmbientGroup →* d.AmbientGroup :=
  D4Tripled.frobenius d.1.characteristic d.1.fieldExponent d.1.Closure

/-- The Frobenius of a `³D₄` index is the tripled carrier's Frobenius at the characteristic and the
exponent the index records. This is its unfolding lemma; the definition itself stays sealed. -/
-- Not `@[simp]`: `frobenius_simpleRootSubgroup` and `coe_frobenius_apply` are the normal forms the
-- pinning equations of this file are stated against, and unfolding to `TauCeti.D4Tripled.frobenius`
-- would keep them from firing.
theorem frobenius_def :
    d.frobenius = D4Tripled.frobenius d.1.characteristic d.1.fieldExponent d.1.Closure :=
  (rfl)

/-- The Frobenius acts on the ambient group by raising every entry of the `24 × 24` matrix of a
point to the `q`-th power. -/
@[simp]
theorem coe_frobenius_apply (g : d.AmbientGroup) (r c : Fin 24) :
    ((d.frobenius g : Matrix.GeneralLinearGroup (Fin 24) d.1.Closure) :
        Matrix (Fin 24) (Fin 24) d.1.Closure) r c =
      ((g : Matrix.GeneralLinearGroup (Fin 24) d.1.Closure) :
        Matrix (Fin 24) (Fin 24) d.1.Closure) r c ^ d.1.fieldOrder := by
  rw [frobenius_def, d.1.fieldOrder_eq_characteristic_pow]
  exact D4Tripled.coe_frobenius_apply _ _ _ g r c

/-- **The Frobenius fixes the Bourbaki numbering of a simple-root subgroup and raises its parameter
to the `q`-th power**, that is, `Frob_q (x_i(u)) = x_i(u ^ q)`. The diagram permutation of the
twisted family enters through the other factor `γ₃` of the Steinberg map, and not through this
one. -/
@[simp]
theorem frobenius_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.frobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [frobenius_def, simpleRootSubgroup_def, D4Tripled.frobenius_rootSubgroupPoints,
    ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]

/-- **A point of the ambient group is fixed by the Frobenius exactly when every entry of its
`24 × 24` matrix lies in the field of definition.** Writing `𝔽_q` for
`TauCeti.ValidLieTypeIndex.fixedField`, the Frobenius-fixed subgroup is the group of points of the
tripled carrier with coordinates in `𝔽_q`. It is not the group of points fixed by the twisted
composite `γ₃ ∘ Frob_q`, which is the one the classification recipe for this branch is run
inside. -/
-- Not `@[simp]`, as for `TauCeti.ValidLieTypeIndex.mem_fixedSubgroup_geckFrobenius_iff`:
-- `TauCeti.fixedSubgroup` is `MonoidHom.eqLocus` against the identity, so `simp` rewrites the
-- left-hand side to `d.frobenius g = g` through `MonoidHom.mem_eqLocus`, and the `simpNF` linter
-- rejects the annotation.
theorem mem_fixedSubgroup_frobenius_iff (g : d.AmbientGroup) :
    g ∈ fixedSubgroup d.frobenius ↔
      ∀ r c, ((g : Matrix.GeneralLinearGroup (Fin 24) d.1.Closure) :
        Matrix (Fin 24) (Fin 24) d.1.Closure) r c ∈ d.1.fixedField := by
  rw [mem_fixedSubgroup, frobenius_def, D4Tripled.frobenius_eq_self_iff]
  simp only [mem_frobeniusFixedSubring, ValidLieTypeIndex.mem_fixedField,
    d.1.fieldOrder_eq_characteristic_pow]

/-! ## The triality factor of the Steinberg map -/

/-- **The graph automorphism of a validated `³D₄` index**: triality on the points of the tripled
carrier, conjugation by the permutation matrix of `TauCeti.DynkinType.d4TripledTrialityPerm`. It
satisfies the pinning equations `γ₃ (x_i(u)) = x_{σ i}(u)` on the numbered positive simple-root
subgroups, `σ` being the diagram permutation `TauCeti.GraphTwistedIndex.diagramPerm` already
attached to the index, which is `TauCeti.trialityPermD4`; no pinning of the carrier itself is
constructed. -/
def graphAut : MulAut d.AmbientGroup :=
  D4Tripled.trialityPoints d.1.Closure

/-- The graph automorphism of a `³D₄` index is triality on the points of the tripled carrier. This
is its unfolding lemma; the definition itself stays sealed. -/
-- Not `@[simp]`: `graphAut_simpleRootSubgroup` and `graphAut_pow_three` are the normal forms the
-- pinning equations of this file are stated against, and unfolding to
-- `TauCeti.D4Tripled.trialityPoints` would keep them from firing.
theorem graphAut_def : d.graphAut = D4Tripled.trialityPoints d.1.Closure :=
  (rfl)

/-- **The graph automorphism satisfies the pinning equation on every positive simple-root
subgroup**: it sends `x_i(u)` to `x_{σ i}(u)`, where `σ` is the diagram permutation of the index,
triality. The parameter is carried across unchanged, with neither a field power nor a sign. -/
@[simp]
theorem graphAut_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.graphAut (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup (d.toTypeDDiagramLieIndex.toGraphTwistedIndex.diagramPerm i) u := by
  -- The `finCongr` round trip that `diagramPerm_toGraphTwistedIndex` introduces preserves the
  -- underlying natural number on the nose, so it cancels by `Fin.ext`.
  have hcast (j : Fin 4) : finCongr d.rank_eq_four (finCongr d.rank_eq_four.symm j) = j :=
    Fin.ext rfl
  rw [graphAut_def, simpleRootSubgroup_def, simpleRootSubgroup_def,
    D4Tripled.trialityPoints_rootSubgroupPoints, MinusculeWeightTable.Symmetry.rootPerm_inl,
    D4Tripled.trialitySymmetry_nodePerm, diagramPerm_toGraphTwistedIndex, hcast]

/-- **The graph automorphism of a `³D₄` index has order dividing three**: `γ₃ ^ 3 = 1`. -/
@[simp]
theorem graphAut_pow_three : d.graphAut ^ 3 = 1 := by
  rw [graphAut_def, D4Tripled.trialityPoints_pow_three]

/-- **The twist order of a `³D₄` index annihilates its graph automorphism.** The twist order is
three, so this is `graphAut_pow_three` read against the order the index records: the relation
required of the graph factor of the Steinberg map of the family, matching
`TauCeti.GraphTwistedIndex.diagramPerm_pow_twistOrder` on the diagram permutation that `γ₃`
realizes. -/
-- Not `@[simp]`: `twistOrder_toGraphTwistedIndex` already rewrites the exponent to `3`, after which
-- `graphAut_pow_three` applies.
theorem graphAut_pow_twistOrder :
    d.graphAut ^ d.toTypeDDiagramLieIndex.toGraphTwistedIndex.twistOrder = 1 := by
  rw [d.twistOrder_toGraphTwistedIndex, graphAut_pow_three]

/-- **The graph automorphism commutes with the Frobenius, as an identity of endomorphisms**:
`γ₃ ∘ Frob_q = Frob_q ∘ γ₃`. Triality is natural in the value ring, and the Frobenius is the map on
points induced by a ring endomorphism of the closure. -/
theorem graphAut_comp_frobenius :
    d.graphAut.toMonoidHom.comp d.frobenius = d.frobenius.comp d.graphAut.toMonoidHom := by
  rw [graphAut_def, frobenius_def, D4Tripled.frobenius_eq_pointsMap]
  exact (D4Tripled.pointsMap_comp_trialityPoints _).symm

/-! ## The Steinberg endomorphism -/

/-- **The Steinberg endomorphism of a validated `³D₄` index, formed on the tripled carrier**: the
graph automorphism `γ₃` composed with the `q`-power Frobenius of the ambient group, `q` being the
field order the index records.

It is the Steinberg map of `³D₄(q)` on the pinned simply connected carrier only along an
identification of the two carriers, of the kind described in the module docstring. -/
def steinberg : d.AmbientGroup →* d.AmbientGroup :=
  d.graphAut.toMonoidHom.comp d.frobenius

/-- **The Steinberg map of a `³D₄` index is its graph automorphism composed with its Frobenius.**
This is its unfolding lemma; the definition itself stays sealed, and it is through this equation
that the two factors reach the Steinberg map. -/
-- Not `@[simp]`: `steinberg_simpleRootSubgroup` is the normal form the pinning equation of the
-- Steinberg map is stated against, and unfolding to the composite would keep it from firing.
theorem steinberg_def : d.steinberg = d.graphAut.toMonoidHom.comp d.frobenius :=
  (rfl)

/-- The Steinberg map may equally be read with its Frobenius factor last, the two factors
commuting. -/
theorem steinberg_eq_frobenius_comp_graphAut :
    d.steinberg = d.frobenius.comp d.graphAut.toMonoidHom := by
  rw [steinberg_def, graphAut_comp_frobenius]

/-- **The Steinberg map satisfies the pinning equation on every positive simple-root subgroup.**
It sends `x_i(u)` to `x_{σ i}(u ^ q)`, where `σ` is the diagram permutation of the index,
triality, and `q` is its recorded field order. -/
@[simp]
theorem steinberg_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.steinberg (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup (d.toTypeDDiagramLieIndex.toGraphTwistedIndex.diagramPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [steinberg_def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, frobenius_simpleRootSubgroup,
    graphAut_simpleRootSubgroup]

/-! ## The finite-group candidate -/

/-- The fixed subgroup of the Steinberg endomorphism attached to a `³D₄` index. -/
abbrev FixedPoints : Type :=
  ↥(fixedSubgroup d.steinberg)

/-- **The finite-simple-group candidate attached to a `³D₄` index**: the derived subgroup of the
Steinberg fixed points, modulo the centre of that derived subgroup, formed on the tripled carrier.

No finiteness or simplicity assertion is part of this definition, nor any assertion that the
carrier is the pinned simply connected group scheme of type `D₄`; it is the candidate group of
`³D₄(q)` on that pinned carrier only along an identification of the kind described in the module
docstring. -/
abbrev Group : Type :=
  FixedPointCandidate d.steinberg

/-- The quotient construction supplies the group instance the candidate group carries. -/
example : _root_.Group d.Group := inferInstance

end

end TypeTrialityD4LieIndex

end TauCeti
