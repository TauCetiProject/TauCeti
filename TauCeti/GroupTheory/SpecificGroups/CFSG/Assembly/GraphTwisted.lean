/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.TrialityD4
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TwistedE6
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeA
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeD
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeE6
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeE7.Frobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Unimodular

/-!
# The candidate groups of the ordinary and graph-twisted Lie-type families

Thirteen of the seventeen Lie-type constructors take an ordinary Steinberg endomorphism, the field
Frobenius composed with a graph automorphism, and `TauCeti.GraphTwistedIndex` is exactly the subtype
of those thirteen. Each of them already has its own carrier, numbered simple root subgroups,
Steinberg endomorphism and candidate group, built family by family on the carrier assigned to it:

| Constructors | Family API |
| --- | --- |
| `A`, `twistedA` | `TauCeti.TypeALieIndex`, on the special linear carrier |
| `B` | `TauCeti.TypeBLieIndex`, on the full-weight type-`B` spin carrier |
| `C` | `TauCeti.TypeCLieIndex`, on the standard symplectic carrier |
| `D` | `TauCeti.TypeDLieIndex`, on the full-weight type-`D` spin carrier |
| `twistedD` | `TauCeti.TypeTwistedDLieIndex`, on the same spin carrier |
| `trialityD4` | `TauCeti.TypeTrialityD4LieIndex`, on the tripled `D₄` carrier |
| `E6` | `TauCeti.TypeE6LieIndex`, on the `27`-dimensional minuscule carrier |
| `twistedE6` | `TauCeti.TypeTwistedE6LieIndex`, on the doubled minuscule carrier |
| `E7` | `TauCeti.TypeE7LieIndex`, on the `56`-dimensional minuscule carrier |
| `E8`, `F4`, `G2` | `TauCeti.UnimodularExceptionalIndex`, on the Geck carrier |

This file joins them into one construction on `TauCeti.GraphTwistedIndex`, by cases on the
constructor: the ambient group `TauCeti.GraphTwistedIndex.AmbientGroup`, its numbered simple root
subgroups, its `q`-power Frobenius, the Steinberg endomorphism, its fixed points, and the candidate
group `TauCeti.GraphTwistedIndex.Group`, the derived subgroup of the fixed points modulo its centre.
Each branch is the family construction, with no new carrier or map; the branch equations
`TauCeti.GraphTwistedIndex.steinberg_A` and its twelve siblings, and likewise for the simple root
subgroups and the Frobenius, say which one. The four Suzuki--Ree and Tits constructors are not
indices of the subtype, and their branches are closed by that hypothesis rather than by a chosen
value.

The two factors of the Steinberg endomorphism are assembled separately as well: its Frobenius
factor is `TauCeti.GraphTwistedIndex.frobenius` and its graph factor is
`TauCeti.GraphTwistedIndex.graphAut`, the automorphism of the ambient group realizing the diagram
permutation the index carries, the identity on the nine untwisted families. They recompose by
`TauCeti.GraphTwistedIndex.steinberg_eq_graphAut_comp_frobenius`, in either order since they
commute.

What the assembly buys is a single statement of the pinned equations for all thirteen families,
`TauCeti.GraphTwistedIndex.frobenius_simpleRootSubgroup` and
`TauCeti.GraphTwistedIndex.steinberg_simpleRootSubgroup`:

```text
Frob_q (x_i(u)) = x_i(u ^ q),        F (x_i(u)) = x_{σ i}(u ^ q),
```

where `σ` is `TauCeti.GraphTwistedIndex.diagramPerm`, the identity on the nine untwisted families,
and `q` is the field order the index records. On those nine families the Steinberg endomorphism is
the Frobenius itself, `TauCeti.GraphTwistedIndex.steinberg_eq_frobenius`: the `A`, `B`, `C` and
`D` family APIs name their Frobenius separately and the assembly takes it, while the `E₆`, `E₇`,
`E₈`, `F₄` and `G₂` family APIs name only the Steinberg endomorphism, which is the Frobenius, and
the assembly takes that. On the four graph-twisted families the Steinberg endomorphism is the graph
automorphism composed with the Frobenius, and the Frobenius is the right-hand factor of that
composite.

Every carrier used here is an explicit one, and none is identified with the pinned simply connected
group scheme of its diagram; the constructions transfer to that pinned group only along such an
identification, once one is proved. Nothing here asserts that a candidate group is finite, perfect
or simple.

## Main definitions

* `TauCeti.GraphTwistedIndex.AmbientGroup`: the ambient group of an ordinary or graph-twisted
  index, with its group structure `TauCeti.GraphTwistedIndex.instGroupAmbientGroup`.
* `TauCeti.GraphTwistedIndex.simpleRootSubgroup`: its Bourbaki-numbered positive simple root
  subgroups.
* `TauCeti.GraphTwistedIndex.frobenius`: its `q`-power Frobenius endomorphism.
* `TauCeti.GraphTwistedIndex.graphAut`: its graph automorphism, the other factor.
* `TauCeti.GraphTwistedIndex.steinberg`: its Steinberg endomorphism.
* `TauCeti.GraphTwistedIndex.FixedPoints` and `TauCeti.GraphTwistedIndex.Group`: the fixed points of
  the Steinberg endomorphism and the candidate group.

## Main results

* `TauCeti.GraphTwistedIndex.frobenius_simpleRootSubgroup` and
  `TauCeti.GraphTwistedIndex.steinberg_simpleRootSubgroup`: the pinned equations of the Frobenius
  and of the Steinberg endomorphism on every simple root subgroup, uniformly in the thirteen
  families.
* `TauCeti.GraphTwistedIndex.graphAut_simpleRootSubgroup`,
  `TauCeti.GraphTwistedIndex.graphAut_pow_twistOrder` and
  `TauCeti.GraphTwistedIndex.graphAut_comp_frobenius`: the graph automorphism sends `x_i(u)` to
  `x_{σ i}(u)`, is annihilated by the twist order of the index, and commutes with the Frobenius.
* `TauCeti.GraphTwistedIndex.steinberg_eq_graphAut_comp_frobenius` and
  `TauCeti.GraphTwistedIndex.steinberg_eq_frobenius_comp_graphAut`: the Steinberg endomorphism is
  the composite of the two factors, in either order.
* `TauCeti.GraphTwistedIndex.steinberg_eq_frobenius` and
  `TauCeti.GraphTwistedIndex.graphAut_eq_one_of_twistOrder_eq_one`: on an untwisted index the
  Steinberg endomorphism is the Frobenius and the graph factor is trivial.
* `TauCeti.GraphTwistedIndex.steinberg_A`, ..., `TauCeti.GraphTwistedIndex.steinberg_trialityD4`,
  `TauCeti.GraphTwistedIndex.frobenius_A`, ..., `TauCeti.GraphTwistedIndex.frobenius_trialityD4`,
  `TauCeti.GraphTwistedIndex.simpleRootSubgroup_A`, ...,
  `TauCeti.GraphTwistedIndex.simpleRootSubgroup_trialityD4` and
  `TauCeti.GraphTwistedIndex.graphAut_A`, ..., `TauCeti.GraphTwistedIndex.graphAut_trialityD4`: on
  each constructor the Steinberg endomorphism, the Frobenius, the simple root subgroups and the
  graph automorphism are those of the family, the last being the identity where the family API
  names none.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §§1.15 and
  1.17, for the ordinary and graph-twisted Steinberg endomorphisms.
* R. Steinberg, *Lectures on Chevalley Groups*, §3, for the graph automorphism attached to a
  symmetry of the Dynkin diagram.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* The case split on the subtype follows `TauCeti.GraphTwistedIndex.diagramPerm` in
  `TauCeti.GroupTheory.SpecificGroups.CFSG.GraphTwisted`.
-/

public section

namespace TauCeti

namespace GraphTwistedIndex

open LieTypeIndex (usesHalfFrobenius_iff)

noncomputable section

/-- **The ambient group of an ordinary or graph-twisted index**: the group of
algebraic-closure-valued points of the explicit carrier assigned to its family. It is generally
infinite, and it is not identified with the points of the pinned simply connected group scheme of
the diagram. The three families on a type-`D` diagram other than `³D₄(q)` share the spin carrier of
`TauCeti.TypeDDiagramLieIndex`, while `³D₄(q)` runs on the tripled carrier that carries
triality. -/
-- The body is exposed so that on each constructor the ambient group reduces to the family carrier:
-- the branch equations below compare maps between the two, and a consumer transferring a family
-- result to this assembly needs the same reduction.
@[expose] def AmbientGroup : GraphTwistedIndex → Type
  | ⟨⟨.A _ _, hv⟩, _⟩ | ⟨⟨.twistedA _ _, hv⟩, _⟩ => TypeALieIndex.AmbientGroup ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.B _ _, hv⟩, _⟩ => TypeBLieIndex.AmbientGroup ⟨⟨_, hv⟩, trivial⟩
  | ⟨⟨.C _ _, hv⟩, _⟩ => TypeCLieIndex.AmbientGroup ⟨⟨_, hv⟩, trivial⟩
  | ⟨⟨.D _ _, hv⟩, _⟩ | ⟨⟨.twistedD _ _, hv⟩, _⟩ =>
      TypeDDiagramLieIndex.AmbientGroup ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.E6 _, hv⟩, _⟩ => TypeE6LieIndex.AmbientGroup ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.E7 _, hv⟩, _⟩ => TypeE7LieIndex.AmbientGroup ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.E8 _, hv⟩, h⟩ | ⟨⟨.F4 _, hv⟩, h⟩ | ⟨⟨.G2 _, hv⟩, h⟩ =>
      UnimodularExceptionalIndex.AmbientGroup ⟨⟨⟨_, hv⟩, by simp⟩, h⟩
  | ⟨⟨.twistedE6 _, hv⟩, _⟩ => TypeTwistedE6LieIndex.AmbientGroup ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.trialityD4 _, hv⟩, _⟩ => TypeTrialityD4LieIndex.AmbientGroup ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.suzuki _, _⟩, hh⟩ | ⟨⟨.reeG2 _, _⟩, hh⟩ | ⟨⟨.reeF4 _, _⟩, hh⟩ | ⟨⟨.tits, _⟩, hh⟩ =>
      absurd ((usesHalfFrobenius_iff _).mpr trivial) hh

/-- The ambient group carries the group structure of the carrier it is on. -/
instance instGroupAmbientGroup : (d : GraphTwistedIndex) → Group d.AmbientGroup
  | ⟨⟨.A _ _, hv⟩, _⟩ | ⟨⟨.twistedA _ _, hv⟩, _⟩ =>
      inferInstanceAs (Group (TypeALieIndex.AmbientGroup ⟨⟨_, hv⟩, by simp⟩))
  | ⟨⟨.B _ _, hv⟩, _⟩ => inferInstanceAs (Group (TypeBLieIndex.AmbientGroup ⟨⟨_, hv⟩, trivial⟩))
  | ⟨⟨.C _ _, hv⟩, _⟩ => inferInstanceAs (Group (TypeCLieIndex.AmbientGroup ⟨⟨_, hv⟩, trivial⟩))
  | ⟨⟨.D _ _, hv⟩, _⟩ | ⟨⟨.twistedD _ _, hv⟩, _⟩ =>
      inferInstanceAs (Group (TypeDDiagramLieIndex.AmbientGroup ⟨⟨_, hv⟩, by simp⟩))
  | ⟨⟨.E6 _, hv⟩, _⟩ => inferInstanceAs (Group (TypeE6LieIndex.AmbientGroup ⟨⟨_, hv⟩, by simp⟩))
  | ⟨⟨.E7 _, hv⟩, _⟩ => inferInstanceAs (Group (TypeE7LieIndex.AmbientGroup ⟨⟨_, hv⟩, by simp⟩))
  | ⟨⟨.E8 _, hv⟩, h⟩ | ⟨⟨.F4 _, hv⟩, h⟩ | ⟨⟨.G2 _, hv⟩, h⟩ =>
      inferInstanceAs (Group (UnimodularExceptionalIndex.AmbientGroup ⟨⟨⟨_, hv⟩, by simp⟩, h⟩))
  | ⟨⟨.twistedE6 _, hv⟩, _⟩ =>
      inferInstanceAs (Group (TypeTwistedE6LieIndex.AmbientGroup ⟨⟨_, hv⟩, by simp⟩))
  | ⟨⟨.trialityD4 _, hv⟩, _⟩ =>
      inferInstanceAs (Group (TypeTrialityD4LieIndex.AmbientGroup ⟨⟨_, hv⟩, by simp⟩))
  | ⟨⟨.suzuki _, _⟩, hh⟩ | ⟨⟨.reeG2 _, _⟩, hh⟩ | ⟨⟨.reeF4 _, _⟩, hh⟩ | ⟨⟨.tits, _⟩, hh⟩ =>
      absurd ((usesHalfFrobenius_iff _).mpr trivial) hh

/-- **The positive simple root subgroup at the Bourbaki-numbered node `i`**, as a homomorphism
from the additive group of the algebraic closure. On each constructor it is the simple root
subgroup of the family's carrier, by `simpleRootSubgroup_A` and its siblings. -/
def simpleRootSubgroup :
    (d : GraphTwistedIndex) → Fin d.1.rank → Multiplicative d.1.Closure →* d.AmbientGroup
  | ⟨⟨.A _ _, hv⟩, _⟩ | ⟨⟨.twistedA _ _, hv⟩, _⟩ =>
      TypeALieIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.B _ _, hv⟩, _⟩ => TypeBLieIndex.simpleRootSubgroup ⟨⟨_, hv⟩, trivial⟩
  | ⟨⟨.C _ _, hv⟩, _⟩ => TypeCLieIndex.simpleRootSubgroup ⟨⟨_, hv⟩, trivial⟩
  | ⟨⟨.D _ _, hv⟩, _⟩ | ⟨⟨.twistedD _ _, hv⟩, _⟩ =>
      TypeDDiagramLieIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.E6 _, hv⟩, _⟩ => TypeE6LieIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.E7 _, hv⟩, _⟩ => TypeE7LieIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.E8 _, hv⟩, h⟩ | ⟨⟨.F4 _, hv⟩, h⟩ | ⟨⟨.G2 _, hv⟩, h⟩ =>
      UnimodularExceptionalIndex.simpleRootSubgroup ⟨⟨⟨_, hv⟩, by simp⟩, h⟩
  | ⟨⟨.twistedE6 _, hv⟩, _⟩ => TypeTwistedE6LieIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.trialityD4 _, hv⟩, _⟩ => TypeTrialityD4LieIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.suzuki _, _⟩, hh⟩ | ⟨⟨.reeG2 _, _⟩, hh⟩ | ⟨⟨.reeF4 _, _⟩, hh⟩ | ⟨⟨.tits, _⟩, hh⟩ =>
      absurd ((usesHalfFrobenius_iff _).mpr trivial) hh

/-- **The `q`-power Frobenius endomorphism of an ordinary or graph-twisted index**, for `q` the
field order the index records. On each constructor it is the Frobenius of the family, by
`frobenius_A` and its siblings: the family's own `frobenius` where the family API names one
(`A`, `twistedA`, `B`, `C`, `D`, `twistedD`, `twistedE6`, `trialityD4`), and the family's
Steinberg endomorphism on `E6`, `E7`, `E8`, `F4` and `G2`, where that endomorphism is the
Frobenius itself. On the nine untwisted families it agrees with `steinberg`, by
`steinberg_eq_frobenius`; on the four graph-twisted ones it is the Frobenius factor of the
family's Steinberg composite. Its action on the simple root subgroups is
`frobenius_simpleRootSubgroup`. -/
def frobenius : (d : GraphTwistedIndex) → d.AmbientGroup →* d.AmbientGroup
  | ⟨⟨.A _ _, hv⟩, _⟩ | ⟨⟨.twistedA _ _, hv⟩, _⟩ => TypeALieIndex.frobenius ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.B _ _, hv⟩, _⟩ => TypeBLieIndex.frobenius ⟨⟨_, hv⟩, trivial⟩
  | ⟨⟨.C _ _, hv⟩, _⟩ => TypeCLieIndex.frobenius ⟨⟨_, hv⟩, trivial⟩
  | ⟨⟨.D _ _, hv⟩, _⟩ | ⟨⟨.twistedD _ _, hv⟩, _⟩ =>
      TypeDDiagramLieIndex.frobenius ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.E6 _, hv⟩, _⟩ => TypeE6LieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.E7 _, hv⟩, _⟩ => TypeE7LieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.E8 _, hv⟩, h⟩ | ⟨⟨.F4 _, hv⟩, h⟩ | ⟨⟨.G2 _, hv⟩, h⟩ =>
      UnimodularExceptionalIndex.steinberg ⟨⟨⟨_, hv⟩, by simp⟩, h⟩
  | ⟨⟨.twistedE6 _, hv⟩, _⟩ => TypeTwistedE6LieIndex.frobenius ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.trialityD4 _, hv⟩, _⟩ => TypeTrialityD4LieIndex.frobenius ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.suzuki _, _⟩, hh⟩ | ⟨⟨.reeG2 _, _⟩, hh⟩ | ⟨⟨.reeF4 _, _⟩, hh⟩ | ⟨⟨.tits, _⟩, hh⟩ =>
      absurd ((usesHalfFrobenius_iff _).mpr trivial) hh

/-- **The Steinberg endomorphism of an ordinary or graph-twisted index**: the `q`-power Frobenius
on the nine untwisted families, and the graph automorphism of the family composed with it on
`²Aₙ(q)`, `²Dₙ(q)`, `²E₆(q)` and `³D₄(q)`. On each constructor it is the Steinberg endomorphism of
the family, by `steinberg_A` and its siblings; its action on the simple root subgroups is
`steinberg_simpleRootSubgroup`. -/
def steinberg : (d : GraphTwistedIndex) → d.AmbientGroup →* d.AmbientGroup
  | ⟨⟨.A _ _, hv⟩, _⟩ | ⟨⟨.twistedA _ _, hv⟩, _⟩ => TypeALieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.B _ _, hv⟩, _⟩ => TypeBLieIndex.steinberg ⟨⟨_, hv⟩, trivial⟩
  | ⟨⟨.C _ _, hv⟩, _⟩ => TypeCLieIndex.steinberg ⟨⟨_, hv⟩, trivial⟩
  | ⟨⟨.D _ _, hv⟩, _⟩ => TypeDLieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.twistedD _ _, hv⟩, _⟩ => TypeTwistedDLieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.E6 _, hv⟩, _⟩ => TypeE6LieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.E7 _, hv⟩, _⟩ => TypeE7LieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.E8 _, hv⟩, h⟩ | ⟨⟨.F4 _, hv⟩, h⟩ | ⟨⟨.G2 _, hv⟩, h⟩ =>
      UnimodularExceptionalIndex.steinberg ⟨⟨⟨_, hv⟩, by simp⟩, h⟩
  | ⟨⟨.twistedE6 _, hv⟩, _⟩ => TypeTwistedE6LieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.trialityD4 _, hv⟩, _⟩ => TypeTrialityD4LieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.suzuki _, _⟩, hh⟩ | ⟨⟨.reeG2 _, _⟩, hh⟩ | ⟨⟨.reeF4 _, _⟩, hh⟩ | ⟨⟨.tits, _⟩, hh⟩ =>
      absurd ((usesHalfFrobenius_iff _).mpr trivial) hh

/-! ### The branch equations

On each of the thirteen constructors the Steinberg endomorphism, the simple root subgroups and the
Frobenius are those of the family API the constructor belongs to. -/

section Branches

variable {n : ℕ} {q : PrimePower}

/-- On `Aₙ(q)` the Steinberg endomorphism is that of the family. -/
theorem steinberg_A (hv : (LieTypeIndex.A n q).Valid) :
    steinberg ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeALieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `Aₙ(q)` the simple root subgroups are those of the family. -/
theorem simpleRootSubgroup_A (hv : (LieTypeIndex.A n q).Valid) :
    simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeALieIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `Aₙ(q)` the Frobenius is that of the family. -/
theorem frobenius_A (hv : (LieTypeIndex.A n q).Valid) :
    frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeALieIndex.frobenius ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `²Aₙ(q)` the Steinberg endomorphism is that of the family. -/
theorem steinberg_twistedA (hv : (LieTypeIndex.twistedA n q).Valid) :
    steinberg ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeALieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `²Aₙ(q)` the simple root subgroups are those of the family. -/
theorem simpleRootSubgroup_twistedA (hv : (LieTypeIndex.twistedA n q).Valid) :
    simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeALieIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `²Aₙ(q)` the Frobenius is that of the family. -/
theorem frobenius_twistedA (hv : (LieTypeIndex.twistedA n q).Valid) :
    frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeALieIndex.frobenius ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `Bₙ(q)` the Steinberg endomorphism is that of the family. -/
theorem steinberg_B (hv : (LieTypeIndex.B n q).Valid) :
    steinberg ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeBLieIndex.steinberg ⟨⟨_, hv⟩, trivial⟩ :=
  (rfl)

/-- On `Bₙ(q)` the simple root subgroups are those of the family. -/
theorem simpleRootSubgroup_B (hv : (LieTypeIndex.B n q).Valid) :
    simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeBLieIndex.simpleRootSubgroup ⟨⟨_, hv⟩, trivial⟩ :=
  (rfl)

/-- On `Bₙ(q)` the Frobenius is that of the family. -/
theorem frobenius_B (hv : (LieTypeIndex.B n q).Valid) :
    frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeBLieIndex.frobenius ⟨⟨_, hv⟩, trivial⟩ :=
  (rfl)

/-- On `Cₙ(q)` the Steinberg endomorphism is that of the family. -/
theorem steinberg_C (hv : (LieTypeIndex.C n q).Valid) :
    steinberg ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeCLieIndex.steinberg ⟨⟨_, hv⟩, trivial⟩ :=
  (rfl)

/-- On `Cₙ(q)` the simple root subgroups are those of the family. -/
theorem simpleRootSubgroup_C (hv : (LieTypeIndex.C n q).Valid) :
    simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeCLieIndex.simpleRootSubgroup ⟨⟨_, hv⟩, trivial⟩ :=
  (rfl)

/-- On `Cₙ(q)` the Frobenius is that of the family. -/
theorem frobenius_C (hv : (LieTypeIndex.C n q).Valid) :
    frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeCLieIndex.frobenius ⟨⟨_, hv⟩, trivial⟩ :=
  (rfl)

/-- On `Dₙ(q)` the Steinberg endomorphism is that of the family. -/
theorem steinberg_D (hv : (LieTypeIndex.D n q).Valid) :
    steinberg ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeDLieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `Dₙ(q)` the simple root subgroups are those of the family. -/
theorem simpleRootSubgroup_D (hv : (LieTypeIndex.D n q).Valid) :
    simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeDDiagramLieIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `Dₙ(q)` the Frobenius is that of the family. -/
theorem frobenius_D (hv : (LieTypeIndex.D n q).Valid) :
    frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeDDiagramLieIndex.frobenius ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `²Dₙ(q)` the Steinberg endomorphism is that of the family. -/
theorem steinberg_twistedD (hv : (LieTypeIndex.twistedD n q).Valid) :
    steinberg ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeTwistedDLieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `²Dₙ(q)` the simple root subgroups are those of the family. -/
theorem simpleRootSubgroup_twistedD (hv : (LieTypeIndex.twistedD n q).Valid) :
    simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeDDiagramLieIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `²Dₙ(q)` the Frobenius is that of the family. -/
theorem frobenius_twistedD (hv : (LieTypeIndex.twistedD n q).Valid) :
    frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeDDiagramLieIndex.frobenius ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `E₆(q)` the Steinberg endomorphism is that of the family. -/
theorem steinberg_E6 (hv : (LieTypeIndex.E6 q).Valid) :
    steinberg ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeE6LieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `E₆(q)` the simple root subgroups are those of the family. -/
theorem simpleRootSubgroup_E6 (hv : (LieTypeIndex.E6 q).Valid) :
    simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeE6LieIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `E₆(q)` the Frobenius is the Steinberg endomorphism of the family, that family being
untwisted. -/
theorem frobenius_E6 (hv : (LieTypeIndex.E6 q).Valid) :
    frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeE6LieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `E₇(q)` the Steinberg endomorphism is that of the family. -/
theorem steinberg_E7 (hv : (LieTypeIndex.E7 q).Valid) :
    steinberg ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeE7LieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `E₇(q)` the simple root subgroups are those of the family. -/
theorem simpleRootSubgroup_E7 (hv : (LieTypeIndex.E7 q).Valid) :
    simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeE7LieIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `E₇(q)` the Frobenius is the Steinberg endomorphism of the family, that family being
untwisted. -/
theorem frobenius_E7 (hv : (LieTypeIndex.E7 q).Valid) :
    frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeE7LieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `E₈(q)` the Steinberg endomorphism is that of the family. -/
theorem steinberg_E8 (hv : (LieTypeIndex.E8 q).Valid) :
    steinberg ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      UnimodularExceptionalIndex.steinberg ⟨⟨⟨_, hv⟩, by simp⟩, by simp⟩ :=
  (rfl)

/-- On `E₈(q)` the simple root subgroups are those of the family. -/
theorem simpleRootSubgroup_E8 (hv : (LieTypeIndex.E8 q).Valid) :
    simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      UnimodularExceptionalIndex.simpleRootSubgroup ⟨⟨⟨_, hv⟩, by simp⟩, by simp⟩ :=
  (rfl)

/-- On `E₈(q)` the Frobenius is the Steinberg endomorphism of the family, that family being
untwisted. -/
theorem frobenius_E8 (hv : (LieTypeIndex.E8 q).Valid) :
    frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      UnimodularExceptionalIndex.steinberg ⟨⟨⟨_, hv⟩, by simp⟩, by simp⟩ :=
  (rfl)

/-- On `F₄(q)` the Steinberg endomorphism is that of the family. -/
theorem steinberg_F4 (hv : (LieTypeIndex.F4 q).Valid) :
    steinberg ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      UnimodularExceptionalIndex.steinberg ⟨⟨⟨_, hv⟩, by simp⟩, by simp⟩ :=
  (rfl)

/-- On `F₄(q)` the simple root subgroups are those of the family. -/
theorem simpleRootSubgroup_F4 (hv : (LieTypeIndex.F4 q).Valid) :
    simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      UnimodularExceptionalIndex.simpleRootSubgroup ⟨⟨⟨_, hv⟩, by simp⟩, by simp⟩ :=
  (rfl)

/-- On `F₄(q)` the Frobenius is the Steinberg endomorphism of the family, that family being
untwisted. -/
theorem frobenius_F4 (hv : (LieTypeIndex.F4 q).Valid) :
    frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      UnimodularExceptionalIndex.steinberg ⟨⟨⟨_, hv⟩, by simp⟩, by simp⟩ :=
  (rfl)

/-- On `G₂(q)` the Steinberg endomorphism is that of the family. -/
theorem steinberg_G2 (hv : (LieTypeIndex.G2 q).Valid) :
    steinberg ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      UnimodularExceptionalIndex.steinberg ⟨⟨⟨_, hv⟩, by simp⟩, by simp⟩ :=
  (rfl)

/-- On `G₂(q)` the simple root subgroups are those of the family. -/
theorem simpleRootSubgroup_G2 (hv : (LieTypeIndex.G2 q).Valid) :
    simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      UnimodularExceptionalIndex.simpleRootSubgroup ⟨⟨⟨_, hv⟩, by simp⟩, by simp⟩ :=
  (rfl)

/-- On `G₂(q)` the Frobenius is the Steinberg endomorphism of the family, that family being
untwisted. -/
theorem frobenius_G2 (hv : (LieTypeIndex.G2 q).Valid) :
    frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      UnimodularExceptionalIndex.steinberg ⟨⟨⟨_, hv⟩, by simp⟩, by simp⟩ :=
  (rfl)

/-- On `²E₆(q)` the Steinberg endomorphism is that of the family. -/
theorem steinberg_twistedE6 (hv : (LieTypeIndex.twistedE6 q).Valid) :
    steinberg ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeTwistedE6LieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `²E₆(q)` the simple root subgroups are those of the family. -/
theorem simpleRootSubgroup_twistedE6 (hv : (LieTypeIndex.twistedE6 q).Valid) :
    simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeTwistedE6LieIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `²E₆(q)` the Frobenius is that of the family. -/
theorem frobenius_twistedE6 (hv : (LieTypeIndex.twistedE6 q).Valid) :
    frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeTwistedE6LieIndex.frobenius ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `³D₄(q)` the Steinberg endomorphism is that of the family. -/
theorem steinberg_trialityD4 (hv : (LieTypeIndex.trialityD4 q).Valid) :
    steinberg ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeTrialityD4LieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `³D₄(q)` the simple root subgroups are those of the family. -/
theorem simpleRootSubgroup_trialityD4 (hv : (LieTypeIndex.trialityD4 q).Valid) :
    simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeTrialityD4LieIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `³D₄(q)` the Frobenius is that of the family. -/
theorem frobenius_trialityD4 (hv : (LieTypeIndex.trialityD4 q).Valid) :
    frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeTrialityD4LieIndex.frobenius ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

end Branches

/-! ### The pinned equations -/

/-- **The Frobenius has the pinned action on every simple root subgroup.** It sends `x_i(u)` to
`x_i(u ^ q)`, where `q` is the field order the index records. This is the defining equation of the
`q`-power Frobenius, now stated once for all thirteen families. -/
@[simp]
theorem frobenius_simpleRootSubgroup (d : GraphTwistedIndex) (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.frobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  -- As for `steinberg_simpleRootSubgroup`: the branch equations turn the uniform maps into the
  -- family ones, whose pinned Frobenius equation closes the goal.
  obtain ⟨⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, hv⟩, h⟩ := d
  · rw [frobenius_A, simpleRootSubgroup_A]
    exact TypeALieIndex.frobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [frobenius_twistedA, simpleRootSubgroup_twistedA]
    exact TypeALieIndex.frobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [frobenius_B, simpleRootSubgroup_B]
    exact TypeBLieIndex.frobenius_simpleRootSubgroup ⟨⟨_, hv⟩, trivial⟩ i u
  · rw [frobenius_C, simpleRootSubgroup_C]
    exact TypeCLieIndex.frobenius_simpleRootSubgroup ⟨⟨_, hv⟩, trivial⟩ i u
  · rw [frobenius_D, simpleRootSubgroup_D]
    exact TypeDDiagramLieIndex.frobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [frobenius_twistedD, simpleRootSubgroup_twistedD]
    exact TypeDDiagramLieIndex.frobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [frobenius_E6, simpleRootSubgroup_E6]
    exact TypeE6LieIndex.steinberg_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [frobenius_E7, simpleRootSubgroup_E7]
    exact TypeE7LieIndex.steinberg_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [frobenius_E8, simpleRootSubgroup_E8]
    exact UnimodularExceptionalIndex.steinberg_geckRootSubgroup ⟨⟨⟨_, hv⟩, by simp⟩, h⟩ (.inl i) u
  · rw [frobenius_F4, simpleRootSubgroup_F4]
    exact UnimodularExceptionalIndex.steinberg_geckRootSubgroup ⟨⟨⟨_, hv⟩, by simp⟩, h⟩ (.inl i) u
  · rw [frobenius_G2, simpleRootSubgroup_G2]
    exact UnimodularExceptionalIndex.steinberg_geckRootSubgroup ⟨⟨⟨_, hv⟩, by simp⟩, h⟩ (.inl i) u
  · rw [frobenius_twistedE6, simpleRootSubgroup_twistedE6]
    exact TypeTwistedE6LieIndex.frobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [frobenius_trialityD4, simpleRootSubgroup_trialityD4]
    exact TypeTrialityD4LieIndex.frobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  all_goals exact absurd ((usesHalfFrobenius_iff _).mpr trivial) h

/-- **The Steinberg endomorphism has the pinned action on every simple root subgroup.** It sends
`x_i(u)` to `x_{σ i}(u ^ q)`, where `σ` is the diagram permutation of the index, the identity on
the nine untwisted families, and `q` is its recorded field order. This is the defining equation of
an ordinary or graph-twisted Steinberg endomorphism, now stated once for all thirteen families. -/
@[simp]
theorem steinberg_simpleRootSubgroup (d : GraphTwistedIndex) (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.steinberg (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup (d.diagramPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  -- On each constructor the branch equations turn the uniform maps into the family ones, and the
  -- family's pinned equation closes the goal; the group structure on the ambient group is, by
  -- definition of `instGroupAmbientGroup`, the family's own. The untwisted branches also unfold
  -- the trivial diagram permutation.
  obtain ⟨⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, hv⟩, h⟩ := d
  · rw [steinberg_A, simpleRootSubgroup_A]
    exact TypeALieIndex.steinberg_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [steinberg_twistedA, simpleRootSubgroup_twistedA]
    exact TypeALieIndex.steinberg_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [steinberg_B, simpleRootSubgroup_B, diagramPerm_B, Equiv.Perm.one_apply]
    exact TypeBLieIndex.steinberg_simpleRootSubgroup ⟨⟨_, hv⟩, trivial⟩ i u
  · rw [steinberg_C, simpleRootSubgroup_C, diagramPerm_C, Equiv.Perm.one_apply]
    exact TypeCLieIndex.steinberg_simpleRootSubgroup ⟨⟨_, hv⟩, trivial⟩ i u
  · rw [steinberg_D, simpleRootSubgroup_D, diagramPerm_D, Equiv.Perm.one_apply]
    exact TypeDLieIndex.steinberg_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [steinberg_twistedD, simpleRootSubgroup_twistedD]
    exact TypeTwistedDLieIndex.steinberg_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [steinberg_E6, simpleRootSubgroup_E6, diagramPerm_E6, Equiv.Perm.one_apply]
    exact TypeE6LieIndex.steinberg_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [steinberg_E7, simpleRootSubgroup_E7, diagramPerm_E7, Equiv.Perm.one_apply]
    exact TypeE7LieIndex.steinberg_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [steinberg_E8, simpleRootSubgroup_E8, diagramPerm_E8, Equiv.Perm.one_apply]
    exact UnimodularExceptionalIndex.steinberg_geckRootSubgroup ⟨⟨⟨_, hv⟩, by simp⟩, h⟩ (.inl i) u
  · rw [steinberg_F4, simpleRootSubgroup_F4, diagramPerm_F4, Equiv.Perm.one_apply]
    exact UnimodularExceptionalIndex.steinberg_geckRootSubgroup ⟨⟨⟨_, hv⟩, by simp⟩, h⟩ (.inl i) u
  · rw [steinberg_G2, simpleRootSubgroup_G2, diagramPerm_G2, Equiv.Perm.one_apply]
    exact UnimodularExceptionalIndex.steinberg_geckRootSubgroup ⟨⟨⟨_, hv⟩, by simp⟩, h⟩ (.inl i) u
  · rw [steinberg_twistedE6, simpleRootSubgroup_twistedE6]
    exact TypeTwistedE6LieIndex.steinberg_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [steinberg_trialityD4, simpleRootSubgroup_trialityD4]
    exact TypeTrialityD4LieIndex.steinberg_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  all_goals exact absurd ((usesHalfFrobenius_iff _).mpr trivial) h

/-- **On an untwisted index the Steinberg endomorphism is the Frobenius.** The hypothesis
`d.twistOrder = 1` picks out the nine untwisted families, on which the diagram permutation is
trivial; on the four graph-twisted families the two maps differ by the graph automorphism, the
family relations `TauCeti.TypeALieIndex.steinberg_eq_graphAut_comp_frobenius`,
`TauCeti.TypeTwistedDLieIndex.steinberg_def`, `TauCeti.TypeTwistedE6LieIndex.steinberg_def` and
`TauCeti.TypeTrialityD4LieIndex.steinberg_def`. -/
theorem steinberg_eq_frobenius (d : GraphTwistedIndex) (hd : d.twistOrder = 1) :
    d.steinberg = d.frobenius := by
  -- On `E6`, `E7`, `E8`, `F4` and `G2` the two branches are the same family map; on `A`, `B`, `C`
  -- and `D` the family's own unfolding of its Steinberg endomorphism closes the goal; on the four
  -- graph-twisted constructors the twist order is `2` or `3`, against the hypothesis.
  obtain ⟨⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, hv⟩, h⟩ := d
  · rw [steinberg_A, frobenius_A, TypeALieIndex.steinberg_eq_graphAut_comp_frobenius,
      TypeALieIndex.graphAut_ofA]
    exact MonoidHom.ext fun g => by
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.one_apply]
  · exact absurd hd (by rw [twistOrder_twistedA]; decide)
  · rw [steinberg_B, frobenius_B, TypeBLieIndex.steinberg_def]
  · rw [steinberg_C, frobenius_C, TypeCLieIndex.steinberg_def]
  · rw [steinberg_D, frobenius_D, TypeDLieIndex.steinberg_def]
  · exact absurd hd (by rw [twistOrder_twistedD]; decide)
  · rw [steinberg_E6, frobenius_E6]
  · rw [steinberg_E7, frobenius_E7]
  · rw [steinberg_E8, frobenius_E8]
  · rw [steinberg_F4, frobenius_F4]
  · rw [steinberg_G2, frobenius_G2]
  · exact absurd hd (by rw [twistOrder_twistedE6]; decide)
  · exact absurd hd (by rw [twistOrder_trialityD4]; decide)
  all_goals exact absurd ((usesHalfFrobenius_iff _).mpr trivial) h

/-! ### The graph automorphism factor

The Steinberg endomorphism assembled above factors as `γ ∘ Frob_q`, and its Frobenius factor is
`frobenius`. This section assembles the remaining factor, the automorphism `γ` of the ambient
group realizing the diagram permutation the index carries, together with the three equations
that make it that factor rather than an unrelated automorphism. -/

/-- **The graph automorphism of an ordinary or graph-twisted index**: the automorphism of the
ambient group realizing the diagram permutation `TauCeti.GraphTwistedIndex.diagramPerm` the index
carries. On the four graph-twisted constructors it is the graph automorphism of the family, by
`graphAut_twistedA` and its siblings; on the nine untwisted constructors, whose diagram
permutation is trivial, it is the identity automorphism. Its action on the simple root subgroups
is `graphAut_simpleRootSubgroup`, and it is the left-hand factor of the Steinberg endomorphism, by
`steinberg_eq_graphAut_comp_frobenius`. -/
def graphAut : (d : GraphTwistedIndex) → MulAut d.AmbientGroup
  | ⟨⟨.A _ _, hv⟩, _⟩ | ⟨⟨.twistedA _ _, hv⟩, _⟩ => TypeALieIndex.graphAut ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.B _ _, _⟩, _⟩ => 1
  | ⟨⟨.C _ _, _⟩, _⟩ => 1
  | ⟨⟨.D _ _, _⟩, _⟩ => 1
  | ⟨⟨.twistedD _ _, hv⟩, _⟩ => TypeTwistedDLieIndex.graphAut ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.E6 _, _⟩, _⟩ => 1
  | ⟨⟨.E7 _, _⟩, _⟩ => 1
  | ⟨⟨.E8 _, _⟩, _⟩ | ⟨⟨.F4 _, _⟩, _⟩ | ⟨⟨.G2 _, _⟩, _⟩ => 1
  | ⟨⟨.twistedE6 _, hv⟩, _⟩ => TypeTwistedE6LieIndex.graphAut ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.trialityD4 _, hv⟩, _⟩ => TypeTrialityD4LieIndex.graphAut ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.suzuki _, _⟩, hh⟩ | ⟨⟨.reeG2 _, _⟩, hh⟩ | ⟨⟨.reeF4 _, _⟩, hh⟩ | ⟨⟨.tits, _⟩, hh⟩ =>
      absurd ((usesHalfFrobenius_iff _).mpr trivial) hh

/-! ### The branch equations of the graph automorphism

On each of the thirteen constructors the graph automorphism is that of the family the constructor
belongs to, or the identity automorphism where the family API names none. -/

section GraphAutBranches

variable {n : ℕ} {q : PrimePower}

/-- On `Aₙ(q)` the graph automorphism is that of the type-`A` family, which is trivial there. -/
theorem graphAut_A (hv : (LieTypeIndex.A n q).Valid) :
    graphAut ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeALieIndex.graphAut ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `²Aₙ(q)` the graph automorphism is that of the type-`A` family, signed reverse inverse
transpose. -/
theorem graphAut_twistedA (hv : (LieTypeIndex.twistedA n q).Valid) :
    graphAut ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeALieIndex.graphAut ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `Bₙ(q)` the graph automorphism is the identity, the `Bₙ` diagram having no automorphism:
its two root lengths are not exchanged by any permutation of the nodes preserving the Cartan
matrix. -/
theorem graphAut_B (hv : (LieTypeIndex.B n q).Valid) :
    graphAut ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 :=
  (rfl)

/-- On `Cₙ(q)` the graph automorphism is the identity, the `Cₙ` diagram having no
automorphism. -/
theorem graphAut_C (hv : (LieTypeIndex.C n q).Valid) :
    graphAut ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 :=
  (rfl)

/-- On `Dₙ(q)` the graph automorphism is the identity: the fork exchange of the `Dₙ` diagram is
the twist of `²Dₙ(q)`, and the untwisted family does not use it. -/
theorem graphAut_D (hv : (LieTypeIndex.D n q).Valid) :
    graphAut ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 :=
  (rfl)

/-- On `²Dₙ(q)` the graph automorphism is that of the family, the fork exchange of the spin
carrier. -/
theorem graphAut_twistedD (hv : (LieTypeIndex.twistedD n q).Valid) :
    graphAut ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeTwistedDLieIndex.graphAut ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `E₆(q)` the graph automorphism is the identity: the `E₆` diagram symmetry is the twist of
`²E₆(q)`, and the untwisted family does not use it. -/
theorem graphAut_E6 (hv : (LieTypeIndex.E6 q).Valid) :
    graphAut ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 :=
  (rfl)

/-- On `E₇(q)` the graph automorphism is the identity, the `E₇` diagram having no
automorphism. -/
theorem graphAut_E7 (hv : (LieTypeIndex.E7 q).Valid) :
    graphAut ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 :=
  (rfl)

/-- On `E₈(q)` the graph automorphism is the identity, the `E₈` diagram having no
automorphism. -/
theorem graphAut_E8 (hv : (LieTypeIndex.E8 q).Valid) :
    graphAut ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 :=
  (rfl)

/-- On `F₄(q)` the graph automorphism is the identity: the length-exchanging symmetry of the `F₄`
diagram is not a diagram automorphism, and this family is untwisted. -/
theorem graphAut_F4 (hv : (LieTypeIndex.F4 q).Valid) :
    graphAut ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 :=
  (rfl)

/-- On `G₂(q)` the graph automorphism is the identity: the length-exchanging symmetry of the `G₂`
diagram is not a diagram automorphism, and this family is untwisted. -/
theorem graphAut_G2 (hv : (LieTypeIndex.G2 q).Valid) :
    graphAut ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 :=
  (rfl)

/-- On `²E₆(q)` the graph automorphism is that of the family, the exchange of the two minuscule
summands of the doubled carrier. -/
theorem graphAut_twistedE6 (hv : (LieTypeIndex.twistedE6 q).Valid) :
    graphAut ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeTwistedE6LieIndex.graphAut ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `³D₄(q)` the graph automorphism is that of the family, triality on the tripled carrier. -/
theorem graphAut_trialityD4 (hv : (LieTypeIndex.trialityD4 q).Valid) :
    graphAut ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      TypeTrialityD4LieIndex.graphAut ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

end GraphAutBranches

/-! ### The pinned equations of the graph automorphism -/

/-- **On an untwisted index the graph automorphism is the identity.** The hypothesis
`d.twistOrder = 1` picks out the nine untwisted families, whose diagram permutation is trivial and
whose Steinberg endomorphism is the Frobenius outright; on the four graph-twisted families the
twist order is two or three. -/
theorem graphAut_eq_one_of_twistOrder_eq_one (d : GraphTwistedIndex) (hd : d.twistOrder = 1) :
    d.graphAut = 1 := by
  -- On the eight untwisted constructors other than `Aₙ(q)` the branch equation is the statement;
  -- on `Aₙ(q)` the type-`A` family's graph automorphism is itself trivial, that family covering
  -- both `Aₙ(q)` and `²Aₙ(q)`. The four graph-twisted constructors contradict the hypothesis.
  obtain ⟨⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, hv⟩, h⟩ := d
  · rw [graphAut_A]
    exact TypeALieIndex.graphAut_ofA _ _ hv
  · exact absurd hd (by rw [twistOrder_twistedA]; decide)
  · exact graphAut_B hv
  · exact graphAut_C hv
  · exact graphAut_D hv
  · exact absurd hd (by rw [twistOrder_twistedD]; decide)
  · exact graphAut_E6 hv
  · exact graphAut_E7 hv
  · exact graphAut_E8 hv
  · exact graphAut_F4 hv
  · exact graphAut_G2 hv
  · exact absurd hd (by rw [twistOrder_twistedE6]; decide)
  · exact absurd hd (by rw [twistOrder_trialityD4]; decide)
  all_goals exact absurd ((usesHalfFrobenius_iff _).mpr trivial) h

/-- **The graph automorphism has the pinned action on every simple root subgroup.** It sends
`x_i(u)` to `x_{σ i}(u)`, where `σ` is the diagram permutation of the index, the identity on the
nine untwisted families. The parameter is carried across unchanged, with neither a field power nor
a sign; on a general root the equation would acquire a sign forced by the Chevalley structure
constants. -/
@[simp]
theorem graphAut_simpleRootSubgroup (d : GraphTwistedIndex) (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.graphAut (d.simpleRootSubgroup i u) = d.simpleRootSubgroup (d.diagramPerm i) u := by
  -- On each constructor the branch equations turn the uniform maps into the family ones, whose
  -- pinned equation closes the goal; the untwisted branches also unfold the trivial diagram
  -- permutation and the identity automorphism.
  obtain ⟨⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, hv⟩, h⟩ := d
  · rw [graphAut_A, simpleRootSubgroup_A]
    exact TypeALieIndex.graphAut_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [graphAut_twistedA, simpleRootSubgroup_twistedA]
    exact TypeALieIndex.graphAut_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [graphAut_B, MulAut.one_apply, diagramPerm_B, Equiv.Perm.one_apply]
  · rw [graphAut_C, MulAut.one_apply, diagramPerm_C, Equiv.Perm.one_apply]
  · rw [graphAut_D, MulAut.one_apply, diagramPerm_D, Equiv.Perm.one_apply]
  · rw [graphAut_twistedD, simpleRootSubgroup_twistedD]
    exact TypeTwistedDLieIndex.graphAut_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [graphAut_E6, MulAut.one_apply, diagramPerm_E6, Equiv.Perm.one_apply]
  · rw [graphAut_E7, MulAut.one_apply, diagramPerm_E7, Equiv.Perm.one_apply]
  · rw [graphAut_E8, MulAut.one_apply, diagramPerm_E8, Equiv.Perm.one_apply]
  · rw [graphAut_F4, MulAut.one_apply, diagramPerm_F4, Equiv.Perm.one_apply]
  · rw [graphAut_G2, MulAut.one_apply, diagramPerm_G2, Equiv.Perm.one_apply]
  · rw [graphAut_twistedE6, simpleRootSubgroup_twistedE6]
    exact TypeTwistedE6LieIndex.graphAut_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [graphAut_trialityD4, simpleRootSubgroup_trialityD4]
    exact TypeTrialityD4LieIndex.graphAut_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  all_goals exact absurd ((usesHalfFrobenius_iff _).mpr trivial) h

/-- **The twist order of the index annihilates its graph automorphism**, so `γ = 1` on the nine
untwisted families, `γ ^ 2 = 1` on `²Aₙ(q)`, `²Dₙ(q)` and `²E₆(q)`, and `γ ^ 3 = 1` on `³D₄(q)`.
This matches `TauCeti.GraphTwistedIndex.diagramPerm_pow_twistOrder` on the diagram permutation
that `γ` realizes. -/
theorem graphAut_pow_twistOrder (d : GraphTwistedIndex) : d.graphAut ^ d.twistOrder = 1 := by
  -- An untwisted index has a trivial graph automorphism; on the four graph-twisted constructors
  -- the branch equation reduces the claim to the family's own order relation.
  by_cases hd : d.twistOrder = 1
  · rw [graphAut_eq_one_of_twistOrder_eq_one d hd, one_pow]
  obtain ⟨⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, hv⟩, h⟩ := d
  · exact absurd (twistOrder_A hv) hd
  · rw [graphAut_twistedA]
    exact TypeALieIndex.graphAut_pow_twistOrder ⟨⟨_, hv⟩, by simp⟩
  · exact absurd (twistOrder_B hv) hd
  · exact absurd (twistOrder_C hv) hd
  · exact absurd (twistOrder_D hv) hd
  · rw [graphAut_twistedD]
    exact TypeTwistedDLieIndex.graphAut_pow_twistOrder ⟨⟨_, hv⟩, by simp⟩
  · exact absurd (twistOrder_E6 hv) hd
  · exact absurd (twistOrder_E7 hv) hd
  · exact absurd (twistOrder_E8 hv) hd
  · exact absurd (twistOrder_F4 hv) hd
  · exact absurd (twistOrder_G2 hv) hd
  · rw [graphAut_twistedE6]
    exact TypeTwistedE6LieIndex.graphAut_pow_twistOrder ⟨⟨_, hv⟩, by simp⟩
  · rw [graphAut_trialityD4]
    exact TypeTrialityD4LieIndex.graphAut_pow_twistOrder ⟨⟨_, hv⟩, by simp⟩
  all_goals exact absurd ((usesHalfFrobenius_iff _).mpr trivial) h

/-- **The graph automorphism commutes with the Frobenius, as an identity of endomorphisms**:
`γ ∘ Frob_q = Frob_q ∘ γ`. This is what makes the order of composition immaterial in
`steinberg_eq_graphAut_comp_frobenius`, and on the graph-twisted families it is the relation that
lets a power of the Steinberg endomorphism be computed factor by factor. -/
theorem graphAut_comp_frobenius (d : GraphTwistedIndex) :
    d.graphAut.toMonoidHom.comp d.frobenius = d.frobenius.comp d.graphAut.toMonoidHom := by
  -- An untwisted index has a trivial graph automorphism, so both composites are the Frobenius;
  -- on the four graph-twisted constructors the branch equations reduce the claim to the family's
  -- own commutation.
  by_cases hd : d.twistOrder = 1
  · rw [graphAut_eq_one_of_twistOrder_eq_one d hd]
    exact MonoidHom.ext fun g => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.one_apply, MulAut.one_apply]
  obtain ⟨⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, hv⟩, h⟩ := d
  · exact absurd (twistOrder_A hv) hd
  · rw [graphAut_twistedA, frobenius_twistedA]
    exact TypeALieIndex.graphAut_comp_frobenius ⟨⟨_, hv⟩, by simp⟩
  · exact absurd (twistOrder_B hv) hd
  · exact absurd (twistOrder_C hv) hd
  · exact absurd (twistOrder_D hv) hd
  · rw [graphAut_twistedD, frobenius_twistedD]
    exact TypeTwistedDLieIndex.graphAut_comp_frobenius ⟨⟨_, hv⟩, by simp⟩
  · exact absurd (twistOrder_E6 hv) hd
  · exact absurd (twistOrder_E7 hv) hd
  · exact absurd (twistOrder_E8 hv) hd
  · exact absurd (twistOrder_F4 hv) hd
  · exact absurd (twistOrder_G2 hv) hd
  · rw [graphAut_twistedE6, frobenius_twistedE6]
    exact TypeTwistedE6LieIndex.graphAut_comp_frobenius ⟨⟨_, hv⟩, by simp⟩
  · rw [graphAut_trialityD4, frobenius_trialityD4]
    exact TypeTrialityD4LieIndex.graphAut_comp_frobenius ⟨⟨_, hv⟩, by simp⟩
  all_goals exact absurd ((usesHalfFrobenius_iff _).mpr trivial) h

/-- **The Steinberg endomorphism is the graph automorphism composed with the Frobenius**,
uniformly in the thirteen ordinary and graph-twisted families. On the nine untwisted ones the
graph factor is trivial and the composite is the Frobenius itself, which is
`TauCeti.GraphTwistedIndex.steinberg_eq_frobenius`. -/
theorem steinberg_eq_graphAut_comp_frobenius (d : GraphTwistedIndex) :
    d.steinberg = d.graphAut.toMonoidHom.comp d.frobenius := by
  -- On an untwisted index both sides are the Frobenius; on the four graph-twisted constructors
  -- the branch equations reduce the claim to the family's own factorization.
  by_cases hd : d.twistOrder = 1
  · rw [steinberg_eq_frobenius d hd, graphAut_eq_one_of_twistOrder_eq_one d hd]
    exact MonoidHom.ext fun g => by
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.one_apply]
  obtain ⟨⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, hv⟩, h⟩ := d
  · exact absurd (twistOrder_A hv) hd
  · rw [steinberg_twistedA, graphAut_twistedA, frobenius_twistedA]
    exact TypeALieIndex.steinberg_eq_graphAut_comp_frobenius ⟨⟨_, hv⟩, by simp⟩
  · exact absurd (twistOrder_B hv) hd
  · exact absurd (twistOrder_C hv) hd
  · exact absurd (twistOrder_D hv) hd
  · rw [steinberg_twistedD, graphAut_twistedD, frobenius_twistedD]
    exact TypeTwistedDLieIndex.steinberg_def ⟨⟨_, hv⟩, by simp⟩
  · exact absurd (twistOrder_E6 hv) hd
  · exact absurd (twistOrder_E7 hv) hd
  · exact absurd (twistOrder_E8 hv) hd
  · exact absurd (twistOrder_F4 hv) hd
  · exact absurd (twistOrder_G2 hv) hd
  · rw [steinberg_twistedE6, graphAut_twistedE6, frobenius_twistedE6]
    exact TypeTwistedE6LieIndex.steinberg_def ⟨⟨_, hv⟩, by simp⟩
  · rw [steinberg_trialityD4, graphAut_trialityD4, frobenius_trialityD4]
    exact TypeTrialityD4LieIndex.steinberg_def ⟨⟨_, hv⟩, by simp⟩
  all_goals exact absurd ((usesHalfFrobenius_iff _).mpr trivial) h

/-- The Steinberg endomorphism may equally be read with its Frobenius factor last, the two factors
commuting. -/
theorem steinberg_eq_frobenius_comp_graphAut (d : GraphTwistedIndex) :
    d.steinberg = d.frobenius.comp d.graphAut.toMonoidHom := by
  rw [steinberg_eq_graphAut_comp_frobenius, graphAut_comp_frobenius]

/-- The fixed subgroup of the Steinberg endomorphism of an ordinary or graph-twisted index. -/
abbrev FixedPoints (d : GraphTwistedIndex) : Type := ↥(fixedSubgroup d.steinberg)

/-- **The finite-simple-group candidate attached to an ordinary or graph-twisted index**: the
derived subgroup of the fixed points of its Steinberg endomorphism, modulo the centre of that
derived subgroup. On each constructor it is the candidate group of the family, the Steinberg
endomorphisms agreeing by `steinberg_A` and its siblings. No finiteness or simplicity assertion is
part of this definition, nor any identification of the carrier with the pinned simply connected
group scheme of the diagram. -/
abbrev Group (d : GraphTwistedIndex) : Type := FixedPointCandidate d.steinberg

/-- The candidate carries a group structure; the quotient construction supplies it. -/
example (d : GraphTwistedIndex) : _root_.Group d.Group := inferInstance

end

end GraphTwistedIndex

end TauCeti
