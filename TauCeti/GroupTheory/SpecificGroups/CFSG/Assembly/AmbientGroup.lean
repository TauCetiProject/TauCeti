/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeF4.Carrier
public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Carrier
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Tits.Carrier
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Two

/-!
# The ambient group of an arbitrary valid Lie-type index

Every one of the seventeen Lie-type constructors of the classification list now has an explicit
carrier: a matrix group over the algebraic closure of its prime field, together with its
Bourbaki-numbered positive simple root subgroups and its `q`-power Frobenius, for `q` the field
order the index records. The thirteen constructors with an ordinary or graph-twisted Steinberg
endomorphism are already joined into `TauCeti.GraphTwistedIndex.AmbientGroup`; the remaining four,
whose Steinberg endomorphism is an odd power of a half-Frobenius, have carriers of their own:

| Constructor | Family API |
| --- | --- |
| `suzuki` | `TauCeti.RankTwoBLieIndex`, on the rank-two standard symplectic carrier |
| `reeG2` | `TauCeti.ReeG2LieIndex`, on the short-root type-`G₂` carrier over `𝔽₃` |
| `reeF4` | `TauCeti.ReeF4LieIndex`, on the short-root type-`F₄` carrier over `𝔽₂` |
| `tits` | `TauCeti.TitsLieIndex`, on the same short-root type-`F₄` carrier |

This file joins all seventeen into one construction on `TauCeti.ValidLieTypeIndex`, by cases on the
constructor: the ambient group `TauCeti.ValidLieTypeIndex.AmbientGroup` with its `Group` instance,
its numbered simple root subgroups `TauCeti.ValidLieTypeIndex.simpleRootSubgroup`, and its Frobenius
`TauCeti.ValidLieTypeIndex.frobenius`. Each branch is an existing construction, with no new carrier
or map: the thirteen ordinary and graph-twisted branches are the graph-twisted assembly, and the
four half-Frobenius branches are the family carriers. The branch equations
`TauCeti.ValidLieTypeIndex.simpleRootSubgroup_A`, ...,
`TauCeti.ValidLieTypeIndex.simpleRootSubgroup_tits` and `TauCeti.ValidLieTypeIndex.frobenius_A`,
..., `TauCeti.ValidLieTypeIndex.frobenius_tits` say which one on each constructor.

What the assembly buys is a single statement, for every valid index, of the Frobenius equation on
the numbered simple root subgroups, `TauCeti.ValidLieTypeIndex.frobenius_simpleRootSubgroup`:

```text
Frob_q (x_i(u)) = x_i(u ^ q).
```

The Frobenius is the Steinberg endomorphism on the nine untwisted families only. On the four
graph-twisted families the Steinberg endomorphism is a graph automorphism composed with it, and on
the four half-Frobenius families it is the odd power of an exceptional isogeny whose square is the
prime-field Frobenius. The Suzuki and Ree `G₂` family APIs expose such isogenies as
`TauCeti.SuzukiLieIndex.halfFrobenius` and `TauCeti.ReeG2LieIndex.halfFrobenius`; exceptional
isogenies remain separate from this Frobenius assembly. The uniform Steinberg endomorphism is not
assembled here.

Beside it the assembly carries the prime-field Frobenius
`TauCeti.ValidLieTypeIndex.primeFrobenius`, the `p`-power map for `p` the defining characteristic,
of which the `q`-power map is the `e`-th power,
`TauCeti.ValidLieTypeIndex.frobenius_eq_primeFrobenius_pow`:

```text
Frob_q = Frob_p ^ e,        Frob_p (x_i(u)) = x_i(u ^ p).
```

The two agree on an index of prime field order, the Tits index among them. It is the
prime-field map, and not the `q`-power one, that the exceptional isogeny of the Suzuki and Ree
`G₂` families squares to.

Every carrier used here is an explicit one, and none is identified with the pinned simply connected
group scheme of its diagram; the constructions transfer to that pinned group only along such an
identification, once one is proved. Nothing here asserts that any group is finite, perfect or
simple, nor that any carrier is reductive.

## Main definitions

* `TauCeti.ValidLieTypeIndex.AmbientGroup`: the ambient group of a valid Lie-type index, with its
  group structure `TauCeti.ValidLieTypeIndex.instGroupAmbientGroup`.
* `TauCeti.ValidLieTypeIndex.simpleRootSubgroup`: its Bourbaki-numbered positive simple root
  subgroups.
* `TauCeti.ValidLieTypeIndex.frobenius`: its `q`-power Frobenius endomorphism.
* `TauCeti.ValidLieTypeIndex.primeFrobenius`: its prime-field Frobenius endomorphism, the
  `p`-power map for `p` the defining characteristic.

## Main results

* `TauCeti.ValidLieTypeIndex.frobenius_simpleRootSubgroup` and
  `TauCeti.ValidLieTypeIndex.primeFrobenius_simpleRootSubgroup`: the two Frobenius maps raise the
  parameter of every simple root subgroup to the `q`-th and to the `p`-th power, uniformly in the
  seventeen constructors.
* `TauCeti.ValidLieTypeIndex.frobenius_eq_primeFrobenius_pow`: the `q`-power Frobenius is the
  `e`-th power of the prime-field one, for `e` the field exponent the index records.
* `TauCeti.ValidLieTypeIndex.simpleRootSubgroup_A`, ...,
  `TauCeti.ValidLieTypeIndex.simpleRootSubgroup_tits`, `TauCeti.ValidLieTypeIndex.frobenius_A`,
  ..., `TauCeti.ValidLieTypeIndex.frobenius_tits` and
  `TauCeti.ValidLieTypeIndex.primeFrobenius_A`, ...,
  `TauCeti.ValidLieTypeIndex.primeFrobenius_tits`: on each constructor the simple root subgroups
  and the two Frobenius maps are those of the graph-twisted assembly or of the half-Frobenius
  family.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Chapters 4, 13 and 14, for the carriers and the
  Frobenius of each family.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* The case split follows `TauCeti.GraphTwistedIndex.AmbientGroup` in
  `TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted`, extended to the four
  half-Frobenius constructors.
-/

public section

namespace TauCeti

namespace ValidLieTypeIndex

open LieTypeIndex (usesHalfFrobenius_iff)

noncomputable section

/-- **The ambient group of a valid Lie-type index**: the group of algebraic-closure-valued points
of the explicit carrier assigned to its family. It is generally infinite, and it is not identified
with the points of the pinned simply connected group scheme of the diagram. On the thirteen ordinary
and graph-twisted constructors it is `TauCeti.GraphTwistedIndex.AmbientGroup`; the Suzuki family
runs on the rank-two symplectic carrier, the Ree family of type `G₂` on the short-root `G₂` carrier
over `𝔽₃`, and the Ree family of type `F₄` and the Tits construction on the short-root `F₄`
carrier over `𝔽₂`. -/
-- The body is exposed for the same reason as `GraphTwistedIndex.AmbientGroup`: the branch equations
-- below compare maps between this ambient group and the one on the branch, and a consumer
-- transferring a branch result to this assembly needs the same reduction.
@[expose] def AmbientGroup : ValidLieTypeIndex → Type
  | ⟨.A _ _, hv⟩ | ⟨.twistedA _ _, hv⟩ | ⟨.B _ _, hv⟩ | ⟨.C _ _, hv⟩ | ⟨.D _ _, hv⟩
  | ⟨.twistedD _ _, hv⟩ | ⟨.E6 _, hv⟩ | ⟨.E7 _, hv⟩ | ⟨.E8 _, hv⟩ | ⟨.F4 _, hv⟩ | ⟨.G2 _, hv⟩
  | ⟨.twistedE6 _, hv⟩ | ⟨.trialityD4 _, hv⟩ =>
      GraphTwistedIndex.AmbientGroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩
  | ⟨.suzuki m, hv⟩ => (RankTwoBLieIndex.ofSuzuki m hv).AmbientGroup
  | ⟨.reeG2 m, hv⟩ => (ReeG2LieIndex.of m hv).AmbientGroup
  | ⟨.reeF4 m, hv⟩ => (ReeF4LieIndex.of m hv).AmbientGroup
  | ⟨.tits, _⟩ => TitsLieIndex.of.AmbientGroup

/-- The ambient group carries the group structure of the carrier it is on. -/
instance instGroupAmbientGroup : (d : ValidLieTypeIndex) → Group d.AmbientGroup
  | ⟨.A _ _, hv⟩ | ⟨.twistedA _ _, hv⟩ | ⟨.B _ _, hv⟩ | ⟨.C _ _, hv⟩ | ⟨.D _ _, hv⟩
  | ⟨.twistedD _ _, hv⟩ | ⟨.E6 _, hv⟩ | ⟨.E7 _, hv⟩ | ⟨.E8 _, hv⟩ | ⟨.F4 _, hv⟩ | ⟨.G2 _, hv⟩
  | ⟨.twistedE6 _, hv⟩ | ⟨.trialityD4 _, hv⟩ =>
      inferInstanceAs
        (Group (GraphTwistedIndex.AmbientGroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩))
  | ⟨.suzuki m, hv⟩ => inferInstanceAs (Group (RankTwoBLieIndex.ofSuzuki m hv).AmbientGroup)
  | ⟨.reeG2 m, hv⟩ => inferInstanceAs (Group (ReeG2LieIndex.of m hv).AmbientGroup)
  | ⟨.reeF4 m, hv⟩ => inferInstanceAs (Group (ReeF4LieIndex.of m hv).AmbientGroup)
  | ⟨.tits, _⟩ => inferInstanceAs (Group TitsLieIndex.of.AmbientGroup)

/-- **The positive simple root subgroup at the Bourbaki-numbered node `i`**, as a homomorphism
from the additive group of the algebraic closure. On each constructor it is the simple root
subgroup of the graph-twisted assembly or of the half-Frobenius family, by `simpleRootSubgroup_A`
and its siblings. -/
def simpleRootSubgroup :
    (d : ValidLieTypeIndex) → Fin d.rank → Multiplicative d.Closure →* d.AmbientGroup
  | ⟨.A _ _, hv⟩ | ⟨.twistedA _ _, hv⟩ | ⟨.B _ _, hv⟩ | ⟨.C _ _, hv⟩ | ⟨.D _ _, hv⟩
  | ⟨.twistedD _ _, hv⟩ | ⟨.E6 _, hv⟩ | ⟨.E7 _, hv⟩ | ⟨.E8 _, hv⟩ | ⟨.F4 _, hv⟩ | ⟨.G2 _, hv⟩
  | ⟨.twistedE6 _, hv⟩ | ⟨.trialityD4 _, hv⟩ =>
      GraphTwistedIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩
  | ⟨.suzuki m, hv⟩ => (RankTwoBLieIndex.ofSuzuki m hv).simpleRootSubgroup
  | ⟨.reeG2 m, hv⟩ => (ReeG2LieIndex.of m hv).simpleRootSubgroup
  | ⟨.reeF4 m, hv⟩ => (ReeF4LieIndex.of m hv).simpleRootSubgroup
  | ⟨.tits, _⟩ => TitsLieIndex.of.simpleRootSubgroup

/-- **The `q`-power Frobenius endomorphism of the ambient group of a valid Lie-type index**, for
`q` the field order the index records. On each constructor it is the Frobenius of the graph-twisted
assembly or of the half-Frobenius family, by `frobenius_A` and its siblings; its action on the
simple root subgroups is `frobenius_simpleRootSubgroup`.

It is the Steinberg endomorphism of the nine untwisted families only. On the four graph-twisted
families the Steinberg endomorphism composes a graph automorphism with it, and on the four
half-Frobenius families the Steinberg endomorphism is an odd power of an exceptional isogeny whose
square is the prime-field Frobenius `primeFrobenius`. The Frobenius defined here is distinct from
those exceptional isogenies, which belong to the family APIs. -/
def frobenius : (d : ValidLieTypeIndex) → d.AmbientGroup →* d.AmbientGroup
  | ⟨.A _ _, hv⟩ | ⟨.twistedA _ _, hv⟩ | ⟨.B _ _, hv⟩ | ⟨.C _ _, hv⟩ | ⟨.D _ _, hv⟩
  | ⟨.twistedD _ _, hv⟩ | ⟨.E6 _, hv⟩ | ⟨.E7 _, hv⟩ | ⟨.E8 _, hv⟩ | ⟨.F4 _, hv⟩ | ⟨.G2 _, hv⟩
  | ⟨.twistedE6 _, hv⟩ | ⟨.trialityD4 _, hv⟩ =>
      GraphTwistedIndex.frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩
  | ⟨.suzuki m, hv⟩ => (RankTwoBLieIndex.ofSuzuki m hv).frobenius
  | ⟨.reeG2 m, hv⟩ => (ReeG2LieIndex.of m hv).frobenius
  | ⟨.reeF4 m, hv⟩ => (ReeF4LieIndex.of m hv).frobenius
  | ⟨.tits, _⟩ => TitsLieIndex.of.frobenius

/-- **The prime-field Frobenius endomorphism of the ambient group of a valid Lie-type index**, the
`p`-power map for `p` the defining characteristic. On each constructor it is the prime-field
Frobenius of the graph-twisted assembly or of the half-Frobenius family, by `primeFrobenius_A` and
its siblings; its action on the simple root subgroups is `primeFrobenius_simpleRootSubgroup`.

The `q`-power Frobenius is its `e`-th power, for `e` the field exponent the index records, by
`frobenius_eq_primeFrobenius_pow`, so the two agree on an index of prime field order. On the
Suzuki and Ree `G₂` constructors it is the map that the family's exceptional isogeny
(`TauCeti.SuzukiLieIndex.halfFrobenius`, `TauCeti.ReeG2LieIndex.halfFrobenius`) squares to.
Exceptional isogenies are not part of this uniform API. -/
def primeFrobenius : (d : ValidLieTypeIndex) → d.AmbientGroup →* d.AmbientGroup
  | ⟨.A _ _, hv⟩ | ⟨.twistedA _ _, hv⟩ | ⟨.B _ _, hv⟩ | ⟨.C _ _, hv⟩ | ⟨.D _ _, hv⟩
  | ⟨.twistedD _ _, hv⟩ | ⟨.E6 _, hv⟩ | ⟨.E7 _, hv⟩ | ⟨.E8 _, hv⟩ | ⟨.F4 _, hv⟩ | ⟨.G2 _, hv⟩
  | ⟨.twistedE6 _, hv⟩ | ⟨.trialityD4 _, hv⟩ =>
      GraphTwistedIndex.primeFrobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩
  | ⟨.suzuki m, hv⟩ => (RankTwoBLieIndex.ofSuzuki m hv).primeFrobenius
  | ⟨.reeG2 m, hv⟩ => (ReeG2LieIndex.of m hv).primeFrobenius
  | ⟨.reeF4 m, hv⟩ => (ReeF4LieIndex.of m hv).primeFrobenius
  | ⟨.tits, _⟩ => TitsLieIndex.of.frobenius

/-! ### The branch equations

On each of the thirteen ordinary and graph-twisted constructors the simple root subgroups and the
Frobenius are those of `TauCeti.GraphTwistedIndex`, and on each of the four half-Frobenius
constructors they are those of the family API the constructor belongs to. -/

section Branches

variable {n m : ℕ} {q : PrimePower}

/-- On `Aₙ(q)` the simple root subgroups are those of the graph-twisted assembly. -/
theorem simpleRootSubgroup_A (hv : (LieTypeIndex.A n q).Valid) :
    simpleRootSubgroup ⟨_, hv⟩ =
      GraphTwistedIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `Aₙ(q)` the Frobenius is that of the graph-twisted assembly. -/
theorem frobenius_A (hv : (LieTypeIndex.A n q).Valid) :
    frobenius ⟨_, hv⟩ = GraphTwistedIndex.frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `²Aₙ(q)` the simple root subgroups are those of the graph-twisted assembly. -/
theorem simpleRootSubgroup_twistedA (hv : (LieTypeIndex.twistedA n q).Valid) :
    simpleRootSubgroup ⟨_, hv⟩ =
      GraphTwistedIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `²Aₙ(q)` the Frobenius is that of the graph-twisted assembly. -/
theorem frobenius_twistedA (hv : (LieTypeIndex.twistedA n q).Valid) :
    frobenius ⟨_, hv⟩ = GraphTwistedIndex.frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `Bₙ(q)` the simple root subgroups are those of the graph-twisted assembly. -/
theorem simpleRootSubgroup_B (hv : (LieTypeIndex.B n q).Valid) :
    simpleRootSubgroup ⟨_, hv⟩ =
      GraphTwistedIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `Bₙ(q)` the Frobenius is that of the graph-twisted assembly. -/
theorem frobenius_B (hv : (LieTypeIndex.B n q).Valid) :
    frobenius ⟨_, hv⟩ = GraphTwistedIndex.frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `Cₙ(q)` the simple root subgroups are those of the graph-twisted assembly. -/
theorem simpleRootSubgroup_C (hv : (LieTypeIndex.C n q).Valid) :
    simpleRootSubgroup ⟨_, hv⟩ =
      GraphTwistedIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `Cₙ(q)` the Frobenius is that of the graph-twisted assembly. -/
theorem frobenius_C (hv : (LieTypeIndex.C n q).Valid) :
    frobenius ⟨_, hv⟩ = GraphTwistedIndex.frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `Dₙ(q)` the simple root subgroups are those of the graph-twisted assembly. -/
theorem simpleRootSubgroup_D (hv : (LieTypeIndex.D n q).Valid) :
    simpleRootSubgroup ⟨_, hv⟩ =
      GraphTwistedIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `Dₙ(q)` the Frobenius is that of the graph-twisted assembly. -/
theorem frobenius_D (hv : (LieTypeIndex.D n q).Valid) :
    frobenius ⟨_, hv⟩ = GraphTwistedIndex.frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `²Dₙ(q)` the simple root subgroups are those of the graph-twisted assembly. -/
theorem simpleRootSubgroup_twistedD (hv : (LieTypeIndex.twistedD n q).Valid) :
    simpleRootSubgroup ⟨_, hv⟩ =
      GraphTwistedIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `²Dₙ(q)` the Frobenius is that of the graph-twisted assembly. -/
theorem frobenius_twistedD (hv : (LieTypeIndex.twistedD n q).Valid) :
    frobenius ⟨_, hv⟩ = GraphTwistedIndex.frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `E₆(q)` the simple root subgroups are those of the graph-twisted assembly. -/
theorem simpleRootSubgroup_E6 (hv : (LieTypeIndex.E6 q).Valid) :
    simpleRootSubgroup ⟨_, hv⟩ =
      GraphTwistedIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `E₆(q)` the Frobenius is that of the graph-twisted assembly. -/
theorem frobenius_E6 (hv : (LieTypeIndex.E6 q).Valid) :
    frobenius ⟨_, hv⟩ = GraphTwistedIndex.frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `E₇(q)` the simple root subgroups are those of the graph-twisted assembly. -/
theorem simpleRootSubgroup_E7 (hv : (LieTypeIndex.E7 q).Valid) :
    simpleRootSubgroup ⟨_, hv⟩ =
      GraphTwistedIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `E₇(q)` the Frobenius is that of the graph-twisted assembly. -/
theorem frobenius_E7 (hv : (LieTypeIndex.E7 q).Valid) :
    frobenius ⟨_, hv⟩ = GraphTwistedIndex.frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `E₈(q)` the simple root subgroups are those of the graph-twisted assembly. -/
theorem simpleRootSubgroup_E8 (hv : (LieTypeIndex.E8 q).Valid) :
    simpleRootSubgroup ⟨_, hv⟩ =
      GraphTwistedIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `E₈(q)` the Frobenius is that of the graph-twisted assembly. -/
theorem frobenius_E8 (hv : (LieTypeIndex.E8 q).Valid) :
    frobenius ⟨_, hv⟩ = GraphTwistedIndex.frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `F₄(q)` the simple root subgroups are those of the graph-twisted assembly. -/
theorem simpleRootSubgroup_F4 (hv : (LieTypeIndex.F4 q).Valid) :
    simpleRootSubgroup ⟨_, hv⟩ =
      GraphTwistedIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `F₄(q)` the Frobenius is that of the graph-twisted assembly. -/
theorem frobenius_F4 (hv : (LieTypeIndex.F4 q).Valid) :
    frobenius ⟨_, hv⟩ = GraphTwistedIndex.frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `G₂(q)` the simple root subgroups are those of the graph-twisted assembly. -/
theorem simpleRootSubgroup_G2 (hv : (LieTypeIndex.G2 q).Valid) :
    simpleRootSubgroup ⟨_, hv⟩ =
      GraphTwistedIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `G₂(q)` the Frobenius is that of the graph-twisted assembly. -/
theorem frobenius_G2 (hv : (LieTypeIndex.G2 q).Valid) :
    frobenius ⟨_, hv⟩ = GraphTwistedIndex.frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `²E₆(q)` the simple root subgroups are those of the graph-twisted assembly. -/
theorem simpleRootSubgroup_twistedE6 (hv : (LieTypeIndex.twistedE6 q).Valid) :
    simpleRootSubgroup ⟨_, hv⟩ =
      GraphTwistedIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `²E₆(q)` the Frobenius is that of the graph-twisted assembly. -/
theorem frobenius_twistedE6 (hv : (LieTypeIndex.twistedE6 q).Valid) :
    frobenius ⟨_, hv⟩ = GraphTwistedIndex.frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `³D₄(q)` the simple root subgroups are those of the graph-twisted assembly. -/
theorem simpleRootSubgroup_trialityD4 (hv : (LieTypeIndex.trialityD4 q).Valid) :
    simpleRootSubgroup ⟨_, hv⟩ =
      GraphTwistedIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `³D₄(q)` the Frobenius is that of the graph-twisted assembly. -/
theorem frobenius_trialityD4 (hv : (LieTypeIndex.trialityD4 q).Valid) :
    frobenius ⟨_, hv⟩ = GraphTwistedIndex.frobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `²B₂(2^(2m+1))` the simple root subgroups are those of the rank-two symplectic carrier. -/
theorem simpleRootSubgroup_suzuki (hv : (LieTypeIndex.suzuki m).Valid) :
    simpleRootSubgroup ⟨_, hv⟩ = (RankTwoBLieIndex.ofSuzuki m hv).simpleRootSubgroup :=
  (rfl)

/-- On `²B₂(2^(2m+1))` the Frobenius is that of the rank-two symplectic carrier. -/
theorem frobenius_suzuki (hv : (LieTypeIndex.suzuki m).Valid) :
    frobenius ⟨_, hv⟩ = (RankTwoBLieIndex.ofSuzuki m hv).frobenius :=
  (rfl)

/-- On `²G₂(3^(2m+1))` the simple root subgroups are those of the family. -/
theorem simpleRootSubgroup_reeG2 (hv : (LieTypeIndex.reeG2 m).Valid) :
    simpleRootSubgroup ⟨_, hv⟩ = (ReeG2LieIndex.of m hv).simpleRootSubgroup :=
  (rfl)

/-- On `²G₂(3^(2m+1))` the Frobenius is that of the family. -/
theorem frobenius_reeG2 (hv : (LieTypeIndex.reeG2 m).Valid) :
    frobenius ⟨_, hv⟩ = (ReeG2LieIndex.of m hv).frobenius :=
  (rfl)

/-- On `²F₄(2^(2m+1))` the simple root subgroups are those of the family. -/
theorem simpleRootSubgroup_reeF4 (hv : (LieTypeIndex.reeF4 m).Valid) :
    simpleRootSubgroup ⟨_, hv⟩ = (ReeF4LieIndex.of m hv).simpleRootSubgroup :=
  (rfl)

/-- On `²F₄(2^(2m+1))` the Frobenius is that of the family. -/
theorem frobenius_reeF4 (hv : (LieTypeIndex.reeF4 m).Valid) :
    frobenius ⟨_, hv⟩ = (ReeF4LieIndex.of m hv).frobenius :=
  (rfl)

/-- On the Tits index the simple root subgroups are those of the Tits construction. -/
theorem simpleRootSubgroup_tits (hv : LieTypeIndex.tits.Valid) :
    simpleRootSubgroup ⟨_, hv⟩ = TitsLieIndex.of.simpleRootSubgroup :=
  (rfl)

/-- On the Tits index the Frobenius is that of the Tits construction. -/
theorem frobenius_tits (hv : LieTypeIndex.tits.Valid) :
    frobenius ⟨_, hv⟩ = TitsLieIndex.of.frobenius :=
  (rfl)

/-- On `Aₙ(q)` the prime-field Frobenius is that of the graph-twisted assembly. -/
theorem primeFrobenius_A (hv : (LieTypeIndex.A n q).Valid) :
    primeFrobenius ⟨_, hv⟩ =
      GraphTwistedIndex.primeFrobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `²Aₙ(q)` the prime-field Frobenius is that of the graph-twisted assembly. -/
theorem primeFrobenius_twistedA (hv : (LieTypeIndex.twistedA n q).Valid) :
    primeFrobenius ⟨_, hv⟩ =
      GraphTwistedIndex.primeFrobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `Bₙ(q)` the prime-field Frobenius is that of the graph-twisted assembly. -/
theorem primeFrobenius_B (hv : (LieTypeIndex.B n q).Valid) :
    primeFrobenius ⟨_, hv⟩ =
      GraphTwistedIndex.primeFrobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `Cₙ(q)` the prime-field Frobenius is that of the graph-twisted assembly. -/
theorem primeFrobenius_C (hv : (LieTypeIndex.C n q).Valid) :
    primeFrobenius ⟨_, hv⟩ =
      GraphTwistedIndex.primeFrobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `Dₙ(q)` the prime-field Frobenius is that of the graph-twisted assembly. -/
theorem primeFrobenius_D (hv : (LieTypeIndex.D n q).Valid) :
    primeFrobenius ⟨_, hv⟩ =
      GraphTwistedIndex.primeFrobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `²Dₙ(q)` the prime-field Frobenius is that of the graph-twisted assembly. -/
theorem primeFrobenius_twistedD (hv : (LieTypeIndex.twistedD n q).Valid) :
    primeFrobenius ⟨_, hv⟩ =
      GraphTwistedIndex.primeFrobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `E₆(q)` the prime-field Frobenius is that of the graph-twisted assembly. -/
theorem primeFrobenius_E6 (hv : (LieTypeIndex.E6 q).Valid) :
    primeFrobenius ⟨_, hv⟩ =
      GraphTwistedIndex.primeFrobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `E₇(q)` the prime-field Frobenius is that of the graph-twisted assembly. -/
theorem primeFrobenius_E7 (hv : (LieTypeIndex.E7 q).Valid) :
    primeFrobenius ⟨_, hv⟩ =
      GraphTwistedIndex.primeFrobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `E₈(q)` the prime-field Frobenius is that of the graph-twisted assembly. -/
theorem primeFrobenius_E8 (hv : (LieTypeIndex.E8 q).Valid) :
    primeFrobenius ⟨_, hv⟩ =
      GraphTwistedIndex.primeFrobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `F₄(q)` the prime-field Frobenius is that of the graph-twisted assembly. -/
theorem primeFrobenius_F4 (hv : (LieTypeIndex.F4 q).Valid) :
    primeFrobenius ⟨_, hv⟩ =
      GraphTwistedIndex.primeFrobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `G₂(q)` the prime-field Frobenius is that of the graph-twisted assembly. -/
theorem primeFrobenius_G2 (hv : (LieTypeIndex.G2 q).Valid) :
    primeFrobenius ⟨_, hv⟩ =
      GraphTwistedIndex.primeFrobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `²E₆(q)` the prime-field Frobenius is that of the graph-twisted assembly. -/
theorem primeFrobenius_twistedE6 (hv : (LieTypeIndex.twistedE6 q).Valid) :
    primeFrobenius ⟨_, hv⟩ =
      GraphTwistedIndex.primeFrobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `³D₄(q)` the prime-field Frobenius is that of the graph-twisted assembly. -/
theorem primeFrobenius_trialityD4 (hv : (LieTypeIndex.trialityD4 q).Valid) :
    primeFrobenius ⟨_, hv⟩ =
      GraphTwistedIndex.primeFrobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ :=
  (rfl)

/-- On `²B₂(2^(2m+1))` the prime-field Frobenius is that of the rank-two symplectic carrier. -/
theorem primeFrobenius_suzuki (hv : (LieTypeIndex.suzuki m).Valid) :
    primeFrobenius ⟨_, hv⟩ = (RankTwoBLieIndex.ofSuzuki m hv).primeFrobenius :=
  (rfl)

/-- On `²G₂(3^(2m+1))` the prime-field Frobenius is that of the family. -/
theorem primeFrobenius_reeG2 (hv : (LieTypeIndex.reeG2 m).Valid) :
    primeFrobenius ⟨_, hv⟩ = (ReeG2LieIndex.of m hv).primeFrobenius :=
  (rfl)

/-- On `²F₄(2^(2m+1))` the prime-field Frobenius is that of the family. -/
theorem primeFrobenius_reeF4 (hv : (LieTypeIndex.reeF4 m).Valid) :
    primeFrobenius ⟨_, hv⟩ = (ReeF4LieIndex.of m hv).primeFrobenius :=
  (rfl)

/-- On the Tits index the prime-field Frobenius is the Frobenius of the Tits construction: that
index records field order two, so its `q`-power Frobenius is already the `2`-power one and the
family names no second map. -/
theorem primeFrobenius_tits (hv : LieTypeIndex.tits.Valid) :
    primeFrobenius ⟨_, hv⟩ = TitsLieIndex.of.frobenius :=
  (rfl)

end Branches

/-! ### The Frobenius equation -/

/-- **The Frobenius has the pinned action on every simple root subgroup.** It sends `x_i(u)` to
`x_i(u ^ q)`, where `q` is the field order the index records. This is the defining equation of
the `q`-power Frobenius, now stated once for all seventeen constructors. -/
@[simp]
theorem frobenius_simpleRootSubgroup (d : ValidLieTypeIndex) (i : Fin d.rank)
    (u : Multiplicative d.Closure) :
    d.frobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.fieldOrder)) := by
  -- On each constructor the branch equations turn the uniform maps into those of the branch, and
  -- the branch's pinned Frobenius equation closes the goal; the group structure on the ambient
  -- group is, by definition of `instGroupAmbientGroup`, the branch's own. The Tits branch records
  -- its field order as the literal `2`.
  obtain ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, hv⟩ := d
  · rw [frobenius_A, simpleRootSubgroup_A]
    exact GraphTwistedIndex.frobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [frobenius_twistedA, simpleRootSubgroup_twistedA]
    exact GraphTwistedIndex.frobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [frobenius_B, simpleRootSubgroup_B]
    exact GraphTwistedIndex.frobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [frobenius_C, simpleRootSubgroup_C]
    exact GraphTwistedIndex.frobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [frobenius_D, simpleRootSubgroup_D]
    exact GraphTwistedIndex.frobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [frobenius_twistedD, simpleRootSubgroup_twistedD]
    exact GraphTwistedIndex.frobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [frobenius_E6, simpleRootSubgroup_E6]
    exact GraphTwistedIndex.frobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [frobenius_E7, simpleRootSubgroup_E7]
    exact GraphTwistedIndex.frobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [frobenius_E8, simpleRootSubgroup_E8]
    exact GraphTwistedIndex.frobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [frobenius_F4, simpleRootSubgroup_F4]
    exact GraphTwistedIndex.frobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [frobenius_G2, simpleRootSubgroup_G2]
    exact GraphTwistedIndex.frobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [frobenius_twistedE6, simpleRootSubgroup_twistedE6]
    exact GraphTwistedIndex.frobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [frobenius_trialityD4, simpleRootSubgroup_trialityD4]
    exact GraphTwistedIndex.frobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [frobenius_suzuki, simpleRootSubgroup_suzuki]
    exact RankTwoBLieIndex.frobenius_simpleRootSubgroup (RankTwoBLieIndex.ofSuzuki _ hv) i u
  · rw [frobenius_reeG2, simpleRootSubgroup_reeG2]
    exact ReeG2LieIndex.frobenius_simpleRootSubgroup (ReeG2LieIndex.of _ hv) i u
  · rw [frobenius_reeF4, simpleRootSubgroup_reeF4]
    exact ReeF4LieIndex.frobenius_simpleRootSubgroup (ReeF4LieIndex.of _ hv) i u
  · rw [frobenius_tits, simpleRootSubgroup_tits]
    have h2 : fieldOrder ⟨.tits, hv⟩ = 2 := TitsLieIndex.fieldOrder_eq_two TitsLieIndex.of
    rw [h2]
    exact TitsLieIndex.frobenius_simpleRootSubgroup TitsLieIndex.of i u

/-- **The prime-field Frobenius has the pinned action on every simple root subgroup.** It sends
`x_i(u)` to `x_i(u ^ p)`, where `p` is the defining characteristic of the index. This is the
defining equation of the prime-field Frobenius, stated once for all seventeen constructors. -/
@[simp]
theorem primeFrobenius_simpleRootSubgroup (d : ValidLieTypeIndex) (i : Fin d.rank)
    (u : Multiplicative d.Closure) :
    d.primeFrobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.characteristic)) := by
  -- As for `frobenius_simpleRootSubgroup`: the branch equations turn the uniform maps into those
  -- of the branch, whose pinned equation closes the goal. The three Suzuki--Ree and Tits branches
  -- record their characteristic as a literal.
  obtain ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, hv⟩ := d
  · rw [primeFrobenius_A, simpleRootSubgroup_A]
    exact GraphTwistedIndex.primeFrobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [primeFrobenius_twistedA, simpleRootSubgroup_twistedA]
    exact GraphTwistedIndex.primeFrobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [primeFrobenius_B, simpleRootSubgroup_B]
    exact GraphTwistedIndex.primeFrobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [primeFrobenius_C, simpleRootSubgroup_C]
    exact GraphTwistedIndex.primeFrobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [primeFrobenius_D, simpleRootSubgroup_D]
    exact GraphTwistedIndex.primeFrobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [primeFrobenius_twistedD, simpleRootSubgroup_twistedD]
    exact GraphTwistedIndex.primeFrobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [primeFrobenius_E6, simpleRootSubgroup_E6]
    exact GraphTwistedIndex.primeFrobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [primeFrobenius_E7, simpleRootSubgroup_E7]
    exact GraphTwistedIndex.primeFrobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [primeFrobenius_E8, simpleRootSubgroup_E8]
    exact GraphTwistedIndex.primeFrobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [primeFrobenius_F4, simpleRootSubgroup_F4]
    exact GraphTwistedIndex.primeFrobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [primeFrobenius_G2, simpleRootSubgroup_G2]
    exact GraphTwistedIndex.primeFrobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [primeFrobenius_twistedE6, simpleRootSubgroup_twistedE6]
    exact GraphTwistedIndex.primeFrobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [primeFrobenius_trialityD4, simpleRootSubgroup_trialityD4]
    exact GraphTwistedIndex.primeFrobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [primeFrobenius_suzuki, simpleRootSubgroup_suzuki]
    exact RankTwoBLieIndex.primeFrobenius_simpleRootSubgroup (RankTwoBLieIndex.ofSuzuki _ hv) i u
  -- On these three branches the family states its equation at the literal characteristic the
  -- constructor carries. That literal cannot be rewritten in the goal, `characteristic` occurring
  -- in `Closure` and so in the types, so the exponent is transported by `congrArg` instead.
  · rw [primeFrobenius_reeG2, simpleRootSubgroup_reeG2]
    refine (ReeG2LieIndex.primeFrobenius_simpleRootSubgroup (ReeG2LieIndex.of _ hv) i u).trans ?_
    exact congrArg (fun k : ℕ => (ReeG2LieIndex.of _ hv).simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ k)))
      (ReeG2LieIndex.characteristic_eq_three (ReeG2LieIndex.of _ hv)).symm
  · rw [primeFrobenius_reeF4, simpleRootSubgroup_reeF4]
    refine (ReeF4LieIndex.primeFrobenius_simpleRootSubgroup (ReeF4LieIndex.of _ hv) i u).trans ?_
    exact congrArg (fun k : ℕ => (ReeF4LieIndex.of _ hv).simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ k)))
      (ReeF4LieIndex.characteristic_eq_two (ReeF4LieIndex.of _ hv)).symm
  · rw [primeFrobenius_tits, simpleRootSubgroup_tits]
    refine (TitsLieIndex.frobenius_simpleRootSubgroup TitsLieIndex.of i u).trans ?_
    exact congrArg (fun k : ℕ => TitsLieIndex.of.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ k)))
      (TitsLieIndex.characteristic_eq_two TitsLieIndex.of).symm

-- The `show` reads the prime-field Frobenius in the endomorphism monoid of the ambient group,
-- there being no power operation on `MonoidHom` itself; this is the form the carriers state their
-- iteration law in.
/-- **The `q`-power Frobenius is the `e`-th power of the prime-field Frobenius**, for `e` the field
exponent the index records, stated once for all seventeen constructors. On an index of prime field
order, the Tits index among them, the exponent is one and the two maps agree. -/
theorem frobenius_eq_primeFrobenius_pow (d : ValidLieTypeIndex) :
    d.frobenius = (show Monoid.End _ from d.primeFrobenius) ^ d.fieldExponent := by
  obtain ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, hv⟩ := d
  · rw [frobenius_A, primeFrobenius_A]
    exact GraphTwistedIndex.frobenius_eq_primeFrobenius_pow ⟨⟨_, hv⟩, by simp⟩
  · rw [frobenius_twistedA, primeFrobenius_twistedA]
    exact GraphTwistedIndex.frobenius_eq_primeFrobenius_pow ⟨⟨_, hv⟩, by simp⟩
  · rw [frobenius_B, primeFrobenius_B]
    exact GraphTwistedIndex.frobenius_eq_primeFrobenius_pow ⟨⟨_, hv⟩, by simp⟩
  · rw [frobenius_C, primeFrobenius_C]
    exact GraphTwistedIndex.frobenius_eq_primeFrobenius_pow ⟨⟨_, hv⟩, by simp⟩
  · rw [frobenius_D, primeFrobenius_D]
    exact GraphTwistedIndex.frobenius_eq_primeFrobenius_pow ⟨⟨_, hv⟩, by simp⟩
  · rw [frobenius_twistedD, primeFrobenius_twistedD]
    exact GraphTwistedIndex.frobenius_eq_primeFrobenius_pow ⟨⟨_, hv⟩, by simp⟩
  · rw [frobenius_E6, primeFrobenius_E6]
    exact GraphTwistedIndex.frobenius_eq_primeFrobenius_pow ⟨⟨_, hv⟩, by simp⟩
  · rw [frobenius_E7, primeFrobenius_E7]
    exact GraphTwistedIndex.frobenius_eq_primeFrobenius_pow ⟨⟨_, hv⟩, by simp⟩
  · rw [frobenius_E8, primeFrobenius_E8]
    exact GraphTwistedIndex.frobenius_eq_primeFrobenius_pow ⟨⟨_, hv⟩, by simp⟩
  · rw [frobenius_F4, primeFrobenius_F4]
    exact GraphTwistedIndex.frobenius_eq_primeFrobenius_pow ⟨⟨_, hv⟩, by simp⟩
  · rw [frobenius_G2, primeFrobenius_G2]
    exact GraphTwistedIndex.frobenius_eq_primeFrobenius_pow ⟨⟨_, hv⟩, by simp⟩
  · rw [frobenius_twistedE6, primeFrobenius_twistedE6]
    exact GraphTwistedIndex.frobenius_eq_primeFrobenius_pow ⟨⟨_, hv⟩, by simp⟩
  · rw [frobenius_trialityD4, primeFrobenius_trialityD4]
    exact GraphTwistedIndex.frobenius_eq_primeFrobenius_pow ⟨⟨_, hv⟩, by simp⟩
  · rw [frobenius_suzuki, primeFrobenius_suzuki]
    exact RankTwoBLieIndex.frobenius_eq_primeFrobenius_pow (RankTwoBLieIndex.ofSuzuki _ hv)
  · rw [frobenius_reeG2, primeFrobenius_reeG2]
    exact ReeG2LieIndex.frobenius_eq_primeFrobenius_pow (ReeG2LieIndex.of _ hv)
  · rw [frobenius_reeF4, primeFrobenius_reeF4]
    exact ReeF4LieIndex.frobenius_eq_primeFrobenius_pow (ReeF4LieIndex.of _ hv)
  -- The Tits index records field exponent one, so its Frobenius is the prime-field one.
  · rw [frobenius_tits, primeFrobenius_tits]
    have h1 : fieldExponent ⟨.tits, hv⟩ = 1 := TitsLieIndex.fieldExponent_eq_one TitsLieIndex.of
    rw [h1, pow_one]

end

end ValidLieTypeIndex

end TauCeti
