/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# The unbundled action underlying a representation

Mathlib's `Rep.ofDistribMulAction` builds an object of `Rep k G` from a `k`-module carrying a
compatible `DistribMulAction` of a monoid `G`. This file supplies the inverse, so that a result
stated in Mathlib's unbundled classes — `AddCommGroup`, `Module k`, `DistribMulAction G`,
`SMulCommClass G k` — can be applied to an arbitrary object of `Rep k G` and its conclusion read
back as a statement about that object.

`TopRep.distribMulAction` in
`TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete` is the same construction
for Mathlib's topological representations. Both are `DistribMulAction.compHom` applied to the
carrier's own operators, and neither is a case of the other: the shared step cannot be stated once
for a bare `Representation k G V`, because such a declaration is not a legal instance — its `ρ`
occurs neither in another instance argument nor in `DistribMulAction G V`. Each bundled carrier
therefore needs its own wrapper, in which the carrier does occur.

## Main definitions

* `Rep.distribMulAction`: the `G`-action on the underlying module of an object of `Rep k G`.

## Main statements

* `Rep.distribMulAction_smul`: the derived action is the operator `A.ρ g`.
* `Rep.smulCommClass`: the derived action commutes with the scalars.
* `Rep.ofDistribMulAction_distribMulAction`: `Rep.ofDistribMulAction` of the derived action is
  the original representation, by definition.
-/

public section

namespace Rep

variable {k G : Type*} [Semiring k] [Monoid G]

/-- The `G`-action on the underlying module of an object of `Rep k G`, read off from its
operators. This is the object half of the translation back to Mathlib's unbundled classes.

It is not a global instance: its carrier `A.V` is a projection, so as a global instance it would
be a candidate on action goals whose carrier is still undetermined. Files that need it bring it
into scope with `attribute [local instance]`. The body is `@[expose]`d because that is the whole
content of the file: an importing module cannot reduce `g • x` to `A.ρ g x`, nor use the round
trip below definitionally, unless it can see the body. -/
@[expose, instance_reducible] def distribMulAction (A : Rep k G) : DistribMulAction G A.V :=
  .compHom A.V A.ρ

attribute [local instance] distribMulAction

/-- The derived action is the operator. This is the direction the simp set rewrites in: `•`
reduces to `A.ρ`, never the reverse. -/
@[simp] lemma distribMulAction_smul (A : Rep k G) (g : G) (x : A.V) : g • x = A.ρ g x := (rfl)

/-- The derived `G`-action commutes with the scalars, because every operator is `k`-linear.

The scalar action is the `k`-module one on `A.V`, which matters only for elaboration: at `k = ℤ`
a standalone `SMulCommClass G ℤ A.V` goal reads the `AddCommGroup` `zsmul` action instead — the
same action, a different instance term, which this lemma's type does not match. Where an earlier
`[Module k M]` argument fixes the scalar action, as in `Rep.ofDistribMulAction`, it is this one
and the lemma applies. -/
lemma smulCommClass (A : Rep k G) : SMulCommClass G k A.V := ⟨fun g r x ↦ map_smul (A.ρ g) r x⟩

section Ring

variable {k G : Type*} [Ring k] [Monoid G]

/-- Rebuilding a representation from its own derived action returns that representation itself,
**by definition** — not merely an isomorphic copy, and not only on operators. A construction
carried out on `Rep.ofDistribMulAction k G A.V` is therefore already a construction on `A`, with
nothing to transport along; and, being an equality in `Rep k G`, it rewrites anywhere `A`
appears, including in the cohomology of `A`. Rewriting with it is manual: the instance the
statement fixes is not one typeclass search would produce, so this is not a `simp` lemma.

`Rep.ofDistribMulAction` is stated over a ring, so this is too; nothing above needs one. -/
lemma ofDistribMulAction_distribMulAction (A : Rep k G) :
    letI := A.smulCommClass
    ofDistribMulAction k G A.V = A := (rfl)

end Ring

end Rep
