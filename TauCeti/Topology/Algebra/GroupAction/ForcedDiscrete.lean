/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.MulAction

/-!
# Forcing the discrete topology on a module

Galois cohomology takes its coefficients in a *discrete* module on which a profinite group acts
with open point stabilizers. Many coefficient modules come with no topology of their own, and some
come with a different one that must not be used (the units of an algebraic closure of a `p`-adic
field carry the `p`-adic topology). This file supplies the wrapper that imposes the discrete
topology on a bare abelian group `M`:

```text
TauCeti.ForcedDiscrete M := M,   with the topology ⊥.
```

`TauCeti.ForcedDiscrete` is a `def`, not an `abbrev`, so no topology instance on `M` is visible on
`ForcedDiscrete M`. The discrete topology is therefore the only one in play, by construction
rather than by one instance winning against another. The additive structure and an action of `G`
on `M` are transferred.

For a topological group `G`, the transferred action is continuous exactly when every point of `M`
has an open stabilizer (`TauCeti.ForcedDiscrete.continuousSMul_iff`). So `ForcedDiscrete M` is a
discrete `G`-module in the sense that continuous cohomology asks for, and the continuous
cohomology of `G` with coefficients in `ForcedDiscrete M` is the cohomology of `G` acting with
open stabilizers on the bare group `M`. All of the continuous-cohomology API stated for a module
with `[DiscreteTopology M] [ContinuousSMul G M]` applies to it unchanged: the explicit `H⁰`, `H¹`
and `H²`, the long exact sequence of a `TauCeti.ContCohomology.DiscreteShortExact`, and, for
compact `G`, the comparison with the colimit over finite quotients
`TauCeti.ContCohomology.continuousFiniteQuotientColimit`.

A coefficient module whose action is not an instance on `M` (for example the points of an elliptic
curve over a separable closure, where an instance would put the Galois action on the point type
itself) is a type synonym of `ForcedDiscrete M` carrying that action.

## Main definitions

* `TauCeti.ForcedDiscrete`: `M` with the discrete topology imposed.
* `TauCeti.ForcedDiscrete.addEquiv`: the identification `M ≃+ ForcedDiscrete M`.

## Main results

* `TauCeti.ForcedDiscrete.continuousSMul_iff`: the action on `ForcedDiscrete M` is continuous
  exactly when the point stabilizers of the action on `M` are open.

## Implementation notes

Mathlib's `WithTopology M ⊥` also puts the discrete topology on a copy of `M`, but it is a
one-field structure that transfers order structure and no algebraic structure. A coefficient module
needs the group structure and the action, so this file uses a `def` synonym, as the other
coefficient modules of the project do, and transfers both with `inferInstanceAs`.
-/

public section

namespace TauCeti

universe u

/-- **A bare abelian group `M` with the discrete topology imposed.** It is a type synonym for `M`,
so the topology `⊥` lives on it and no topology on `M` itself is ever used. -/
@[expose] def ForcedDiscrete (M : Type u) : Type u := M

namespace ForcedDiscrete

variable (M : Type u) [AddCommGroup M]

instance : AddCommGroup (ForcedDiscrete M) := inferInstanceAs (AddCommGroup M)

instance : TopologicalSpace (ForcedDiscrete M) := ⊥

instance : DiscreteTopology (ForcedDiscrete M) := ⟨rfl⟩

/-- The identification of `M` with `ForcedDiscrete M`. -/
@[expose] def addEquiv : M ≃+ ForcedDiscrete M := AddEquiv.refl M

section Monoid

variable {G : Type*} [Monoid G] [DistribMulAction G M]

instance : DistribMulAction G (ForcedDiscrete M) := inferInstanceAs (DistribMulAction G M)

variable {M} in
/-- The action of `G` on `ForcedDiscrete M` is the action on `M`. -/
@[simp]
theorem smul_addEquiv (g : G) (x : M) : g • addEquiv M x = addEquiv M (g • x) :=
  (rfl)

end Monoid

section Group

variable {G : Type*} [Group G] [DistribMulAction G M]

variable {M} in
/-- The stabilizer of a point of `ForcedDiscrete M` is the stabilizer of the point of `M`. -/
@[simp]
theorem stabilizer_addEquiv (x : M) :
    MulAction.stabilizer G (addEquiv M x) = MulAction.stabilizer G x :=
  (rfl)

/-- **`ForcedDiscrete M` is a discrete `G`-module exactly when `G` acts on `M` with open
stabilizers.** -/
theorem continuousSMul_iff [TopologicalSpace G] [IsTopologicalGroup G] :
    ContinuousSMul G (ForcedDiscrete M) ↔
      ∀ x : M, IsOpen (MulAction.stabilizer G x : Set G) :=
  continuousSMul_iff_stabilizer_isOpen.trans (addEquiv M).forall_congr_right.symm

end Group

end ForcedDiscrete

end TauCeti
