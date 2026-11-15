/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Data.Fintype.Shrink
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Universe transfer for classifications of finite simple groups

Suppose a family `C` contains, up to isomorphism, every finite simple group whose carrier lies in
one fixed universe. Then it contains every finite simple group in an arbitrary universe. In
particular, a classification of finite simple groups with carriers in `Type` holds in every
universe.

The reason is specific to finite groups. A finite type is small in every universe, so Mathlib's
`Shrink.{x} G` transports the group structure of a finite group `G : Type u` to a carrier in
`Type x`, and `Shrink.mulEquiv` identifies the two groups. Finiteness and simplicity transport to
the shrunk carrier, so the classification in universe `x` applies there; composing its
isomorphism with `Shrink.mulEquiv.symm` returns an isomorphism from the original group.

The candidates are not assumed to be groups, nor finite or simple. A classification statement
needs only say that each finite simple group is isomorphic to some candidate; structural
properties of the candidates may be established separately.

## Main result

* `TauCeti.exists_mulEquiv_of_forall_finite_isSimpleGroup`: a classification of finite simple
  groups in one universe by a fixed family holds in every universe.
-/

public section

namespace TauCeti

universe u v w x

/-- **A classification of finite simple groups in one universe holds in every universe.**

If every finite simple group with carrier in `Type x` is isomorphic to a member of a fixed family
`C`, then the same conclusion holds for a finite simple group in any universe. The candidates
need only carry a multiplication: no group, finiteness or simplicity assumption is made on them. -/
theorem exists_mulEquiv_of_forall_finite_isSimpleGroup
    {ι : Type w} (C : ι → Type v) [∀ i, Mul (C i)]
    (hC : ∀ (H : Type x) [Group H] [Finite H] [IsSimpleGroup H],
      ∃ i, Nonempty (H ≃* C i))
    (G : Type u) [Group G] [Finite G] [IsSimpleGroup G] :
    ∃ i, Nonempty (G ≃* C i) :=
  let e : Shrink.{x} G ≃* G := Shrink.mulEquiv
  have := e.isSimpleGroup
  (hC (Shrink.{x} G)).imp fun _ ⟨f⟩ ↦ ⟨e.symm.trans f⟩

end TauCeti
