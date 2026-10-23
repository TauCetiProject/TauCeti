/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.RepresentationRing.Basic
public import TauCeti.RepresentationTheory.GrothendieckGroup.FDRep
import TauCeti.RepresentationTheory.Maschke

/-!
# The Green ring and exact Grothendieck ring in the Maschke case

For a finite group whose order is invertible in the coefficient field, every short exact
sequence of finite-dimensional representations splits. Consequently the canonical comparison
from the Green ring to the exact Grothendieck ring is an isomorphism of rings. This permits
computations with direct sums and tensor products to be used with exact-sequence relations.

`repRingEquivExactK0` identifies the two rings and sends the split class of a representation
to its exact class. No algebraic-closure or characteristic-zero hypothesis is needed.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977),
  Chapter 1 (Maschke's theorem) and §14.1 (the Grothendieck ring).
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G]
  [NeZero (Nat.card G : k)]

/-- The Green ring is canonically isomorphic to the exact Grothendieck ring when the group
order is invertible in the coefficient field. -/
noncomputable def repRingEquivExactK0 :
    repRing k G ≃+* ExactK0.{max u v} (ExactStructure.abelian (FDRep k G)) :=
  ExactK0.fromSplitRingEquiv fun hS ↦ FDRep.nonempty_splitting_of_shortExact
    ((ExactStructure.abelian_conflation _).mp hS)

/-- The ring equivalence acts by the canonical split-to-exact comparison. -/
@[simp]
theorem repRingEquivExactK0_apply (x : repRing k G) :
    repRingEquivExactK0 x = ExactK0.fromSplit (ExactStructure.abelian (FDRep k G)) x := by
  exact ExactK0.fromSplitRingEquiv_apply
    (fun hS ↦ FDRep.nonempty_splitting_of_shortExact
      ((ExactStructure.abelian_conflation _).mp hS)) x

/-- The inverse equivalence sends an exact class to the corresponding split class. -/
@[simp]
theorem repRingEquivExactK0_symm_apply_of (V : FDRep k G) :
    repRingEquivExactK0.symm (ExactK0.of V) = SplitK0.of V := by
  apply repRingEquivExactK0.injective
  simp

end TauCeti
