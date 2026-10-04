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

/-- The comparison from split to exact Grothendieck rings of finite-dimensional
representations is bijective in the Maschke case. -/
theorem fromSplitRingHom_fdRep_bijective :
    Function.Bijective
      (ExactK0.fromSplitRingHom (ExactStructure.abelian (FDRep k G)) :
        repRing k G →+* ExactK0.{max u v} (ExactStructure.abelian (FDRep k G))) := by
  have hsplit : ∀ {S : ShortComplex (FDRep k G)},
      (ExactStructure.abelian (FDRep k G)).Conflation S → Nonempty S.Splitting :=
    fun hS ↦ nonempty_splitting_fdRep_of_shortExact
      ((ExactStructure.abelian_conflation _).mp hS)
  have heq : ⇑(ExactK0.fromSplitEquiv hsplit) =
      ⇑(ExactK0.fromSplitRingHom (ExactStructure.abelian (FDRep k G))) := by
    funext x
    rw [ExactK0.fromSplitEquiv_apply]
    exact (congrArg (fun f : repRing k G →+ _ ↦ f x)
      (ExactK0.fromSplitRingHom_toAddMonoidHom
        (E := ExactStructure.abelian (FDRep k G)))).symm
  exact heq ▸ (ExactK0.fromSplitEquiv hsplit).bijective

/-- The Green ring is canonically isomorphic to the exact Grothendieck ring when the group
order is invertible in the coefficient field. -/
noncomputable def repRingEquivExactK0 :
    repRing k G ≃+* ExactK0.{max u v} (ExactStructure.abelian (FDRep k G)) :=
  RingEquiv.ofBijective (ExactK0.fromSplitRingHom (ExactStructure.abelian (FDRep k G)))
    fromSplitRingHom_fdRep_bijective

/-- The ring equivalence acts by the canonical split-to-exact comparison. -/
@[simp]
theorem repRingEquivExactK0_apply (x : repRing k G) :
    repRingEquivExactK0 x = ExactK0.fromSplit (ExactStructure.abelian (FDRep k G)) x := by
  exact congrArg (fun f : repRing k G →+ _ ↦ f x)
    (ExactK0.fromSplitRingHom_toAddMonoidHom (E := ExactStructure.abelian (FDRep k G)))

/-- The inverse equivalence sends an exact class to the corresponding split class. -/
@[simp]
theorem repRingEquivExactK0_symm_of (V : FDRep k G) :
    repRingEquivExactK0.symm (ExactK0.of V) = SplitK0.of V := by
  apply repRingEquivExactK0.injective
  simp

end TauCeti
