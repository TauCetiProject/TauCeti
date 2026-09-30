/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Isomorphism
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Transport

/-!
# The Weyl group is an invariant of the Cartan type

Two root systems carrying bases of the same Cartan type are isomorphic as root pairings, and an
isomorphism of root pairings transports the Weyl group. Putting the two together, the Weyl group of
a root system depends only on the Cartan type of any one of its bases.

Nothing new is proved: `TauCeti.nonempty_equiv_of_hasCartanType` supplies the isomorphism and
`RootPairing.Equiv.weylGroupEquiv` transports the Weyl group along it.

## Main results

* `TauCeti.nonempty_weylGroup_mulEquiv_of_hasCartanType`: **two root systems carrying bases of the
  same Cartan type have isomorphic Weyl groups.**

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §4.
-/

public section

namespace TauCeti

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂}
  [CharZero R] [IsDomain R] [Finite ι] [Finite ι₂]
  [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
  [Q.IsRootSystem] [Q.IsCrystallographic] [Q.IsReduced]

/-- **Two root systems carrying bases of the same Cartan type have isomorphic Weyl groups.** The
Weyl group is therefore an invariant of the Dynkin type alone, so it may be computed on any one
pinned model of that type and read off on every root system of that type.

Only the existence of an isomorphism is asserted, because
`TauCeti.nonempty_equiv_of_hasCartanType` only asserts the existence of an isomorphism of root
systems: the one produced depends on the two labellings of the supports by the nodes of `t`. -/
theorem nonempty_weylGroup_mulEquiv_of_hasCartanType (b : P.Base) (b₂ : Q.Base) (t : DynkinType)
    (h : HasCartanType P b t) (h₂ : HasCartanType Q b₂ t) :
    Nonempty (RootPairing.weylGroup P ≃* RootPairing.weylGroup Q) :=
  (nonempty_equiv_of_hasCartanType b b₂ t h h₂).elim fun e ↦ ⟨e.weylGroupEquiv⟩

end TauCeti
