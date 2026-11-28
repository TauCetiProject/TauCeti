/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Balanced.Basic
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Faithfulness of the Weyl group permutation action for balanced root pairings

This file proves that for any balanced root pairing `P`, the permutation action
`P.weylGroupToPerm` of the Weyl group on root indices is faithful.

## Main results

* `RootPairing.weylGroupToPerm_injective_of_isBalanced`: `P.weylGroupToPerm` is injective for any
  balanced root pairing.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §1.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N)

/-- In a balanced root pairing, the permutation action of the Weyl group on root indices is
faithful. -/
theorem weylGroupToPerm_injective_of_isBalanced [P.IsBalanced] :
    Function.Injective P.weylGroupToPerm := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro w hw
  refine weylGroup.eq_one_of_smul_eq_self fun x ↦ ?_
  have h1 : w • (P.rootSpanProj x : M) = (P.rootSpanProj x : M) :=
    P.smul_eq_self_of_mem_ker_indexHom hw (P.rootSpanProj x).property
  have h2 : w • (x - (P.rootSpanProj x : M)) = x - (P.rootSpanProj x : M) :=
    weylGroup_smul_eq_self_of_mem_corootKer (P.sub_coe_rootSpanProj_mem_corootKer x) w
  have hsum := congrArg₂ (· + ·) h1 h2
  rwa [← smul_add, add_sub_cancel] at hsum

end RootPairing
