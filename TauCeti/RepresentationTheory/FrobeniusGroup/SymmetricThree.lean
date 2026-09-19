/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.FinThree
public import TauCeti.RepresentationTheory.FrobeniusGroup

/-!
# A Frobenius group: `S₃` with complement a point stabilizer

`S₃` is the smallest Frobenius group.  It decomposes as `A₃ ⋊ ⟨(a+1 a+2)⟩`, with complement the
point stabilizer of `a` -- of order two -- and kernel the alternating subgroup, of order three;
the complement acts on the kernel without nonidentity fixed points because a transposition
inverts each of the two three-cycles, and a three-cycle is not its own inverse.

That makes `S₃` a place to run the character-theoretic construction of
`TauCeti/RepresentationTheory/FrobeniusGroup.lean` against a group whose normal complement is
already known.  The Frobenius kernel is built as the common kernel of representations affording
the extended irreducible characters of the two-element subgroup `⟨(a+1 a+2)⟩`, with no reference
to `A₃` anywhere in the construction, and it comes out equal to `A₃`
(`TauCeti.frobeniusKernelSubgroup_stabilizer_perm_fin_three`).

The two group-theoretic facts this consumes -- the complementarity and the fixed-point freeness --
are settled over the six permutations in `TauCeti/GroupTheory/Perm/FinThree.lean`, as the rest of
the description of the two subgroups of `S₃` is.  All this file adds is the passage through the
character theory.

## Main statements

* `TauCeti.isFrobeniusComplement_stabilizer_perm_fin_three`: **`S₃` is a Frobenius group** with
  complement a point stabilizer, which `TauCeti.isTISubgroup_stabilizer_perm_fin_three` records as
  a trivial-intersection subgroup.
* `TauCeti.frobeniusKernelSubgroup_stabilizer_perm_fin_three`: **the Frobenius kernel of a point
  stabilizer of `S₃` is `A₃`**, of order three by
  `TauCeti.card_frobeniusKernelSubgroup_stabilizer_perm_fin_three`.
-/

public section

namespace TauCeti

/-- **A point stabilizer of `S₃` is a trivial-intersection subgroup**, by the fixed-point-free
action of `TauCeti.isTISubgroup_of_isComplement'_of_fixedPointFree` on the alternating
complement. -/
theorem isTISubgroup_stabilizer_perm_fin_three (a : Fin 3) :
    IsTISubgroup (MulAction.stabilizer (Equiv.Perm (Fin 3)) a) :=
  isTISubgroup_of_isComplement'_of_fixedPointFree
    (isComplement'_alternatingGroup_stabilizer_perm_fin_three a)
    (conj_ne_self_of_mem_alternatingGroup_fin_three a)

/-- **`S₃` is a Frobenius group with complement a point stabilizer.**  Properness and
nontriviality come from the stabilizer not being normal, which `⊥` and `⊤` both are. -/
theorem isFrobeniusComplement_stabilizer_perm_fin_three (a : Fin 3) :
    IsFrobeniusComplement (MulAction.stabilizer (Equiv.Perm (Fin 3)) a) := by
  refine isFrobeniusComplement_of_isComplement'_of_fixedPointFree
    (isComplement'_alternatingGroup_stabilizer_perm_fin_three a) ?_ ?_
    (conj_ne_self_of_mem_alternatingGroup_fin_three a)
  · intro hbot
    refine not_normal_stabilizer_perm_fin_three a ?_
    rw [hbot]
    infer_instance
  · intro htop
    refine not_normal_stabilizer_perm_fin_three a ?_
    rw [htop]
    infer_instance

/-- **The Frobenius kernel of a point stabilizer of `S₃` is the alternating group `A₃`.**  The
kernel that the exceptional-character correspondence constructs -- as the common kernel of
representations affording the extended irreducible characters of the two-element subgroup
`⟨(a+1 a+2)⟩`, with no reference to `A₃` at all -- is the alternating subgroup that the semidirect
decomposition `S₃ = A₃ ⋊ ⟨(a+1 a+2)⟩` supplies directly. -/
theorem frobeniusKernelSubgroup_stabilizer_perm_fin_three (a : Fin 3) :
    frobeniusKernelSubgroup (isTISubgroup_stabilizer_perm_fin_three a)
      = alternatingGroup (Fin 3) :=
  frobeniusKernelSubgroup_eq_of_isComplement' _
    (isComplement'_alternatingGroup_stabilizer_perm_fin_three a)

/-- **The Frobenius kernel of a point stabilizer of `S₃` has order three.** -/
theorem card_frobeniusKernelSubgroup_stabilizer_perm_fin_three (a : Fin 3) :
    Nat.card (frobeniusKernelSubgroup (isTISubgroup_stabilizer_perm_fin_three a)) = 3 := by
  rw [frobeniusKernelSubgroup_stabilizer_perm_fin_three, card_alternatingGroup_fin_three]

end TauCeti
